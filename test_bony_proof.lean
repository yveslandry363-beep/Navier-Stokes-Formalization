import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt

open Real

def geometric_gain_summable : Prop :=
  Summable (fun (j : ℕ) => (2 : ℝ) ^ (- (j : ℝ) / 2))

lemma geometric_gain_converges : geometric_gain_summable := by
  unfold geometric_gain_summable
  have h_eq : (fun (j : ℕ) => (2 : ℝ) ^ (- (j : ℝ) / 2)) = (fun (j : ℕ) => ((2 : ℝ) ^ (- (1 / 2 : ℝ))) ^ j) := by
    ext j
    have h1 : - (j : ℝ) / 2 = (- (1 / 2 : ℝ)) * (j : ℝ) := by ring
    rw [h1]
    rw [Real.rpow_mul (by norm_num)]
    exact Real.rpow_natCast _ _
  rw [h_eq]
  apply summable_geometric_of_lt_one
  · exact Real.rpow_nonneg (by norm_num) _
  · have h2 : (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by norm_num
    rw [h2]
    rw [Real.rpow_lt_rpow_left_iff (by norm_num)]
    norm_num
