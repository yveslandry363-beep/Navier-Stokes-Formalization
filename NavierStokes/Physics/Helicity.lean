import NavierStokes.Foundations.Torus3D
import NavierStokes.Foundations.Sobolev
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open MeasureTheory TopologicalSpace Metric Real Complex Finset
open UnitAddTorus

noncomputable section

namespace Helicity

/-- 3D Cross Product for complex vectors. -/
def crossProduct (a b : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => match i with
    | 0 => a 1 * b 2 - a 2 * b 1
    | 1 => a 2 * b 0 - a 0 * b 2
    | 2 => a 0 * b 1 - a 1 * b 0

/-- Fourier coefficients of a vector-valued L2 function. -/
def fourierCoeffVector
    (u : Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Torus3))
    (k : Index3) :
    Fin 3 → ℂ :=
  fun i => ∫ x, (u x i : ℂ) * star (torusMon k x) ∂volume

/-- The summand for the helicity bilinear form in Fourier space. -/
def helicitySummand (k : Index3) (u_hat v_hat : Fin 3 → ℂ) : ℝ :=
  (∑ i, u_hat i * star ((I : ℂ) • crossProduct (fun j => (k j : ℂ)) v_hat i)).re

/-- Continuous bilinear form associated with helicity. -/
def helicityBilinear (u v : Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Torus3)) : ℝ :=
  ∑' k : Index3, helicitySummand k (fourierCoeffVector u k) (fourierCoeffVector v k)

/-- The concrete helicity functional. -/
def helicity_functional (u : Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Torus3)) : ℝ := 
  helicityBilinear u u

/-!
### Fourier-Space Beltrami Wave Construction
-/

section FourierBeltrami

def helicitySummandOf (k : Index3) (a : Fin 3 → ℂ) : ℝ :=
  helicitySummand k a a

private def k_e1 : Index3 := fun i => if i = 0 then 1 else 0
private def bA : Fin 3 → ℂ := fun i => match i with | 0 => 0 | 1 => 1 | 2 => I
private def bA_conj : Fin 3 → ℂ := fun i => match i with | 0 => 0 | 1 => 1 | 2 => -I

lemma helicitySummand_at_e1 : helicitySummandOf k_e1 bA = 2 := by
  unfold helicitySummandOf helicitySummand crossProduct k_e1 bA
  simp [Fin.sum_univ_three, Complex.I_mul_I]
  norm_num

lemma helicitySummand_at_neg_e1 :
  helicitySummandOf (-k_e1) bA_conj = 2 := by
  unfold helicitySummandOf helicitySummand crossProduct k_e1 bA_conj
  simp [Pi.neg_apply, Fin.sum_univ_three, Complex.I_mul_I]
  norm_num

theorem beltrami_fourier_helicity_ne_zero (k : Index3) (a : Fin 3 → ℂ)
    (h_ev : crossProduct (fun i => (k i : ℂ)) a = (-I) • a) (h_u : a ≠ 0) :
    helicitySummandOf k a ≠ 0 := by
  let k_c : Fin 3 → ℂ := fun i => (k i : ℂ)
  have curl_eq : (I : ℂ) • crossProduct k_c a = a := by
    rw [h_ev]; simp [smul_smul, I_mul_I]
  have h_curl_eval : ∀ i, (I : ℂ) * crossProduct k_c a i = a i := by
    intro i; exact (congr_fun curl_eq i : _)
  unfold helicitySummandOf helicitySummand
  simp_rw [smul_eq_mul]
  have h_sum_c : ∑ i : Fin 3, a i * star ((I : ℂ) * crossProduct k_c a i) =
      ∑ i : Fin 3, (Complex.normSq (a i) : ℂ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [h_curl_eval i, Complex.star_def, Complex.mul_conj]
  rw [h_sum_c]
  simp only [Fin.sum_univ_three, Complex.add_re, Complex.ofReal_re]
  let sum_norm := Complex.normSq (a 0) + Complex.normSq (a 1) + Complex.normSq (a 2)
  have h_nz : sum_norm ≠ 0 := by
    intro h_eq
    have ha0 : a 0 = 0 := Complex.normSq_eq_zero.mp (by
      linarith [
        Complex.normSq_nonneg (a 0),
        Complex.normSq_nonneg (a 1),
        Complex.normSq_nonneg (a 2)
      ])
    have ha1 : a 1 = 0 := Complex.normSq_eq_zero.mp (by
      linarith [
        Complex.normSq_nonneg (a 0),
        Complex.normSq_nonneg (a 1),
        Complex.normSq_nonneg (a 2)
      ])
    have ha2 : a 2 = 0 := Complex.normSq_eq_zero.mp (by
      linarith [
        Complex.normSq_nonneg (a 0),
        Complex.normSq_nonneg (a 1),
        Complex.normSq_nonneg (a 2)
      ])
    have ha : a = 0 := by
      ext i; fin_cases i <;> assumption
    exact h_u ha
  exact h_nz

end FourierBeltrami

def globalHelicity
    (u : Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Torus3)) :
    ℝ :=
  helicity_functional u

def beltramiCoefficient (u_val omega_val : Fin 3 → ℝ) : ℝ :=
  let u_c : Fin 3 → ℂ := fun i => (u_val i : ℂ)
  let w_c : Fin 3 → ℂ := fun i => (omega_val i : ℂ)
  let cp := crossProduct u_c w_c
  let cp_norm := Real.sqrt (∑ i, (cp i).normSq)
  let u_norm := Real.sqrt (∑ i, (u_val i)^2)
  let w_norm := Real.sqrt (∑ i, (omega_val i)^2)
  if u_norm * w_norm = 0 then 0 else cp_norm / (u_norm * w_norm)

lemma sh_zero : helicity_functional 0 = 0 := by
  unfold helicity_functional helicityBilinear
  have h_zero : ∀ k, fourierCoeffVector 0 k = 0 := by
    intro k; ext i; unfold fourierCoeffVector
    have h_ae :
        (fun x => ((0 : Lp (EuclideanSpace ℝ (Fin 3)) 2 volume) x i : ℂ) * star (torusMon k x))
          =ᶠ[ae volume] (fun _ => 0) := by
      filter_upwards [Lp.coeFn_zero (EuclideanSpace ℝ (Fin 3)) 2 volume] with x hx
      simp
    rw [integral_congr_ae h_ae, integral_zero]; rfl
  simp [h_zero, helicitySummand]

lemma cauchy_schwarz_fin3 (a b : Fin 3 → ℂ) :
    (∑ i, (a i * star (b i)).re) ≤
    √(∑ i, Complex.normSq (a i)) * √(∑ i, Complex.normSq (b i)) := by
  let a_n : Fin 3 → ℝ := fun i => ‖a i‖
  let b_n : Fin 3 → ℝ := fun i => ‖b i‖
  have h_cs : ∑ i, a_n i * b_n i ≤ √(∑ i, a_n i ^ 2) * √(∑ i, b_n i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a_n b_n
  have h_re : (∑ i, (a i * star (b i)).re) ≤ ∑ i, a_n i * b_n i := by
    apply sum_le_sum; intro i _
    calc (a i * star (b i)).re ≤ |(a i * star (b i)).re| := le_abs_self _
      _ ≤ ‖a i * star (b i)‖ := Complex.abs_re_le_norm _
      _ = ‖a i‖ * ‖star (b i)‖ := norm_mul _ _
      _ = ‖a i‖ * ‖b i‖ := by rw [norm_star]
  simp only [Complex.normSq_eq_norm_sq]
  exact h_re.trans h_cs

lemma cross_product_bound (k a : Fin 3 → ℂ) :
    ∑ i, Complex.normSq (crossProduct k a i) ≤
    (∑ i, Complex.normSq (k i)) * (∑ i, Complex.normSq (a i)) := by
  let dot := k 0 * star (a 0) + k 1 * star (a 1) + k 2 * star (a 2)
  have h_lagrange : (∑ i, Complex.normSq (k i)) * (∑ i, Complex.normSq (a i)) =
    (∑ i, Complex.normSq (crossProduct k a i)) + Complex.normSq dot := by
    simp [dot, crossProduct, Fin.sum_univ_three, Complex.normSq_apply]
    ring
  rw [h_lagrange]
  nlinarith [Complex.normSq_nonneg dot]

end Helicity
