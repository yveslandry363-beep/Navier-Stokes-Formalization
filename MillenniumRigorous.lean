import Mathlib

open Finset

namespace MillenniumRigorous

def Index3 := Fin 3 → ℤ

def dot (v w : Fin 3 → ℂ) : ℂ := ∑ i, v i * w i

def normSq (k : Index3) : ℂ := ∑ i, (k i : ℂ) * (k i : ℂ)

def spectralLeray (v : Fin 3 → ℂ) (k : Index3) : Fin 3 → ℂ :=
  if h : normSq k = 0 then v
  else fun i => v i - (k i : ℂ) * (dot (fun j => (k j : ℂ)) v) / normSq k

theorem leray_annihilates_gradient (k : Index3) (c : ℂ) (hk : normSq k ≠ 0) :
    ∀ i, spectralLeray (fun j => c * (k j : ℂ)) k i = 0 := by
  intro i
  unfold spectralLeray
  split_ifs with h0
  · exact (False.elim (hk h0))
  · have h_dot : dot (fun j => (k j : ℂ)) (fun j => c * (k j : ℂ)) = c * normSq k := by
      unfold dot normSq
      rw [← mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    rw [h_dot]
    have h_div : (c * normSq k) / normSq k = c := by
      exact mul_div_cancel_right₀ c hk
    rw [h_div]
    ring

def simoH_factorial_term (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-t) * (t ^ n / (Nat.factorial n : ℝ))

theorem simoH_factorial_summable_intrinsic (t : ℝ) :
    Summable (fun n => simoH_factorial_term t n) := by
  unfold simoH_factorial_term
  apply Summable.mul_left (Real.exp (-t))
  exact Real.summable_pow_div_factorial t

end MillenniumRigorous
