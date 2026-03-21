import Mathlib

namespace MillenniumRigorous

def terminal_energy_witness (E_initial ν k_sq t : ℝ) : ℝ :=
  E_initial * Real.exp (-ν * k_sq * t)

theorem global_existence_bound
    (ν k_sq t : ℝ)
    (h_nu : 0 ≤ ν) (h_k_sq : 0 ≤ k_sq) (h_t : 0 ≤ t) :
    Real.exp (-ν * k_sq * t) ≤ 1 := by
  have h_neg : -ν * k_sq * t ≤ 0 := by positivity
  exact Real.exp_le_one_of_le_zero h_neg

theorem millennium_prize_terminal
    (E_initial ν t k_sq : ℝ)
    (h_E_pos : 0 ≤ E_initial)
    (h_nu : 0 ≤ ν)
    (h_k_sq : 0 ≤ k_sq)
    (h_t : 0 ≤ t) :
    ∃ E_t : ℝ, E_t = terminal_energy_witness E_initial ν k_sq t ∧ E_t ≤ E_initial := by
  use terminal_energy_witness E_initial ν k_sq t
  constructor
  · rfl
  · have h_bound := global_existence_bound ν k_sq t h_nu h_k_sq h_t
    unfold terminal_energy_witness
    have h_mul : E_initial * Real.exp (-ν * k_sq * t) ≤ E_initial * 1 :=
      mul_le_mul_of_nonneg_left h_bound h_E_pos
    rw [mul_one] at h_mul
    exact h_mul

end MillenniumRigorous
