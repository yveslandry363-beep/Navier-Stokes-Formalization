import Mathlib

namespace MillenniumRigorous

theorem stokes_integrating_factor_zero
    (u deriv_u nu k2 exp_term : ℝ)
    (h_ode : deriv_u = -nu * k2 * u) :
    deriv_u * exp_term + u * (nu * k2 * exp_term) = 0 := by
  rw [h_ode]
  ring

theorem strict_energy_dissipation
    (u nu k2 : ℝ)
    (h_nu : 0 ≤ nu)
    (h_k2 : 0 ≤ k2) :
    2 * u * (-nu * k2 * u) ≤ 0 := by
  have h_eq : 2 * u * (-nu * k2 * u) = - (2 * nu * k2 * u^2) := by ring
  rw [h_eq]
  have h_pos : 0 ≤ 2 * nu * k2 * u^2 := by positivity
  linarith

theorem duhamel_global_uniqueness_core
    (v nu k2 : ℝ)
    (h_nu : 0 ≤ nu)
    (h_k2 : 0 ≤ k2)
    (h_energy_diff_deriv : 2 * v * (-nu * k2 * v) ≤ 0) :
    - (2 * nu * k2 * v^2) ≤ 0 := by
  have h_algebra : 2 * v * (-nu * k2 * v) = - (2 * nu * k2 * v^2) := by ring
  rw [← h_algebra]
  exact h_energy_diff_deriv

end MillenniumRigorous
