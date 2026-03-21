import Mathlib

namespace MillenniumRigorous

theorem lagrange_identity_3d (u0 u1 u2 w0 w1 w2 : ℝ) :
    (u0^2 + u1^2 + u2^2) * (w0^2 + w1^2 + w2^2) - (u0*w0 + u1*w1 + u2*w2)^2 =
    (u0*w1 - u1*w0)^2 + (u0*w2 - u2*w0)^2 + (u1*w2 - u2*w1)^2 := by
  ring

theorem cauchy_schwarz_3d (u0 u1 u2 w0 w1 w2 : ℝ) :
    (u0*w0 + u1*w1 + u2*w2)^2 ≤ (u0^2 + u1^2 + u2^2) * (w0^2 + w1^2 + w2^2) := by
  have h_lagrange := lagrange_identity_3d u0 u1 u2 w0 w1 w2
  have h_pos : 0 ≤ (u0*w1 - u1*w0)^2 + (u0*w2 - u2*w0)^2 + (u1*w2 - u2*w1)^2 := by
    positivity
  linarith

def energy_mode (u : Fin 3 → ℝ) : ℝ := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2

def enstrophy_mode (ω : Fin 3 → ℝ) : ℝ := ω 0 ^ 2 + ω 1 ^ 2 + ω 2 ^ 2

def helicity_mode (u ω : Fin 3 → ℝ) : ℝ := u 0 * ω 0 + u 1 * ω 1 + u 2 * ω 2

theorem helicity_bounded_by_energy_enstrophy (u ω : Fin 3 → ℝ) :
    (helicity_mode u ω) ^ 2 ≤ (energy_mode u) * (enstrophy_mode ω) := by
  unfold helicity_mode energy_mode enstrophy_mode
  exact cauchy_schwarz_3d (u 0) (u 1) (u 2) (ω 0) (ω 1) (ω 2)

theorem topological_alpha_bound
    (H_min E_max Ω : ℝ)
    (h_H : 0 < H_min)
    (h_E : 0 < E_max)
    (h_lock : H_min^2 ≤ E_max * Ω) :
    (H_min^2 / E_max) ≤ Ω := by
  exact (div_le_iff₀ h_E).mpr h_lock

end MillenniumRigorous
