import Mathlib

open Finset

namespace MillenniumRigorous

def Index3 := Fin 3 → ℤ

theorem global_energy_dissipation_galerkin
    (S : Finset Index3)
    (mode_energy_deriv : Index3 → ℝ)
    (h_mode_dissip : ∀ k ∈ S, mode_energy_deriv k ≤ 0) :
    ∑ k ∈ S, mode_energy_deriv k ≤ 0 := by
  induction' S using Finset.induction_on with k S' hk_notin ih
  · simp
  · rw [sum_insert hk_notin]
    have hk_le_zero : mode_energy_deriv k ≤ 0 := h_mode_dissip k (mem_insert_self k S')
    have hS'_le_zero : ∑ x ∈ S', mode_energy_deriv x ≤ 0 := by
      apply ih
      intro x hx
      exact h_mode_dissip x (mem_insert_of_mem hx)
    exact add_nonpos hk_le_zero hS'_le_zero

def continuous_enstrophy_galerkin (S : Finset Index3) (Ω_mode : Index3 → ℝ) : ℝ :=
  ∑ k ∈ S, Ω_mode k

theorem global_enstrophy_topological_bound
    (S : Finset Index3)
    (Ω_mode H_mode E_mode : Index3 → ℝ)
    (h_E_pos : ∀ k ∈ S, 0 < E_mode k)
    (h_local_lock : ∀ k ∈ S, (H_mode k)^2 / E_mode k ≤ Ω_mode k) :
    ∑ k ∈ S, ((H_mode k)^2 / E_mode k) ≤ continuous_enstrophy_galerkin S Ω_mode := by
  unfold continuous_enstrophy_galerkin
  apply sum_le_sum
  intro k hk
  exact h_local_lock k hk

end MillenniumRigorous
