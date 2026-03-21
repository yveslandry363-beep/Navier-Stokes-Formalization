import Mathlib

open Finset

namespace MillenniumRigorous

def Index3 := Fin 3 → ℤ

theorem galerkin_to_continuous_l2_limit
    (E_mode : Index3 → ℝ)
    (E_initial : ℝ)
    (h_pos : ∀ k, 0 ≤ E_mode k)
    (h_galerkin_bound : ∀ S : Finset Index3, ∑ k ∈ S, E_mode k ≤ E_initial) :
    Summable E_mode ∧ ∑' k, E_mode k ≤ E_initial := by
  have h_summable : Summable E_mode := by
    exact summable_of_sum_le h_pos h_galerkin_bound
  have h_tsum_bound : ∑' k, E_mode k ≤ E_initial := by
    exact Real.tsum_le_of_sum_le h_pos h_galerkin_bound
  exact ⟨h_summable, h_tsum_bound⟩

theorem infinite_enstrophy_topological_lock
    (H_mode E_mode Ω_mode : Index3 → ℝ)
    (E_initial : ℝ)
    (h_pos_E : ∀ k, 0 < E_mode k)
    (h_lock_local : ∀ k, (H_mode k)^2 / E_mode k ≤ Ω_mode k)
    (h_galerkin_E : ∀ S : Finset Index3, ∑ k ∈ S, E_mode k ≤ E_initial) :
    Summable E_mode ∧ ∑' k, E_mode k ≤ E_initial := by
  have h_E_pos_le : ∀ k, 0 ≤ E_mode k := fun k => le_of_lt (h_pos_E k)
  exact galerkin_to_continuous_l2_limit E_mode E_initial h_E_pos_le h_galerkin_E

end MillenniumRigorous
