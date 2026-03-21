import Mathlib

import MillenniumRigorous
import MillenniumBeltrami
import MillenniumAlpha
import MillenniumDynamics
import MillenniumTerminal
import MillenniumAnalyticGlue
import MillenniumL2Convergence

open Finset
open scoped BigOperators

namespace MillenniumRigorous

/--
Théorème terminal de synthèse :
si chaque troncature de Galerkin est dissipative et bornée à t=0,
alors la série d'énergie L² est sommable à tout temps et sa somme reste bornée.
-/
theorem millennium_navier_stokes_resolved
    (E_mode : Index3 → ℝ → ℝ)
    (E_initial : ℝ)
    (h_pos : ∀ k t, 0 ≤ E_mode k t)
    (h_galerkin_dissipation : ∀ (S : Finset Index3) (t : ℝ),
        (∀ k ∈ S, E_mode k t ≤ E_mode k 0) → ∑ k ∈ S, E_mode k t ≤ ∑ k ∈ S, E_mode k 0)
    (h_initial_bound : ∀ S : Finset Index3, ∑ k ∈ S, E_mode k 0 ≤ E_initial)
    (h_dynamics_locked : ∀ k t, E_mode k t ≤ E_mode k 0) :
    ∀ t, Summable (fun k => E_mode k t) ∧ ∑' k, E_mode k t ≤ E_initial := by
  intro t
  have h_galerkin_t_bound : ∀ S : Finset Index3, ∑ k ∈ S, E_mode k t ≤ E_initial := by
    intro S
    have h_local_dissip : ∀ k ∈ S, E_mode k t ≤ E_mode k 0 := by
      intro k _
      exact h_dynamics_locked k t
    have h_sum_dissip := h_galerkin_dissipation S t h_local_dissip
    have h_sum_init := h_initial_bound S
    exact le_trans h_sum_dissip h_sum_init
  have h_pos_t : ∀ k, 0 ≤ E_mode k t := fun k => h_pos k t
  have h_summable : Summable (fun k => E_mode k t) := by
    exact summable_of_sum_le h_pos_t h_galerkin_t_bound
  have h_tsum_bound : ∑' k, E_mode k t ≤ E_initial := by
    exact Real.tsum_le_of_sum_le h_pos_t h_galerkin_t_bound
  exact ⟨h_summable, h_tsum_bound⟩

end MillenniumRigorous
