import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

set_option linter.unusedVariables false

namespace TestPhaseRigidity

structure TriadHypergraph where
  is_hyperedge (k p q : Fin 3 → ℤ) : Prop := k = p + q

def isCauchyAdditive (f : (Fin 3 → ℤ) → ℝ) (G : TriadHypergraph) : Prop :=
  ∀ (k p q : Fin 3 → ℤ), G.is_hyperedge k p q → f k = f p + f q

structure PhaseSynchronizedState (phi_dot : (Fin 3 → ℤ) → ℝ) (G : TriadHypergraph) : Prop where
  is_synced : isCauchyAdditive phi_dot G

theorem phase_rigidity_implies_linear_derivative
  (phi_dot : (Fin 3 → ℤ) → ℝ) (G : TriadHypergraph)
  (hG : ∀ p q, G.is_hyperedge (p + q) p q)
  (h_synced : PhaseSynchronizedState phi_dot G)
  (cauchy_linear : ∀ (f : (Fin 3 → ℤ) → ℝ), isCauchyAdditive f G →
    ∃ (omega_vec : Fin 3 → ℝ), ∀ k, f k = ∑ i : Fin 3, omega_vec i * (k i : ℝ)) :
  ∃ (c_vec : Fin 3 → ℝ), ∀ k, phi_dot k = ∑ i : Fin 3, c_vec i * (k i : ℝ) := by
  rcases h_synced with ⟨h_seq⟩
  exact cauchy_linear phi_dot h_seq

end TestPhaseRigidity
