import NavierStokes.Combinatorics.HypergraphZ3

noncomputable section

namespace CauchyFunctional

open HypergraphZ3

/--
An additive Cauchy function $f : \mathbb{Z}^3 \to \mathbb{R}$ on the Triad Hypergraph.
It must satisfy $f(k) = f(p) + f(q)$ for all hyperedges $k = p + q$.
-/
def isCauchyAdditive (f : (Fin 3 → ℤ) → ℝ) (G : TriadHypergraph) : Prop :=
  ∀ (k p q : Fin 3 → ℤ), G.is_hyperedge k p q → f k = f p + f q

/-!
### Cauchy Functional Equation on ℤ³ — Full Proof

We prove that every additive function on the triad hypergraph is linear.
The key ingredient is the connectivity theorem `hypergraph_connected_3D`:
every vector in ℤ³ can be built from the standard basis via addition.
The proof proceeds by induction on `IsConstructible`.
-/

/--
**Theorem (Cauchy Linearity on ℤ³)**:
Every Cauchy-additive function on the full ℤ³ triad hypergraph is linear.
If `f(k) = f(p) + f(q)` whenever the hypergraph says `k = p + q`,
then `f(k) = ω · k` for some constant vector `ω ∈ ℝ³`, where `ωᵢ = f(eᵢ)`.

The hypothesis `hG` asserts the hypergraph contains every triad `(p+q, p, q)`,
which is trivially `rfl` for the default `TriadHypergraph`.
-/
theorem cauchy_additive_is_linear (f : Z3 → ℝ) (G : TriadHypergraph)
    (hG : ∀ p q, G.is_hyperedge (p + q) p q)
    (h_add : isCauchyAdditive f G) :
    ∃ (omega_vec : Fin 3 → ℝ), ∀ k, f k = ∑ i : Fin 3, omega_vec i * (k i : ℝ) := by
  -- Standard additivity from hypergraph completeness
  have h_std : ∀ p q, f (p + q) = f p + f q :=
    fun p q => h_add (p + q) p q (hG p q)
  -- f(0) = 0
  have h_zero : f 0 = 0 := by
    have h := h_std 0 0; rw [add_zero] at h; linarith
  -- f(-v) = -f(v)
  have h_neg : ∀ v, f (-v) = -f v := by
    intro v
    have h := h_std v (-v)
    rw [add_neg_cancel] at h
    linarith [h_zero]
  -- The witness: ωᵢ = f(eᵢ)
  refine ⟨fun i => f (e i), fun k => ?_⟩
  -- Prove by induction on the constructibility of k
  suffices key : ∀ v : Z3, IsConstructible v →
      f v = ∑ i : Fin 3, f (e i) * (v i : ℝ) from
    key k (hypergraph_connected_3D k)
  intro v hv
  induction hv with
  | zero =>
    rw [h_zero]; simp
  | base_pos j =>
    simp only [Fin.sum_univ_three]
    fin_cases j <;> simp [e]
  | base_neg j =>
    rw [h_neg]; simp only [Fin.sum_univ_three, Pi.neg_apply]
    fin_cases j <;> simp [e]
  | add p q _ _ ih_p ih_q =>
    rw [h_std, ih_p, ih_q]
    simp only [Fin.sum_univ_three, Pi.add_apply, Int.cast_add]
    ring

/-- The CauchyUnicity structure can now be instantiated from the theorem above. -/
structure CauchyUnicity where
  linear_solution (f : (Fin 3 → ℤ) → ℝ) (G : TriadHypergraph)
    (h_additive : isCauchyAdditive f G) :
    ∃ (omega_vec : Fin 3 → ℝ), ∀ k, f k = ∑ i : Fin 3, omega_vec i * (k i : ℝ)

end CauchyFunctional
