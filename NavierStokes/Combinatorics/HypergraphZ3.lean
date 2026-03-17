import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace HypergraphZ3

/-- Z3 is the 3D integer lattice -/
abbrev Z3 := Fin 3 → ℤ

/-- The resonance condition for a triad: k = p + q -/
def is_resonant (k p q : Z3) : Prop :=
  k = p + q

/--
The Triad Hypergraph $\mathcal{G}(\mathbb{Z}^3)$.
A hyperedge exists between nodes $k, p, q \in \mathbb{Z}^3$ if $k = p + q$.
This graph describes the exact resonant nonlinear energy transfer channels
in the discrete Fourier space.
-/
structure TriadHypergraph where
  /-- A hyperedge is a set of 3 nodes sum-constrained. -/
  is_hyperedge (k p q : Fin 3 → ℤ) : Prop :=
    k = p + q

/-- The standard basis vectors for Z3 -/
def e (i : Fin 3) : Z3 :=
  fun j => if i = j then 1 else 0

/--
A vector is constructible if it can be generated from the standard basis
and their opposites via the resonance condition.
-/
inductive IsConstructible : Z3 → Prop
  | zero : IsConstructible 0
  | base_pos (i : Fin 3) : IsConstructible (e i)
  | base_neg (i : Fin 3) : IsConstructible (-e i)
  | add (p q : Z3) (hp : IsConstructible p) (hq : IsConstructible q) : IsConstructible (p + q)

/--
To establish the methodology cleanly, we demonstrate
1D connectiveness on ℤ first, avoiding any 'sorry'.
-/
inductive IsConstructible1D : ℤ → Prop
  | zero : IsConstructible1D 0
  | base_pos : IsConstructible1D 1
  | base_neg : IsConstructible1D (-1)
  | add (p q : ℤ) (hp : IsConstructible1D p) (hq : IsConstructible1D q) : IsConstructible1D (p + q)

lemma hypergraph_connected_1D_pos (k : ℕ) : IsConstructible1D (k : ℤ) := by
  induction k with
  | zero => exact IsConstructible1D.zero
  | succ n ih =>
    have h : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; rfl
    rw [h]
    exact IsConstructible1D.add (n : ℤ) 1 ih IsConstructible1D.base_pos

lemma hypergraph_connected_1D_neg (k : ℕ) : IsConstructible1D (-(k : ℤ)) := by
  induction k with
  | zero =>
    have h : -((0 : ℕ) : ℤ) = 0 := by rfl
    rw [h]
    exact IsConstructible1D.zero
  | succ n ih =>
    have h : -((n + 1 : ℕ) : ℤ) = -(n : ℤ) + (-1) := by push_cast; ring
    rw [h]
    exact IsConstructible1D.add (-(n : ℤ)) (-1) ih IsConstructible1D.base_neg

lemma hypergraph_connected_1D (k : ℤ) : IsConstructible1D k := by
  cases k with
  | ofNat n => exact hypergraph_connected_1D_pos n
  | negSucc n =>
    have h : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := rfl
    rw [h]
    exact hypergraph_connected_1D_neg (n + 1)

/-
Extension to 3D: We prove that any vector k ∈ Z3 is constructible.
We do this by showing each component along an axis is constructible,
and then adding them together.
-/

lemma constructible_axis_pos (k : ℕ) (i : Fin 3) :
  IsConstructible (fun j => if i = j then (k : ℤ) else 0) := by
  induction k with
  | zero =>
    have h : (fun j => if i = j then ((0 : ℕ) : ℤ) else 0) = 0 := by ext j; split_ifs <;> rfl
    rw [h]
    exact IsConstructible.zero
  | succ n ih =>
    have h : (fun j => if i = j then ((n + 1 : ℕ) : ℤ) else 0) =
             (fun j => if i = j then (n : ℤ) else 0) + e i := by
      ext j
      push_cast
      simp [e]
      split_ifs
      · ring
      · ring
    rw [h]
    exact IsConstructible.add _ _ ih (IsConstructible.base_pos i)

lemma constructible_axis_neg (k : ℕ) (i : Fin 3) :
  IsConstructible (fun j => if i = j then -(k : ℤ) else 0) := by
  induction k with
  | zero =>
    have h : (fun j => if i = j then -((0 : ℕ) : ℤ) else 0) = 0 := by ext j; split_ifs <;> rfl
    rw [h]
    exact IsConstructible.zero
  | succ n ih =>
    have h : (fun j => if i = j then -((n + 1 : ℕ) : ℤ) else 0) =
             (fun j => if i = j then -(n : ℤ) else 0) + (-e i) := by
      ext j
      push_cast
      simp [e]
      split_ifs
      · ring
      · ring
    rw [h]
    exact IsConstructible.add _ _ ih (IsConstructible.base_neg i)

lemma constructible_axis (n : ℤ) (i : Fin 3) :
  IsConstructible (fun j => if i = j then n else 0) := by
  cases n with
  | ofNat k => exact constructible_axis_pos k i
  | negSucc k =>
    have h : Int.negSucc k = -((k + 1 : ℕ) : ℤ) := rfl
    rw [h]
    exact constructible_axis_neg (k + 1) i

theorem hypergraph_connected_3D (k : Z3) : IsConstructible k := by
  have h_decomp : k = (fun j => if 0 = j then k 0 else 0) +
                      (fun j => if 1 = j then k 1 else 0) +
                      (fun j => if 2 = j then k 2 else 0) := by
    ext x
    fin_cases x <;> simp
  rw [h_decomp]
  apply IsConstructible.add
  · apply IsConstructible.add
    · exact constructible_axis (k 0) 0
    · exact constructible_axis (k 1) 1
  · exact constructible_axis (k 2) 2

end HypergraphZ3
