import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace HypergraphZ3

abbrev Z3 := Fin 3 → ℤ

def is_resonant (k p q : Z3) : Prop := k = p + q

def e (i : Fin 3) : Z3 := fun j => if i = j then 1 else 0

inductive IsConstructible : Z3 → Prop
  | zero : IsConstructible 0
  | base_pos (i : Fin 3) : IsConstructible (e i)
  | base_neg (i : Fin 3) : IsConstructible (-e i)
  | add (p q : Z3) (hp : IsConstructible p) (hq : IsConstructible q) : IsConstructible (p + q)

lemma constructible_axis_pos (k : ℕ) (i : Fin 3) : IsConstructible (fun j => if i = j then (k : ℤ) else 0) := by
  induction k with
  | zero =>
    have h : (fun j => if i = j then (0 : ℤ) else 0) = 0 := by ext j; split <;> rfl
    rw [h]
    exact IsConstructible.zero
  | succ n ih =>
    have h : (fun j => if i = j then ((n + 1 : ℕ) : ℤ) else 0) = 
             (fun j => if i = j then (n : ℤ) else 0) + e i := by
      ext j
      push_cast
      simp [e]
      split
      · ring
      · ring
    rw [h]
    exact IsConstructible.add _ _ ih (IsConstructible.base_pos i)

lemma constructible_axis_neg (k : ℕ) (i : Fin 3) : IsConstructible (fun j => if i = j then -(k : ℤ) else 0) := by
  induction k with
  | zero =>
    have h : (fun j => if i = j then -(0 : ℤ) else 0) = 0 := by ext j; split <;> rfl
    rw [h]
    exact IsConstructible.zero
  | succ n ih =>
    have h : (fun j => if i = j then -((n + 1 : ℕ) : ℤ) else 0) = 
             (fun j => if i = j then -(n : ℤ) else 0) + (-e i) := by
      ext j
      push_cast
      simp [e]
      split
      · ring
      · ring
    rw [h]
    exact IsConstructible.add _ _ ih (IsConstructible.base_neg i)

lemma constructible_axis (n : ℤ) (i : Fin 3) : IsConstructible (fun j => if i = j then n else 0) := by
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
