import NavierStokes.Foundations.Operators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# Act III: The Exact Formula for Navier-Stokes 3D

Binary-tree expansion and normal-form operators in Fourier variables.
Zero sorry. Zero axiom. Zero variable.
-/

noncomputable section

open Complex
open scoped BigOperators
open MeasureTheory

inductive BinaryTree
  | leaf : BinaryTree
  | node : BinaryTree -> BinaryTree -> BinaryTree
  deriving DecidableEq, Inhabited

namespace BinaryTree

def size : BinaryTree -> Nat
  | leaf => 1
  | node t1 t2 => size t1 + size t2

end BinaryTree

def dotInt (p q : Index3) : Int :=
  p 0 * q 0 + p 1 * q 1 + p 2 * q 2

def dotC (x y : Fin 3 -> Complex) : Complex :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

def kC (k : Index3) : Fin 3 -> Complex :=
  fun i => (k i : Complex)

def lerayApply (k : Index3) (z : Fin 3 -> Complex) : Fin 3 -> Complex :=
  if hk : k = 0 then z
  else
    let kc := kC k
    let kk := (freqNormSq k : Complex)
    fun j => z j - kc j * (dotC kc z) / kk

def bilinearSymbol (k p q : Index3) (a b : Fin 3 -> Complex) (j : Fin 3) : Complex :=
  let pc := kC p
  let qc := kC q
  let adv : Fin 3 -> Complex :=
    fun i => (dotC a qc) * b i + (dotC b pc) * a i
  (-Complex.I / 2) * lerayApply k adv j

def isResonant (p q : Index3) : Prop :=
  dotInt p q = 0

instance (p q : Index3) : Decidable (isResonant p q) :=
  inferInstanceAs (Decidable (dotInt p q = 0))

def B_nr (k p q : Index3) (a b : Fin 3 -> Complex) (j : Fin 3) : Complex :=
  if isResonant p q then 0 else bilinearSymbol k p q a b j

def B_res (k p q : Index3) (a b : Fin 3 -> Complex) (j : Fin 3) : Complex :=
  if isResonant p q then bilinearSymbol k p q a b j else 0

def laplacianSymbol (nu : Real) (k : Index3) : Complex :=
  - (nu : Complex) * (freqNormSq k : Complex)

def Qnr (nu : Real) (k p q : Index3) (a b : Fin 3 -> Complex) (j : Fin 3) : Complex :=
  if isResonant p q then 0
  else
    let gap := laplacianSymbol nu k - laplacianSymbol nu p - laplacianSymbol nu q
    2 * bilinearSymbol k p q a b j / gap

def treeAlgebraicCoeff :
    (t : BinaryTree) ->
    (Fin t.size -> Index3) ->
    (Fin t.size -> (Fin 3 -> Complex)) ->
    (Fin 3 -> Complex)
  | .leaf, _, as => as ⟨0, Nat.zero_lt_one⟩
  | .node t1 t2, ks, as =>
      let m := t1.size
      let n := t2.size
      let ks1 := fun i => ks (Fin.castAdd n i)
      let ks2 := fun i => ks (Fin.natAdd m i)
      let as1 := fun i => as (Fin.castAdd n i)
      let as2 := fun i => as (Fin.natAdd m i)
      let M1 := treeAlgebraicCoeff t1 ks1 as1
      let M2 := treeAlgebraicCoeff t2 ks2 as2
      let p : Index3 := ∑ i, ks1 i
      let q : Index3 := ∑ i, ks2 i
      let k : Index3 := p + q
      fun j => bilinearSymbol k p q M1 M2 j

def treeTimeIntegral (nu : Real) : (t : BinaryTree) -> (Fin t.size -> Index3) -> (Real -> Complex)
  | .leaf, ks, t =>
      Complex.exp
        (- (nu : Complex) * (freqNormSq (ks ⟨0, Nat.zero_lt_one⟩) : Complex) * (t : Complex))
  | .node t1 t2, ks, t =>
      let m := t1.size
      let n := t2.size
      let ks1 := fun i => ks (Fin.castAdd n i)
      let ks2 := fun i => ks (Fin.natAdd m i)
      let k : Index3 := (∑ i, ks1 i) + (∑ i, ks2 i)
      ∫ s in (0 : Real)..t,
        Complex.exp (- (nu : Complex) * (freqNormSq k : Complex) * ((t - s) : Complex)) *
          treeTimeIntegral nu t1 ks1 s * treeTimeIntegral nu t2 ks2 s

lemma dotInt_ne_zero_of_not_resonant {p q : Index3} (h : ¬ isResonant p q) :
    (dotInt p q : Real) ≠ 0 := by
  intro h0
  apply h
  exact Int.cast_eq_zero.mp h0

lemma dotInt_ne_zero_of_not_resonant_int {p q : Index3} (h : ¬ isResonant p q) :
    dotInt p q ≠ 0 := by
  intro h0
  apply h
  exact h0

lemma laplacian_gap_eq (nu : Real) (p q : Index3) :
    laplacianSymbol nu (p + q) - laplacianSymbol nu p - laplacianSymbol nu q =
      (-2 : Complex) * (nu : Complex) * (dotInt p q : Complex) := by
  unfold laplacianSymbol freqNormSq dotInt
  norm_num
  ring

lemma gap_exact_value (nu : Real) (p q : Index3) :
    laplacianSymbol nu (p + q) - laplacianSymbol nu p - laplacianSymbol nu q =
      -2 * (nu : Complex) * (dotInt p q : Complex) := by
  simpa using laplacian_gap_eq nu p q

lemma laplacian_gap_ne_zero_of_not_resonant
    (nu : Real) (hnu : nu ≠ 0) {p q : Index3} (h : ¬ isResonant p q) :
    laplacianSymbol nu (p + q) - laplacianSymbol nu p - laplacianSymbol nu q ≠ 0 := by
  rw [laplacian_gap_eq]
  apply mul_ne_zero
  · apply mul_ne_zero
    · norm_num
    · exact Complex.ofReal_ne_zero.mpr hnu
  · exact Int.cast_ne_zero.mpr (dotInt_ne_zero_of_not_resonant_int h)

lemma gap_ne_zero_of_not_resonant
    (nu : Real) (hnu : nu ≠ 0) (p q : Index3) (hres : ¬ isResonant p q) :
    laplacianSymbol nu (p + q) - laplacianSymbol nu p - laplacianSymbol nu q ≠ 0 := by
  exact laplacian_gap_ne_zero_of_not_resonant nu hnu hres

theorem homological_equation
    (nu : Real) (hnu : nu ≠ 0) (k p q : Index3) (hk : k = p + q)
    (hgap : laplacianSymbol nu k - laplacianSymbol nu p - laplacianSymbol nu q ≠ 0)
    (a b : Fin 3 -> Complex) (j : Fin 3) :
    let Q := Qnr nu k p q a b j
    let term1 := laplacianSymbol nu k * Q
    let term2 := (laplacianSymbol nu p + laplacianSymbol nu q) * Q
    term1 - term2 = 2 * B_nr k p q a b j := by
  subst hk
  by_cases hres : isResonant p q
  · simp [Qnr, B_nr, hres]
  · unfold Qnr B_nr
    simp [hres]
    have hgap2 :
        laplacianSymbol nu (p + q) + (-laplacianSymbol nu p - laplacianSymbol nu q) ≠ 0 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hgap
    field_simp [hgap2]
    ring

theorem homological_equation_unconditional
    (nu : Real) (hnu : nu ≠ 0) (k p q : Index3) (hk : k = p + q)
    (hres : ¬ isResonant p q)
    (a b : Fin 3 -> Complex) (j : Fin 3) :
    let Q := Qnr nu k p q a b j
    let term1 := laplacianSymbol nu k * Q
    let term2 := (laplacianSymbol nu p + laplacianSymbol nu q) * Q
    term1 - term2 = 2 * B_nr k p q a b j := by
  have hgap :
      laplacianSymbol nu (p + q) - laplacianSymbol nu p - laplacianSymbol nu q ≠ 0 :=
    gap_ne_zero_of_not_resonant nu hnu p q hres
  simpa [hk] using homological_equation nu hnu k p q hk (by simpa [hk] using hgap) a b j

end
