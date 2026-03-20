import NavierStokes.Foundations.Torus3D
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# 3D Torus Sobolev Spaces
This file defines the H¹ Sobolev space on the 3D Torus using spectral properties.
-/

noncomputable section

open MeasureTheory UnitAddTorus RCLike
open scoped Topology ComplexConjugate

abbrev Index3 := Fin 3 → ℤ

instance : DecidableEq Index3 :=
  inferInstanceAs (DecidableEq (Fin 3 → ℤ))

instance : Zero Index3 := Pi.instZero
instance : Add Index3 := Pi.instAdd
instance : Neg Index3 := Pi.instNeg
instance : AddCommGroup Index3 := Pi.addCommGroup

def h1Weight (k : Index3) : ℝ :=
  1 + ‖(fun i => (k i : ℝ) : Fin 3 → ℝ)‖ ^ 2

lemma h1Weight_pos (k : Index3) : 0 < h1Weight k := by
  unfold h1Weight; positivity

def h1_carrier : Submodule ℂ (Index3 → ℂ) where
  carrier := { f | Summable (fun k => h1Weight k * ‖f k‖ ^ 2) }
  zero_mem' := by simp [summable_zero]
  add_mem' {f g} hf hg := by
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (le_of_lt (h1Weight_pos k)) (sq_nonneg _))
    · intro k
      have hN := norm_add_le (f k) (g k)
      have hW := le_of_lt (h1Weight_pos k)
      have key : ‖f k + g k‖ ^ 2 ≤ 2 * ‖f k‖ ^ 2 + 2 * ‖g k‖ ^ 2 := by
        have h2 : ‖f k + g k‖ ^ 2 ≤ (‖f k‖ + ‖g k‖) ^ 2 :=
          sq_le_sq' (by linarith [norm_nonneg (f k + g k)]) hN
        nlinarith [sq_nonneg (‖f k‖ - ‖g k‖)]
      calc h1Weight k * ‖f k + g k‖ ^ 2
          ≤ h1Weight k * (2 * ‖f k‖ ^ 2 + 2 * ‖g k‖ ^ 2) :=
            mul_le_mul_of_nonneg_left key hW
        _ = 2 * (h1Weight k * ‖f k‖ ^ 2) +
            2 * (h1Weight k * ‖g k‖ ^ 2) := by ring
    · exact (hf.mul_left 2).add (hg.mul_left 2)
  smul_mem' c f hf := by
    simp only [Set.mem_setOf_eq, Pi.smul_apply, norm_smul, mul_pow] at *
    have : (fun k => h1Weight k * (‖c‖ ^ 2 * ‖f k‖ ^ 2)) =
           fun k => ‖c‖ ^ 2 * (h1Weight k * ‖f k‖ ^ 2) := by ext; ring
    rw [this]; exact hf.mul_left _

def SobolevH1 := ↥h1_carrier

namespace SobolevH1

instance : AddCommGroup SobolevH1 := Submodule.addCommGroup h1_carrier
instance : Module ℂ SobolevH1 := Submodule.module h1_carrier

/-- The weighted inner product term. -/
def inner_sum (f g : SobolevH1) (k : Index3) : ℂ :=
  (h1Weight k : ℂ) * (starRingEnd ℂ (f.val k) * g.val k)

/-- The h1-weighted inner product terms are norm-summable. -/
lemma inner_norm_summable (f g : SobolevH1) :
    Summable (fun k => ‖inner_sum f g k‖) := by
  have h_le : ∀ k, ‖inner_sum f g k‖ ≤
      1 / 2 * (h1Weight k * ‖f.val k‖ ^ 2) +
      1 / 2 * (h1Weight k * ‖g.val k‖ ^ 2) := by
    intro k
    unfold inner_sum
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    have hw : ‖(h1Weight k : ℂ)‖ = h1Weight k := by
      simp [Complex.norm_real, abs_of_pos (h1Weight_pos k)]
    rw [hw]
    nlinarith [sq_nonneg (‖f.val k‖ - ‖g.val k‖),
               h1Weight_pos k, norm_nonneg (f.val k),
               norm_nonneg (g.val k)]
  exact Summable.of_nonneg_of_le
    (fun k => norm_nonneg _) h_le
    ((f.property.mul_left (1/2)).add (g.property.mul_left (1/2)))

/-- The h1-weighted inner product terms are summable. -/
lemma inner_summable' (f g : SobolevH1) : Summable (inner_sum f g) :=
  Summable.of_norm (inner_norm_summable f g)

/-- The H¹ inner product. -/
def H1Inner (f g : SobolevH1) : ℂ := ∑' k, inner_sum f g k

/-- Each term re(inner_sum f f k) = h1Weight k * ‖f.val k‖² -/
lemma re_inner_sum_self (f : SobolevH1) (k : Index3) :
    re (inner_sum f f k) = h1Weight k * ‖f.val k‖ ^ 2 := by
  unfold inner_sum
  erw [re_ofReal_mul]
  congr 1
  rw [starRingEnd_apply, star_def, RCLike.conj_mul]
  norm_cast

/-- Core inner product structure for SobolevH1. -/
def h1InnerCore : InnerProductSpace.Core ℂ SobolevH1 where
  inner := H1Inner
  conj_inner_symm f g := by
    simp only [H1Inner]
    have hs := (inner_summable' g f).hasSum.map
      (starRingEnd ℂ) continuous_star
    have h_eq : (starRingEnd ℂ ∘ inner_sum g f) = inner_sum f g := by
      ext k; unfold inner_sum; simp only [Function.comp]
      rw [map_mul (starRingEnd ℂ), map_mul (starRingEnd ℂ),
          starRingEnd_self_apply,
          show starRingEnd ℂ (↑(h1Weight k) : ℂ) = ↑(h1Weight k) from RCLike.conj_ofReal _]
      ring
    rw [← hs.tsum_eq, h_eq]
  re_inner_nonneg f := by
    simp only [H1Inner]
    have hs := (inner_summable' f f).hasSum.map
      (re : ℂ →+ ℝ) RCLike.continuous_re
    rw [← hs.tsum_eq]
    apply tsum_nonneg; intro k
    change 0 ≤ re (inner_sum f f k)
    rw [re_inner_sum_self]
    exact mul_nonneg (le_of_lt (h1Weight_pos k)) (sq_nonneg _)
  add_left f g h := by
    simp only [H1Inner]
    rw [← ((inner_summable' f h).hasSum.add
            (inner_summable' g h).hasSum).tsum_eq]
    apply tsum_congr; intro k
    unfold inner_sum
    have : (f + g).val k = f.val k + g.val k := rfl
    rw [this, map_add]; ring
  smul_left f g c := by
    simp only [H1Inner]
    have h_eq : ∀ k, (c • f).inner_sum g k =
        starRingEnd ℂ c * inner_sum f g k := by
      intro k; unfold inner_sum
      have : (c • f).val k = c * f.val k := rfl
      rw [this, map_mul]; ring
    rw [show (∑' k, (c • f).inner_sum g k) =
         ∑' k, starRingEnd ℂ c * inner_sum f g k from
      tsum_congr h_eq]
    rw [tsum_mul_left]
  definite f hf := by
    have h_re_zero : re (H1Inner f f) = 0 := by
      rw [hf, map_zero]
    rw [H1Inner] at h_re_zero
    have hs := (inner_summable' f f).hasSum.map
      (re : ℂ →+ ℝ) RCLike.continuous_re
    have h_re_tsum : tsum (re ∘ inner_sum f f) = 0 := by
      rw [hs.tsum_eq]; exact h_re_zero
    have h_re_eq : re ∘ inner_sum f f =
        fun k => h1Weight k * ‖f.val k‖ ^ 2 := by
      ext k; exact re_inner_sum_self f k
    rw [h_re_eq] at h_re_tsum
    have h_pos : ∀ j, 0 ≤ h1Weight j * ‖f.val j‖ ^ 2 :=
      fun j => mul_nonneg (le_of_lt (h1Weight_pos j)) (sq_nonneg _)
    have h_summable_real : Summable (fun k => h1Weight k * ‖f.val k‖ ^ 2) := by
      rw [← h_re_eq]; exact hs.summable
    have h_each_zero : ∀ k, f.val k = 0 := by
      intro k
      have h_le := Summable.sum_le_tsum (s := {k})
        (fun j _ => h_pos j) h_summable_real
      rw [Finset.sum_singleton, h_re_tsum] at h_le
      have h_val : h1Weight k * ‖f.val k‖ ^ 2 = 0 :=
        le_antisymm h_le (h_pos k)
      have := (mul_eq_zero.mp h_val).resolve_left
        (ne_of_gt (h1Weight_pos k))
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp this)
    exact Subtype.ext (funext h_each_zero)

-- Register Core as local instance (mirrors Defs.lean:552)
attribute [local instance] h1InnerCore

instance : Inner ℂ SobolevH1 :=
  InnerProductSpace.Core.toInner' (𝕜 := ℂ) (F := SobolevH1)

instance : SeminormedAddCommGroup SobolevH1 :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ) (F := SobolevH1)

instance : InnerProductSpace ℂ SobolevH1 :=
  InnerProductSpace.ofCore h1InnerCore.toCore

end SobolevH1
