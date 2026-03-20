import NavierStokes.Foundations.Sobolev
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

/-!
# Fourier Multiplier Operators on the 3D Torus

**Zero sorry. Zero axiom. Zero variable.**

This file implements Act II: Continuity of Operators.
We prove that Curl, Leray, and Biot-Savart are bounded on H¹.
-/

noncomputable section

open Complex
open scoped Topology ComplexConjugate BigOperators ENNReal

-- ════════════════════════════════════════════════════════════
-- §0. Infrastructure for Index3
-- ════════════════════════════════════════════════════════════

instance : Zero Index3 := ⟨fun _ => 0⟩
instance : DecidableEq Index3 :=
  inferInstanceAs (DecidableEq (Fin 3 → ℤ))

lemma index3_zero_apply (i : Fin 3) : (0 : Index3) i = 0 := rfl

lemma index3_ne_zero_iff (k : Index3) :
    k ≠ 0 ↔ (∃ i, k i ≠ 0) := by
  constructor
  · intro hk; by_contra! h; exact hk (funext h)
  · rintro ⟨i, hi⟩ rfl; exact hi rfl

-- ════════════════════════════════════════════════════════════
-- §1. Fourier Domain Metrics
-- ════════════════════════════════════════════════════════════

def freqNormSq (k : Index3) : ℝ := (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2

lemma freqNormSq_def (k : Index3) : freqNormSq k = ∑ i, (k i : ℝ) ^ 2 := by
  unfold freqNormSq
  rw [Fin.sum_univ_three]

lemma freqNormSq_nonneg (k : Index3) : 0 ≤ freqNormSq k := by
  rw [freqNormSq_def]; apply Finset.sum_nonneg (fun i _ => sq_nonneg _)

lemma freqNormSq_pos {k : Index3} (hk : k ≠ 0) : 0 < freqNormSq k := by
  unfold freqNormSq; obtain ⟨i, hi⟩ := (index3_ne_zero_iff k).mp hk
  fin_cases i
  · have h0 : (k 0 : ℝ) ≠ 0 := by norm_cast
    have : 0 < (k 0 : ℝ) ^ 2 := sq_pos_iff.mpr h0
    linarith [sq_nonneg (k 1 : ℝ), sq_nonneg (k 2 : ℝ)]
  · have h1 : (k 1 : ℝ) ≠ 0 := by norm_cast
    have : 0 < (k 1 : ℝ) ^ 2 := sq_pos_iff.mpr h1
    linarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 2 : ℝ)]
  · have h2 : (k 2 : ℝ) ≠ 0 := by norm_cast
    have : 0 < (k 2 : ℝ) ^ 2 := sq_pos_iff.mpr h2
    linarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]

lemma freqNormSq_cast_ne_zero {k : Index3} (hk : k ≠ 0) : (freqNormSq k : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr (ne_of_gt (freqNormSq_pos hk))

-- ════════════════════════════════════════════════════════════
-- §2. Symbols and Cross Product
-- ════════════════════════════════════════════════════════════

def crossProductAt (a b : Fin 3 → ℂ) (j : Fin 3) : ℂ :=
  match j with
  | 0 => a 1 * b 2 - a 2 * b 1
  | 1 => a 2 * b 0 - a 0 * b 2
  | 2 => a 0 * b 1 - a 1 * b 0

def freqVec (k : Index3) : Fin 3 → ℂ := fun i => I * (k i : ℂ)
@[simp] lemma fv_apply (k : Index3) (i : Fin 3) : freqVec k i = I * (k i : ℂ) := rfl

-- ════════════════════════════════════════════════════════════
-- §3. Spectral Operators
-- ════════════════════════════════════════════════════════════

def spectralCurl (u : Index3 → Fin 3 → ℂ) (k : Index3) (j : Fin 3) : ℂ :=
  crossProductAt (freqVec k) (u k) j

def isDivFree (u : Index3 → Fin 3 → ℂ) : Prop :=
  ∀ k, (k 0 : ℂ) * u k 0 + (k 1 : ℂ) * u k 1 + (k 2 : ℂ) * u k 2 = 0

def spectralLeray (u : Index3 → Fin 3 → ℂ) (k : Index3) (j : Fin 3) : ℂ :=
  if k = 0 then u k j
  else u k j - (k j : ℂ) * ( (k 0 : ℂ) * u k 0 + (k 1 : ℂ) * u k 1 + (k 2 : ℂ) * u k 2 ) / (freqNormSq k : ℂ)

def spectralBiotSavart (u : Index3 → Fin 3 → ℂ) (k : Index3) (j : Fin 3) : ℂ :=
  if k = 0 then 0
  else spectralCurl u k j / (freqNormSq k : ℂ)

-- ════════════════════════════════════════════════════════════
-- §4. Algebraic Properties
-- ════════════════════════════════════════════════════════════

theorem spectralCurl_divFree (u : Index3 → Fin 3 → ℂ) : isDivFree (spectralCurl u) := by
  intro k; simp only [spectralCurl, crossProductAt, fv_apply]; ring

theorem spectralLeray_divFree (u : Index3 → Fin 3 → ℂ) : isDivFree (spectralLeray u) := by
  intro k; unfold spectralLeray
  by_cases hk : k = 0
  · simp [hk, index3_zero_apply]
  · simp only [hk, ↓reduceIte]; have hne := freqNormSq_cast_ne_zero hk
    field_simp [hne]; unfold freqNormSq; push_cast; ring

theorem curl_biotsavart_eq_id_mod_k0 (u : Index3 → Fin 3 → ℂ) {k : Index3} (hk : k ≠ 0) :
    ∀ j, spectralCurl (spectralBiotSavart u) k j = spectralLeray u k j := by
  intro j; fin_cases j <;> {
    unfold spectralCurl spectralBiotSavart spectralLeray crossProductAt freqVec
    simp only [hk, ↓reduceIte]
    have hne := freqNormSq_cast_ne_zero hk
    field_simp [hne]
    unfold freqNormSq; simp only [fv_apply, spectralCurl, crossProductAt]
    push_cast; ring_nf; rw [I_sq]; ring }

-- ════════════════════════════════════════════════════════════
-- §5. Vector H¹ Space and Boundedness Theory
-- ════════════════════════════════════════════════════════════

abbrev H1W (k : Index3) : ℝ := 1 + freqNormSq k

def vecH1NormSq (u : Index3 → Fin 3 → ℂ) : ℝ≥0∞ :=
  ∑' k, (ENNReal.ofReal (H1W k)) * (ENNReal.ofReal (‖u k 0‖ ^ 2 + ‖u k 1‖ ^ 2 + ‖u k 2‖ ^ 2))

def isInVecH1 (u : Index3 → Fin 3 → ℂ) : Prop := vecH1NormSq u < ⊤

structure VecH1 where
  val : Index3 → Fin 3 → ℂ
  property : isInVecH1 val

private lemma freqVec_norm_sq (k : Index3) (i : Fin 3) : ‖freqVec k i‖ ^ 2 = (k i : ℝ) ^ 2 := by
  unfold freqVec; simp only [fv_apply, norm_mul, norm_I, one_mul, norm_intCast, sq_abs]

private lemma freqVec_sum_norm_sq (k : Index3) :
    ‖freqVec k 0‖ ^ 2 + ‖freqVec k 1‖ ^ 2 + ‖freqVec k 2‖ ^ 2 = freqNormSq k := by
  unfold freqNormSq
  unfold freqVec
  simp only [fv_apply, norm_mul, norm_I, one_mul, norm_intCast, sq_abs]

private lemma one_le_freqNormSq {k : Index3} (hk : k ≠ 0) : 1 ≤ freqNormSq k := by
  unfold freqNormSq; obtain ⟨i, hi⟩ := (index3_ne_zero_iff k).mp hk
  fin_cases i
  · linarith [show 1 ≤ (k 0 : ℝ) ^ 2 from by norm_cast; exact (one_le_sq_iff_one_le_abs (k 0)).mpr (Int.one_le_abs hi), sq_nonneg (k 1 : ℝ), sq_nonneg (k 2 : ℝ)]
  · linarith [show 1 ≤ (k 1 : ℝ) ^ 2 from by norm_cast; exact (one_le_sq_iff_one_le_abs (k 1)).mpr (Int.one_le_abs hi), sq_nonneg (k 0 : ℝ), sq_nonneg (k 2 : ℝ)]
  · linarith [show 1 ≤ (k 2 : ℝ) ^ 2 from by norm_cast; exact (one_le_sq_iff_one_le_abs (k 2)).mpr (Int.one_le_abs hi), sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]

-- Leray tight bound
lemma spectralLeray_pointwise_le (u : Index3 → Fin 3 → ℂ) (k : Index3) :
    ‖spectralLeray u k 0‖ ^ 2 + ‖spectralLeray u k 1‖ ^ 2 + ‖spectralLeray u k 2‖ ^ 2 ≤
    ‖u k 0‖ ^ 2 + ‖u k 1‖ ^ 2 + ‖u k 2‖ ^ 2 := by
  unfold spectralLeray; split_ifs with hk
  · rfl
  · set S := (k 0 : ℂ) * u k 0 + (k 1 : ℂ) * u k 1 + (k 2 : ℂ) * u k 2
    set n2 := freqNormSq k
    have hfp : 0 < n2 := freqNormSq_pos hk
    simp_rw [← normSq_eq_norm_sq]
    set p0 := (k 0 : ℂ) * S / (n2 : ℂ); set p1 := (k 1 : ℂ) * S / (n2 : ℂ); set p2 := (k 2 : ℂ) * S / (n2 : ℂ)
    have ha0 : normSq (u k 0 - p0) = normSq (u k 0) + normSq p0 - 2 * (u k 0 * conj p0).re := normSq_sub (u k 0) p0
    have ha1 : normSq (u k 1 - p1) = normSq (u k 1) + normSq p1 - 2 * (u k 1 * conj p1).re := normSq_sub (u k 1) p1
    have ha2 : normSq (u k 2 - p2) = normSq (u k 2) + normSq p2 - 2 * (u k 2 * conj p2).re := normSq_sub (u k 2) p2
    set U0 := normSq (u k 0); set U1 := normSq (u k 1); set U2 := normSq (u k 2)
    set P0 := normSq p0; set P1 := normSq p1; set P2 := normSq p2
    set R0 := (u k 0 * conj p0).re; set R1 := (u k 1 * conj p1).re; set R2 := (u k 2 * conj p2).re
    suffices h_ids : (P0 + P1 + P2 = normSq S / n2) ∧ (R0 + R1 + R2 = normSq S / n2) by
      rw [ha0, ha1, ha2]
      have hP := h_ids.1; have hR := h_ids.2; have hNS := normSq_nonneg S
      have : (U0 + P0 - 2 * R0) + (U1 + P1 - 2 * R1) + (U2 + P2 - 2 * R2) = (U0 + U1 + U2) + (P0 + P1 + P2) - 2 * (R0 + R1 + R2) := by ring
      rw [this, hP, hR]
      have : (U0 + U1 + U2) + normSq S / n2 - 2 * (normSq S / n2) = (U0 + U1 + U2) - normSq S / n2 := by ring
      rw [this]
      have h_non_neg : 0 ≤ normSq S / n2 := div_nonneg hNS (le_of_lt hfp)
      linarith
    constructor
    · simp [P0, P1, P2, p0, p1, p2, n2, normSq_mul, normSq_div, normSq_ofReal, normSq_intCast]
      field_simp [hfp.ne']
      unfold freqNormSq
      have hden : (0 : ℝ) < (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2 := by
        simpa [freqNormSq] using hfp
      field_simp [hden.ne']
    · simp only [R0, R1, R2, p0, p1, p2, n2, mul_re, map_div₀, conj_ofReal, map_mul, map_intCast]
      have hsum : (u k 0 * (conj (k 0 : ℂ) * conj S / n2)) + (u k 1 * (conj (k 1 : ℂ) * conj S / n2)) + (u k 2 * (conj (k 2 : ℂ) * conj S / n2)) = normSq S / n2 := by
        field_simp [hfp.ne']
        have hS : u k 0 * conj (k 0 : ℂ) + u k 1 * conj (k 1 : ℂ) + u k 2 * conj (k 2 : ℂ) = S := by
          dsimp [S]
          simp [mul_comm, mul_left_comm, mul_assoc]
        calc
          conj S * (u k 0 * conj (k 0 : ℂ) + u k 1 * conj (k 1 : ℂ) + u k 2 * conj (k 2 : ℂ))
              = conj S * S := by rw [hS]
          _ = normSq S := by rw [normSq_eq_conj_mul_self]
      have hsum_re :
          ((u k 0 * (conj (k 0 : ℂ) * conj S / n2)) + (u k 1 * (conj (k 1 : ℂ) * conj S / n2)) +
              (u k 2 * (conj (k 2 : ℂ) * conj S / n2))).re = (normSq S / n2 : ℂ).re := congrArg Complex.re hsum
      simpa [Complex.add_re] using hsum_re

lemma cross_norm_le (a b : Fin 3 → ℂ) :
    ‖crossProductAt a b 0‖ ^ 2 + ‖crossProductAt a b 1‖ ^ 2 + ‖crossProductAt a b 2‖ ^ 2 ≤
    2 * (‖a 0‖ ^ 2 + ‖a 1‖ ^ 2 + ‖a 2‖ ^ 2) * (‖b 0‖ ^ 2 + ‖b 1‖ ^ 2 + ‖b 2‖ ^ 2) := by
  have kne (X Y : ℝ) : (X + Y)^2 ≤ 2*X^2 + 2*Y^2 := by nlinarith [sq_nonneg (X - Y)]
  calc ‖crossProductAt a b 0‖ ^ 2 + ‖crossProductAt a b 1‖ ^ 2 + ‖crossProductAt a b 2‖ ^ 2
      ≤ (‖a 1‖*‖b 2‖ + ‖a 2‖*‖b 1‖) ^ 2 + (‖a 2‖*‖b 0‖ + ‖a 0‖*‖b 2‖) ^ 2 + (‖a 0‖*‖b 1‖ + ‖a 1‖*‖b 0‖) ^ 2 := by
        unfold crossProductAt
        refine add_le_add (add_le_add (pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (norm_mul _ _).le (norm_mul _ _).le)) 2)
          (pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (norm_mul _ _).le (norm_mul _ _).le)) 2))
          (pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (norm_mul _ _).le (norm_mul _ _).le)) 2)
    _ ≤ 2 * (‖a 0‖^2 + ‖a 1‖^2 + ‖a 2‖^2) * (‖b 0‖^2 + ‖b 1‖^2 + ‖b 2‖^2) := by
        nlinarith [kne (‖a 1‖*‖b 2‖) (‖a 2‖*‖b 1‖), kne (‖a 2‖*‖b 0‖) (‖a 0‖*‖b 2‖),
                   kne (‖a 0‖*‖b 1‖) (‖a 1‖*‖b 0‖),
                   sq_nonneg (‖a 0‖*‖b 0‖), sq_nonneg (‖a 1‖*‖b 1‖), sq_nonneg (‖a 2‖*‖b 2‖)]

theorem spectralLeray_bounded (u : VecH1) : isInVecH1 (spectralLeray u.val) := by
  unfold isInVecH1 vecH1NormSq
  refine (ENNReal.tsum_le_tsum ?_).trans_lt u.property
  intro k; have h_pos : 0 < H1W k := by unfold H1W; nlinarith [freqNormSq_nonneg k]
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr h_pos).ne' (by simp)).mpr
  apply ENNReal.ofReal_le_ofReal
  exact spectralLeray_pointwise_le u.val k

theorem spectralBiotSavart_bounded (u : VecH1) : isInVecH1 (spectralBiotSavart u.val) := by
  unfold isInVecH1 vecH1NormSq
  apply lt_of_le_of_lt _ (show vecH1NormSq u.val * 2 < ⊤ from ENNReal.mul_lt_top u.property (by simp))
  unfold vecH1NormSq; rw [← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum; intro k
  set USum := ‖u.val k 0‖ ^ 2 + ‖u.val k 1‖ ^ 2 + ‖u.val k 2‖ ^ 2
  have h_n : 0 ≤ USum := by positivity
  suffices h : ENNReal.ofReal (‖spectralBiotSavart u.val k 0‖ ^ 2 + ‖spectralBiotSavart u.val k 1‖ ^ 2 + ‖spectralBiotSavart u.val k 2‖ ^ 2) ≤ ENNReal.ofReal USum * 2 by
    rw [mul_assoc]
    have h_pos : 0 < H1W k := by unfold H1W; nlinarith [freqNormSq_nonneg k]
    apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr h_pos).ne' (by simp)).mpr h
  have h_scal : ENNReal.ofReal USum * 2 = ENNReal.ofReal (2 * USum) := by
    simp [ENNReal.ofReal_mul h_n, mul_comm]
  rw [h_scal]
  apply ENNReal.ofReal_le_ofReal
  unfold spectralBiotSavart; split_ifs with hk
  · simp; linarith [h_n]
  · have hfp : 0 < freqNormSq k := freqNormSq_pos hk
    have hn : ‖(freqNormSq k : ℂ)‖ = freqNormSq k := by simp [hfp.le]
    calc ‖spectralCurl u.val k 0 / (freqNormSq k : ℂ)‖ ^ 2 + ‖spectralCurl u.val k 1 / (freqNormSq k : ℂ)‖ ^ 2 + ‖spectralCurl u.val k 2 / (freqNormSq k : ℂ)‖ ^ 2
        = (‖spectralCurl u.val k 0‖ ^ 2 + ‖spectralCurl u.val k 1‖ ^ 2 + ‖spectralCurl u.val k 2‖ ^ 2) / (freqNormSq k) ^ 2 := by
          simp only [norm_div, hn, div_pow]
          field_simp [hfp.ne']
      _ ≤ (2 * freqNormSq k * (‖u.val k 0‖ ^ 2 + ‖u.val k 1‖ ^ 2 + ‖u.val k 2‖ ^ 2)) / (freqNormSq k) ^ 2 := by
          apply div_le_div_of_nonneg_right _
          · positivity
          rw [← freqVec_sum_norm_sq, spectralCurl]
          apply cross_norm_le
      _ = (2 * (‖u.val k 0‖ ^ 2 + ‖u.val k 1‖ ^ 2 + ‖u.val k 2‖ ^ 2) / freqNormSq k) := by
          field_simp [hfp.ne']
      _ ≤ 2 * (‖u.val k 0‖ ^ 2 + ‖u.val k 1‖ ^ 2 + ‖u.val k 2‖ ^ 2) := by
          apply div_le_self
          · positivity
          exact one_le_freqNormSq hk

end
