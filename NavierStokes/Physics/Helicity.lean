import NavierStokes.Foundation.TorusMath
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open MeasureTheory TopologicalSpace Metric Real Complex Finset
open Torus3 Fourier

noncomputable section

namespace Helicity

/-- 3D Cross Product for complex vectors. -/
def crossProduct (a b : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => match i with
    | 0 => a 1 * b 2 - a 2 * b 1
    | 1 => a 2 * b 0 - a 0 * b 2
    | 2 => a 0 * b 1 - a 1 * b 0

/-- Fourier coefficients of a vector-valued L2 function. -/
def fourierCoeffVector (u : Torus3.L2RealVector) (k : Fin 3 → ℤ) : Fin 3 → ℂ :=
  fun i => ∫ x, (u x i : ℂ) * star (Fourier.char3D k x) ∂volume

/-- The summand for the helicity bilinear form in Fourier space. -/
def helicitySummand (k : Fin 3 → ℤ) (u_hat v_hat : Fin 3 → ℂ) : ℝ :=
  (∑ i, u_hat i * star ((I : ℂ) • crossProduct (fun j => (k j : ℂ)) v_hat i)).re

/-- Continuous bilinear form associated with helicity. -/
def helicityBilinear (u v : Torus3.L2RealVector) : ℝ :=
  ∑' k : Fin 3 → ℤ, helicitySummand k (fourierCoeffVector u k) (fourierCoeffVector v k)

/--
The concrete helicity functional: $H(u) = \int_{\mathbb{T}^3} u \cdot (\nabla \times u) \, dx$.
In Fourier space, this is
$\sum_{k \in \mathbb{Z}^3} \hat{u}(k) \cdot \overline{i k \times \hat{u}(k)}$.
-/
def helicity_functional (u : Torus3.L2RealVector) : ℝ := helicityBilinear u u

/-!
### Fourier-Space Beltrami Wave Construction
-/

section FourierBeltrami

def helicitySummandOf (k : Fin 3 → ℤ) (a : Fin 3 → ℂ) : ℝ :=
  helicitySummand k a a

private def k_e1 : Fin 3 → ℤ := fun i => if i = 0 then 1 else 0
private def bA : Fin 3 → ℂ := fun i => match i with | 0 => 0 | 1 => 1 | 2 => I
private def bA_conj : Fin 3 → ℂ := fun i => match i with | 0 => 0 | 1 => 1 | 2 => -I

lemma helicitySummand_at_e1 : helicitySummandOf k_e1 bA = 2 := by
  unfold helicitySummandOf helicitySummand crossProduct k_e1 bA
  simp [Fin.sum_univ_three, Complex.I_mul_I]
  norm_num

lemma helicitySummand_at_neg_e1 : helicitySummandOf (-k_e1) bA_conj = 2 := by
  unfold helicitySummandOf helicitySummand crossProduct k_e1 bA_conj
  simp [Pi.neg_apply, Fin.sum_univ_three, Complex.I_mul_I]
  norm_num

theorem beltrami_fourier_helicity_ne_zero (k : Fin 3 → ℤ) (a : Fin 3 → ℂ)
    (h_ev : crossProduct (fun i => (k i : ℂ)) a = (-I) • a) (h_u : a ≠ 0) :
    helicitySummandOf k a ≠ 0 := by
  let k_c : Fin 3 → ℂ := fun i => (k i : ℂ)
  have curl_eq : (I : ℂ) • crossProduct k_c a = a := by
    rw [h_ev]; simp [smul_smul, I_mul_I]
  have h_curl_eval : ∀ i, (I : ℂ) * crossProduct k_c a i = a i := by
    intro i; exact congr_fun curl_eq i
  unfold helicitySummandOf helicitySummand
  simp_rw [smul_eq_mul]
  have h_sum_c : ∑ i : Fin 3, a i * star ((I : ℂ) * crossProduct k_c a i) =
      ∑ i : Fin 3, (Complex.normSq (a i) : ℂ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [h_curl_eval i, Complex.star_def, Complex.mul_conj]
  rw [h_sum_c]
  simp only [Fin.sum_univ_three, Complex.add_re, Complex.ofReal_re]
  let sum_norm := Complex.normSq (a 0) + Complex.normSq (a 1) + Complex.normSq (a 2)
  have h_nz : sum_norm ≠ 0 := by
    intro h_eq
    have hn0 := Complex.normSq_nonneg (a 0)
    have hn1 := Complex.normSq_nonneg (a 1)
    have hn2 := Complex.normSq_nonneg (a 2)
    have h0 : Complex.normSq (a 0) = 0 := by linarith
    have h1 : Complex.normSq (a 1) = 0 := by linarith
    have h2 : Complex.normSq (a 2) = 0 := by linarith
    have ha0 : a 0 = 0 := Complex.normSq_eq_zero.mp h0
    have ha1 : a 1 = 0 := Complex.normSq_eq_zero.mp h1
    have ha2 : a 2 = 0 := Complex.normSq_eq_zero.mp h2
    have ha : a = 0 := by
      ext i
      fin_cases i
      · exact ha0
      · exact ha1
      · exact ha2
    exact h_u ha
  exact h_nz

end FourierBeltrami

def globalHelicity (u : Torus3.L2RealVector) : ℝ := helicity_functional u

def beltramiCoefficient (u_val omega_val : Fin 3 → ℝ) : ℝ :=
  let u_c : Fin 3 → ℂ := fun i => (u_val i : ℂ)
  let w_c : Fin 3 → ℂ := fun i => (omega_val i : ℂ)
  let cp := crossProduct u_c w_c
  let cp_norm := Real.sqrt (∑ i, (cp i).normSq)
  let u_norm := Real.sqrt (∑ i, (u_val i)^2)
  let w_norm := Real.sqrt (∑ i, (omega_val i)^2)
  if u_norm * w_norm = 0 then 0 else cp_norm / (u_norm * w_norm)

/-- L'hélicité d'un fluide au repos est strictement nulle. -/
lemma sh_zero : helicity_functional 0 = 0 := by
  unfold helicity_functional helicityBilinear
  have h_zero : ∀ k, fourierCoeffVector 0 k = 0 := by
    intro k; ext i; unfold fourierCoeffVector
    have h_ae : (fun x => ((0 : Torus3.L2RealVector) x i : ℂ) * star (Fourier.char3D k x))
        =ᶠ[ae volume] (fun _ => 0) := by
      filter_upwards [Lp.coeFn_zero (EuclideanSpace ℝ (Fin 3)) 2 volume] with x hx
      have h_eval : ((0 : Torus3.L2RealVector) x i : ℂ) = 0 := by rw [hx]; rfl
      rw [h_eval, zero_mul]
    rw [integral_congr_ae h_ae, integral_zero]; rfl
  have h_bilin_zero : ∀ v, helicityBilinear 0 v = 0 := by
    intro v; unfold helicityBilinear
    simp_rw [h_zero]
    have h_inner : ∀ k, helicitySummand k 0 (fourierCoeffVector v k) = 0 := by
      intro k; unfold helicitySummand; simp
    simp_rw [h_inner]
    exact tsum_zero
  exact h_bilin_zero 0

/-- Cauchy-Schwarz sur C^3 réduit à l'inégalité réelle via l'identite discrete. -/
lemma cauchy_schwarz_fin3 (a b : Fin 3 → ℂ) :
    (∑ i, (a i * star (b i)).re) ≤
    √(∑ i, Complex.normSq (a i)) * √(∑ i, Complex.normSq (b i)) := by
  let a_n : Fin 3 → ℝ := fun i => ‖a i‖
  let b_n : Fin 3 → ℝ := fun i => ‖b i‖
  have h_cs : ∑ i, a_n i * b_n i ≤ √(∑ i, a_n i ^ 2) * √(∑ i, b_n i ^ 2) := by
    exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a_n b_n
  have h_re : (∑ i, (a i * star (b i)).re) ≤ ∑ i, a_n i * b_n i := by
    apply sum_le_sum; intro i _
    calc (a i * star (b i)).re ≤ |(a i * star (b i)).re| := le_abs_self _
      _ ≤ ‖a i * star (b i)‖ := Complex.abs_re_le_norm _
      _ = ‖a i‖ * ‖star (b i)‖ := norm_mul _ _
      _ = ‖a i‖ * ‖b i‖ := by rw [norm_star]
  simp only [Complex.normSq_eq_norm_sq]
  exact h_re.trans h_cs

/-- Lagrange identity for cross product bound in C^3. -/
lemma cross_product_bound (k a : Fin 3 → ℂ) :
    ∑ i, Complex.normSq (crossProduct k a i) ≤
    (∑ i, Complex.normSq (k i)) * (∑ i, Complex.normSq (a i)) := by
  let dot := k 0 * star (a 0) + k 1 * star (a 1) + k 2 * star (a 2)
  have h_lagrange : (∑ i, Complex.normSq (k i)) * (∑ i, Complex.normSq (a i)) =
    (∑ i, Complex.normSq (crossProduct k a i)) + Complex.normSq dot := by
    simp [dot, crossProduct, Fin.sum_univ_three, Complex.normSq_apply]
    ring
  rw [h_lagrange]
  nlinarith [Complex.normSq_nonneg dot]

end Helicity
