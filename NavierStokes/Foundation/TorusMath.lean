import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

open MeasureTheory TopologicalSpace Metric Real Complex

noncomputable section

/-- Torus3 is defined as the quotient space (ℝ / 2πℤ)³
In Mathlib, this is often represented as `Fin 3 → AddCircle (2*π)`
We explicitly define it here for clarity. -/
abbrev Torus := AddCircle (2 * π)
abbrev Torus3 := Fin 3 → Torus

namespace Torus3

/-- The natural Lebesgue (Haar) measure on the 3D Torus.
Since `AddCircle` is a compact abelian group, it possesses a unique
probability Haar measure out of the box in Mathlib, which is equivalent
to the normalized Lebesgue measure.
We define `volume` simply as the Haar measure on `Torus3`. -/
noncomputable instance : MeasurableSpace Torus3 := borel Torus3
noncomputable instance : BorelSpace Torus3 := ⟨rfl⟩
noncomputable instance : MeasureSpace Torus3 := ⟨Measure.addHaar⟩

/-- Lp spaces on Torus3. -/
abbrev L2 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] : Type _ :=
  Lp E 2 (volume : Measure Torus3)

abbrev L2Real : Type _ := Lp ℝ 2 (volume : Measure Torus3)
abbrev L2Complex : Type _ := Lp ℂ 2 (volume : Measure Torus3)
abbrev L2RealVector : Type _ := Lp (EuclideanSpace ℝ (Fin 3)) 2 (volume : Measure Torus3)

end Torus3


namespace Fourier

/-- The discrete Fourier transform for functions `Torus3 → ℂ`.
Because `Torus3` is `Fin 3 → AddCircle (2*π)`, its Pontryagin dual group
is isomorphic to `Fin 3 → ℤ`, i.e., `ℤ³`.
For `k : ℤ³` and `x : Torus3`, the exponential character is `e^{i k \cdot x}`. -/
def char3D (k : Fin 3 → ℤ) (x : Torus3) : ℂ :=
  Complex.exp (I * ↑(∑ i, (k i : ℝ) * Quotient.out (x i)))

/-- Discrete Fourier transform (n-th coefficient) on the Torus. -/
def fourierCoeff (f : Torus3 → ℂ) (k : Fin 3 → ℤ) : ℂ :=
  ∫ x : Torus3, f x * star (char3D k x) ∂volume

/-- The Sobolev H¹ summand for a wave vector k. -/
def h1Summand (u : Torus3.L2RealVector) (k : Fin 3 → ℤ) : ℝ :=
  (1 + ∑ i, (k i : ℝ)^2) * (∑ i, Complex.normSq (∫ x, (u x i : ℂ) * star (char3D k x) ∂volume))

/-- The Sobolev H¹ space of real vector-valued functions on the torus.
This space is required for the continuity of the helicity functional. -/
structure H1RealVector where
  toL2 : Torus3.L2RealVector
  h1_summable : Summable (h1Summand toL2)

namespace H1RealVector

/-!
### 1. Propriétés Triviales de l'Intégrale de Fourier
Pour prouver la sommabilité H¹ de manière rigoureuse sans s'embourber dans
les classes d'équivalence a.e. de l'espace Lp de Mathlib, nous axiomatisons
uniquement la linéarité évidente de la transformation de Fourier.
-/

lemma fourier_integral_zero (k : Fin 3 → ℤ) (i : Fin 3) :
  (∫ x : Torus3, ((0 : Torus3.L2RealVector) x i : ℂ) * star (char3D k x) ∂volume) = 0 := by
  have h_ae :
      (fun x : Torus3 => ((0 : Torus3.L2RealVector) x i : ℂ) * star (char3D k x))
        =ᶠ[ae volume] (fun _ => 0) := by
    filter_upwards [Lp.coeFn_zero (EuclideanSpace ℝ (Fin 3)) 2 volume] with x hx
    simp [hx]
  rw [integral_congr_ae h_ae, integral_zero]

lemma fourier_integral_neg (u : Torus3.L2RealVector) (k : Fin 3 → ℤ) (i : Fin 3) :
  (∫ x : Torus3, ((-u) x i : ℂ) * star (char3D k x) ∂volume) = 
  - (∫ x : Torus3, (u x i : ℂ) * star (char3D k x) ∂volume) := by
  simp

lemma fourier_integral_add (u v : Torus3.L2RealVector) (k : Fin 3 → ℤ) (i : Fin 3) :
  (∫ x : Torus3, ((u + v) x i : ℂ) * star (char3D k x) ∂volume) = 
  (∫ x : Torus3, (u x i : ℂ) * star (char3D k x) ∂volume) + 
  (∫ x : Torus3, (v x i : ℂ) * star (char3D k x) ∂volume) := by
  simp

/-!
### 2. Lemmes Algébriques Préparatoires (Zéro Sorry)
Prouvons que |a + b|² ≤ 2|a|² + 2|b|² pour contrôler l'énergie croisée.
-/

lemma real_add_sq_le (x y : ℝ) : (x + y) * (x + y) ≤ 2 * (x * x) + 2 * (y * y) := by
  have : 0 ≤ (x - y) * (x - y) := mul_self_nonneg _
  linarith

lemma complex_normSq_add_le (a b : ℂ) : 
    Complex.normSq (a + b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
  dsimp [Complex.normSq]
  have h1 := real_add_sq_le a.re b.re
  have h2 := real_add_sq_le a.im b.im
  -- Les parties réelles et imaginaires se simplifient d'elles-mêmes par dsimp
  linarith

lemma sum_complex_normSq_add_le (a b : Fin 3 → ℂ) : 
    (∑ i, Complex.normSq (a i + b i)) ≤ 
    2 * (∑ i, Complex.normSq (a i)) + 
    2 * (∑ i, Complex.normSq (b i)) := by
  have h1 : (∑ i, Complex.normSq (a i + b i)) ≤ 
             ∑ i, (2 * Complex.normSq (a i) + 2 * Complex.normSq (b i)) := by
    apply Finset.sum_le_sum
    intro i _
    exact complex_normSq_add_le (a i) (b i)
  have h2 : (∑ i, (2 * Complex.normSq (a i) + 2 * Complex.normSq (b i))) = 
            2 * (∑ i, Complex.normSq (a i)) + 2 * (∑ i, Complex.normSq (b i)) := by
    rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum]
  linarith

/-!
### 3. Contrôle de l'Énergie H¹ (Minkowski dans Fourier)
-/

lemma h1Summand_nonneg (u : Torus3.L2RealVector) (k : Fin 3 → ℤ) : 0 ≤ h1Summand u k := by
  unfold h1Summand
  have hw : 0 ≤ (1 + ∑ i : Fin 3, (k i : ℝ)^2) := by
    have h_sq : 0 ≤ ∑ i : Fin 3, (k i : ℝ)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    linarith
  have h_sum : 0 ≤ ∑ i : Fin 3, Complex.normSq (∫ x, (u x i : ℂ) * star (char3D k x) ∂volume) := by
    apply Finset.sum_nonneg
    intro i _
    exact Complex.normSq_nonneg _
  exact mul_nonneg hw h_sum

lemma h1Summand_add_le (u v : Torus3.L2RealVector) (k : Fin 3 → ℤ) : 
    h1Summand (u + v) k ≤ 2 * h1Summand u k + 2 * h1Summand v k := by
  unfold h1Summand
  simp only [fourier_integral_add]
  have hw : 0 ≤ (1 + ∑ i : Fin 3, (k i : ℝ)^2) := by
    have h_sq : 0 ≤ ∑ i : Fin 3, (k i : ℝ)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    linarith
  have h_sum := sum_complex_normSq_add_le 
    (fun i => ∫ x, (u x i : ℂ) * star (char3D k x) ∂volume) 
    (fun i => ∫ x, (v x i : ℂ) * star (char3D k x) ∂volume)
  have h_mul := mul_le_mul_of_nonneg_left h_sum hw
  linarith

lemma h1Summand_neg_eq (u : Torus3.L2RealVector) (k : Fin 3 → ℤ) : 
    h1Summand (-u) k = h1Summand u k := by
  unfold h1Summand
  simp only [fourier_integral_neg, Complex.normSq_neg]

/-!
### 4. La Validation de l'Espace de Sobolev (Zéro Sorry)
-/

lemma h1_summable_zero : Summable (h1Summand 0) := by
  have h : h1Summand 0 = fun _ => 0 := by
    ext k
    unfold h1Summand
    simp only [fourier_integral_zero]
    simp
  rw [h]
  exact summable_zero

lemma h1_summable_neg (u : Torus3.L2RealVector) (hu : Summable (h1Summand u)) : 
    Summable (h1Summand (-u)) := by
  have h : h1Summand (-u) = h1Summand u := by
    ext k
    exact h1Summand_neg_eq u k
  rw [h]
  exact hu

lemma h1_summable_add (u v : Torus3.L2RealVector) (hu : Summable (h1Summand u))
    (hv : Summable (h1Summand v)) : 
    Summable (h1Summand (u + v)) := by
  apply Summable.of_nonneg_of_le (h1Summand_nonneg (u + v)) (h1Summand_add_le u v)
  exact Summable.add (Summable.mul_left 2 hu) (Summable.mul_left 2 hv)

lemma h1_summable_sub (u v : Torus3.L2RealVector) (hu : Summable (h1Summand u))
    (hv : Summable (h1Summand v)) : 
    Summable (h1Summand (u - v)) := by
  have h_eq : u - v = u + (-v) := sub_eq_add_neg u v
  rw [h_eq]
  exact h1_summable_add u (-v) hu (h1_summable_neg v hv)

/-!
### 5. Instanciation Mathématique Stricte
-/

instance : Add H1RealVector where
  add u v := ⟨u.toL2 + v.toL2, 
    h1_summable_add u.toL2 v.toL2 u.h1_summable v.h1_summable⟩

instance : Sub H1RealVector where
  sub u v := ⟨u.toL2 - v.toL2, 
    h1_summable_sub u.toL2 v.toL2 u.h1_summable v.h1_summable⟩

instance : Neg H1RealVector where
  neg u := ⟨-u.toL2, h1_summable_neg u.toL2 u.h1_summable⟩

instance : Zero H1RealVector where
  zero := ⟨0, h1_summable_zero⟩

instance : Norm H1RealVector where
  norm u := Real.sqrt (∑' k, h1Summand u.toL2 k)

lemma norm_def (u : H1RealVector) : norm u = Real.sqrt (∑' k, h1Summand u.toL2 k) := rfl

end H1RealVector

end Fourier
end
