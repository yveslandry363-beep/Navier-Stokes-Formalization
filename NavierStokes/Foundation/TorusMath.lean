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

-- Axiomatisation des propriétés linéaires standards de l'espace de Sobolev H¹
axiom h1_summable_add (u v : Torus3.L2RealVector) :
  Summable (h1Summand u) → Summable (h1Summand v) → Summable (h1Summand (u + v))

axiom h1_summable_sub (u v : Torus3.L2RealVector) :
  Summable (h1Summand u) → Summable (h1Summand v) → Summable (h1Summand (u - v))

axiom h1_summable_neg (u : Torus3.L2RealVector) :
  Summable (h1Summand u) → Summable (h1Summand (-u))

axiom h1_summable_zero : Summable (h1Summand 0)

instance : Add H1RealVector where
  add u v := ⟨u.toL2 + v.toL2, h1_summable_add u.toL2 v.toL2 u.h1_summable v.h1_summable⟩

instance : Sub H1RealVector where
  sub u v := ⟨u.toL2 - v.toL2, h1_summable_sub u.toL2 v.toL2 u.h1_summable v.h1_summable⟩

instance : Neg H1RealVector where
  neg u := ⟨-u.toL2, h1_summable_neg u.toL2 u.h1_summable⟩

instance : Zero H1RealVector where
  zero := ⟨0, h1_summable_zero⟩

instance : Norm H1RealVector where
  norm u := Real.sqrt (∑' k, h1Summand u.toL2 k)

lemma norm_def (u : H1RealVector) : norm u = Real.sqrt (∑' k, h1Summand u.toL2 k) := rfl

end H1RealVector
