import NavierStokes.Foundations.AddCircleInstances
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# 3D Torus Foundations
This file establishes the 3D Torus as a formal measure space.
-/

noncomputable section

open Set MeasureTheory UnitAddTorus ENNReal

/-- The 3D Torus is defined as (ℝ/ℤ)³. -/
abbrev Torus3 := UnitAddTorus (Fin 3)

/-- Standard volume on Torus3. -/
instance : MeasureSpace Torus3 := 
  ⟨Measure.pi (fun _ => (volume : Measure UnitAddCircle))⟩

instance : IsProbabilityMeasure (volume : Measure Torus3) where
  measure_univ := by
    change (Measure.pi fun _ => volume) (univ : Set Torus3) = 1
    rw [Measure.pi_univ]
    simp [measure_univ]

-- Necessary Fact for toLp (p=2)
instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Fourier monomials on the 3D Torus. -/
def torusMon (k : Fin 3 → ℤ) : C(Torus3, ℂ) := mFourier k

/-- Orthnormality of Fourier monomials in L²(Torus3). -/
theorem orthonormal_torusMon : 
    Orthonormal ℂ (fun k : Fin 3 → ℤ => ContinuousMap.toLp (E := ℂ) 2 volume ℂ (torusMon k)) :=
  orthonormal_mFourier

/-- Definition of Fourier coefficients for L² functions on Torus3. -/
def torusFourierCoeff (f : Lp ℂ 2 (volume : Measure Torus3)) (k : Fin 3 → ℤ) : ℂ :=
  (mFourierBasis (d := Fin 3)).repr f k
