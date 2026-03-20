import Mathlib.Analysis.Fourier.AddCircle

/-!
# Global Instances for UnitAddCircle
Mathlib's `AddCircleMulti.lean` uses local instances for `UnitAddCircle`.
This file exports them globally so that `UnitAddTorus` (the product) can 
automatically resolve topological and measure-theoretic instances.
-/

noncomputable section

open MeasureTheory

/-- Haar measure on the unit circle as the default volume. -/
instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The unit circle is a probability measure space. -/
instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
