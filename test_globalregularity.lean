import Mathlib.Topology.Baire.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Closure

set_option linter.unusedVariables false

open TopologicalSpace Set Metric

noncomputable section

namespace TestGlobalRegularity

section TestHelicityTopology

variable {FluidSpace : Type} [MetricSpace FluidSpace]
variable (helicity_functional : FluidSpace → ℝ)
variable (helicity_continuous : Continuous helicity_functional)
variable (helicity_perturbation :
  ∀ (u : FluidSpace) (ε : ℝ), ε > 0 → ∃ v : FluidSpace, dist u v < ε ∧ helicity_functional v ≠ 0)

def H_zero_set : Set FluidSpace := { u | helicity_functional u = 0 }

lemma H_zero_is_closed : IsClosed (H_zero_set helicity_functional) :=
  isClosed_eq helicity_continuous continuous_const

lemma H_zero_empty_interior : interior (H_zero_set helicity_functional) = ∅ := by
  ext u
  refine ⟨fun hu => ?_, fun h => h.elim⟩
  rcases mem_interior.mp hu with ⟨s, hs_subset, hs_open, hu_s⟩
  rcases Metric.isOpen_iff.mp hs_open u hu_s with ⟨ε, hε, hball⟩
  rcases helicity_perturbation u ε hε with ⟨v, hv_dist, hv_helicity⟩
  have hv_in_s : v ∈ s := hball (by rw [mem_ball, dist_comm]; exact hv_dist)
  exact hv_helicity (hs_subset hv_in_s)

theorem H_nonzero_is_open : IsOpen (H_zero_set helicity_functional)ᶜ :=
  isOpen_compl_iff.mpr (H_zero_is_closed helicity_functional helicity_continuous)

theorem H_nonzero_is_dense : Dense (H_zero_set helicity_functional)ᶜ :=
  (interior_eq_empty_iff_dense_compl (s := H_zero_set helicity_functional)).mp
    (H_zero_empty_interior helicity_functional helicity_perturbation)

end TestHelicityTopology

end TestGlobalRegularity
