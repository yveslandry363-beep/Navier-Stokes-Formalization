import Mathlib.Topology.Basic
import Mathlib.Topology.Closure


open Set TopologicalSpace

variable {X : Type} [TopologicalSpace X]

lemma test_open (s : Set X) (h : IsClosed s) : IsOpen sᶜ :=
  isOpen_compl_iff.mpr h

lemma test_dense (s : Set X) (h : interior s = ∅) : Dense sᶜ :=
  (interior_eq_empty_iff_dense_compl (s := s)).mp h

