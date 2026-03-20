import Mathlib.Topology.Basic
import Mathlib.Topology.Closure


open Set TopologicalSpace

lemma test_open {X : Type} [TopologicalSpace X] (s : Set X) (h : IsClosed s) : IsOpen sᶜ :=
  isOpen_compl_iff.mpr h

lemma test_dense {X : Type} [TopologicalSpace X] (s : Set X) (h : interior s = ∅) : Dense sᶜ :=
  (interior_eq_empty_iff_dense_compl (s := s)).mp h

