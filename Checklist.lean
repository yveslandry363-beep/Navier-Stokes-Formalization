import NavierStokes.Synthesis.GlobalRegularity
import NavierStokes.Physics.AlphaBound
import NavierStokes.Rigidity.PhaseRigidity

/-!
Phase gate checklist (baseline):
- Audit axioms for core synthesis lemmas.
- Track interim theorem while final global regularity theorem is rebuilt.
-/

#print axioms GlobalRegularity.helicity_bounded
#print axioms GlobalRegularity.helicity_continuous
#print axioms GlobalRegularity.navier_stokes_h1_bounded_under_assumptions
#print axioms NavierStokes.anisotropic_helicity_scaling_bound
#print axioms PhaseRigidity.phase_rigidity_implies_linear_derivative
