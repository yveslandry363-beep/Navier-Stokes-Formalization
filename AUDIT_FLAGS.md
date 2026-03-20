# Full Lean Audit (project files only)

## D:\VS Code\NL\NL\Naveier stockes\NavierStokes\Foundation\TorusMath.lean
- L169: lemma h1_summable_neg (u : Torus3.L2RealVector) (hu : Summable (h1Summand u)) :
- L177: lemma h1_summable_add (u v : Torus3.L2RealVector) (hu : Summable (h1Summand u))
- L183: lemma h1_summable_sub (u v : Torus3.L2RealVector) (hu : Summable (h1Summand u))

## D:\VS Code\NL\NL\Naveier stockes\NavierStokes\Foundations\ExactFormula.lean
- L117: lemma dotInt_ne_zero_of_not_resonant {p q : Index3} (h : Â¬ isResonant p q) :

## D:\VS Code\NL\NL\Naveier stockes\NavierStokes\Foundations\Operators.lean
- L60: lemma freqNormSq_pos {k : Index3} (hk : k â‰  0) : 0 < freqNormSq k := by
- L73: lemma freqNormSq_cast_ne_zero {k : Index3} (hk : k â‰  0) : (freqNormSq k : â„‚) â‰  0 :=
- L121: theorem curl_biotsavart_eq_id_mod_k0 (u : Index3 â†’ Fin 3 â†’ â„‚) {k : Index3} (hk : k â‰  0) :

## D:\VS Code\NL\NL\Naveier stockes\NavierStokes\Geometry\AutoLinearization.lean
- L69: lemma bound_chain (a b c d : â„) (hb : 0 â‰¤ b) (h1 : a â‰¤ b * c) (h2 : c â‰¤ d) :
- L78: lemma beta_decay_analytic (u : H1RealVector) (hE : enstrophy u > 1) :
- L97: theorem subcritical_stretching_growth_analytic (u : H1RealVector) (hE : enstrophy u > 1) :

## D:\VS Code\NL\NL\Naveier stockes\NavierStokes\Physics\AlphaBound.lean
- L81: lemma arbitrarily_small (C p H_abs : â„) (hp : p > 0) (hH : H_abs > 0) (hC : C > 0) :
- L96: lemma rpow_algebra (Î´ alpha : â„) (h : Î´ > 0) : Î´ * Î´ ^ (-alpha) = Î´ ^ (1 - alpha) := by

## D:\VS Code\NL\NL\Naveier stockes\NavierStokes\Physics\TopologicalLock.lean
- L23: lemma arbitrarily_small (C p H_abs : â„) (hp : p > 0) (hH : H_abs > 0) (hC : C > 0) :

## D:\VS Code\NL\NL\Naveier stockes\NavierStokes\Rigidity\PhaseRigidity.lean
- L50: lemma energy_decay_in_rigid_wave (wave : RigidTravelingWave) (nu : â„) (hnu : nu > 0) :

## D:\VS Code\NL\NL\Naveier stockes\NavierStokes\Synthesis\GlobalRegularity.lean
- L59: lemma biot_savart_gain_estimate (k : Index3) (omega_hat : Fin 3 â†’ â„‚) (hk : k â‰  0) :

## D:\VS Code\NL\NL\Naveier stockes\test_density_lemmas.lean
- L7: lemma test_open {X : Type} [TopologicalSpace X] (s : Set X) (h : IsClosed s) : IsOpen sá¶œ :=
- L10: lemma test_dense {X : Type} [TopologicalSpace X] (s : Set X) (h : interior s = âˆ…) : Dense sá¶œ :=
