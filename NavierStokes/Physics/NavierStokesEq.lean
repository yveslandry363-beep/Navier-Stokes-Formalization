import NavierStokes.Foundation.TorusMath
import NavierStokes.Physics.Helicity
import NavierStokes.Foundation.SingularIntegrals
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory TopologicalSpace Metric Real Complex
open Torus3 Fourier Helicity

noncomputable section

namespace NavierStokesEq

/-- Le Projecteur de Leray en Fourier. 
Il projette un vecteur champ sur l'espace des champs à divergence nulle.
P_k(w) = w - k (k · w) / |k|² -/
def lerayProjector (k : Fin 3 → ℤ) (w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  if k = 0 then 0 else
    let k_c : Fin 3 → ℂ := fun i => (k i : ℂ)
    let norm_k_sq : ℂ := ∑ i, k_c i * k_c i
    let dot := ∑ i, k_c i * w i
    fun i => w i - (dot / norm_k_sq) * k_c i

/-- Le terme intérieur de la convolution triadique pour le vecteur d'onde k.
Pour k = p + q, on évalue i * (u_p · q) * v_q -/
def triadicSummand (u_hat v_hat : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k p : Fin 3 → ℤ) : Fin 3 → ℂ :=
  let q := fun i => k i - p i
  -- Produit scalaire u_p · q
  let dot_u_q := ∑ i, u_hat p i * (q i : ℂ)
  -- Vecteur résultant
  fun i => (I : ℂ) * dot_u_q * v_hat q i

/-- L'Opérateur Bilinéaire de Convection B(u,v) = P(u · ∇ v) évalué au mode de Fourier k.
C'est la véritable non-linéarité des équations de Navier-Stokes. -/
def convectionOperator (u v : H1RealVector) (k : Fin 3 → ℤ) : Fin 3 → ℂ :=
  let u_hat := fourierCoeffVector u.toL2
  let v_hat := fourierCoeffVector v.toL2
  -- La somme infinie sur tous les modes p
  let raw_sum := ∑' p, triadicSummand u_hat v_hat k p
  -- Projection de Leray pour éliminer le gradient de pression
  lerayProjector k raw_sum

/-- La définition dynamique absolue d'un fluide de Navier-Stokes.
Une trajectoire temporelle dans l'espace de Sobolev H1 qui respecte 
strictement l'équation d'évolution de Navier-Stokes en espace de Fourier. -/
structure NavierStokesFlow where
  -- Le champ de vitesse en fonction du temps
  u : ℝ → H1RealVector
  -- La viscosité cinématique (strictement positive)
  nu : ℝ
  nu_pos : nu > 0
  -- L'équation d'évolution dynamique sur chaque mode de Fourier k
  -- (Dérivée temporelle = Dissipation visqueuse + Convection non-linéaire)
  evolution : ∀ (t : ℝ) (k : Fin 3 → ℤ),
    let k_sq := ∑ i, ((k i : ℝ) : ℂ) ^ 2
    let u_k := fun s => fourierCoeffVector (u s).toL2 k
    let dissipation := - ((nu : ℂ) * k_sq) • u_k t
    let convection := convectionOperator (u t) (u t) k
    HasDerivAt u_k (dissipation - convection) t

/-- Le véritable terme de Vortex Stretching dynamique.
Il est défini comme le transfert d'énergie de l'enstrophie généré EXCLUSIVEMENT 
par l'opérateur de convection bilinéaire au temps t. -/
def dynamic_vortex_stretching (flow : NavierStokesFlow) (t : ℝ) : ℝ :=
  -- La somme de Fourier de (k x u_k) · (k x convection_k)
  (∑' k : Fin 3 → ℤ, 
    let u_k := fourierCoeffVector (flow.u t).toL2 k
    let conv_k := convectionOperator (flow.u t) (flow.u t) k
    let omega_k := (I : ℂ) • crossProduct (fun i => (k i : ℂ)) u_k
    let curl_conv_k := (I : ℂ) • crossProduct (fun i => (k i : ℂ)) conv_k
    (∑ i, omega_k i * star (curl_conv_k i)).re)

end NavierStokesEq
