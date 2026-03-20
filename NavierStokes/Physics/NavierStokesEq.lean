import NavierStokes.Foundations.Torus3D
import NavierStokes.Foundations.Sobolev
import NavierStokes.Physics.Helicity
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory TopologicalSpace Metric Real Complex
open UnitAddTorus

noncomputable section

namespace NavierStokesEq

/-- Le Projecteur de Leray en Fourier. 
P_k(w) = w - k (k · w) / |k|² -/
def lerayProjector (k : Index3) (w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  if k = 0 then 0 else
    let k_c : Fin 3 → ℂ := fun i => (k i : ℂ)
    let norm_k_sq : ℂ := ∑ i, k_c i * k_c i
    let dot := ∑ i, k_c i * w i
    fun i => w i - (dot / norm_k_sq) * k_c i

/-- Le terme intérieur de la convolution triadique pour le vecteur d'onde k. -/
def triadicSummand (u_hat v_hat : Index3 → Fin 3 → ℂ) (k p : Index3) : Fin 3 → ℂ :=
  let q := k - p
  let dot_u_q := ∑ i, u_hat p i * (q i : ℂ)
  fun i => (I : ℂ) * dot_u_q * v_hat q i

/-- L'Opérateur Bilinéaire de Convection B(u,v) = P(u · ∇ v) évalué au mode de Fourier k. -/
def convectionOperator (u v : Index3 → Fin 3 → ℂ) (k : Index3) : Fin 3 → ℂ :=
  let raw_sum := ∑' p, triadicSummand u v k p
  lerayProjector k raw_sum

/-- La définition dynamique absolue d'un fluide de Navier-Stokes. -/
structure NavierStokesFlow where
  u : ℝ → (Index3 → Fin 3 → ℂ) -- amplitudes in Fourier space
  nu : ℝ
  nu_pos : nu > 0
  evolution : ∀ (t : ℝ) (k : Index3),
    let k_sq := ∑ i, ((k i : ℝ) : ℂ) ^ 2
    let u_k := fun s => u s k
    let dissipation := - ((nu : ℂ) * k_sq) • u_k t
    let convection := convectionOperator (u t) (u t) k
    HasDerivAt u_k (dissipation - convection) t

/-- Le véritable terme de Vortex Stretching dynamique. -/
def dynamic_vortex_stretching (flow : NavierStokesFlow) (t : ℝ) : ℝ :=
  (∑' k : Index3, 
    let u_k := flow.u t k
    let conv_k := convectionOperator (flow.u t) (flow.u t) k
    let omega_k := (I : ℂ) • Helicity.crossProduct (fun i => (k i : ℂ)) u_k
    let curl_conv_k := (I : ℂ) • Helicity.crossProduct (fun i => (k i : ℂ)) conv_k
    (∑ i, omega_k i * star (curl_conv_k i)).re)

end NavierStokesEq
