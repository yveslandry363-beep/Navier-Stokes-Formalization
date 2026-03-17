import NavierStokes.Foundation.TorusMath
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open MeasureTheory TopologicalSpace Metric Real Complex
open Torus3 Fourier

noncomputable section

namespace FunctionalSpaces

/--
We define the fractional Sobolev norm $H^s$ on Torus3.

The norm is defined via the discrete Fourier transform coefficients.
$\|u\|_{H^s}^2 = \sum_{k \in \mathbb{Z}^3} (1 + |k|^2)^s |\hat{u}(k)|^2$.

Helper function: $(1 + |k|^2)^s$ for $k \in \mathbb{Z}^3$ and $s \in \mathbb{R}$.
-/
def sobolevWeight (s : ℝ) (k : Fin 3 → ℤ) : ℝ :=
  let norm_k_sq : ℝ := ∑ i : Fin 3, (k i : ℝ)^2
  (1 + norm_k_sq) ^ s

/--
The $H^s$ norm squared of a function $f : Torus3 \to \mathbb{C}$.

We use `tsum` (topological sum) over $\mathbb{Z}^3$.
If the sum does not converge, `tsum` returns 0 in Lean by convention,
but for functions in the space, this sum is finite.
-/
def sobolevNormSq (s : ℝ) (f : Torus3 → ℂ) : ℝ :=
  ∑' k : (Fin 3 → ℤ), (sobolevWeight s k) * Complex.normSq (fourierCoeff f k)

/-- Helper function: $e^{2\delta |k|}$. -/
def gevreyWeight (delta : ℝ) (k : Fin 3 → ℤ) : ℝ :=
  let norm_k : ℝ := Real.sqrt (∑ i : Fin 3, (k i : ℝ)^2)
  Real.exp (2 * delta * norm_k)

/--
The Gevrey norm squared of a function $f : Torus3 \to \mathbb{C}$ with radius $\delta > 0$.
-/
def gevreyNormSq (delta : ℝ) (f : Torus3 → ℂ) : ℝ :=
  ∑' k : (Fin 3 → ℤ), (gevreyWeight delta k) * Complex.normSq (fourierCoeff f k)

/--
The $L^p$ spaces on Torus3 are already available via `Lp` in Mathlib.

We explicitly define $L^6$ and $L^\infty$ for the theorem formulations later.
-/
abbrev L6Complex : Type _ := Lp ℂ 6 (volume : Measure Torus3)
abbrev LInftyComplex : Type _ := Lp ℂ ⊤ (volume : Measure Torus3)

/-
Note on Agmon and Talenti Inequalities:
Mathlib4 currently lacks the specific fractional Sobolev embedding theorems
(like $H^1 \hookrightarrow L^6$ in 3D) and Agmon's inequality
($\|u\|_{L^\infty} \le C \|u\|_{H^1}^{1/2} \|u\|_{H^2}^{1/2}$) out of the box
for `AddCircle` domains without extensive manual proofs.
To strictly respect the "No Sorry / No Hallucination" constraint,
we only declare the spaces and norms here. The proofs for these embeddings
would require a dedicated functional inequalities file built from `tsum` bounds.
-/

end FunctionalSpaces
