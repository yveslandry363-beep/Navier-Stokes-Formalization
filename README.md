# Navier-Stokes Formalization: Topological Constraints & Alpha Exponent

[![Lean 4 Build](https://github.com/yveslandry363-beep/Navier-Stokes-Formalization/actions/workflows/lean.yml/badge.svg)](https://github.com/yveslandry363-beep/Navier-Stokes-Formalization/actions/workflows/lean.yml)

## Abstract
This repository contains a formal verification in **Lean 4** of the topological constraints governing the 3D incompressible Navier-Stokes equations. The core of the project is the analytical extraction of the geometric exponent $\alpha$ and the proof that helicity conservation prevents isotropic blow-up scenarios.

## Key Formalized Results
*   **Helicity Conservation:** Formalized as a topological invariant $H = \int u \cdot \omega \, dx$.
*   **Biot-Savart Continuity:** $L^2 \to H^1$ mapping via Fourier multiplier analysis.
*   **Alpha Lower Bound:** Proof by contradiction that an isotropic collapse with $\alpha < 1/2$ violates the conservation of helicity.
*   **Auto-Linearization:** Derivation of the alignment decay $\beta(u) \le H \cdot \Omega^{-2}$ from kinematic constraints.

## Project Structure
*   `NavierStokes/Physics/`: Core physical laws (Helicity, AlphaBound, Navier-Stokes Eq).
*   `NavierStokes/Foundation/`: Mathematical bedrock (Torus Geometry, Fourier Analysis).
*   `NavierStokes/Geometry/`: Alignment functionals and auto-linearization.

## How to Build
To verify the proofs locally, ensure you have [Elan](https://github.com/leanprover/elan) installed:

```bash
# Clone the repository
git clone [https://github.com/yveslandry363-beep/Navier-Stokes-Formalization.git](https://github.com/yveslandry363-beep/Navier-Stokes-Formalization.git)
cd Navier-Stokes-Formalization

# Fetch dependencies and Mathlib cache
lake exe cache get
lake build