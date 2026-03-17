#!/bin/bash
set -e

# Define workspace
WS_DIR=~/ns_build_final
echo "Setting up workspace in $WS_DIR"

# Clean and recreate project files, preserving .lake
mkdir -p "$WS_DIR"
cd "$WS_DIR"
rm -rf NavierStokes/
rm -f NavierStokes.lean lakefile.toml lean-toolchain lake-manifest.json
mkdir -p NavierStokes

# Copy sources from Windows mount
CP_SOURCE="/mnt/d/VS Code/NL/NL/Naveier stockes/NavierStokes"
if [ -d "$CP_SOURCE" ]; then
    cp -r "$CP_SOURCE/." "$WS_DIR/NavierStokes/"
else
    echo "Source directory not found: $CP_SOURCE"
    exit 1
fi

cd "$WS_DIR"

# Recreate config files
cat <<EOF > lakefile.toml
name = "NavierStokes"
version = "0.1.0"
keywords = ["math"]
defaultTargets = ["NavierStokes"]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.28.0"

[[lean_lib]]
name = "NavierStokes"
EOF

cat <<EOF > lean-toolchain
leanprover/lean4:v4.28.0
EOF

cat <<EOF > lake-manifest.json
{
  "version": "1.1.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {
      "url": "https://github.com/leanprover-community/mathlib4",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "8f9d9cff6bd728b17a24e163c9402775d9e6a365",
      "name": "mathlib",
      "manifestFile": "lake-manifest.json",
      "inputRev": "v4.28.0",
      "inherited": false,
      "configFile": "lakefile.lean"
    }
  ],
  "name": "NavierStokes",
  "lakeDir": ".lake"
}
EOF

cat <<EOF > NavierStokes.lean
import NavierStokes.Foundation.TorusMath
import NavierStokes.Foundation.FunctionalSpaces
import NavierStokes.Foundation.LittlewoodPaley
import NavierStokes.Foundation.SingularIntegrals
import NavierStokes.Foundation.VanDerCorput
import NavierStokes.Physics.NavierStokesEq
import NavierStokes.Physics.Helicity
import NavierStokes.Geometry.AutoLinearization
import NavierStokes.Spectral.WaleffeBasis
import NavierStokes.Spectral.HessianDegeneracy
import NavierStokes.Combinatorics.HypergraphZ3
import NavierStokes.Combinatorics.CauchyFunctional
import NavierStokes.Rigidity.PhaseRigidity
import NavierStokes.Synthesis.BonyClosure
import NavierStokes.Synthesis.GlobalRegularity
EOF

# Build
source ~/.profile
echo "Running lake update..."
lake update
echo "Running lake exe cache get..."
lake exe cache get || echo "Cache get failed, continuing with full build..."
echo "Running lake build..."
lake build
