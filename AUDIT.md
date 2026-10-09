# Reduced repository audit

## Scope

This alpha branch contains the shared thermodynamic foundations and the model
families retained for current development:

- ideal gases and ideal mixtures;
- dilute, regular, and real-solution foundations;
- pure and multicomponent van der Waals;
- pure and multicomponent Berthelot;
- pure and multicomponent Redlich--Kwong;
- generic thermodynamic differentials, equilibrium, stability, and extensivity;
- retained paper-facing applications for the models above.

Shared van der Waals and thermodynamic
foundations were retained even where a historical name or identity refers to
an expansion of a van der Waals expression.

## Retained model coverage

| Model family | Free energy / equation of state | Thermodynamic consequences | Provenance status |
|---|---|---|---|
| Ideal gas and ideal mixtures | Implemented | Implemented for caloric, process, solution, and equilibrium results | Core model API |
| Dilute, regular, and real solutions | Implemented | Implemented for retained solution laws and consequences | Model-level results |
| Pure van der Waals | Implemented | Criticality, coexistence, response, and density identities | Partial derivative provenance |
| van der Waals mixture | Implemented | Stability, coexistence, fixed-composition, and density identities | Coordinate and Frechet certificates |
| Pure Berthelot | Implemented | Equation-of-state and thermodynamic consequences | Model-level provenance |
| Berthelot mixture | Implemented | Thermodynamics, fixed-composition, and derivative consequences | Standalone mixture provenance |
| Pure Redlich--Kwong | Implemented | Fixed-temperature Helmholtz, chemical potential, and pressure identity | No higher derivative claims |
| Redlich--Kwong mixture | Implemented | Fixed-temperature Helmholtz, chemical potential, pressure, and coexistence surface | Pressure identity/provenance follow-up |

## Shared foundations

The retained core includes:

- thermodynamic potentials and Legendre identities;
- coordinate and directional derivative infrastructure;
- Maxwell, Clapeyron, Joule--Thomson, Euler, and Gibbs--Duhem results;
- equilibrium, reaction, phase-rule, and second-law results;
- Hessian, local-stability, and critical-direction interfaces;
- generic finite-component extensivity and Frechet-transfer infrastructure;
- matrix, spectral, affine, projective, cocycle, and reflection mathematics used
  by retained applications.

## Classification policy

Scientific model results, reusable thermodynamic identities, stability,
criticality, coexistence, and public provenance certificates remain
`theorem`. Local algebra, coordinate expansions, symmetry, positivity,
matrix transport, and derivative plumbing are classified as `lemma`.

## Validation

The reduced aggregate is validated with the pinned Lean 4.34.1 toolchain.
Regenerate `MANIFEST.txt` and `LEAN_SOURCE_INVENTORY.txt` after source changes,
then run:

```powershell
powershell.exe -ExecutionPolicy Bypass -File scripts/check_documentation.ps1 -Write
powershell.exe -ExecutionPolicy Bypass -File scripts/check_documentation.ps1
lake build ClassicalThermodynamics
```

The documentation checker must pass, and no `sorry`, `admit`, or new axioms
are permitted.
