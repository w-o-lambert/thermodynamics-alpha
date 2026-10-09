# Classical thermodynamics in Lean

This repository formalises mathematical foundations, thermodynamic concepts,
heterogeneous equilibria, reusable methods, bridges, and paper-facing results in
Lean 4.

## Documentation map

- [INTEGRATION_GUIDE.md](INTEGRATION_GUIDE.md) explains contribution rules,
  dependency placement, and proof-provenance requirements.
- [ARCHITECTURE.md](ARCHITECTURE.md) defines the layer structure and
  formalisation conventions.
- [AUDIT.md](AUDIT.md) records what is implemented, partial, or deferred.
- [ROADMAP.md](ROADMAP.md) lists current engineering and mathematical priorities.
- [TRACEABILITY.md](TRACEABILITY.md) maps publications to paper-facing modules.
- [REFERENCES.md](REFERENCES.md) contains bibliographic sources.

## Toolchain and build

- Lean: `leanprover/lean4:v4.34.1` (`lean-toolchain`)
- Mathlib: `v4.34.1` (`lakefile.toml`, pinned by `lake-manifest.json`)
- Build locally: `lake build`
- Continuous integration: [Lean 4.34 GitHub Actions](.github/workflows/lean-4.34.yml)

The CI workflow uses the Lean community action and Mathlib's prebuilt cache
where available. It builds the package on pushes and pull requests to
`lean-4.34`, and can also be run manually from the Actions tab.

## Package structure

```text
ClassicalThermodynamics/
├── Math/
├── Thermodynamics/
├── Models/
├── Methods/
├── Bridges/
└── Applications/
```

The intended dependency direction is:

```text
Math -> Thermodynamics -> Models -> Methods / Bridges -> Applications
```

The top-level [`ClassicalThermodynamics`](ClassicalThermodynamics.lean) imports the complete
project. [`ClassicalThermodynamics.Core`](ClassicalThermodynamics/Core.lean) provides an
additive entry point for core foundations; other aggregate modules include
[`ClassicalThermodynamics.Models`](ClassicalThermodynamics/Models.lean),
[`ClassicalThermodynamics.VanDerWaals`](ClassicalThermodynamics/VanDerWaals.lean),
[`ClassicalThermodynamics.Models.RedlichKwong`](ClassicalThermodynamics/Models/RedlichKwong.lean),
[`ClassicalThermodynamics.Methods`](ClassicalThermodynamics/Methods.lean),
[`ClassicalThermodynamics.Bridges`](ClassicalThermodynamics/Bridges.lean), and
[`ClassicalThermodynamics.Applications`](ClassicalThermodynamics/Applications.lean). Import a
specific module instead when only a narrow API is needed.

Model coverage includes ideal gases and mixtures, dilute and regular solutions,
binary real-solution Margules expansions,
pure and multicomponent Berthelot, pure and multicomponent van der Waals,
pure and multicomponent fixed-temperature Redlich--Kwong models. The multicomponent
Berthelot model reuses the van der Waals pair-attraction and linear-covolume
mixing rules while retaining Berthelot's distinct `1/T` attraction scaling.
Ideal-gas coverage also includes constant-heat-capacity energy, enthalpy, and
entropy changes, reversible isothermal work, and the logarithmic isentropic
relation.

The thermodynamic foundations also derive the Clapeyron relation from equality
of phase Gibbs potentials, the Joule-Thomson coefficient from the isenthalpic
enthalpy differential, and the Gibbs phase rule under the usual independent-
constraint assumption. The Second Law is represented by an entropy balance
with nonnegative entropy generation, from which cyclic Clausius and adiabatic
entropy results are derived. The Third Law is captured in Nernst form: entropy
differences between admissible equilibrium states vanish in the zero-temperature
limit, so any existing residual entropy limit is state-independent. Chemical
reaction equilibrium follows from Gibbs-energy stationarity with respect to
reaction extent; ideal activity-based potentials yield the logarithmic
mass-action relation and `K = exp(-ΔᵣG°/(RT))`.
The Legendre-transform foundation includes the stationary-branch derivative
rule; semistable Hessians identify zero second variation with a null direction,

## Documentation

- [Architecture and formalisation rules](ARCHITECTURE.md)
- [Formalisation audit](AUDIT.md)
- [Paper and application traceability](TRACEABILITY.md)
- [References](REFERENCES.md)
- [Current roadmap](ROADMAP.md)

The audit distinguishes proved scope from results that are partial or deferred.
A theorem recording a formula does not, by itself, establish analytic
derivative provenance; consult the Lean definitions and proofs for exact
hypotheses and dependencies.
