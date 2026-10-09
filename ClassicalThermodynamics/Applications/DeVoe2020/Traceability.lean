import ClassicalThermodynamics.Applications.DeVoe2020.Thermodynamics
import ClassicalThermodynamics.Applications.DeVoe2020.ClassicalRelations
import ClassicalThermodynamics.Applications.DeVoe2020.ChemicalEquilibrium
import ClassicalThermodynamics.Applications.DeVoe2020.Models
import ClassicalThermodynamics.Applications.DeVoe2020.Coexistence
import ClassicalThermodynamics.Applications.DeVoe2020.Extensivity

/-!
# DeVoe (2020) traceability

Equation wrappers for Howard DeVoe, *Thermodynamics and Chemistry*, second
edition, 2020.

The current coverage includes thermodynamic potentials and their differentials,
Maxwell relations, selected Second- and Third-Law statements, classical
thermodynamic relations, reaction equilibrium, the Gibbs phase rule, the
Euler and Gibbs-Duhem relations, the chemical-potential equality clause for
multicomponent coexistence, and selected ideal-gas, ideal-mixture,
regular-solution, and dilute-solution equations. Each wrapper inherits the
scope and assumptions documented beside it; a source citation is not by itself
a derivation of any unformalized physical premise.

The ideal-gas process coverage pins reversible isothermal work to Eq. (3.5.1)
and the integrated constant-heat-capacity internal-energy change to Eq.
(3.5.3). Isothermal energy invariance and `Q = W` are exposed as consequences
of that relation and the process first-law balance. The adiabatic work result
is likewise a first-law consequence, not a separately numbered source
equation. Eq. (4.5.4) now has both a weak general-process wrapper and a strict
irreversible-process wrapper; strictness is represented by positive internal
entropy generation.

## Deliberate scope limits

- DeVoe's Henry-law equations (9.4.14)-(9.4.15) state the limiting fugacity
  relation as the solute mole fraction tends to zero. The repository now
  represents Henry's law as this infinite-dilution limit in
  `Models.DiluteSolution.Henry`. Its `henryPartialPressure` expression is the
  dilute ideal-gas pressure form, not an assertion of exact finite-composition
  linearity. Fugacity-to-pressure replacement remains a separate gas-phase
  approximation.
- The Chapter 12 coexistence wrapper records only equality of component
  chemical potentials. It does not pin the repository's additional osmotic-
  pressure equality to DeVoe's ordinary-pressure condition, nor does it
  formalize the common-temperature requirement. In the ACS Omega 2021a
  polymer-mixture setting, Equation (10) separately relates osmotic pressure
  to solvent mixing chemical potential when the same nonzero solvent partial
  molar volume applies in both phases.
- The Section 5.5 extensivity wrappers preserve the assumptions of the
  canonical formalization: Euler uses one-homogeneity and a conjugate-variable
  differential, while Gibbs-Duhem uses the differential Euler relation and
  first law as explicit premises.
- The current ideal-gas barometric-height equation and the generic
  activity-based reaction-quotient theorem are not mapped to a numbered
  DeVoe equation in this application.
- The constant-heat-capacity ideal-gas entropy-change specializations and
  isentropic logarithmic relation in the model layer are not yet mapped to
  specific DeVoe equation numbers.
- The Le Chatelier sign predicate is conceptual rather than an equation-level
  result in this source, so it is not presented as a numbered-equation wrapper.
- The Third-Law wrapper retains an abstract admissibility predicate. DeVoe's
  Eq. (6.0.1) specifically concerns pure, perfectly ordered crystals.

See `TRACEABILITY.md` for the application index.
-/

namespace ClassicalThermodynamics.Applications.DeVoe2020

end ClassicalThermodynamics.Applications.DeVoe2020
