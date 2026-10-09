import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Thermodynamics.Equilibrium

/-- Count of independent state variables for `components` components in
`phases` phases: one composition simplex of dimension `C - 1` per phase,
plus common temperature and pressure. -/
def phaseRuleVariableCount (components phases : ℕ) : ℤ :=
  ((components : ℤ) - 1) * (phases : ℤ) + 2

/-- Count of component-chemical-potential equalities between a reference phase
and each of the remaining phases. -/
def phaseRuleConstraintCount (components phases : ℕ) : ℤ :=
  (components : ℤ) * ((phases : ℤ) - 1)

/-- Generic degree-of-freedom count, assuming the chemical-potential
constraints are independent at the equilibrium under consideration. -/
def phaseRuleDegreesOfFreedom (components phases : ℕ) : ℤ :=
  phaseRuleVariableCount components phases -
    phaseRuleConstraintCount components phases

/-- Gibbs phase rule: under the independent-constraint count,
`F = C - P + 2`. This is a dimension count; it does not assert that every
formal combination of components and phases is physically realizable. -/
theorem gibbsPhaseRule (components phases : ℕ) :
    phaseRuleDegreesOfFreedom components phases =
      (components : ℤ) - (phases : ℤ) + 2 := by
  unfold phaseRuleDegreesOfFreedom phaseRuleVariableCount
    phaseRuleConstraintCount
  ring

/-- At fixed temperature the Gibbs phase-rule count loses one degree
of freedom. -/
lemma gibbsPhaseRule_fixedTemperature (components phases : ℕ) :
    phaseRuleDegreesOfFreedom components phases - 1 =
      (components : ℤ) - (phases : ℤ) + 1 := by
  rw [gibbsPhaseRule]
  ring

/-- At fixed temperature and pressure the Gibbs phase-rule count loses
two degrees of freedom. -/
lemma gibbsPhaseRule_fixedTemperaturePressure (components phases : ℕ) :
    phaseRuleDegreesOfFreedom components phases - 2 =
      (components : ℤ) - (phases : ℤ) := by
  rw [gibbsPhaseRule]
  ring

end ClassicalThermodynamics.Thermodynamics.Equilibrium
