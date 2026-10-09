import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace ClassicalThermodynamics.Models.DiluteSolution

/-- A Henry coefficient is the positive-composition limit of fugacity divided
by solute mole fraction. The coefficient is finite because it is a real value;
the nonzero condition is retained as part of the physical coefficient data. -/
def HasHenryCoefficient
    (fugacity : ℝ → ℝ) (henryConstant : ℝ) : Prop :=
  henryConstant ≠ 0 ∧
    Filter.Tendsto (fun x => fugacity x / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds henryConstant)

/-- Henry's law is the infinite-dilution fugacity limit, not an exact
finite-composition linear relation. -/
def HenryLaw (fugacity : ℝ → ℝ) : Prop :=
  ∃ henryConstant, HasHenryCoefficient fugacity henryConstant

/-- The dilute, ideal-gas pressure form associated with a Henry coefficient.
Interpreting this as a pressure law additionally approximates fugacity by
partial pressure; the definition does not assert exact linearity at finite
composition. -/
noncomputable def henryPartialPressure (henryConstant moleFraction : ℝ) : ℝ := henryConstant * moleFraction

end ClassicalThermodynamics.Models.DiluteSolution
