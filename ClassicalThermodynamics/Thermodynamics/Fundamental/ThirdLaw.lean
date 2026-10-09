import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Instances.Real.Lemmas

namespace ClassicalThermodynamics.Thermodynamics.Fundamental

/-- Nernst's heat theorem: for admissible equilibrium states, their entropy
difference tends to zero as the positive temperature approaches absolute zero.
This fixes entropy differences, but not a common additive residual entropy. -/
def NernstHeatTheorem {State : Type*}
    (entropy : ℝ → State → ℝ) (admissible : State → Prop) : Prop :=
  ∀ x y, admissible x → admissible y →
    Filter.Tendsto (fun T => entropy T x - entropy T y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- The entropy of a fixed state has limit `value` as positive temperature
approaches absolute zero. -/
def EntropyLimitAtZero {State : Type*}
    (entropy : ℝ → State → ℝ) (x : State) (value : ℝ) : Prop :=
  Filter.Tendsto (fun T => entropy T x)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds value)

/-- If the Nernst heat theorem holds and the zero-temperature entropy limits
exist, all admissible states have the same residual entropy. -/
theorem nernst_entropyLimits_eq
    {State : Type*} (entropy : ℝ → State → ℝ)
    (admissible : State → Prop) (x y : State) (valueX valueY : ℝ)
    (hNernst : NernstHeatTheorem entropy admissible)
    (hx : admissible x) (hy : admissible y)
    (hLimitX : EntropyLimitAtZero entropy x valueX)
    (hLimitY : EntropyLimitAtZero entropy y valueY) :
    valueX = valueY := by
  change Filter.Tendsto (fun T => entropy T x)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds valueX) at hLimitX
  change Filter.Tendsto (fun T => entropy T y)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds valueY) at hLimitY
  have hDifference :
      Filter.Tendsto (fun T => entropy T x - entropy T y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (valueX - valueY)) :=
    Filter.Tendsto.sub hLimitX hLimitY
  have hNernstDifference := hNernst x y hx hy
  have hZero : valueX - valueY = 0 :=
    tendsto_nhds_unique hDifference hNernstDifference
  linarith

end ClassicalThermodynamics.Thermodynamics.Fundamental
