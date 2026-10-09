import ClassicalThermodynamics.Models.VanDerWaals.Pure.CoexistenceObservables
import ClassicalThermodynamics.Methods.CoexistenceParametrisation.BranchAsymptotics

namespace ClassicalThermodynamics.Models.VanDerWaals.Pure

open ClassicalThermodynamics.Methods.CoexistenceParametrisation

/-- Formal critical-limit specification for the exact coexistence parametrisation. -/
def CriticalLimitSpecification : Prop :=
  Filter.Tendsto vdwGeometricMidpoint (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) ∧
  Filter.Tendsto reducedLiquidDensity (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
  Filter.Tendsto reducedGasDensity (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
  Filter.Tendsto reducedCoexistenceTemperature (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
  Filter.Tendsto reducedCoexistencePressure (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)

/-- Formal low-temperature/large-parameter specification. -/
def LowTemperatureLimitSpecification : Prop :=
  Filter.Tendsto reducedCoexistenceTemperature Filter.atTop (nhds 0) ∧
  Filter.Tendsto reducedCoexistencePressure Filter.atTop (nhds 0) ∧
  Filter.Tendsto reducedGasDensity Filter.atTop (nhds 0) ∧
  Filter.Tendsto reducedLiquidDensity Filter.atTop (nhds 3)

/-- The continuous extension has the required critical midpoint value. -/
theorem criticalMidpoint_extension_value :
    vdwGeometricMidpointWithCriticalValue 0 = 1 / 2 :=
  vdwGeometricMidpointWithCriticalValue_zero

end ClassicalThermodynamics.Models.VanDerWaals.Pure
