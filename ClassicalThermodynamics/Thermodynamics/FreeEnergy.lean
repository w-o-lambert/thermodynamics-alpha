import Mathlib.Basic.Real.Basic
namespace ClassicalThermodynamics.Thermodynamics
structure FreeEnergyModel (State : Type*) where
  admissible : State -> Prop
  freeEnergy : State -> Real
end ClassicalThermodynamics.Thermodynamics
