import Mathlib.Basic.Real.Basic
namespace ClassicalThermodynamics.Thermodynamics

structure MechanicalObservable (Model State : Type*) where
  value : Model → State → ℝ

def MechanicalEquilibrium {Model State : Type*}
    (O : MechanicalObservable Model State) (M : Model) (a b : State) : Prop :=
  O.value M a = O.value M b

end ClassicalThermodynamics.Thermodynamics
