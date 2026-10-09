import ClassicalThermodynamics.Thermodynamics.MechanicalObservable
namespace ClassicalThermodynamics.Thermodynamics
structure HasPressure (Model State : Type*) where pressure : Model → State → ℝ

def pressureObservable {Model State : Type*}
    (P : HasPressure Model State) : MechanicalObservable Model State := ⟨P.pressure⟩
end ClassicalThermodynamics.Thermodynamics
