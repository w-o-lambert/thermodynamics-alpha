import ClassicalThermodynamics.Thermodynamics.MechanicalObservable
namespace ClassicalThermodynamics.Thermodynamics
class HasOsmoticPressure (Model State : Type*) where osmoticPressure : Model → State → ℝ

def osmoticPressureObservable {Model State : Type*}
    (P : HasOsmoticPressure Model State) : MechanicalObservable Model State := ⟨P.osmoticPressure⟩
end ClassicalThermodynamics.Thermodynamics
