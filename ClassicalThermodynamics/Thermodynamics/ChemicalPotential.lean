import ClassicalThermodynamics.Thermodynamics.FreeEnergy
namespace ClassicalThermodynamics.Thermodynamics
class HasChemicalPotential (iota State Model : Type*) where
  chemicalPotential : Model -> State -> iota -> Real
end ClassicalThermodynamics.Thermodynamics
