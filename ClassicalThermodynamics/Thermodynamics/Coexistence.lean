import ClassicalThermodynamics.Thermodynamics.FreeEnergyModel
namespace ClassicalThermodynamics.Thermodynamics
variable {State Model : Type*}
def Coexist (ι : Type*) [HasChemicalPotential ι State Model]
    [HasOsmoticPressure Model State] (M : Model) (a b : State) : Prop :=
  (∀ i : ι, HasChemicalPotential.chemicalPotential M a i =
      HasChemicalPotential.chemicalPotential M b i) ∧
  HasOsmoticPressure.osmoticPressure M a = HasOsmoticPressure.osmoticPressure M b
end ClassicalThermodynamics.Thermodynamics

namespace ClassicalThermodynamics.Thermodynamics
variable {iota State Model : Type*}
theorem coexist_chemicalPotential_eq [HasChemicalPotential iota State Model]
    [HasOsmoticPressure Model State] {M : Model} {a b : State}
    (h : Coexist iota M a b) : ∀ i : iota, HasChemicalPotential.chemicalPotential M a i = HasChemicalPotential.chemicalPotential M b i := h.1
theorem coexist_chemicalPotential_sub_eq_zero [HasChemicalPotential iota State Model]
    [HasOsmoticPressure Model State] {M : Model} {a b : State}
    (h : Coexist iota M a b) : ∀ i : iota, HasChemicalPotential.chemicalPotential M a i - HasChemicalPotential.chemicalPotential M b i = 0 := fun i => sub_eq_zero.mpr (h.1 i)
theorem coexist_osmoticPressure_eq [HasChemicalPotential iota State Model]
    [HasOsmoticPressure Model State] {M : Model} {a b : State}
    (h : Coexist iota M a b) : HasOsmoticPressure.osmoticPressure M a = HasOsmoticPressure.osmoticPressure M b := h.2
theorem coexist_osmoticPressure_sub_eq_zero [HasChemicalPotential iota State Model]
    [HasOsmoticPressure Model State] {M : Model} {a b : State}
    (h : Coexist iota M a b) : HasOsmoticPressure.osmoticPressure M a - HasOsmoticPressure.osmoticPressure M b = 0 := sub_eq_zero.mpr h.2
end ClassicalThermodynamics.Thermodynamics
