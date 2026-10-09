import ClassicalThermodynamics.Thermodynamics.Coexistence

namespace ClassicalThermodynamics.Thermodynamics

variable {ι State Model κ : Type*}

/-- A finite family of phases coexists when every pair has identical chemical
potentials and osmotic pressure. -/
def MultiphaseCoexist [HasChemicalPotential ι State Model]
    [HasOsmoticPressure Model State]
    (M : Model) (phase : κ → State) : Prop :=
  ∀ K L, Coexist ι M (phase K) (phase L)

/-- Pairwise coexistence is the two-phase instance of multiphase coexistence. -/
theorem multiphaseCoexist_fin_two_iff
    [HasChemicalPotential ι State Model]
    [HasOsmoticPressure Model State]
    (M : Model) (a b : State) :
    MultiphaseCoexist (ι := ι) M (![a, b] : Fin 2 → State) ↔ Coexist ι M a b := by
  constructor
  · intro h
    exact h 0 1
  · intro hab K L
    fin_cases K <;> fin_cases L
    · exact ⟨fun _ => rfl, rfl⟩
    · exact hab
    · exact ⟨fun i => (hab.1 i).symm, hab.2.symm⟩
    · exact ⟨fun _ => rfl, rfl⟩

/-- It suffices to compare every phase with one selected reference phase. -/
theorem multiphaseCoexist_iff_reference
    [HasChemicalPotential ι State Model]
    [HasOsmoticPressure Model State]
    (M : Model) (phase : κ → State) (r : κ) :
    MultiphaseCoexist (ι := ι) M phase ↔ ∀ K, Coexist ι M (phase K) (phase r) := by
  constructor
  · intro h K
    exact h K r
  · intro h K L
    constructor
    · intro i
      calc
        HasChemicalPotential.chemicalPotential M (phase K) i =
            HasChemicalPotential.chemicalPotential M (phase r) i := (h K).1 i
        _ = HasChemicalPotential.chemicalPotential M (phase L) i := ((h L).1 i).symm
    · calc
        HasOsmoticPressure.osmoticPressure M (phase K) =
            HasOsmoticPressure.osmoticPressure M (phase r) := (h K).2
        _ = HasOsmoticPressure.osmoticPressure M (phase L) := (h L).2.symm

end ClassicalThermodynamics.Thermodynamics
