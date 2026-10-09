import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Thermodynamics

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι Phase : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite multiphase coexistence. -/
def MultiphaseCoexist (M : Model (ι := ι))
    (phase : Phase → State (ι := ι)) : Prop :=
  ∀ K L, Coexist M (phase K) (phase L)

/-- Pairwise coexistence is symmetric. -/
theorem coexist_symm {κ : Type*} [Fintype κ]
    (M : Model (ι := κ)) {a b : State (ι := κ)} :
    Coexist M a b → Coexist M b a := by
  intro h
  exact ⟨h.1.symm, fun i => (h.2 i).symm⟩

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
