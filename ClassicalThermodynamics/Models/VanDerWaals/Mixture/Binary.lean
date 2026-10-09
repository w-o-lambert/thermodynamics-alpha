import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Hessian
namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture.Binary
abbrev Model := ClassicalThermodynamics.Models.VanDerWaals.Mixture.Model (ι := Fin 2)
abbrev State := Fin 2 → ℝ
noncomputable abbrev freeEnergy
    (M : Model) (rho : State) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.freeEnergy (ι := Fin 2) M rho
noncomputable abbrev chemicalPotential
    (M : Model) (rho : State) (i : Fin 2) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.chemicalPotential (ι := Fin 2) M rho i
noncomputable abbrev pressure
    (M : Model) (rho : State) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.pressure (ι := Fin 2) M rho
noncomputable abbrev hessian
    (M : Model) (rho : State) : Matrix (Fin 2) (Fin 2) ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.hessian (ι := Fin 2) M rho
abbrev Coexist (M : Model) (rhoA rhoB : State) : Prop :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.Coexist (ι := Fin 2) M rhoA rhoB
end ClassicalThermodynamics.Models.VanDerWaals.Mixture.Binary
