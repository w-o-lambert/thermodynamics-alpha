import ClassicalThermodynamics.Thermodynamics.Equilibrium.Variational
import ClassicalThermodynamics.Thermodynamics.Pressure
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Thermodynamics

namespace ClassicalThermodynamics.Bridges.ThermodynamicFoundation
open ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def vanDerWaalsMixturePressureData :
    ClassicalThermodynamics.Thermodynamics.HasPressure (Model (ι := ι)) (State (ι := ι)) :=
  ⟨pressure⟩

omit [DecidableEq ι] in
/-- Model coexistence is exactly the foundation's neutral chemical-plus-mechanical
two-phase equilibrium instantiated with physical pressure. -/
theorem coexist_iff_twoPhaseEquilibrium
    (M : Model (ι := ι)) (a b : State (ι := ι)) :
    Coexist M a b ↔
      ClassicalThermodynamics.Thermodynamics.Equilibrium.TwoPhaseEquilibrium
        chemicalPotential
        (ClassicalThermodynamics.Thermodynamics.pressureObservable
          (vanDerWaalsMixturePressureData (ι := ι))) M a b := by
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

end ClassicalThermodynamics.Bridges.ThermodynamicFoundation
