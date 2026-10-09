import ClassicalThermodynamics.Thermodynamics.MechanicalObservable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF
namespace ClassicalThermodynamics.Thermodynamics.Equilibrium

def ChemicalEquilibrium {ι State : Type*} (mu : State → ι → ℝ) (a b : State) : Prop :=
  ∀ i, mu a i = mu b i

def TwoPhaseEquilibrium {ι Model State : Type*}
    (mu : Model → State → ι → ℝ)
    (O : ClassicalThermodynamics.Thermodynamics.MechanicalObservable Model State)
    (M : Model) (a b : State) : Prop :=
  ChemicalEquilibrium (mu M) a b ∧
    ClassicalThermodynamics.Thermodynamics.MechanicalEquilibrium O M a b

/-- First variation under transfer of component `i` from phase beta to phase alpha. -/
def componentTransferFirstVariation {ι : Type*}
    (muAlpha muBeta : ι → ℝ) (i : ι) : ℝ :=
  muAlpha i - muBeta i

/-- First variation under volume transfer between phases; for physical pressure
this is `-Pα + Pβ`. The same neutral form supports other mechanical observables. -/
def mechanicalTransferFirstVariation (mAlpha mBeta : ℝ) : ℝ :=
  -mAlpha + mBeta

/-- Stationarity against every component-transfer direction. -/
def ComponentTransferStationary {ι : Type*}
    (muAlpha muBeta : ι → ℝ) : Prop :=
  ∀ i, componentTransferFirstVariation muAlpha muBeta i = 0

/-- Stationarity against volume/mechanical transfer. -/
def MechanicalTransferStationary (mAlpha mBeta : ℝ) : Prop :=
  mechanicalTransferFirstVariation mAlpha mBeta = 0

/-- Variational stationarity derives equality of every chemical potential. -/
lemma chemicalEquilibrium_of_componentTransferStationary
    {ι : Type*} {muAlpha muBeta : ι → ℝ}
    (h : ComponentTransferStationary muAlpha muBeta) :
    ∀ i, muAlpha i = muBeta i := by
  intro i
  unfold ComponentTransferStationary componentTransferFirstVariation at h
  linarith [h i]

/-- Variational stationarity derives equality of the mechanical observable. -/
lemma mechanicalObservable_eq_of_transferStationary
    {mAlpha mBeta : ℝ} (h : MechanicalTransferStationary mAlpha mBeta) :
    mAlpha = mBeta := by
  unfold MechanicalTransferStationary mechanicalTransferFirstVariation at h
  linarith

/-- The constrained first-order stationarity conditions imply two-phase equilibrium. -/
theorem twoPhaseEquilibrium_of_transferStationarity
    {ι Model State : Type*}
    (mu : Model → State → ι → ℝ)
    (O : ClassicalThermodynamics.Thermodynamics.MechanicalObservable Model State)
    (M : Model) (a b : State)
    (hchem : ComponentTransferStationary (mu M a) (mu M b))
    (hmech : MechanicalTransferStationary (O.value M a) (O.value M b)) :
    TwoPhaseEquilibrium mu O M a b := by
  constructor
  · exact chemicalEquilibrium_of_componentTransferStationary hchem
  · exact mechanicalObservable_eq_of_transferStationary hmech

/-- Conversely, equilibrium annihilates all constrained transfer first variations. -/
lemma transferStationarity_of_twoPhaseEquilibrium
    {ι Model State : Type*}
    (mu : Model → State → ι → ℝ)
    (O : ClassicalThermodynamics.Thermodynamics.MechanicalObservable Model State)
    (M : Model) (a b : State)
    (h : TwoPhaseEquilibrium mu O M a b) :
    ComponentTransferStationary (mu M a) (mu M b) ∧
      MechanicalTransferStationary (O.value M a) (O.value M b) := by
  constructor
  · intro i
    unfold componentTransferFirstVariation
    rw [h.1 i]
    ring
  · unfold MechanicalTransferStationary mechanicalTransferFirstVariation
    rw [h.2]
    ring

theorem transferStationarity_iff_twoPhaseEquilibrium
    {ι Model State : Type*}
    (mu : Model → State → ι → ℝ)
    (O : ClassicalThermodynamics.Thermodynamics.MechanicalObservable Model State)
    (M : Model) (a b : State) :
    (ComponentTransferStationary (mu M a) (mu M b) ∧
      MechanicalTransferStationary (O.value M a) (O.value M b)) ↔
    TwoPhaseEquilibrium mu O M a b := by
  constructor
  · intro h
    exact twoPhaseEquilibrium_of_transferStationarity mu O M a b h.1 h.2
  · exact transferStationarity_of_twoPhaseEquilibrium mu O M a b

end ClassicalThermodynamics.Thermodynamics.Equilibrium
