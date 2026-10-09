import ClassicalThermodynamics.Models.Berthelot.Mixture.Model
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Thermodynamics
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Hessian
import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Criticality

open scoped BigOperators

namespace ClassicalThermodynamics.Models.Berthelot.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def totalDensity (rho : State (ι := ι)) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.totalDensity rho

noncomputable def occupiedFraction
    (M : Model (ι := ι)) (rho : State (ι := ι)) : ℝ :=
  ∑ i, M.excludedVolume i * rho i

noncomputable def freeVolumeFraction
    (M : Model (ι := ι)) (rho : State (ι := ι)) : ℝ :=
  1 - occupiedFraction M rho

/-- Physical density domain for the Berthelot mixture. -/
def Physical (M : Model (ι := ι)) (rho : State (ι := ι)) : Prop :=
  (∀ i, 0 < rho i) ∧ occupiedFraction M rho < 1

/-- Dimensionless Helmholtz free-energy density, `F/(R T)`. -/
noncomputable def freeEnergy
    (M : Model (ι := ι)) (temperature : ℝ) (rho : State (ι := ι)) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.freeEnergy
    (dimensionlessVanDerWaalsModel M temperature) rho

/-- Component chemical potential divided by `R T`. -/
noncomputable def chemicalPotential
    (M : Model (ι := ι)) (temperature : ℝ)
    (rho : State (ι := ι)) (i : ι) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.chemicalPotential
    (dimensionlessVanDerWaalsModel M temperature) rho i

/-- Pressure divided by `R T`, with Berthelot attraction scaling `a/(R T²)`. -/
noncomputable def pressure
    (M : Model (ι := ι)) (temperature : ℝ)
    (rho : State (ι := ι)) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.pressure
    (dimensionlessVanDerWaalsModel M temperature) rho

omit [DecidableEq ι] in
@[simp] theorem freeEnergy_formula
    (M : Model (ι := ι)) (temperature : ℝ) (rho : State (ι := ι)) :
    freeEnergy M temperature rho =
      (∑ i, rho i * (Real.log (rho i) - 1)) -
        totalDensity rho * Real.log (freeVolumeFraction M rho) -
        ∑ i, ∑ j, alpha M temperature i j / 2 * rho i * rho j := by
  rfl

omit [DecidableEq ι] in
@[simp] theorem chemicalPotential_formula
    (M : Model (ι := ι)) (temperature : ℝ)
    (rho : State (ι := ι)) (i : ι) :
    chemicalPotential M temperature rho i =
      Real.log (rho i / freeVolumeFraction M rho) +
        M.excludedVolume i * totalDensity rho /
          freeVolumeFraction M rho -
        ∑ j, alpha M temperature i j * rho j := by
  rfl

omit [DecidableEq ι] in
@[simp] theorem pressure_formula
    (M : Model (ι := ι)) (temperature : ℝ) (rho : State (ι := ι)) :
    pressure M temperature rho =
      totalDensity rho / freeVolumeFraction M rho -
        ∑ i, ∑ j, alpha M temperature i j / 2 * rho i * rho j := by
  rfl

/-- Dimensional pressure obtained from the dimensionless mixture pressure. -/
noncomputable def dimensionalPressure
    (M : Model (ι := ι)) (temperature : ℝ)
    (rho : State (ι := ι)) : ℝ :=
  M.gasConstant * temperature * pressure M temperature rho

/-- The dimensionless Hessian controlling local mixture stability. -/
noncomputable def hessian
    (M : Model (ι := ι)) (temperature : ℝ)
    (rho : State (ι := ι)) : Matrix ι ι ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.hessian
    (dimensionlessVanDerWaalsModel M temperature) rho

/-- N-component two-phase coexistence: equal pressure and all component
chemical potentials at a common temperature. -/
def Coexist
    (M : Model (ι := ι)) (temperature : ℝ)
    (rhoA rhoB : State (ι := ι)) : Prop :=
  pressure M temperature rhoA = pressure M temperature rhoB ∧
  ∀ i, chemicalPotential M temperature rhoA i =
    chemicalPotential M temperature rhoB i

omit [DecidableEq ι] in
theorem coexist_iff_vanDerWaals
    (M : Model (ι := ι)) (temperature : ℝ)
    (rhoA rhoB : State (ι := ι)) :
    Coexist M temperature rhoA rhoB ↔
      ClassicalThermodynamics.Models.VanDerWaals.Mixture.Coexist
        (dimensionlessVanDerWaalsModel M temperature) rhoA rhoB := Iff.rfl

/-- Spinodal candidate with a nonzero null direction of the stability Hessian. -/
def IsSpinodalWithDirection
    (M : Model (ι := ι)) (temperature : ℝ)
    (rho q : State (ι := ι)) : Prop :=
  q ≠ 0 ∧ Matrix.mulVec (hessian M temperature rho) q = 0

/-- Third directional derivative condition for a mixture critical direction. -/
noncomputable def thirdDirectionalDerivative
    (M : Model (ι := ι)) (temperature : ℝ)
    (rho q : State (ι := ι)) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.thirdDirectionalDerivative
    (dimensionlessVanDerWaalsModel M temperature) rho q

def IsCriticalWithDirection
    (M : Model (ι := ι)) (temperature : ℝ)
    (rho q : State (ι := ι)) : Prop :=
  IsSpinodalWithDirection M temperature rho q ∧
  thirdDirectionalDerivative M temperature rho q = 0

theorem criticalDirection_iff_vanDerWaals
    (M : Model (ι := ι)) (temperature : ℝ)
    (rho q : State (ι := ι)) :
    IsCriticalWithDirection M temperature rho q ↔
      ClassicalThermodynamics.Models.VanDerWaals.Mixture.IsCriticalWithDirection
        (dimensionlessVanDerWaalsModel M temperature) rho q := Iff.rfl

@[simp] theorem hessian_eq_vanDerWaals
    (M : Model (ι := ι)) (temperature : ℝ) (rho : State (ι := ι)) :
    hessian M temperature rho =
      ClassicalThermodynamics.Models.VanDerWaals.Mixture.hessian
        (dimensionlessVanDerWaalsModel M temperature) rho := rfl

theorem hessian_isSymm
    (M : Model (ι := ι)) (temperature : ℝ) (rho : State (ι := ι)) :
    (hessian M temperature rho).IsSymm :=
  ClassicalThermodynamics.Models.VanDerWaals.Mixture.hessian_isSymm
    (dimensionlessVanDerWaalsModel M temperature) rho

omit [DecidableEq ι] in
theorem pressure_eq_sum_rho_mul_mu_sub_freeEnergy
    (M : Model (ι := ι)) (temperature : ℝ) (rho : State (ι := ι))
    (hfree : freeVolumeFraction M rho ≠ 0) :
    pressure M temperature rho =
      (∑ i, rho i * chemicalPotential M temperature rho i) -
        freeEnergy M temperature rho := by
  apply ClassicalThermodynamics.Models.VanDerWaals.Mixture.pressure_eq_sum_rho_mul_mu_sub_freeEnergy
  simpa [freeVolumeFraction, occupiedFraction,
    dimensionlessVanDerWaalsModel,
    ClassicalThermodynamics.Models.VanDerWaals.Mixture.freeVolumeFraction,
    ClassicalThermodynamics.Models.VanDerWaals.Mixture.occupiedFraction] using hfree

end ClassicalThermodynamics.Models.Berthelot.Mixture
