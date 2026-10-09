import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Hessian

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Spinodal candidate with an explicit nonzero Hessian null direction. -/
def IsSpinodalWithDirection
    (M : Model (ι := ι)) (rho q : ι → ℝ) : Prop :=
  q ≠ 0 ∧ Matrix.mulVec (hessian M rho) q = 0

/-- Third directional criticality expression for the mixture free energy. -/
noncomputable def thirdDirectionalDerivative
    (M : Model (ι := ι)) (rho q : ι → ℝ) : ℝ :=
  ∑ i, -(q i)^3 / (rho i)^2 +
  3 * totalDensity q * (occupiedFraction M q)^2 /
      (freeVolumeFraction M rho)^2 +
  2 * totalDensity rho * (occupiedFraction M q)^3 /
      (freeVolumeFraction M rho)^3

/-- N-component critical-direction condition. -/
def IsCriticalWithDirection
    (M : Model (ι := ι)) (rho q : ι → ℝ) : Prop :=
  IsSpinodalWithDirection M rho q ∧
  thirdDirectionalDerivative M rho q = 0

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
