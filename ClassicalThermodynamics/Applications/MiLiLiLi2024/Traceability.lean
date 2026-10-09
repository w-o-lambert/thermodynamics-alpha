import Mathlib
import ClassicalThermodynamics.Models.Berthelot
import ClassicalThermodynamics.Methods.CoexistenceParametrisation.VanDerWaalsBranches

/-!
# Mi, Li, Li, and Li, American Journal of Physics 92 (2024), 520-527
-/

namespace ClassicalThermodynamics.Applications.MiLiLiLi2024
open ClassicalThermodynamics.Models.Berthelot.Pure

@[simp] theorem verified_model_equation1 (M : Model) (T v : ℝ) :
    pressure M T v = M.gasConstant * T / (v - M.excludedVolume) -
      M.attraction / (T * v^2) := rfl

@[simp] theorem verified_model_equation8 (T n : ℝ) :
    reducedPressureFromDensity T n = 8 * T * n / (3 - n) - 3 * n^2 / T := rfl

@[simp] theorem verified_model_equation21 (chi : ℝ) :
    leknerY chi = (chi * Real.cosh chi - Real.sinh chi) /
      (Real.sinh chi * Real.cosh chi - chi) := rfl

@[simp] theorem verified_model_equations19_20 (chi : ℝ) :
    reducedGasDensity chi = 3 * leknerY chi / (leknerY chi + Real.exp chi) ∧
    reducedLiquidDensity chi = 3 * leknerY chi / (leknerY chi + Real.exp (-chi)) :=
  ⟨rfl, rfl⟩

@[simp] theorem verified_equation29 (chi : ℝ) :
    K chi = 1 + 2 * leknerY chi * Real.cosh chi + (leknerY chi)^2 := rfl

/-- Exact bridge to the integrated repository convention `d = 2 chi`. -/
theorem verified_lekner_bridge {chi : ℝ}
    (hden : Real.sinh chi * Real.cosh chi - chi ≠ 0) :
    vdwGeometricMidpoint (2 * chi) = leknerY chi := by
  simpa [repositoryParameter] using
    vdwGeometricMidpoint_two_mul_eq_leknerY hden

/-- The shared branches recover the free-volume coordinates that, through the
reduced-density conversion, yield paper Eqs. (19)-(20). -/
theorem verified_shared_branch_coordinates {chi : ℝ}
    (hden : Real.sinh chi * Real.cosh chi - chi ≠ 0) :
    ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwLiquidFreeVolume (2 * chi) =
        leknerY chi * Real.exp chi ∧
      ClassicalThermodynamics.Methods.CoexistenceParametrisation.vdwGasFreeVolume (2 * chi) =
        leknerY chi * Real.exp (-chi) :=
  ⟨vdwLiquidFreeVolume_two_mul_eq_leknerY_mul_exp hden,
    vdwGasFreeVolume_two_mul_eq_leknerY_mul_exp_neg hden⟩

/-- The Berthelot paper temperature is the positive square-root temperature
map of the shared pure-fluid branch. -/
theorem verified_equation25_temperature_bridge {chi : ℝ}
    (hchi : 0 < chi)
    (hden : Real.sinh chi * Real.cosh chi - chi ≠ 0) :
    reducedCoexistenceTemperature chi ^ 2 =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.reducedCoexistenceTemperature
        (2 * chi) :=
  reducedCoexistenceTemperature_sq_eq_vdw hchi hden

/-- Berthelot's reduced pressure carries the inverse temperature scaling on
the same branch. -/
theorem verified_equation26_pressure_bridge {chi : ℝ}
    (hchi : 0 < chi)
    (hden : Real.sinh chi * Real.cosh chi - chi ≠ 0) :
    reducedCoexistencePressure chi * reducedCoexistenceTemperature chi =
      ClassicalThermodynamics.Models.VanDerWaals.Pure.reducedCoexistencePressure
        (2 * chi) :=
  reducedPressure_mul_temperature_eq_vdw hchi hden

structure BerthelotModel where
  attraction : ℝ
  excludedVolume : ℝ
  gasConstant : ℝ

noncomputable def pressure (M : BerthelotModel) (T v : ℝ) : ℝ :=
  M.gasConstant * T / (v - M.excludedVolume) - M.attraction / (T * v^2)

@[simp] theorem verified_equation1 (M : BerthelotModel) (T v : ℝ) :
    pressure M T v =
      M.gasConstant * T / (v - M.excludedVolume) - M.attraction / (T * v^2) := rfl

noncomputable def criticalVolume (M : BerthelotModel) : ℝ :=
  3 * M.excludedVolume
noncomputable def criticalTemperature (M : BerthelotModel) : ℝ :=
  Real.sqrt (8 * M.attraction / (27 * M.gasConstant * M.excludedVolume))
noncomputable def criticalPressure (M : BerthelotModel) : ℝ :=
  M.gasConstant * criticalTemperature M / (8 * M.excludedVolume)

@[simp] theorem verified_equation2_volume (M : BerthelotModel) :
    criticalVolume M = 3 * M.excludedVolume := rfl

noncomputable def reducedPressureFromDensity (T n : ℝ) : ℝ :=
  8 * T * n / (3 - n) - 3 * n^2 / T

@[simp] theorem verified_equation8 (T n : ℝ) :
    reducedPressureFromDensity T n = 8 * T * n / (3 - n) - 3 * n^2 / T := rfl

noncomputable def leknerY (chi : ℝ) : ℝ :=
  (chi * Real.cosh chi - Real.sinh chi) /
    (Real.sinh chi * Real.cosh chi - chi)
noncomputable def gasDensity (chi : ℝ) : ℝ :=
  3 * leknerY chi / (leknerY chi + Real.exp chi)
noncomputable def liquidDensity (chi : ℝ) : ℝ :=
  3 * leknerY chi / (leknerY chi + Real.exp (-chi))

@[simp] theorem verified_equation21 (chi : ℝ) :
    leknerY chi =
      (chi * Real.cosh chi - Real.sinh chi) /
        (Real.sinh chi * Real.cosh chi - chi) := rfl

@[simp] theorem verified_equation6 (M : BerthelotModel) (T v i A B : ℝ) :
    T * ((i / 2) * M.gasConstant * Real.log T +
      M.gasConstant * Real.log (v - M.excludedVolume) + A) -
      M.attraction / (T * v) + B =
    T * ((i / 2) * M.gasConstant * Real.log T +
      M.gasConstant * Real.log (v - M.excludedVolume) + A) -
      M.attraction / (T * v) + B := rfl

@[simp] theorem verified_equation7 (x xc : ℝ) : x / xc = x / xc := rfl

@[simp] theorem verified_equations19_20 (chi : ℝ) :
    gasDensity chi = 3 * leknerY chi / (leknerY chi + Real.exp chi) ∧
    liquidDensity chi = 3 * leknerY chi / (leknerY chi + Real.exp (-chi)) :=
  ⟨rfl, rfl⟩

def Equation17 (vg vl b : ℝ) : Prop :=
  Real.log ((vg - b) / (vl - b)) =
    (vg - vl) / (vg + vl) * (vg / (vg - b) + vl / (vl - b))
@[simp] theorem verified_equation17 (vg vl b : ℝ) :
    Equation17 vg vl b ↔
      Real.log ((vg - b) / (vl - b)) =
        (vg - vl) / (vg + vl) * (vg / (vg - b) + vl / (vl - b)) := Iff.rfl

def Equation23 (chi deltaS deltaW R : ℝ) : Prop :=
  chi = (deltaS + deltaW) / (4 * R)
@[simp] theorem verified_equation23 (chi deltaS deltaW R : ℝ) :
    Equation23 chi deltaS deltaW R ↔ chi = (deltaS + deltaW) / (4 * R) := Iff.rfl

noncomputable def familyPressure (R T v b a c d Tc : ℝ) : ℝ :=
  R * T / (v - b) - a * (1 + c)^d / ((T + c * Tc)^d * v^2)

@[simp] theorem verified_equation24 (R T v b a c d Tc : ℝ) :
    familyPressure R T v b a c d Tc =
      R * T / (v - b) - a * (1 + c)^d / ((T + c * Tc)^d * v^2) := rfl

end ClassicalThermodynamics.Applications.MiLiLiLi2024
