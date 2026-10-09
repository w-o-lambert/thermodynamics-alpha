import ClassicalThermodynamics.Models.VanDerWaals.Mixture.FixedCompositionCoexistence
import ClassicalThermodynamics.Models.VanDerWaals.Pure.CriticalCoordinates

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def fixedCompositionCriticalDensity
    (M : Model (ι := ι)) (x : ι → ℝ) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Pure.criticalDensity (effectivePureModel M x)

noncomputable def fixedCompositionCriticalTemperature
    (M : Model (ι := ι)) (x : ι → ℝ) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Pure.criticalTemperature (effectivePureModel M x)

noncomputable def fixedCompositionCriticalPressure
    (M : Model (ι := ι)) (x : ι → ℝ) : ℝ :=
  ClassicalThermodynamics.Models.VanDerWaals.Pure.criticalPressure (effectivePureModel M x)

omit [DecidableEq ι] in
@[simp] theorem fixedCompositionCriticalDensity_formula
    (M : Model (ι := ι)) (x : ι → ℝ) :
    fixedCompositionCriticalDensity M x = 1 / (3 * mixtureCovolume M x) := rfl

omit [DecidableEq ι] in
@[simp] theorem fixedCompositionCriticalTemperature_formula
    (M : Model (ι := ι)) (x : ι → ℝ) :
    fixedCompositionCriticalTemperature M x =
      8 * mixtureAttraction M x /
        (27 * M.gasConstant * mixtureCovolume M x) := rfl

omit [DecidableEq ι] in
@[simp] theorem fixedCompositionCriticalPressure_formula
    (M : Model (ι := ι)) (x : ι → ℝ) :
    fixedCompositionCriticalPressure M x =
      mixtureAttraction M x / (27 * (mixtureCovolume M x)^2) := rfl

omit [DecidableEq ι] in
/-- Fixed-composition criticality is exactly pure criticality of the effective model. -/
theorem fixedComposition_critical_point
    (M : Model (ι := ι)) (x : ι → ℝ)
    (ha : mixtureAttraction M x ≠ 0) (hb : mixtureCovolume M x ≠ 0)
    (hR : M.gasConstant ≠ 0) :
    ClassicalThermodynamics.Models.VanDerWaals.Pure.IsCritical
      { effectivePureModel M x with
        temperature := fixedCompositionCriticalTemperature M x }
      (fixedCompositionCriticalDensity M x) := by
  exact ClassicalThermodynamics.Models.VanDerWaals.Pure.critical_point_formula
    (effectivePureModel M x) ha hb hR

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
