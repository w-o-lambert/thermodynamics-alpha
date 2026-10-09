import ClassicalThermodynamics.Models.Berthelot.Mixture.ResponseFunctions
import ClassicalThermodynamics.Models.Berthelot.Pure.CriticalCoordinates

namespace ClassicalThermodynamics.Models.Berthelot.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def fixedCompositionCriticalVolume
    (M : Model (ι := ι)) (x : ι → ℝ) : ℝ :=
  ClassicalThermodynamics.Models.Berthelot.Pure.criticalVolume (effectivePureModel M x)

noncomputable def fixedCompositionCriticalTemperature
    (M : Model (ι := ι)) (x : ι → ℝ) : ℝ :=
  ClassicalThermodynamics.Models.Berthelot.Pure.criticalTemperature (effectivePureModel M x)

noncomputable def fixedCompositionCriticalPressure
    (M : Model (ι := ι)) (x : ι → ℝ) : ℝ :=
  ClassicalThermodynamics.Models.Berthelot.Pure.criticalPressure (effectivePureModel M x)

omit [DecidableEq ι] in
@[simp] theorem fixedCompositionCriticalVolume_formula
    (M : Model (ι := ι)) (x : ι → ℝ) :
    fixedCompositionCriticalVolume M x =
      3 * mixtureCovolume M x := rfl

omit [DecidableEq ι] in
@[simp] theorem fixedCompositionCriticalTemperature_formula
    (M : Model (ι := ι)) (x : ι → ℝ) :
    fixedCompositionCriticalTemperature M x =
      Real.sqrt (8 * mixtureAttraction M x /
        (27 * M.gasConstant * mixtureCovolume M x)) := rfl

omit [DecidableEq ι] in
@[simp] theorem fixedCompositionCriticalPressure_formula
    (M : Model (ι := ι)) (x : ι → ℝ) :
    fixedCompositionCriticalPressure M x =
      M.gasConstant * fixedCompositionCriticalTemperature M x /
        (8 * mixtureCovolume M x) := rfl

end ClassicalThermodynamics.Models.Berthelot.Mixture
