import ClassicalThermodynamics.Models.Berthelot.Mixture.ResponseFunctions

namespace ClassicalThermodynamics.Models.Berthelot.Mixture

/-- Embed a pure Berthelot model as a one-component mixture. The factor of two
matches the mixture's `1/2` convention in its quadratic attraction sum. -/
noncomputable def ofPure
    (M : ClassicalThermodynamics.Models.Berthelot.Pure.Model) :
    Model (ι := Unit) where
  attraction := fun _ _ => 2 * M.attraction
  symmetricAttraction := by
    ext i j
    rfl
  excludedVolume := fun _ => M.excludedVolume
  gasConstant := M.gasConstant

noncomputable def unitComposition : Unit → ℝ := fun _ => 1

@[simp] theorem mixtureCovolume_ofPure
    (M : ClassicalThermodynamics.Models.Berthelot.Pure.Model) :
    mixtureCovolume (ofPure M) unitComposition = M.excludedVolume := by
  simp [mixtureCovolume, ofPure, unitComposition]

@[simp] theorem mixtureAttraction_ofPure
    (M : ClassicalThermodynamics.Models.Berthelot.Pure.Model) :
    mixtureAttraction (ofPure M) unitComposition = M.attraction := by
  simp [mixtureAttraction, ofPure, unitComposition]

theorem pressureTVAtComposition_ofPure
    (M : ClassicalThermodynamics.Models.Berthelot.Pure.Model)
    (temperature molarVolume : ℝ) :
    pressureTVAtComposition (ofPure M) unitComposition temperature molarVolume =
      ClassicalThermodynamics.Models.Berthelot.Pure.pressure M temperature molarVolume := by
  rw [pressureTVAtComposition, mixtureCovolume_ofPure, mixtureAttraction_ofPure]
  rfl

end ClassicalThermodynamics.Models.Berthelot.Mixture
