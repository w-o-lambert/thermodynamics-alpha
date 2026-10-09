import ClassicalThermodynamics.Models.VanDerWaals.Pure.CriticalCoordinates
namespace ClassicalThermodynamics.Models.VanDerWaals.Pure
noncomputable def reducedPressureVariable (M : Model) (pressure : ℝ) : ℝ := pressure / criticalPressure M
noncomputable def reducedTemperatureVariable (M : Model) (temperature : ℝ) : ℝ := temperature / criticalTemperature M
noncomputable def reducedVolumeVariable (M : Model) (volume : ℝ) : ℝ := volume / criticalVolume M
noncomputable def correspondingStatesPressure (tR vR : ℝ) : ℝ := 8*tR/(3*vR-1)-3/vR^2
def CorrespondingStatesEquation (pR tR vR : ℝ) : Prop := (pR+3/vR^2)*(3*vR-1)=8*tR
lemma correspondingStatesEquation_iff {pR tR vR : ℝ}
    (hv : vR ≠ 0) (hf : 3 * vR - 1 ≠ 0) :
    CorrespondingStatesEquation pR tR vR ↔
      pR = correspondingStatesPressure tR vR := by
  unfold CorrespondingStatesEquation correspondingStatesPressure
  constructor
  · intro h
    apply (eq_sub_iff_add_eq).2
    apply (eq_div_iff hf).2
    linarith
  · intro h
    rw [h]
    field_simp [hv, hf]
    ring

theorem pressureTV_eq_criticalPressure_mul_correspondingStatesPressure
    (M : Model) (temperature volume : ℝ)
    (ha : M.attraction ≠ 0) (hb : M.excludedVolume ≠ 0)
    (_hR : M.gasConstant ≠ 0)
    (hV : volume ≠ 0) (hfree : volume - M.excludedVolume ≠ 0) :
    pressureTV M temperature volume = criticalPressure M *
      correspondingStatesPressure
        (reducedTemperatureVariable M temperature)
        (reducedVolumeVariable M volume) := by
  have hpc : criticalPressure M ≠ 0 := by
    unfold criticalPressure
    exact div_ne_zero ha (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb))
  have hvr : reducedVolumeVariable M volume ≠ 0 := by
    unfold reducedVolumeVariable criticalVolume
    exact div_ne_zero hV (mul_ne_zero (by norm_num) hb)
  have hvrfree : 3 * reducedVolumeVariable M volume - 1 ≠ 0 := by
    intro hzero
    apply hfree
    unfold reducedVolumeVariable criticalVolume at hzero
    field_simp [hb] at hzero
    linarith
  have hred :
      reducedPressureVariable M (pressureTV M temperature volume) =
        correspondingStatesPressure
          (reducedTemperatureVariable M temperature)
          (reducedVolumeVariable M volume) := by
    apply (correspondingStatesEquation_iff hvr hvrfree).1
    unfold CorrespondingStatesEquation reducedPressureVariable
      reducedTemperatureVariable reducedVolumeVariable
      pressureTV criticalPressure criticalTemperature criticalVolume
    field_simp [ha, hb, _hR, hV, hfree]
    ring
  unfold reducedPressureVariable at hred
  simpa [mul_comm] using (div_eq_iff hpc).1 hred

theorem reducedPressureVariable_pressureTV
    (M : Model) (temperature volume : ℝ)
    (ha : M.attraction ≠ 0) (hb : M.excludedVolume ≠ 0) (hR : M.gasConstant ≠ 0)
    (hV : volume ≠ 0) (hfree : volume-M.excludedVolume ≠ 0) :
    reducedPressureVariable M (pressureTV M temperature volume) = correspondingStatesPressure
      (reducedTemperatureVariable M temperature) (reducedVolumeVariable M volume) := by
  rw [pressureTV_eq_criticalPressure_mul_correspondingStatesPressure M temperature volume ha hb hR hV hfree]
  unfold reducedPressureVariable criticalPressure
  field_simp [ha,hb]
theorem law_of_corresponding_states
    (M : Model) (temperature volume : ℝ)
    (ha : M.attraction ≠ 0) (hb : M.excludedVolume ≠ 0) (hR : M.gasConstant ≠ 0)
    (hV : volume ≠ 0) (hfree : volume-M.excludedVolume ≠ 0)
    (hVr : reducedVolumeVariable M volume ≠ 0)
    (hVrFree : 3*reducedVolumeVariable M volume-1 ≠ 0) :
    CorrespondingStatesEquation (reducedPressureVariable M (pressureTV M temperature volume))
      (reducedTemperatureVariable M temperature) (reducedVolumeVariable M volume) := by
  apply (correspondingStatesEquation_iff hVr hVrFree).2
  exact reducedPressureVariable_pressureTV M temperature volume ha hb hR hV hfree
end ClassicalThermodynamics.Models.VanDerWaals.Pure
