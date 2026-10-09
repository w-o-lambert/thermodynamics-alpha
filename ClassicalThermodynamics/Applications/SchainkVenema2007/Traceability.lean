import ClassicalThermodynamics.Models.VanDerWaals.Pure.CorrespondingStates

/-!
## Schaink and Venema (2007)

Paper: H. M. Schaink and P. Venema, "The van der Waals Equation of State and the
Law of Corresponding States: A Spreadsheet Experiment", Journal of Chemical
Education 84 (12), 2030 (2007), DOI 10.1021/ed084p2030.

The paper-facing layer delegates the reduced equation of state to the generic pure
van der Waals model. No spreadsheet or numerical procedure is made part of the
thermodynamic model assumption.
-/

namespace ClassicalThermodynamics.Applications.SchainkVenema2007

open ClassicalThermodynamics.Models.VanDerWaals.Pure

/-- Thin wrapper for the universal reduced van der Waals equation used to express
the law of corresponding states. -/
theorem verified_reduced_equation
    {pR tR vR : ℝ} (hv : vR ≠ 0) (hfree : 3 * vR - 1 ≠ 0) :
    CorrespondingStatesEquation pR tR vR ↔
      pR = correspondingStatesPressure tR vR :=
  correspondingStatesEquation_iff hv hfree

/-- Thin wrapper connecting the dimensional equation of state to the universal
reduced equation. -/
theorem verified_law_of_corresponding_states
    (M : Model) (temperature volume : ℝ)
    (ha : M.attraction ≠ 0) (hb : M.excludedVolume ≠ 0)
    (hR : M.gasConstant ≠ 0)
    (hV : volume ≠ 0) (hfree : volume - M.excludedVolume ≠ 0)
    (hVr : reducedVolumeVariable M volume ≠ 0)
    (hVrFree : 3 * reducedVolumeVariable M volume - 1 ≠ 0) :
    CorrespondingStatesEquation
      (reducedPressureVariable M (pressureTV M temperature volume))
      (reducedTemperatureVariable M temperature)
      (reducedVolumeVariable M volume) :=
  law_of_corresponding_states M temperature volume
    ha hb hR hV hfree hVr hVrFree

end ClassicalThermodynamics.Applications.SchainkVenema2007
