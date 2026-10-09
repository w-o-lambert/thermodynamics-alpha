import ClassicalThermodynamics.Models.VanDerWaals.Pure.FreeVolume

namespace ClassicalThermodynamics.Models.VanDerWaals.Pure

/-- Dimensionless configurational entropy per particle, defined up to an additive
constant. Its phase difference is independent of that constant. -/
noncomputable def configurationalEntropyPerParticle
    (M : Model) (rho : State) : ℝ :=
  -Real.log (rho / (1 - M.excludedVolume * rho))

/-- Dimensionless entropy difference between a low-density and high-density phase. -/
noncomputable def entropyDifferencePerParticle
    (M : Model) (rhoLow rhoHigh : State) : ℝ :=
  configurationalEntropyPerParticle M rhoLow -
    configurationalEntropyPerParticle M rhoHigh

/-- In free-volume coordinates the entropy difference is the logarithmic branch ratio. -/
theorem entropyDifference_densityFromFreeVolume
    (M : Model) {zHigh zLow : ℝ}
    (hbpos : 0 < M.excludedVolume)
    (hHigh : 0 < zHigh) (hLow : 0 < zLow) :
    entropyDifferencePerParticle M
      (densityFromFreeVolume M zLow)
      (densityFromFreeVolume M zHigh) = Real.log (zHigh / zLow) := by
  unfold entropyDifferencePerParticle configurationalEntropyPerParticle
  have hb : M.excludedVolume ≠ 0 := ne_of_gt hbpos
  have hHp1 : 1 + zHigh ≠ 0 := by positivity
  have hLp1 : 1 + zLow ≠ 0 := by positivity
  have hH := densityFromFreeVolume_div_freeFraction M zHigh hb hHp1
  have hL := densityFromFreeVolume_div_freeFraction M zLow hb hLp1
  rw [hH, hL, Real.log_div hHigh.ne' hbpos.ne',
    Real.log_div hLow.ne' hbpos.ne', Real.log_div hHigh.ne' hLow.ne']
  ring

end ClassicalThermodynamics.Models.VanDerWaals.Pure
