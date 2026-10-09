import ClassicalThermodynamics.Models.VanDerWaals.Pure.AsymptoticTargets
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Asymptotics.Defs

namespace ClassicalThermodynamics.Models.VanDerWaals.Pure

open Filter
open ClassicalThermodynamics.Methods.CoexistenceParametrisation

/-- Numerator of the closed geometric-midpoint formula. -/
noncomputable def criticalMidpointNumerator (d : ℝ) : ℝ :=
  d * Real.cosh (d / 2) - 2 * Real.sinh (d / 2)

/-- Denominator of the closed geometric-midpoint formula. -/
noncomputable def criticalMidpointDenominator (d : ℝ) : ℝ :=
  Real.sinh d - d

/-- A general cubic cancellation lemma used for the removable `0/0` singularity.
The hypotheses say `f(d) = a d^3 + o(d^3)` and
`g(d) = b d^3 + o(d^3)`. -/
lemma tendsto_div_of_cubic_isLittleO
    {f g : ℝ → ℝ} {a b : ℝ} (hb : b ≠ 0)
    (hf : (fun d => f d - a * d^3) =o[nhds 0] (fun d => d^3))
    (hg : (fun d => g d - b * d^3) =o[nhds 0] (fun d => d^3)) :
    Tendsto (fun d => f d / g d)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (a / b)) := by
  have hp : ∀ᶠ d : ℝ in nhdsWithin 0 (Set.Ioi 0), d^3 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact pow_ne_zero 3 (ne_of_gt hd)
  have hf0 : Tendsto (fun d => (f d - a * d^3) / d^3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact (hf.mono_left inf_le_left).tendsto_div_nhds_zero
  have hg0 : Tendsto (fun d => (g d - b * d^3) / d^3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact (hg.mono_left inf_le_left).tendsto_div_nhds_zero
  have hfn : Tendsto (fun d => a + (f d - a*d^3)/d^3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
    simpa using tendsto_const_nhds.add hf0
  have hgn : Tendsto (fun d => b + (g d - b*d^3)/d^3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds b) := by
    simpa using tendsto_const_nhds.add hg0
  apply Tendsto.congr'
  · filter_upwards [hp] with d hd
    field_simp [hd]
    ring
  · exact hfn.div hgn hb

/-- Cubic expansion of `exp d` at zero. -/
lemma exp_cubic_isLittleO :
    (fun d : ℝ => Real.exp d - (1 + d + d^2/2 + d^3/6))
      =o[nhds 0] (fun d => d^3) := by
  simpa [Finset.sum_range_succ, Nat.factorial] using
    (Real.exp_sub_sum_range_succ_isLittleO_pow 3)

/-- Cubic expansion of `exp (-d)` at zero. -/
lemma exp_neg_cubic_isLittleO :
    (fun d : ℝ => Real.exp (-d) - (1 - d + d^2/2 - d^3/6))
      =o[nhds 0] (fun d => d^3) := by
  have h := exp_cubic_isLittleO.comp_tendsto
    tendsto_neg_nhds_0 (by simpa using (isTheta_neg_id_at_zero.pow 3))
  simpa using h

/-- Cubic expansion of `exp (d/2)` at zero. -/
lemma exp_half_cubic_isLittleO :
    (fun d : ℝ => Real.exp (d/2) -
      (1 + d/2 + d^2/8 + d^3/48))
      =o[nhds 0] (fun d => d^3) := by
  have h := exp_cubic_isLittleO.comp_tendsto
    (tendsto_id.const_div 2) (by
      simpa [div_pow] using (isTheta_id_const_mul_at_zero (1/2 : ℝ) (by norm_num)).pow 3)
  simpa [div_pow] using h

/-- Cubic expansion of `exp (-d/2)` at zero. -/
lemma exp_neg_half_cubic_isLittleO :
    (fun d : ℝ => Real.exp (-d/2) -
      (1 - d/2 + d^2/8 - d^3/48))
      =o[nhds 0] (fun d => d^3) := by
  have h := exp_half_cubic_isLittleO.comp_tendsto
    tendsto_neg_nhds_0 (by simpa using (isTheta_neg_id_at_zero.pow 3))
  simpa using h

/-- The midpoint numerator is `d^3/12 + o(d^3)`. -/
lemma criticalMidpointNumerator_cubic :
    (fun d => criticalMidpointNumerator d - (1/12 : ℝ) * d^3)
      =o[nhds 0] (fun d => d^3) := by
  unfold criticalMidpointNumerator
  rw [show (fun d : ℝ => d * Real.cosh (d/2) - 2 * Real.sinh (d/2) -
      (1/12 : ℝ) * d^3) =
      fun d =>
        d/2 * (Real.exp (d/2) + Real.exp (-d/2)) -
        (Real.exp (d/2) - Real.exp (-d/2)) - (1/12 : ℝ)*d^3 by
    funext d
    rw [Real.cosh_eq, Real.sinh_eq]
    ring]
  have hp := exp_half_cubic_isLittleO
  have hm := exp_neg_half_cubic_isLittleO
  convert ((hp.add hm).const_mul (1/2 : ℝ)).mul_isBigO
      (isBigO_id) |>.sub (hp.sub hm) using 1 <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] <;> ring

/-- The midpoint denominator is `d^3/6 + o(d^3)`. -/
lemma criticalMidpointDenominator_cubic :
    (fun d => criticalMidpointDenominator d - (1/6 : ℝ) * d^3)
      =o[nhds 0] (fun d => d^3) := by
  unfold criticalMidpointDenominator
  rw [show (fun d : ℝ => Real.sinh d - d - (1/6 : ℝ)*d^3) =
      fun d => (Real.exp d - Real.exp (-d))/2 - d - (1/6 : ℝ)*d^3 by
    funext d
    rw [Real.sinh_eq]]
  convert (exp_cubic_isLittleO.sub exp_neg_cubic_isLittleO).const_mul (1/2 : ℝ)
    using 1 <;> simp only [Pi.sub_apply, Pi.mul_apply] <;> ring

/-- The difficult removable-singularity theorem: `H_vdW(d) -> 1/2` as `d -> 0+`. -/
theorem tendsto_vdwGeometricMidpoint_zero_right :
    Tendsto vdwGeometricMidpoint
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1/2)) := by
  unfold vdwGeometricMidpoint
  change Tendsto (fun d => criticalMidpointNumerator d /
      criticalMidpointDenominator d) _ _
  convert tendsto_div_of_cubic_isLittleO
    (a := (1/12 : ℝ)) (b := (1/6 : ℝ)) (by norm_num)
    criticalMidpointNumerator_cubic criticalMidpointDenominator_cubic using 1 <;>
  norm_num

/-- Both free-volume branches tend to `1/2` at the critical point. -/
theorem tendsto_vdwLiquidFreeVolume_zero_right :
    Tendsto vdwLiquidFreeVolume (nhdsWithin 0 (Set.Ioi 0)) (nhds (1/2)) := by
  unfold vdwLiquidFreeVolume
  have he : Tendsto (fun d : ℝ => Real.exp (d/2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    convert (continuousAt_exp.tendsto.comp
      ((tendsto_id.const_div 2).mono_left inf_le_left)) using 1 <;> norm_num
  convert tendsto_vdwGeometricMidpoint_zero_right.mul he using 1 <;> norm_num

theorem tendsto_vdwGasFreeVolume_zero_right :
    Tendsto vdwGasFreeVolume (nhdsWithin 0 (Set.Ioi 0)) (nhds (1/2)) := by
  unfold vdwGasFreeVolume
  have he : Tendsto (fun d : ℝ => Real.exp (-d/2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    convert (continuousAt_exp.tendsto.comp
      (((tendsto_neg_nhds_0.const_div 2)).mono_left inf_le_left)) using 1 <;> norm_num
  convert tendsto_vdwGeometricMidpoint_zero_right.mul he using 1 <;> norm_num

/-- The reduced-density map is continuous at the critical free-volume value. -/
theorem tendsto_reducedDensityFromFreeVolume_half
    {l : Filter ℝ} {z : ℝ → ℝ}
    (hz : Tendsto z l (nhds (1/2))) :
    Tendsto (fun d => reducedDensityFromFreeVolume (z d)) l (nhds 1) := by
  unfold reducedDensityFromFreeVolume
  convert (tendsto_const_nhds.mul hz).div (tendsto_const_nhds.add hz)
    (by norm_num : (1 + (1/2 : ℝ)) ≠ 0) using 1 <;> norm_num

theorem tendsto_reducedLiquidDensity_zero_right :
    Tendsto reducedLiquidDensity (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  unfold reducedLiquidDensity
  exact tendsto_reducedDensityFromFreeVolume_half tendsto_vdwLiquidFreeVolume_zero_right

theorem tendsto_reducedGasDensity_zero_right :
    Tendsto reducedGasDensity (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  unfold reducedGasDensity
  exact tendsto_reducedDensityFromFreeVolume_half tendsto_vdwGasFreeVolume_zero_right

/-- The free-volume product tends to `9/4`. -/
theorem tendsto_coexistenceFreeVolumeProduct_zero_right :
    Tendsto coexistenceFreeVolumeProduct
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (9/4)) := by
  unfold coexistenceFreeVolumeProduct
  convert (tendsto_const_nhds.add tendsto_vdwLiquidFreeVolume_zero_right).mul
    (tendsto_const_nhds.add tendsto_vdwGasFreeVolume_zero_right) using 1 <;> norm_num

/-- Reduced coexistence temperature tends to one at criticality. -/
theorem tendsto_reducedCoexistenceTemperature_zero_right :
    Tendsto reducedCoexistenceTemperature
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  unfold reducedCoexistenceTemperature
  have hc : Tendsto (fun d : ℝ => Real.cosh (d/2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    convert (Real.continuous_cosh.continuousAt.tendsto.comp
      ((tendsto_id.const_div 2).mono_left inf_le_left)) using 1 <;> norm_num
  have hp := tendsto_coexistenceFreeVolumeProduct_zero_right.pow 2
  convert ((tendsto_const_nhds.mul tendsto_vdwGeometricMidpoint_zero_right).mul
    (tendsto_vdwGeometricMidpoint_zero_right.add hc)).div
      (tendsto_const_nhds.mul hp) (by norm_num : (4:ℝ)*(9/4)^2 ≠ 0)
    using 1 <;> norm_num

/-- Reduced coexistence pressure tends to one at criticality. -/
theorem tendsto_reducedCoexistencePressure_zero_right :
    Tendsto reducedCoexistencePressure
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  unfold reducedCoexistencePressure
  have hm2 := tendsto_vdwGeometricMidpoint_zero_right.pow 2
  have hp := tendsto_coexistenceFreeVolumeProduct_zero_right.pow 2
  convert ((tendsto_const_nhds.mul hm2).mul (tendsto_const_nhds.sub hm2)).div
    hp (by norm_num : (9/4 : ℝ)^2 ≠ 0) using 1 <;> norm_num

/-- Full critical `d -> 0+` conjunction. -/
theorem criticalLimitSpecification : CriticalLimitSpecification := by
  exact ⟨tendsto_vdwGeometricMidpoint_zero_right,
    tendsto_reducedLiquidDensity_zero_right,
    tendsto_reducedGasDensity_zero_right,
    tendsto_reducedCoexistenceTemperature_zero_right,
    tendsto_reducedCoexistencePressure_zero_right⟩

end ClassicalThermodynamics.Models.VanDerWaals.Pure
