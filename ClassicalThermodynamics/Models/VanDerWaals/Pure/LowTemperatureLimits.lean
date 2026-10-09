import ClassicalThermodynamics.Models.VanDerWaals.Pure.AsymptoticTargets
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed

namespace ClassicalThermodynamics.Models.VanDerWaals.Pure

open Filter
open ClassicalThermodynamics.Methods.CoexistenceParametrisation

/-- Exponentially normalized denominator of the closed branch formulas. -/
noncomputable def normalizedVdwDenominator (d : ℝ) : ℝ :=
  1 - Real.exp (-2 * d) - 2 * d * Real.exp (-d)

/-- Normalized numerator of the geometric midpoint. -/
noncomputable def normalizedMidpointNumerator (d : ℝ) : ℝ :=
  (d - 2) * Real.exp (-d / 2) +
    (d + 2) * Real.exp (-3 * d / 2)

/-- Normalized gas-branch numerator. -/
noncomputable def normalizedLowNumerator (d : ℝ) : ℝ :=
  (d - 2) * Real.exp (-d) +
    (d + 2) * Real.exp (-2 * d)

/-- Exact denominator normalization by `exp d`. -/
lemma vdwDenominator_eq_exp_mul (d : ℝ) :
    Real.exp d - Real.exp (-d) - 2 * d =
      Real.exp d * normalizedVdwDenominator d := by
  unfold normalizedVdwDenominator
  have h1 : Real.exp d * Real.exp (-2 * d) = Real.exp (-d) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp d * Real.exp (-d) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h2' : 2 * d = 2 * d * (Real.exp d * Real.exp (-d)) := by
    rw [h2]
    ring
  calc
    Real.exp d - Real.exp (-d) - 2 * d =
        Real.exp d - Real.exp d * Real.exp (-2 * d) - 2 * d := by
      rw [h1]
    _ = Real.exp d - Real.exp d * Real.exp (-2 * d) -
        2 * d * (Real.exp d * Real.exp (-d)) := by
      conv_lhs => rw [h2']
    _ = Real.exp d * (1 - Real.exp (-2 * d) - 2 * d * Real.exp (-d)) := by ring

/-- Exact midpoint quotient after removing the dominant exponential. -/
lemma vdwGeometricMidpoint_eq_normalized
    {d : ℝ} (hden : normalizedVdwDenominator d ≠ 0) :
    vdwGeometricMidpoint d =
      normalizedMidpointNumerator d / normalizedVdwDenominator d := by
  have hraw : Real.exp d - Real.exp (-d) - 2 * d ≠ 0 := by
    rw [vdwDenominator_eq_exp_mul]
    exact mul_ne_zero (Real.exp_ne_zero _) hden
  rw [vdwGeometricMidpoint_exp_form hraw]
  unfold normalizedMidpointNumerator
  rw [vdwDenominator_eq_exp_mul]
  have hpos : Real.exp (d / 2) = Real.exp d * Real.exp (-d / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hneg : Real.exp (-d / 2) = Real.exp d * Real.exp (-3 * d / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpos' : Real.exp (d / 2) =
      Real.exp d * Real.exp (-(d / 2)) := by
    simpa only [neg_div] using hpos
  have hneg' : Real.exp (-(d / 2)) =
      Real.exp d * Real.exp (-(d * 3 / 2)) := by
    convert hneg using 1 <;> congr 1 <;> ring
  have hnum :
      (d - 2) * Real.exp (d / 2) + (d + 2) * Real.exp (-(d / 2)) =
        Real.exp d * ((d - 2) * Real.exp (-(d / 2)) +
          (d + 2) * Real.exp (-(d * 3 / 2))) := by
    rw [hpos', hneg']
    ring
  field_simp [Real.exp_ne_zero, hden]
  rw [hnum]

/-- Exact gas branch after denominator normalization. -/
lemma vdwGasFreeVolume_eq_normalized
    {d : ℝ} (hden : normalizedVdwDenominator d ≠ 0) :
    vdwGasFreeVolume d = normalizedLowNumerator d / normalizedVdwDenominator d := by
  have hraw : Real.exp d - Real.exp (-d) - 2 * d ≠ 0 := by
    rw [vdwDenominator_eq_exp_mul]
    exact mul_ne_zero (Real.exp_ne_zero _) hden
  rw [vdwGasFreeVolume_exp_form hraw]
  unfold normalizedLowNumerator
  rw [vdwDenominator_eq_exp_mul]
  have h1 : Real.exp (-d) = Real.exp d * Real.exp (-2 * d) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-2 * d) = Real.exp d * Real.exp (-3 * d) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h0 : Real.exp d * Real.exp (-d) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hnum :
      (d - 2) + (d + 2) * Real.exp (-d) =
        Real.exp d * ((d - 2) * Real.exp (-d) +
          (d + 2) * Real.exp (-2 * d)) := by
    calc
      (d - 2) + (d + 2) * Real.exp (-d) =
          (d - 2) * (Real.exp d * Real.exp (-d)) +
            (d + 2) * (Real.exp d * Real.exp (-2 * d)) := by
        rw [h0, ← h1]
        ring
      _ = Real.exp d * ((d - 2) * Real.exp (-d) +
          (d + 2) * Real.exp (-2 * d)) := by ring
  field_simp [Real.exp_ne_zero, hden]
  rw [hnum]
  ring

/-- The basic exponential factors vanish at positive infinity. -/
lemma tendsto_exp_neg_atTop :
    Tendsto (fun d : ℝ => Real.exp (-d)) atTop (nhds 0) := by
  simpa only [Function.comp_def] using
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

/-- Linear factors remain negligible compared with exponential decay. -/
lemma tendsto_mul_exp_neg_atTop :
    Tendsto (fun d : ℝ => d * Real.exp (-d)) atTop (nhds 0) := by
  simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1

/-- Linear factors are negligible against exponential decay at any positive rate. -/
lemma tendsto_mul_exp_neg_linear (a : ℝ) (ha : 0 < a) :
    Tendsto (fun d : ℝ => d * Real.exp (-a * d)) atTop (nhds 0) := by
  have hlin : Tendsto (fun d : ℝ => a * d) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ha).2 tendsto_id
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
  convert hbase.const_mul a⁻¹ using 1
  · ext d
    simp only [Function.comp_apply, pow_one]
    field_simp [ha.ne']
  · simp

/-- The normalized denominator tends to one. -/
lemma tendsto_normalizedVdwDenominator :
    Tendsto normalizedVdwDenominator atTop (nhds 1) := by
  unfold normalizedVdwDenominator
  have h2 : Tendsto (fun d : ℝ => Real.exp (-2 * d)) atTop (nhds 0) := by
    have hlin : Tendsto (fun d : ℝ => 2 * d) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp hlin)
  have hd := tendsto_mul_exp_neg_atTop
  have h2d : Tendsto (fun d : ℝ => 2 * (d * Real.exp (-d))) atTop (nhds 0) :=
    by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2)).mul hd
  simpa [normalizedVdwDenominator, mul_assoc, mul_left_comm, mul_comm] using
    (tendsto_const_nhds.sub h2).sub h2d

/-- The normalized denominator is eventually nonzero. -/
lemma eventually_normalizedVdwDenominator_ne_zero :
    ∀ᶠ d : ℝ in atTop, normalizedVdwDenominator d ≠ 0 := by
  filter_upwards [tendsto_normalizedVdwDenominator.eventually
    (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))] with d hd
  exact hd

/-- The normalized midpoint numerator vanishes. -/
lemma tendsto_normalizedMidpointNumerator :
    Tendsto normalizedMidpointNumerator atTop (nhds 0) := by
  unfold normalizedMidpointNumerator
  have hhalf : Tendsto (fun d : ℝ => d * Real.exp (-d / 2)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      tendsto_mul_exp_neg_linear (1 / 2) (by norm_num)
  have hehalf : Tendsto (fun d : ℝ => Real.exp (-d / 2)) atTop (nhds 0) := by
    have hlin : Tendsto (fun d : ℝ => d / 2) atTop atTop :=
      by simpa [div_eq_mul_inv, mul_comm] using
        (tendsto_const_mul_atTop_of_pos
          (by norm_num : (0 : ℝ) < 1 / 2)).2 tendsto_id
    have hf : (fun d : ℝ => Real.exp (-d / 2)) =
        fun d => Real.exp (-(d / 2)) := by
      funext d
      congr 1
      ring
    rw [hf]
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlin)
  have hthree : Tendsto (fun d : ℝ => d * Real.exp (-3 * d / 2)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      tendsto_mul_exp_neg_linear (3 / 2) (by norm_num)
  have hethree : Tendsto (fun d : ℝ => Real.exp (-3 * d / 2)) atTop (nhds 0) := by
    have hlin : Tendsto (fun d : ℝ => 3 * d / 2) atTop atTop := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (tendsto_const_mul_atTop_of_pos
          (by norm_num : (0 : ℝ) < 3 / 2)).2 tendsto_id
    have hf : (fun d : ℝ => Real.exp (-3 * d / 2)) =
        fun d => Real.exp (-(3 * d / 2)) := by
      funext d
      congr 1
      ring
    rw [hf]
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlin)
  have h2ehalf : Tendsto (fun d : ℝ => 2 * Real.exp (-d / 2))
      atTop (nhds 0) :=
    by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2)).mul hehalf
  have h2ethree : Tendsto (fun d : ℝ => 2 * Real.exp (-3 * d / 2))
      atTop (nhds 0) :=
    by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2)).mul hethree
  convert ((hhalf.sub h2ehalf).add (hthree.add h2ethree)) using 1
  · ext d
    ring
  · norm_num

/-- The closed midpoint tends to zero at low temperature. -/
theorem tendsto_vdwGeometricMidpoint_atTop :
    Tendsto vdwGeometricMidpoint atTop (nhds 0) := by
  apply Tendsto.congr'
  · filter_upwards [eventually_normalizedVdwDenominator_ne_zero] with d hd
    exact (vdwGeometricMidpoint_eq_normalized hd).symm
  · convert tendsto_normalizedMidpointNumerator.div tendsto_normalizedVdwDenominator
      (by norm_num : (1 : ℝ) ≠ 0) using 1; norm_num

/-- The normalized gas numerator vanishes. -/
lemma tendsto_normalizedLowNumerator :
    Tendsto normalizedLowNumerator atTop (nhds 0) := by
  unfold normalizedLowNumerator
  have hd1 := tendsto_mul_exp_neg_atTop
  have he1 := tendsto_exp_neg_atTop
  have hd2 : Tendsto (fun d : ℝ => d * Real.exp (-2*d)) atTop (nhds 0) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      tendsto_mul_exp_neg_linear 2 (by norm_num)
  have he2 : Tendsto (fun d : ℝ => Real.exp (-2*d)) atTop (nhds 0) := by
    have hlin : Tendsto (fun d : ℝ => 2*d) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 tendsto_id
    have hf : (fun d : ℝ => Real.exp (-2*d)) =
        fun d => Real.exp (-(2*d)) := by
      funext d
      congr 1
      ring
    rw [hf]
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlin)
  have h2e1 : Tendsto (fun d : ℝ => 2 * Real.exp (-d))
      atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2)).mul he1
  have h2e2 : Tendsto (fun d : ℝ => 2 * Real.exp (-2*d))
      atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2)).mul he2
  convert ((hd1.sub h2e1).add (hd2.add h2e2)) using 1
  · ext d
    ring
  · norm_num

/-- The gas free-volume coordinate tends to zero. -/
theorem tendsto_vdwGasFreeVolume_atTop : Tendsto vdwGasFreeVolume atTop (nhds 0) := by
  apply Tendsto.congr'
  · filter_upwards [eventually_normalizedVdwDenominator_ne_zero] with d hd
    exact (vdwGasFreeVolume_eq_normalized hd).symm
  · convert tendsto_normalizedLowNumerator.div tendsto_normalizedVdwDenominator
      (by norm_num : (1 : ℝ) ≠ 0) using 1; norm_num

/-- The liquid free-volume coordinate diverges to positive infinity. -/
theorem tendsto_vdwLiquidFreeVolume_atTop : Tendsto vdwLiquidFreeVolume atTop atTop := by
  have hbase : Tendsto (fun d : ℝ => d - 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-2 : ℝ) tendsto_id
  have hm : Tendsto (fun d : ℝ => (d - 2) / 2) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_const_mul_atTop_of_pos
        (by norm_num : (0 : ℝ) < 1 / 2)).2 hbase
  have hineq : (fun d : ℝ => (d - 2) / 2) ≤ᶠ[atTop] vdwLiquidFreeVolume := by
    filter_upwards [eventually_normalizedVdwDenominator_ne_zero,
      tendsto_normalizedVdwDenominator.eventually
        (eventually_gt_nhds (by norm_num : (0:ℝ)<1)),
      tendsto_normalizedVdwDenominator.eventually
        (eventually_lt_nhds (by norm_num : (1:ℝ)<2)),
      eventually_ge_atTop (2 : ℝ)]
      with d hne hpos hlt hd
    have hraw : Real.exp d - Real.exp (-d) - 2 * d ≠ 0 := by
      rw [vdwDenominator_eq_exp_mul]
      exact mul_ne_zero (Real.exp_ne_zero _) hne
    rw [vdwLiquidFreeVolume_exp_form hraw, vdwDenominator_eq_exp_mul]
    have he : 0 < Real.exp d := Real.exp_pos d
    let n := (d - 2) * Real.exp d + (d + 2)
    have hn : (d - 2) * Real.exp d ≤ n := by
      dsimp [n]
      nlinarith [Real.exp_pos d]
    have hfactor : 0 ≤ (d - 2) * Real.exp d :=
      mul_nonneg (by linarith) he.le
    have hcross : (d - 2) * (Real.exp d *
        normalizedVdwDenominator d) ≤ n * 2 := by
      calc
        (d - 2) * (Real.exp d * normalizedVdwDenominator d) =
            ((d - 2) * Real.exp d) * normalizedVdwDenominator d := by ring
        _ ≤ ((d - 2) * Real.exp d) * 2 :=
          mul_le_mul_of_nonneg_left hlt.le hfactor
        _ ≤ n * 2 := mul_le_mul_of_nonneg_right hn (by norm_num)
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (mul_pos he hpos)).2
    simpa [n, div_eq_mul_inv] using hcross
  exact tendsto_atTop_mono' atTop hineq hm

/-- Reduced gas density tends to zero. -/
theorem tendsto_reducedGasDensity_atTop :
    Tendsto reducedGasDensity atTop (nhds 0) := by
  unfold reducedGasDensity reducedDensityFromFreeVolume
  have hnum : Tendsto (fun d : ℝ => (3 : ℝ) * vdwGasFreeVolume d)
      atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (3 : ℝ)) atTop (nhds 3)).mul
          tendsto_vdwGasFreeVolume_atTop
  have hden : Tendsto (fun d : ℝ => 1 + vdwGasFreeVolume d)
      atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).add
          tendsto_vdwGasFreeVolume_atTop
  convert hnum.div hden (by norm_num) using 1; norm_num

/-- Reduced liquid density tends to the close-packing value three. -/
theorem tendsto_reducedLiquidDensity_atTop :
    Tendsto reducedLiquidDensity atTop (nhds 3) := by
  have hplus : Tendsto (fun z : ℝ => 1 + z) atTop atTop :=
    by
      convert tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_id : Tendsto (fun z : ℝ => z) atTop atTop) using 1
      ext z
      dsimp [id]
      ring
  have hinv : Tendsto (fun z : ℝ => (1+z)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hplus
  have hcomp := hinv.comp tendsto_vdwLiquidFreeVolume_atTop
  have hrepr : ∀ᶠ d : ℝ in atTop,
      reducedLiquidDensity d =
        3 - 3 * (1 + vdwLiquidFreeVolume d)⁻¹ := by
    filter_upwards [tendsto_vdwLiquidFreeVolume_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))] with d hd
    have hden : 1 + vdwLiquidFreeVolume d ≠ 0 := ne_of_gt (by linarith)
    unfold reducedLiquidDensity reducedDensityFromFreeVolume
    change 3 * vdwLiquidFreeVolume d / (1 + vdwLiquidFreeVolume d) =
      3 - 3 * (1 + vdwLiquidFreeVolume d)⁻¹
    rw [div_eq_mul_inv]
    have hcancel : (1 + vdwLiquidFreeVolume d) * (1 + vdwLiquidFreeVolume d)⁻¹ = 1 :=
      mul_inv_cancel₀ hden
    calc
      3 * vdwLiquidFreeVolume d * (1 + vdwLiquidFreeVolume d)⁻¹ =
          3 * ((1 + vdwLiquidFreeVolume d) * (1 + vdwLiquidFreeVolume d)⁻¹ -
            (1 + vdwLiquidFreeVolume d)⁻¹) := by ring
      _ = 3 - 3 * (1 + vdwLiquidFreeVolume d)⁻¹ := by rw [hcancel]; ring
  apply Tendsto.congr'
  · filter_upwards [hrepr] with d hd
    exact hd.symm
  · simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (3 : ℝ)) atTop (nhds 3)).sub
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (3 : ℝ)) atTop (nhds 3)).mul hcomp)

/-- Free-volume product diverges because the liquid branch diverges while the gas
branch tends to zero. -/
theorem tendsto_coexistenceFreeVolumeProduct_atTop :
    Tendsto coexistenceFreeVolumeProduct atTop atTop := by
  unfold coexistenceFreeVolumeProduct
  have hhigh : Tendsto (fun d : ℝ => 1 + vdwLiquidFreeVolume d) atTop atTop := by
    simpa [add_comm] using
      tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_vdwLiquidFreeVolume_atTop
  have hlow : Tendsto (fun d : ℝ => 1 + vdwGasFreeVolume d) atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).add
          tendsto_vdwGasFreeVolume_atTop
  have hhalf : Tendsto (fun d : ℝ =>
      (1 / 2 : ℝ) * (1 + vdwLiquidFreeVolume d)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).2
      hhigh
  have hge : (fun d : ℝ =>
      (1 / 2 : ℝ) * (1 + vdwLiquidFreeVolume d)) ≤ᶠ[atTop]
      (fun d => (1 + vdwLiquidFreeVolume d) * (1 + vdwGasFreeVolume d)) := by
    filter_upwards
      [hhigh.eventually (eventually_gt_atTop (0 : ℝ)),
        hlow.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
      with d hhigh' hlow'
    nlinarith [mul_nonneg (le_of_lt hhigh')
      (by linarith : 0 ≤ 1 + vdwGasFreeVolume d - 1 / 2)]
  exact tendsto_atTop_mono' atTop hge hhalf

/-- Candidate low-temperature reduced-temperature limit. -/
theorem tendsto_reducedCoexistenceTemperature_atTop :
    Tendsto reducedCoexistenceTemperature atTop (nhds 0) := by
  unfold reducedCoexistenceTemperature
  have hmid2 : Tendsto (fun d : ℝ => vdwGeometricMidpoint d ^ 2)
      atTop (nhds 0) :=
    by simpa using tendsto_vdwGeometricMidpoint_atTop.pow 2
  have hratio : Tendsto (fun d : ℝ =>
      (1 - vdwGeometricMidpoint d ^ 2) /
        coexistenceFreeVolumeProduct d) atTop (nhds 0) :=
    by
      have hratioNum : Tendsto (fun d : ℝ =>
          1 - vdwGeometricMidpoint d ^ 2) atTop (nhds 1) := by
        simpa using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).sub hmid2
      exact Filter.Tendsto.div_atTop (𝕜 := ℝ) (a := (1 : ℝ)) hratioNum
        tendsto_coexistenceFreeVolumeProduct_atTop
  have hnum : Tendsto (fun d : ℝ =>
      27 * vdwGeometricMidpoint d *
        (vdwGeometricMidpoint d + Real.cosh (d / 2)) /
        coexistenceFreeVolumeProduct d) atTop (nhds (27 / 2)) := by
    have hbase := ((tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).sub
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).mul hratio))
    have hscaled : Tendsto (fun d : ℝ =>
        ((27 : ℝ) / 2) *
          (1 - (1 - vdwGeometricMidpoint d ^ 2) /
            coexistenceFreeVolumeProduct d)) atTop (nhds (27 / 2)) := by
      simpa using hbase.const_mul ((27 : ℝ) / 2)
    have heq : ∀ᶠ d : ℝ in atTop,
        (27 * vdwGeometricMidpoint d *
          (vdwGeometricMidpoint d + Real.cosh (d / 2)) /
          coexistenceFreeVolumeProduct d) =
        ((27 : ℝ) / 2) *
          (1 - (1 - vdwGeometricMidpoint d ^ 2) /
            coexistenceFreeVolumeProduct d) := by
      filter_upwards [tendsto_coexistenceFreeVolumeProduct_atTop.eventually
        (eventually_gt_atTop (0 : ℝ))] with d hd
      have hden : coexistenceFreeVolumeProduct d ≠ 0 := ne_of_gt hd
      rw [coexistenceFreeVolumeProduct_eq]
      have hden' : 1 + 2 * vdwGeometricMidpoint d * Real.cosh (d / 2) +
          vdwGeometricMidpoint d ^ 2 ≠ 0 := by
        rw [← coexistenceFreeVolumeProduct_eq]
        exact hden
      have hden'' :
          1 + vdwGeometricMidpoint d * 2 * Real.cosh (d / 2) +
              vdwGeometricMidpoint d ^ 2 ≠ 0 := by
        convert hden' using 1
        ring
      field_simp [hden'']
      ring
    apply Tendsto.congr'
    · filter_upwards [heq] with d hd
      exact hd.symm
    · exact hscaled
  have hfourprod : Tendsto
      (fun d : ℝ => 4 * coexistenceFreeVolumeProduct d) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 4)).2
      tendsto_coexistenceFreeVolumeProduct_atTop
  have hinv : Tendsto
      (fun d : ℝ => (4 * coexistenceFreeVolumeProduct d)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hfourprod
  have hidentity : ∀ d : ℝ,
      reducedCoexistenceTemperature d =
        (27 * vdwGeometricMidpoint d *
          (vdwGeometricMidpoint d + Real.cosh (d / 2)) /
          coexistenceFreeVolumeProduct d) *
          (4 * coexistenceFreeVolumeProduct d)⁻¹ := by
    intro d
    unfold reducedCoexistenceTemperature
    let p := coexistenceFreeVolumeProduct d
    change (27 * vdwGeometricMidpoint d *
        (vdwGeometricMidpoint d + Real.cosh (d / 2))) / (4 * p ^ 2) =
      ((27 * vdwGeometricMidpoint d *
        (vdwGeometricMidpoint d + Real.cosh (d / 2))) / p) * (4 * p)⁻¹
    rw [div_eq_mul_inv, div_eq_mul_inv,
      show 4 * p ^ 2 = (4 * p) * p by ring, mul_inv]
    ring
  apply Tendsto.congr' (Eventually.of_forall fun d => (hidentity d).symm)
  simpa using hnum.mul hinv

/-- Candidate low-temperature reduced-pressure limit. -/
theorem tendsto_reducedCoexistencePressure_atTop :
    Tendsto reducedCoexistencePressure atTop (nhds 0) := by
  unfold reducedCoexistencePressure
  have hmid2 : Tendsto (fun d : ℝ => vdwGeometricMidpoint d ^ 2)
      atTop (nhds 0) := by
    simpa using tendsto_vdwGeometricMidpoint_atTop.pow 2
  have hnum : Tendsto (fun d : ℝ =>
      27 * vdwGeometricMidpoint d ^ 2 *
        (1 - vdwGeometricMidpoint d ^ 2)) atTop (nhds 0) := by
    have hscale : Tendsto (fun d : ℝ => (27 : ℝ) *
        vdwGeometricMidpoint d ^ 2) atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (27 : ℝ)) atTop (nhds 27)).mul hmid2
    have hfactor : Tendsto (fun d : ℝ =>
        1 - vdwGeometricMidpoint d ^ 2) atTop (nhds 1) := by
      simpa using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1)).sub hmid2
    convert hscale.mul hfactor using 1; norm_num
  have hden : Tendsto (fun d => (coexistenceFreeVolumeProduct d)^2)
      atTop atTop := by
    have hge : (fun d : ℝ => coexistenceFreeVolumeProduct d) ≤ᶠ[atTop]
        (fun d => (coexistenceFreeVolumeProduct d)^2) := by
      filter_upwards [tendsto_coexistenceFreeVolumeProduct_atTop.eventually
        (eventually_ge_atTop (1 : ℝ))] with d hd
      nlinarith
    exact tendsto_atTop_mono' atTop hge
      tendsto_coexistenceFreeVolumeProduct_atTop
  exact hnum.div_atTop hden

/-- Full low-temperature/large-parameter conjunction. -/
theorem lowTemperatureLimitSpecification : LowTemperatureLimitSpecification := by
  exact ⟨tendsto_reducedCoexistenceTemperature_atTop,
    tendsto_reducedCoexistencePressure_atTop,
    tendsto_reducedGasDensity_atTop,
    tendsto_reducedLiquidDensity_atTop⟩

end ClassicalThermodynamics.Models.VanDerWaals.Pure
