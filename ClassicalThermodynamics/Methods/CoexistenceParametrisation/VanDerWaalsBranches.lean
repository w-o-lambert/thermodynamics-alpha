import ClassicalThermodynamics.Models.VanDerWaals.Pure.Coexistence
namespace ClassicalThermodynamics.Methods.CoexistenceParametrisation
open ClassicalThermodynamics.Models.VanDerWaals.Pure

noncomputable def vdwGeometricMidpointFormula (d : ℝ) : ℝ :=
  (d * Real.cosh (d / 2) - 2 * Real.sinh (d / 2)) / (Real.sinh d - d)

/-- Common pure-fluid coexistence function for the van der Waals and Berthelot
equations. Its value at zero is the removable critical value of the quotient. -/
noncomputable def vdwGeometricMidpoint (d : ℝ) : ℝ :=
  if d = 0 then 1 / 2 else vdwGeometricMidpointFormula d

lemma vdwGeometricMidpoint_eq_formula {d : ℝ} (hd : d ≠ 0) :
    vdwGeometricMidpoint d = vdwGeometricMidpointFormula d := by
  simp [vdwGeometricMidpoint, hd]

@[simp] theorem vdwGeometricMidpoint_zero :
    vdwGeometricMidpoint 0 = 1 / 2 := by
  simp [vdwGeometricMidpoint]

noncomputable def vdwLiquidFreeVolume (d : ℝ) : ℝ := vdwGeometricMidpoint d * Real.exp (d / 2)
noncomputable def vdwGasFreeVolume (d : ℝ) : ℝ := vdwGeometricMidpoint d * Real.exp (-d / 2)

@[simp] theorem vdwLiquidFreeVolume_zero : vdwLiquidFreeVolume 0 = 1 / 2 := by
  simp [vdwLiquidFreeVolume]

@[simp] theorem vdwGasFreeVolume_zero : vdwGasFreeVolume 0 = 1 / 2 := by
  simp [vdwGasFreeVolume]

theorem vdwLiquidFreeVolume_div_vdwGasFreeVolume {d : ℝ} (hm : vdwGeometricMidpoint d ≠ 0) :
    vdwLiquidFreeVolume d / vdwGasFreeVolume d = Real.exp d := by
  unfold vdwLiquidFreeVolume vdwGasFreeVolume
  apply (div_eq_iff (mul_ne_zero hm (Real.exp_ne_zero _))).2
  have he : Real.exp (d / 2) = Real.exp d * Real.exp (-d / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

lemma vdwLiquidFreeVolume_mul_vdwGasFreeVolume (d : ℝ) :
    vdwLiquidFreeVolume d * vdwGasFreeVolume d = (vdwGeometricMidpoint d)^2 := by
  unfold vdwLiquidFreeVolume vdwGasFreeVolume
  calc
    vdwGeometricMidpoint d * Real.exp (d / 2) *
        (vdwGeometricMidpoint d * Real.exp (-d / 2)) =
        vdwGeometricMidpoint d ^ 2 *
          (Real.exp (d / 2) * Real.exp (-d / 2)) := by ring
    _ = vdwGeometricMidpoint d ^ 2 *
        Real.exp (d / 2 + -d / 2) := by rw [← Real.exp_add]
    _ = vdwGeometricMidpoint d ^ 2 := by
      rw [show d / 2 + -d / 2 = 0 by ring, Real.exp_zero, mul_one]

lemma vdwLiquidFreeVolume_sub_vdwGasFreeVolume (d : ℝ) :
    vdwLiquidFreeVolume d - vdwGasFreeVolume d =
      2 * vdwGeometricMidpoint d * Real.sinh (d / 2) := by
  unfold vdwLiquidFreeVolume vdwGasFreeVolume
  rw [Real.sinh_eq]
  ring

lemma vdwLiquidFreeVolume_add_vdwGasFreeVolume (d : ℝ) :
    vdwLiquidFreeVolume d + vdwGasFreeVolume d =
      2 * vdwGeometricMidpoint d * Real.cosh (d / 2) := by
  unfold vdwLiquidFreeVolume vdwGasFreeVolume
  rw [Real.cosh_eq]
  ring

theorem vdwGeometricMidpoint_neg (d : ℝ) :
    vdwGeometricMidpoint (-d) = vdwGeometricMidpoint d := by
  by_cases hd : d = 0
  · simp [hd, vdwGeometricMidpoint]
  · have hneg : -d ≠ 0 := neg_ne_zero.mpr hd
    have hnum :
        (-d) * Real.cosh (-d / 2) - 2 * Real.sinh (-d / 2) =
          -(d * Real.cosh (d / 2) - 2 * Real.sinh (d / 2)) := by
      simp only [neg_div, Real.cosh_neg, Real.sinh_neg]
      ring
    have hden :
        Real.sinh (-d) - (-d) = -(Real.sinh d - d) := by
      rw [Real.sinh_neg]
      ring
    rw [vdwGeometricMidpoint_eq_formula hneg,
      vdwGeometricMidpoint_eq_formula hd]
    unfold vdwGeometricMidpointFormula
    rw [hnum, hden, neg_div, div_neg, neg_neg]

@[simp] theorem vdwLiquidFreeVolume_neg (d : ℝ) : vdwLiquidFreeVolume (-d) = vdwGasFreeVolume d := by
  unfold vdwLiquidFreeVolume vdwGasFreeVolume
  rw [vdwGeometricMidpoint_neg]

@[simp] theorem vdwGasFreeVolume_neg (d : ℝ) : vdwGasFreeVolume (-d) = vdwLiquidFreeVolume d := by
  unfold vdwGasFreeVolume vdwLiquidFreeVolume
  rw [vdwGeometricMidpoint_neg]
  rw [show - -d / 2 = d / 2 by ring]

/-- The closed midpoint scale satisfies the algebraic midpoint equation. -/
lemma vdwGeometricMidpoint_closed_identity
    {d : ℝ} (hden : Real.sinh d - d ≠ 0) :
    d * (Real.cosh (d / 2) + vdwGeometricMidpoint d) =
      2 * Real.sinh (d / 2) *
        (1 + vdwGeometricMidpoint d * Real.cosh (d / 2)) := by
  have hd : d ≠ 0 := by
    intro hz
    subst d
    exact hden (by simp)
  have hsinh : Real.sinh d =
      2 * Real.sinh (d / 2) * Real.cosh (d / 2) := by
    rw [show d = d / 2 + d / 2 by ring, Real.sinh_add]
    ring
  rw [vdwGeometricMidpoint_eq_formula hd]
  unfold vdwGeometricMidpointFormula
  field_simp [hden]
  rw [hsinh]
  ring

/-- Direct verification of the closed branch formula. -/
theorem vdwBranches_parameterFreeCoexistence
    {d : ℝ}
    (hm : vdwGeometricMidpoint d ≠ 0)
    (hbranchDiff : 2 * vdwGeometricMidpoint d * Real.sinh (d / 2) ≠ 0)
    (hpairDen : 2 * vdwGeometricMidpoint d * Real.cosh (d / 2) +
        2 * (vdwGeometricMidpoint d)^2 ≠ 0)
    (hHden : Real.sinh d - d ≠ 0) :
    ParameterFreeCoexistence (vdwLiquidFreeVolume d) (vdwGasFreeVolume d) := by
  have hlog : Real.log (vdwLiquidFreeVolume d / vdwGasFreeVolume d) = d := by
    rw [vdwLiquidFreeVolume_div_vdwGasFreeVolume hm, Real.log_exp]
  have hsum := vdwLiquidFreeVolume_add_vdwGasFreeVolume d
  have hdiff := vdwLiquidFreeVolume_sub_vdwGasFreeVolume d
  have hprod := vdwLiquidFreeVolume_mul_vdwGasFreeVolume d
  have hprod2 :
      2 * vdwLiquidFreeVolume d * vdwGasFreeVolume d =
        2 * vdwGeometricMidpoint d ^ 2 := by
    calc
      2 * vdwLiquidFreeVolume d * vdwGasFreeVolume d =
          2 * (vdwLiquidFreeVolume d * vdwGasFreeVolume d) := by ring
      _ = 2 * vdwGeometricMidpoint d ^ 2 := by rw [hprod]
  have hmid := vdwGeometricMidpoint_closed_identity hHden
  unfold ParameterFreeCoexistence
  rw [hlog]
  rw [hdiff]
  have hpair :
      vdwLiquidFreeVolume d + vdwGasFreeVolume d +
        2 * vdwLiquidFreeVolume d * vdwGasFreeVolume d ≠ 0 := by
    rw [hsum, hprod2]
    exact hpairDen
  apply (div_eq_div_iff hbranchDiff hpair).2
  rw [hsum, hprod2]
  calc
    d * (2 * vdwGeometricMidpoint d * Real.cosh (d / 2) +
        2 * vdwGeometricMidpoint d ^ 2) =
        2 * vdwGeometricMidpoint d *
          (d * (Real.cosh (d / 2) + vdwGeometricMidpoint d)) := by ring
    _ = 2 * vdwGeometricMidpoint d *
          (2 * Real.sinh (d / 2) *
            (1 + vdwGeometricMidpoint d * Real.cosh (d / 2))) := by
      rw [hmid]
    _ = (2 + 2 * vdwGeometricMidpoint d * Real.cosh (d / 2)) *
          (2 * vdwGeometricMidpoint d * Real.sinh (d / 2)) := by ring
    _ = (2 + vdwLiquidFreeVolume d + vdwGasFreeVolume d) *
          (2 * vdwGeometricMidpoint d * Real.sinh (d / 2)) := by
      rw [← hsum]
      ring
end ClassicalThermodynamics.Methods.CoexistenceParametrisation
