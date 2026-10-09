import ClassicalThermodynamics.Methods.CoexistenceParametrisation.VanDerWaalsBranches

namespace ClassicalThermodynamics.Methods.CoexistenceParametrisation

/-- Removable critical value suggested by the cubic-order expansion at `d = 0`. -/
noncomputable abbrev vdwGeometricMidpointWithCriticalValue := vdwGeometricMidpoint

@[simp] theorem vdwGeometricMidpointWithCriticalValue_zero :
    vdwGeometricMidpointWithCriticalValue 0 = 1 / 2 := by
  simp [vdwGeometricMidpointWithCriticalValue, vdwGeometricMidpoint]

/-- Exact exponential representation useful for the large-`d` analysis. -/
theorem vdwGeometricMidpoint_exp_form {d : ℝ}
    (_hden : Real.exp d - Real.exp (-d) - 2 * d ≠ 0) :
    vdwGeometricMidpoint d =
      ((d - 2) * Real.exp (d / 2) + (d + 2) * Real.exp (-d / 2)) /
      (Real.exp d - Real.exp (-d) - 2 * d) := by
  have hd : d ≠ 0 := by
    intro hz
    subst d
    exact _hden (by simp)
  rw [vdwGeometricMidpoint_eq_formula hd]
  unfold vdwGeometricMidpointFormula
  rw [Real.cosh_eq, Real.sinh_eq, Real.sinh_eq]
  field_simp [_hden]
  ring

/-- Exact high-branch form after multiplying the midpoint expression by `exp(d/2)`. -/
theorem vdwLiquidFreeVolume_exp_form {d : ℝ}
    (hden : Real.exp d - Real.exp (-d) - 2 * d ≠ 0) :
    vdwLiquidFreeVolume d =
      ((d - 2) * Real.exp d + (d + 2)) /
      (Real.exp d - Real.exp (-d) - 2 * d) := by
  unfold vdwLiquidFreeVolume
  rw [vdwGeometricMidpoint_exp_form hden]
  field_simp [hden]
  ring_nf
  have hprod :
      Real.exp (d * (1 / 2)) * Real.exp (d * (-1 / 2)) = 1 := by
    rw [← Real.exp_add]
    rw [show d * (1 / 2) + d * (-1 / 2) = 0 by ring, Real.exp_zero]
  have hsquare :
      Real.exp (d * (1 / 2)) ^ 2 = Real.exp d := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hsquare]
  linear_combination
    ((d + 2) * (-(d * 2) + Real.exp d - Real.exp (-d))⁻¹) * hprod

/-- Exact low-branch form that exhibits exponential dilution for large `d`. -/
theorem vdwGasFreeVolume_exp_form {d : ℝ}
    (hden : Real.exp d - Real.exp (-d) - 2 * d ≠ 0) :
    vdwGasFreeVolume d =
      ((d - 2) + (d + 2) * Real.exp (-d)) /
      (Real.exp d - Real.exp (-d) - 2 * d) := by
  unfold vdwGasFreeVolume
  rw [vdwGeometricMidpoint_exp_form hden]
  field_simp [hden]
  ring_nf
  have hprod :
      Real.exp (d * (1 / 2)) * Real.exp (d * (-1 / 2)) = 1 := by
    rw [← Real.exp_add]
    rw [show d * (1 / 2) + d * (-1 / 2) = 0 by ring, Real.exp_zero]
  have hsquare :
      Real.exp (d * (-1 / 2)) ^ 2 = Real.exp (-d) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hsquare]
  have hprod' :
      Real.exp (d * (-1 / 2)) * Real.exp (d * (1 / 2)) = 1 := by
    rw [mul_comm, hprod]
  linear_combination
    ((d - 2) * (-(d * 2) + Real.exp d - Real.exp (-d))⁻¹) * hprod'

end ClassicalThermodynamics.Methods.CoexistenceParametrisation
