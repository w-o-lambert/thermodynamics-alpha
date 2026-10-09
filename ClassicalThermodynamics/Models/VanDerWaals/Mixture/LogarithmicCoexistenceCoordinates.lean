import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Thermodynamics

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Componentwise geometric midpoint of two positive phase-density vectors. -/
noncomputable def logarithmicMidpoint
    (rhoA rhoB : State (ι := ι)) : State (ι := ι) :=
  fun i => Real.sqrt (rhoA i * rhoB i)

/-- Componentwise logarithmic phase separation. -/
noncomputable def logarithmicDifference
    (rhoA rhoB : State (ι := ι)) : State (ι := ι) :=
  fun i => Real.log (rhoA i / rhoB i)

/-- Reconstruction of the high branch from midpoint and logarithmic difference. -/
noncomputable def logarithmicHigh
    (m d : State (ι := ι)) : State (ι := ι) :=
  fun i => m i * Real.exp (d i / 2)

/-- Reconstruction of the low branch from midpoint and logarithmic difference. -/
noncomputable def logarithmicLow
    (m d : State (ι := ι)) : State (ι := ι) :=
  fun i => m i * Real.exp (-d i / 2)

@[simp] theorem logarithmicHigh_mul_logarithmicLow
    (m d : State (ι := ι)) (i : ι) :
    logarithmicHigh m d i * logarithmicLow m d i = (m i)^2 := by
  unfold logarithmicHigh logarithmicLow
  rw [← Real.exp_add]
  simp
  ring

/-- The componentwise branch ratio is exponential in the logarithmic coordinate. -/
theorem logarithmicHigh_div_logarithmicLow
    (m d : State (ι := ι)) (i : ι) (hm : m i ≠ 0) :
    logarithmicHigh m d i / logarithmicLow m d i = Real.exp (d i) := by
  unfold logarithmicHigh logarithmicLow
  have he : Real.exp (-d i / 2) ≠ 0 := Real.exp_ne_zero _
  field_simp [hm, he]
  rw [← Real.exp_sub]
  congr 1
  ring

/-- Positive state pairs are reconstructed exactly by their logarithmic coordinates. -/
theorem logarithmicHigh_of_coordinates
    {rhoA rhoB : State (ι := ι)}
    (hA : ∀ i, 0 < rhoA i) (hB : ∀ i, 0 < rhoB i) (i : ι) :
    logarithmicHigh (logarithmicMidpoint rhoA rhoB)
      (logarithmicDifference rhoA rhoB) i = rhoA i := by
  unfold logarithmicHigh logarithmicMidpoint logarithmicDifference
  rw [Real.exp_half_log (div_pos (hA i) (hB i))]
  rw [Real.sqrt_eq_iff_sq_eq (mul_nonneg (le_of_lt (hA i)) (le_of_lt (hB i)))]
  field_simp [(ne_of_gt (hB i))]
  ring

/-- The low state is likewise reconstructed exactly. -/
theorem logarithmicLow_of_coordinates
    {rhoA rhoB : State (ι := ι)}
    (hA : ∀ i, 0 < rhoA i) (hB : ∀ i, 0 < rhoB i) (i : ι) :
    logarithmicLow (logarithmicMidpoint rhoA rhoB)
      (logarithmicDifference rhoA rhoB) i = rhoB i := by
  unfold logarithmicLow logarithmicMidpoint logarithmicDifference
  have hratio : 0 < rhoA i / rhoB i := div_pos (hA i) (hB i)
  rw [show Real.exp (-Real.log (rhoA i / rhoB i) / 2) =
      Real.sqrt (rhoB i / rhoA i) by
    rw [show -Real.log (rhoA i / rhoB i) = Real.log (rhoB i / rhoA i) by
      rw [Real.log_div (ne_of_gt (hA i)) (ne_of_gt (hB i)),
        Real.log_div (ne_of_gt (hB i)) (ne_of_gt (hA i))]
      ring]
    exact Real.exp_half_log (div_pos (hB i) (hA i))]
  nlinarith [Real.sq_sqrt (mul_nonneg (le_of_lt (hA i)) (le_of_lt (hB i))),
    Real.sq_sqrt (div_nonneg (le_of_lt (hB i)) (le_of_lt (hA i)))]

/-- Coexistence expressed directly in logarithmic midpoint/difference coordinates. -/
def LogarithmicCoexistence
    (M : Model (ι := ι)) (m d : State (ι := ι)) : Prop :=
  Coexist M (logarithmicHigh m d) (logarithmicLow m d)

/-- Phase exchange changes only the sign of the logarithmic-difference vector. -/
@[simp] theorem logarithmicHigh_neg
    (m d : State (ι := ι)) : logarithmicHigh m (fun i => -d i) = logarithmicLow m d := by
  funext i
  unfold logarithmicHigh logarithmicLow
  ring_nf

@[simp] theorem logarithmicLow_neg
    (m d : State (ι := ι)) : logarithmicLow m (fun i => -d i) = logarithmicHigh m d := by
  funext i
  unfold logarithmicHigh logarithmicLow
  ring_nf

end ClassicalThermodynamics.Models.VanDerWaals.Mixture

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive midpoint coordinates reconstruct positive phase states. -/
theorem logarithmicHigh_pos
    (m d : State (ι := ι)) (hm : ∀ i, 0 < m i) :
    ∀ i, 0 < logarithmicHigh m d i := by
  intro i
  unfold logarithmicHigh
  positivity

/-- The low reconstructed branch is positive under the same midpoint condition. -/
theorem logarithmicLow_pos
    (m d : State (ι := ι)) (hm : ∀ i, 0 < m i) :
    ∀ i, 0 < logarithmicLow m d i := by
  intro i
  unfold logarithmicLow
  positivity

/-- Positive phase pairs have positive geometric-midpoint coordinates. -/
theorem logarithmicMidpoint_pos
    {rhoA rhoB : State (ι := ι)}
    (hA : ∀ i, 0 < rhoA i) (hB : ∀ i, 0 < rhoB i) :
    ∀ i, 0 < logarithmicMidpoint rhoA rhoB i := by
  intro i
  unfold logarithmicMidpoint
  exact Real.sqrt_pos.2 (mul_pos (hA i) (hB i))

/-- Full functional reconstruction of the high state. -/
theorem logarithmicHigh_reconstruct
    {rhoA rhoB : State (ι := ι)}
    (hA : ∀ i, 0 < rhoA i) (hB : ∀ i, 0 < rhoB i) :
    logarithmicHigh (logarithmicMidpoint rhoA rhoB)
      (logarithmicDifference rhoA rhoB) = rhoA := by
  funext i
  exact logarithmicHigh_of_coordinates hA hB i

/-- Full functional reconstruction of the low state. -/
theorem logarithmicLow_reconstruct
    {rhoA rhoB : State (ι := ι)}
    (hA : ∀ i, 0 < rhoA i) (hB : ∀ i, 0 < rhoB i) :
    logarithmicLow (logarithmicMidpoint rhoA rhoB)
      (logarithmicDifference rhoA rhoB) = rhoB := by
  funext i
  exact logarithmicLow_of_coordinates hA hB i

/-- Coordinates recover the original logarithmic difference for positive midpoint. -/
theorem logarithmicDifference_reconstruct
    (m d : State (ι := ι)) (hm : ∀ i, 0 < m i) :
    logarithmicDifference (logarithmicHigh m d) (logarithmicLow m d) = d := by
  funext i
  unfold logarithmicDifference
  rw [logarithmicHigh_div_logarithmicLow m d i (ne_of_gt (hm i)), Real.log_exp]

/-- Coordinates recover the original midpoint for positive midpoint. -/
theorem logarithmicMidpoint_reconstruct
    (m d : State (ι := ι)) (hm : ∀ i, 0 < m i) :
    logarithmicMidpoint (logarithmicHigh m d) (logarithmicLow m d) = m := by
  funext i
  unfold logarithmicMidpoint
  rw [logarithmicHigh_mul_logarithmicLow]
  exact Real.sqrt_sq_eq_abs.trans (abs_of_pos (hm i))

/-- Ordering is encoded componentwise by the sign of the logarithmic coordinate. -/
theorem logarithmicLow_lt_high_iff
    (m d : State (ι := ι)) (i : ι) (hm : 0 < m i) :
    logarithmicLow m d i < logarithmicHigh m d i ↔ 0 < d i := by
  unfold logarithmicLow logarithmicHigh
  rw [mul_lt_mul_left hm, Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

end ClassicalThermodynamics.Models.VanDerWaals.Mixture

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Zero logarithmic separation is exactly equality of reconstructed branches. -/
theorem logarithmicHigh_eq_low_iff
    (m d : State (ι := ι)) (i : ι) (hm : 0 < m i) :
    logarithmicHigh m d i = logarithmicLow m d i ↔ d i = 0 := by
  unfold logarithmicHigh logarithmicLow
  rw [mul_left_cancel₀ (ne_of_gt hm)]
  constructor
  · intro h
    have := Real.exp_injective h
    linarith
  · intro h
    rw [h]
    norm_num

/-- A negative logarithmic coordinate reverses the componentwise branch order. -/
theorem logarithmicHigh_lt_low_iff
    (m d : State (ι := ι)) (i : ι) (hm : 0 < m i) :
    logarithmicHigh m d i < logarithmicLow m d i ↔ d i < 0 := by
  unfold logarithmicHigh logarithmicLow
  rw [mul_lt_mul_left hm, Real.exp_lt_exp]
  constructor <;> intro h <;> linarith

/-- Nonpositive logarithmic separation is equivalent to high not exceeding low. -/
theorem logarithmicHigh_le_low_iff
    (m d : State (ι := ι)) (i : ι) (hm : 0 < m i) :
    logarithmicHigh m d i ≤ logarithmicLow m d i ↔ d i ≤ 0 := by
  unfold logarithmicHigh logarithmicLow
  rw [mul_le_mul_left hm, Real.exp_le_exp]
  constructor <;> intro h <;> linarith

/-- Nonnegative logarithmic separation is equivalent to low not exceeding high. -/
theorem logarithmicLow_le_high_iff
    (m d : State (ι := ι)) (i : ι) (hm : 0 < m i) :
    logarithmicLow m d i ≤ logarithmicHigh m d i ↔ 0 ≤ d i := by
  unfold logarithmicHigh logarithmicLow
  rw [mul_le_mul_left hm, Real.exp_le_exp]
  constructor <;> intro h <;> linarith

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
