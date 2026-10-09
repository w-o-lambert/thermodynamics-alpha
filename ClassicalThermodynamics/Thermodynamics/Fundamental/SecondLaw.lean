import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Tactic.Linarith

namespace ClassicalThermodynamics.Thermodynamics.Fundamental

open scoped BigOperators

/-- Entropy accounting for a closed system exchanging heat with finitely many
reservoirs. Heat is positive into the system; `entropyGeneration` is the
internal entropy production required by the Second Law. -/
structure SecondLawData (ι : Type*) [Fintype ι] where
  entropyChange : ℝ
  heatTransfer : ι → ℝ
  reservoirTemperature : ι → ℝ
  reservoirTemperature_pos : ∀ i, 0 < reservoirTemperature i
  entropyGeneration : ℝ
  entropyBalance :
    entropyChange =
      (∑ i, heatTransfer i / reservoirTemperature i) + entropyGeneration
  entropyGeneration_nonneg : 0 ≤ entropyGeneration

/-- Entropy transferred with heat, under the convention that heat into the
system is positive. -/
noncomputable def entropyTransfer {ι : Type*} [Fintype ι] (D : SecondLawData ι) : ℝ :=
  ∑ i, D.heatTransfer i / D.reservoirTemperature i

/-- A reversible process has no internal entropy generation. -/
def Reversible {ι : Type*} [Fintype ι] (D : SecondLawData ι) : Prop :=
  D.entropyGeneration = 0

/-- An irreversible process has strictly positive internal entropy generation. -/
def Irreversible {ι : Type*} [Fintype ι] (D : SecondLawData ι) : Prop :=
  0 < D.entropyGeneration

/-- Entropy change is at least the entropy transferred with heat. -/
theorem entropyChange_ge_entropyTransfer
    {ι : Type*} [Fintype ι] (D : SecondLawData ι) :
    entropyTransfer D ≤ D.entropyChange := by
  rw [D.entropyBalance]
  unfold entropyTransfer
  linarith [D.entropyGeneration_nonneg]

/-- An irreversible process has entropy change strictly greater than the
entropy transferred with heat. -/
theorem entropyChange_gt_entropyTransfer_of_irreversible
    {ι : Type*} [Fintype ι] (D : SecondLawData ι)
    (hIrreversible : Irreversible D) :
    entropyTransfer D < D.entropyChange := by
  rw [D.entropyBalance]
  unfold entropyTransfer Irreversible at *
  linarith

/-- Clausius' inequality for a cycle: the system's entropy change vanishes,
so the net heat entropy transfer is nonpositive. -/
theorem clausiusInequality_of_cycle
    {ι : Type*} [Fintype ι] (D : SecondLawData ι)
    (hCycle : D.entropyChange = 0) :
    entropyTransfer D ≤ 0 := by
  have hTransfer : entropyTransfer D = -D.entropyGeneration := by
    unfold entropyTransfer
    linarith [D.entropyBalance, hCycle]
  rw [hTransfer]
  linarith [D.entropyGeneration_nonneg]

/-- An adiabatic closed-system process cannot decrease entropy. -/
theorem entropyChange_nonneg_of_adiabatic
    {ι : Type*} [Fintype ι] (D : SecondLawData ι)
    (hAdiabatic : ∀ i, D.heatTransfer i = 0) :
    0 ≤ D.entropyChange := by
  rw [D.entropyBalance]
  have hTransfer :
      (∑ i, D.heatTransfer i / D.reservoirTemperature i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hAdiabatic i]
  rw [hTransfer]
  simpa using D.entropyGeneration_nonneg

/-- An adiabatic reversible process is isentropic. -/
theorem entropyChange_eq_zero_of_adiabatic_reversible
    {ι : Type*} [Fintype ι] (D : SecondLawData ι)
    (hAdiabatic : ∀ i, D.heatTransfer i = 0)
    (hReversible : Reversible D) :
    D.entropyChange = 0 := by
  rw [D.entropyBalance]
  have hTransfer :
      (∑ i, D.heatTransfer i / D.reservoirTemperature i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hAdiabatic i]
  rw [hTransfer]
  simpa [Reversible] using hReversible

end ClassicalThermodynamics.Thermodynamics.Fundamental
