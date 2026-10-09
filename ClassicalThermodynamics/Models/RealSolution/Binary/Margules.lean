import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Models.RealSolution.Binary.Margules

/-- Cubic composition expansion for component 1's logarithmic activity
coefficient, expressed in component 2's mole fraction. -/
def logActivity1 (A1 B1 C1 x2 : ℝ) : ℝ :=
  A1 * x2 + B1 * x2 ^ 2 + C1 * x2 ^ 3

/-- Cubic composition expansion for component 2's logarithmic activity
coefficient, expressed in component 1's mole fraction. -/
def logActivity2 (A2 B2 C2 x1 : ℝ) : ℝ :=
  A2 * x1 + B2 * x1 ^ 2 + C2 * x1 ^ 3

/-- Composition derivatives of the truncated activity-coefficient
expressions, with `x2 = 1 - x1`. -/
def gibbsDuhemResidual
    (A1 B1 C1 A2 B2 C2 x1 : ℝ) : ℝ :=
  x1 * (-(A1 + 2 * B1 * (1 - x1) +
      3 * C1 * (1 - x1) ^ 2)) +
    (1 - x1) * (A2 + 2 * B2 * x1 + 3 * C2 * x1 ^ 2)

/-- Gibbs-Duhem compatibility of the two cubic activity expansions at every
binary composition. -/
def GibbsDuhemCompatible
    (A1 B1 C1 A2 B2 C2 : ℝ) : Prop :=
  ∀ x1, gibbsDuhemResidual A1 B1 C1 A2 B2 C2 x1 = 0

/-- For the stated cubic polynomial convention, Gibbs-Duhem compatibility
forces these coefficient identities. In particular, the quadratic coefficient
shift is `3 C1 / 2`; the unscaled coefficient relation in the supplied
extension package does not satisfy the stated cubic identity in general. -/
theorem coefficients_of_gibbsDuhem
    (A1 B1 C1 A2 B2 C2 : ℝ)
    (h : GibbsDuhemCompatible A1 B1 C1 A2 B2 C2) :
    A1 = 0 ∧ A2 = 0 ∧
      B2 = B1 + (3 / 2 : ℝ) * C1 ∧ C2 = -C1 := by
  have h0 := h 0
  have h1 := h 1
  have hhalf := h (1 / 2)
  have htwo := h 2
  simp [gibbsDuhemResidual] at h0 h1 hhalf htwo
  have hA1 : A1 = 0 := by linarith
  have hA2 : A2 = 0 := by linarith
  have hhalf' :
      4 * (B2 - B1) + 3 * (C2 - C1) = 0 := by
    nlinarith
  have htwo' :
      4 * (B1 - B2) - 6 * C1 - 12 * C2 = 0 := by
    nlinarith
  have hC2 : C2 = -C1 := by
    nlinarith [hhalf', htwo']
  have hB2 : B2 = B1 + (3 / 2 : ℝ) * C1 := by
    nlinarith [hhalf', hC2]
  exact ⟨hA1, hA2, hB2, hC2⟩

/-- Conversely, these coefficient identities make the cubic expansions
Gibbs-Duhem compatible at every composition. -/
theorem gibbsDuhem_of_coefficients
    (A1 B1 C1 A2 B2 C2 : ℝ)
    (hA1 : A1 = 0) (hA2 : A2 = 0)
    (hB2 : B2 = B1 + (3 / 2 : ℝ) * C1)
    (hC2 : C2 = -C1) :
    GibbsDuhemCompatible A1 B1 C1 A2 B2 C2 := by
  intro x1
  unfold gibbsDuhemResidual
  rw [hA1, hA2, hB2, hC2]
  ring

/-- The second cubic activity expression in Gibbs-Duhem-compatible normal
form. -/
theorem logActivity2_normalForm
    (A1 B1 C1 A2 B2 C2 x1 : ℝ)
    (h : GibbsDuhemCompatible A1 B1 C1 A2 B2 C2) :
    logActivity2 A2 B2 C2 x1 =
      (B1 + (3 / 2 : ℝ) * C1) * x1 ^ 2 - C1 * x1 ^ 3 := by
  rcases coefficients_of_gibbsDuhem A1 B1 C1 A2 B2 C2 h with
    ⟨_, hA2, hB2, hC2⟩
  unfold logActivity2
  rw [hA2, hB2, hC2]
  ring

end ClassicalThermodynamics.Models.RealSolution.Binary.Margules
