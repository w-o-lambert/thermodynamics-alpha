import ClassicalThermodynamics.Models.IdealMixture.Consequences

/-!
# Kirkwood–Oppenheim: ideal-solution results

Thin wrappers for selected Chapter 11 equations. The composition and
nonnegativity hypotheses are stated at the model layer, not hidden in the
paper-facing declarations.
-/

namespace ClassicalThermodynamics.Applications.KirkwoodOppenheim1961

open ClassicalThermodynamics.Models.IdealMixture

/-- Kirkwood–Oppenheim, Chapter 11, Eq. (11-90): ideal-solution entropy of
mixing. -/
theorem eq_11_90_ideal_entropyOfMixing
    {ι : Type*} [Fintype ι] (R : ℝ) (x : State ι) :
    entropyOfMixing R x =
      -R * ∑ i, x.x i * Real.log (x.x i) :=
  rfl

/-- Kirkwood–Oppenheim, Chapter 11, Eq. (11-90): zero heat of mixing for an
ideal solution. -/
theorem eq_11_90_ideal_heatOfMixing :
    heatOfMixing = 0 :=
  heatOfMixing_eq_zero

/-- Kirkwood–Oppenheim, Chapter 11, Eq. (11-92): zero volume increment of
mixing for an ideal solution. -/
theorem eq_11_92_ideal_volumeOfMixing :
    volumeOfMixing = 0 :=
  volumeOfMixing_eq_zero

/-- The ideal-solution entropy expression is nonnegative for simplex
compositions and a nonnegative gas constant. -/
theorem ideal_entropyOfMixing_nonneg
    {ι : Type*} [Fintype ι] (R : ℝ) (x : State ι)
    (hR : 0 ≤ R) (hx0 : ∀ i, 0 ≤ x.x i) (hx1 : ∀ i, x.x i ≤ 1) :
    0 ≤ entropyOfMixing R x :=
  ClassicalThermodynamics.Models.IdealMixture.entropyOfMixing_nonneg
    R x hR hx0 hx1

end ClassicalThermodynamics.Applications.KirkwoodOppenheim1961
