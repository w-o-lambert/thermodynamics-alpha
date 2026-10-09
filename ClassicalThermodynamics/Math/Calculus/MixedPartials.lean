import Mathlib.Analysis.Calculus.Deriv.Basic
namespace ClassicalThermodynamics.Math.Calculus

/-- Pointwise certificate that two iterated scalar partial derivatives commute.
The analytic Schwarz/Clairaut regularity theorem can later construct this certificate. -/
def MixedPartialsCommute
    (dFirst dSecond : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  dFirst x y = dSecond x y

/-- A named mixed value represented consistently in both differentiation orders. -/
def HasCommutingMixedPartials
    (dFirst dSecond : ℝ → ℝ → ℝ) (mixed x y : ℝ) : Prop :=
  dFirst x y = mixed ∧ dSecond x y = mixed

lemma mixedPartialsCommute_of_common_value
    {dFirst dSecond : ℝ → ℝ → ℝ} {mixed x y : ℝ}
    (h : HasCommutingMixedPartials dFirst dSecond mixed x y) :
    MixedPartialsCommute dFirst dSecond x y := by
  unfold HasCommutingMixedPartials MixedPartialsCommute at *
  linarith [h.1, h.2]

lemma common_value_of_mixedPartialsCommute
    {dFirst dSecond : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : MixedPartialsCommute dFirst dSecond x y) :
    HasCommutingMixedPartials dFirst dSecond (dFirst x y) x y := by
  exact ⟨rfl, h.symm⟩

end ClassicalThermodynamics.Math.Calculus
