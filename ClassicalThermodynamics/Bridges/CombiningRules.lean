import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Model
import Mathlib.Analysis.Real.Sqrt

namespace ClassicalThermodynamics.Bridges.CombiningRules

/-- Geometric-mean pair attraction from pure-component attractions. -/
noncomputable def geometricAttraction {ι : Type*} (a : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => Real.sqrt (a i * a j)

/-- Arithmetic-mean covolume pair rule, retained as an explicit convention. -/
noncomputable def arithmeticCovolumePair {ι : Type*} (b : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => (b i + b j) / 2

/-- Geometric attraction is symmetric. -/
theorem geometricAttraction_isSymm {ι : Type*} (a : ι → ℝ) :
    (geometricAttraction a).IsSymm := by
  ext i j
  change Real.sqrt (a j * a i) = Real.sqrt (a i * a j)
  rw [mul_comm]

end ClassicalThermodynamics.Bridges.CombiningRules
