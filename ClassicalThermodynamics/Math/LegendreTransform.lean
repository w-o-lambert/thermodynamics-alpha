import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring.RingNF
namespace ClassicalThermodynamics.Math

noncomputable def legendreValue (f x p : ℝ) : ℝ := f - p * x
noncomputable def inverseLegendreValue (g x p : ℝ) : ℝ := g + p * x

/-- A Legendre transform evaluated along a stationary branch `x(p)` satisfying
`f'(x(p)) = p`. -/
noncomputable def legendreValueAlong
    (f x : ℝ → ℝ) (p : ℝ) : ℝ :=
  legendreValue (f (x p)) (x p) p

/-- Along a stationary branch, the derivative of the transformed potential is
`-x`; the branch derivative cancels by the defining stationarity condition. -/
theorem hasDerivAt_legendreValueAlong
    (f x : ℝ → ℝ) (p x' : ℝ)
    (hf : HasDerivAt f p (x p))
    (hx : HasDerivAt x x' p) :
    HasDerivAt (legendreValueAlong f x) (-x p) p := by
  unfold legendreValueAlong
  change HasDerivAt (fun y => f (x y) - y * x y) (-x p) p
  have hfx := hf.comp p hx
  have hpx := (hasDerivAt_id p).mul hx
  have hfun : (fun y => f (x y) - y * x y) =
      (fun y => f (x y)) - x * id := by
    funext y
    simp [mul_comm]
  rw [hfun]
  convert hfx.sub hpx using 1 <;> simp [Function.comp_def, mul_comm]

@[simp] theorem inverseLegendreValue_legendreValue (f x p : ℝ) :
    inverseLegendreValue (legendreValue f x p) x p = f := by
  unfold inverseLegendreValue legendreValue
  ring

@[simp] theorem legendreValue_inverseLegendreValue (g x p : ℝ) :
    legendreValue (inverseLegendreValue g x p) x p = g := by
  unfold inverseLegendreValue legendreValue
  ring

end ClassicalThermodynamics.Math
