import Mathlib.Analysis.Calculus.Deriv.Basic
namespace ClassicalThermodynamics.Thermodynamics.Derivatives

def ControlDerivativeDerived {State : Type*}
    (F : ℝ → State → ℝ) (D : ℝ → State → ℝ) (control : ℝ) (x : State) : Prop :=
  HasDerivAt (fun t => F t x) (D control x) control

def ControlDerivativeAtFixedState {State : Type*}
    (F : ℝ → State → ℝ) (control : ℝ) (x : State) (value : ℝ) : Prop :=
  HasDerivAt (fun t => F t x) value control

end ClassicalThermodynamics.Thermodynamics.Derivatives
