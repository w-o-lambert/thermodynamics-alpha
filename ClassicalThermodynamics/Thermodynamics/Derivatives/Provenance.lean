import ClassicalThermodynamics.Thermodynamics.Derivatives.Directional
import ClassicalThermodynamics.Thermodynamics.Derivatives.Mixed
namespace ClassicalThermodynamics.Thermodynamics.Derivatives

def ChemicalPotentialDerived {ι : Type*} [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (mu : (ι → ℝ) → ι → ℝ) (x : ι → ℝ) : Prop :=
  CoordinateDerivativeDerived F mu x

def HessianDerived {ι : Type*} [DecidableEq ι]
    (mu : (ι → ℝ) → ι → ℝ) (H : (ι → ℝ) → ι → ι → ℝ)
    (x : ι → ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun t => mu (coordinatePerturb x j t) i) (H x i j) 0

def EntropyDerived {State : Type*}
    (F : ℝ → State → ℝ) (entropy : ℝ → State → ℝ)
    (temperature : ℝ) (x : State) : Prop :=
  HasDerivAt (fun T => F T x) (-entropy temperature x) temperature

def PressureDerivedFromVolume
    (F : ℝ → ℝ → ℝ) (pressure : ℝ → ℝ → ℝ)
    (temperature volume : ℝ) : Prop :=
  HasDerivAt (fun V => F temperature V) (-pressure temperature volume) volume

end ClassicalThermodynamics.Thermodynamics.Derivatives
