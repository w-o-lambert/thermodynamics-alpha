import ClassicalThermodynamics.Thermodynamics.Derivatives.Coordinate
namespace ClassicalThermodynamics.Thermodynamics.Derivatives

def directionalPerturb {ι : Type*} (x q : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => x i + t * q i

@[simp] theorem directionalPerturb_zero {ι : Type*} (x q : ι → ℝ) :
    directionalPerturb x q 0 = x := by funext i; simp [directionalPerturb]

def DirectionalDerivativeDerived {ι : Type*}
    (F : (ι → ℝ) → ℝ) (D : (ι → ℝ) → (ι → ℝ) → ℝ)
    (x q : ι → ℝ) : Prop :=
  HasDerivAt (fun t => F (directionalPerturb x q t)) (D x q) 0

def ThirdDirectionalDerivativeDerived {ι : Type*}
    (Hq : (ι → ℝ) → (ι → ℝ) → ℝ)
    (D3 : (ι → ℝ) → (ι → ℝ) → ℝ) (x q : ι → ℝ) : Prop :=
  HasDerivAt (fun t => Hq (directionalPerturb x q t) q) (D3 x q) 0

end ClassicalThermodynamics.Thermodynamics.Derivatives
