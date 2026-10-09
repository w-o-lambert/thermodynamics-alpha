import ClassicalThermodynamics.Math.Matrix.CharacteristicPolynomialSigns

namespace ClassicalThermodynamics.Thermodynamics.CharacteristicPolynomialSpinodal
open ClassicalThermodynamics.Math.CharacteristicPolynomialSigns

/-- The inside Hessian has no negative real characteristic root when its
characteristic polynomial has the strict alternating coefficient pattern. -/
theorem no_negative_inside_characteristicRoot_of_alternation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ℝ → Matrix ι ι ℝ) (t eps : ℝ)
    (halt : MatrixStrictAlternatingCoefficients (H (t - eps))) :
    ∀ x : ℝ, x < 0 → ¬ IsCharacteristicRoot (H (t - eps)) x :=
  no_negative_characteristicRoot_of_strictAlternation (H (t - eps)) halt

end ClassicalThermodynamics.Thermodynamics.CharacteristicPolynomialSpinodal
