import Mathlib.Init

namespace ClassicalThermodynamics.Math.Tensor

/-- Full permutation symmetry of a ternary coefficient array. -/
def Symmetric3 {ι R : Type*} (C : ι → ι → ι → R) : Prop :=
  ∀ i j k, C i j k = C i k j ∧ C i j k = C j i k ∧ C i j k = C k j i

theorem symmetric3_swap12 {ι R : Type*} {C : ι → ι → ι → R}
    (hC : Symmetric3 C) (i j k : ι) : C i j k = C j i k :=
  (hC i j k).2.1

theorem symmetric3_swap23 {ι R : Type*} {C : ι → ι → ι → R}
    (hC : Symmetric3 C) (i j k : ι) : C i j k = C i k j :=
  (hC i j k).1

end ClassicalThermodynamics.Math.Tensor
