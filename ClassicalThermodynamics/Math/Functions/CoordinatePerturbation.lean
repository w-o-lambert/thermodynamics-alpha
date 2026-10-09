import Mathlib.Basic.Real.Basic
namespace ClassicalThermodynamics.Math.Functions
def coordinatePerturb {iota : Type*} [DecidableEq iota]
    (x : iota -> Real) (i : iota) (t : Real) : iota -> Real :=
  fun j => x j + if j = i then t else 0
@[simp] theorem coordinatePerturb_apply_same {iota : Type*} [DecidableEq iota]
    (x : iota -> Real) (i : iota) (t : Real) : coordinatePerturb x i t i = x i + t := by simp [coordinatePerturb]
@[simp] theorem coordinatePerturb_apply_of_ne {iota : Type*} [DecidableEq iota]
    (x : iota -> Real) {i j : iota} (hji : j ≠ i) (t : Real) : coordinatePerturb x i t j = x j := by simp [coordinatePerturb, hji]
@[simp] theorem coordinatePerturb_zero {iota : Type*} [DecidableEq iota]
    (x : iota -> Real) (i : iota) : coordinatePerturb x i 0 = x := by funext j; simp [coordinatePerturb]
end ClassicalThermodynamics.Math.Functions
