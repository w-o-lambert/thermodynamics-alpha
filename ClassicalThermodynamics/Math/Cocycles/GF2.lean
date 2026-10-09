import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

namespace ClassicalThermodynamics.Math.Cocycles.GF2

variable {ι : Type*}

abbrev SignMatrix := Matrix ι ι (ZMod 2)

def IsCocycle (s : SignMatrix (ι := ι)) : Prop :=
  (∀ i, s i i = 0) ∧ ∀ i j k, s i j + s j k + s k i = 0

def coboundary (g : ι → ZMod 2) : SignMatrix (ι := ι) :=
  fun i j => g i + g j

lemma two_eq_zero_zmod2 : (2 : ZMod 2) = 0 := by
  change (2 % 2 : Fin 2) = 0
  decide

lemma add_self_zmod2 (x : ZMod 2) : x + x = 0 := by
  calc
    x + x = (2 : ZMod 2) * x := by ring
    _ = 0 := by rw [two_eq_zero_zmod2, zero_mul]

lemma neg_eq_self_zmod2 (x : ZMod 2) : -x = x := by
  apply neg_eq_iff_add_eq_zero.mpr
  exact add_self_zmod2 x

lemma add_eq_zero_iff_eq_zmod2 (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc
      x = -y := eq_neg_of_add_eq_zero_left h
      _ = y := neg_eq_self_zmod2 y
  · intro h
    rw [h]
    exact add_self_zmod2 y

lemma six_term_cancel (a b c : ZMod 2) :
    a + b + (c + b) + (c + a) = 0 := by
  calc
    a + b + (c + b) + (c + a) = (a + a) + (b + b) + (c + c) := by abel
    _ = 0 := by simp [add_self_zmod2]

theorem coboundary_isCocycle (g : ι → ZMod 2) : IsCocycle (coboundary g) := by
  constructor
  · intro i
    exact add_self_zmod2 (g i)
  · intro i j k
    change (g i + g j) + (g j + g k) + (g k + g i) = 0
    calc
      (g i + g j) + (g j + g k) + (g k + g i) =
          (g i + g i) + (g j + g j) + (g k + g k) := by abel
      _ = 0 := by simp [add_self_zmod2]

theorem cocycle_symm (s : SignMatrix (ι := ι))
    (hs : IsCocycle s) (i j : ι) : s i j = s j i := by
  have h := hs.2 i j i
  rw [hs.1 i, add_zero] at h
  exact (add_eq_zero_iff_eq_zmod2 _ _).mp h

theorem cocycle_eq_from_row (s : SignMatrix (ι := ι))
    (hs : IsCocycle s) (r i j : ι) : s i j = s i r + s r j := by
  have h := hs.2 i r j
  rw [cocycle_symm s hs j i] at h
  have hz : (s i r + s r j) + s i j = 0 := by
    simpa [add_assoc] using h
  exact ((add_eq_zero_iff_eq_zmod2 _ _).mp hz).symm

theorem cocycle_ext_from_row (s t : SignMatrix (ι := ι))
    (hs : IsCocycle s) (ht : IsCocycle t) (r : ι)
    (hrow : ∀ j, s r j = t r j) : s = t := by
  funext i j
  rw [cocycle_eq_from_row s hs r i j,
    cocycle_eq_from_row t ht r i j,
    cocycle_symm s hs i r,
    cocycle_symm t ht i r,
    hrow i, hrow j]

end ClassicalThermodynamics.Math.Cocycles.GF2
