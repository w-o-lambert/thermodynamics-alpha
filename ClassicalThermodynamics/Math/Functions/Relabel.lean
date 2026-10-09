import Mathlib.Init
import Mathlib.Logic.Equiv.Basic

namespace ClassicalThermodynamics.Math.Functions

/-- Pull a component-indexed state back along an equivalence of labels. -/
def relabel {ι κ α : Type*} (e : κ ≃ ι) (x : ι → α) : κ → α := fun k => x (e k)

@[simp] theorem relabel_apply {ι κ α : Type*} (e : κ ≃ ι)
    (x : ι → α) (k : κ) : relabel e x k = x (e k) := rfl

@[simp] theorem relabel_refl {ι α : Type*} (x : ι → α) :
    relabel (Equiv.refl ι) x = x := rfl

@[simp] theorem relabel_trans {ι κ rho α : Type*}
    (e : κ ≃ ι) (f : rho ≃ κ) (x : ι → α) :
    relabel f (relabel e x) = relabel (f.trans e) x := rfl

end ClassicalThermodynamics.Math.Functions
