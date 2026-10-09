import ClassicalThermodynamics.Thermodynamics.Extensivity.Homogeneity
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ClassicalThermodynamics.Thermodynamics.Extensivity
open scoped BigOperators

/-- Thermodynamic Euler relation. -/
def EulerRelation {ι : Type*} [Fintype ι]
    (U T S P V : ℝ) (mu N : ι → ℝ) : Prop :=
  U = T*S - P*V + ∑ i, mu i*N i

/-- Euler's theorem for a differentiable positively one-homogeneous function.
The derivative is evaluated on the radial direction `x`. -/
theorem euler_of_oneHomogeneous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (x : E) (F' : E →L[ℝ] ℝ)
    (hhom : OneHomogeneous F) (hF : HasFDerivAt F F' x) :
    F' x = F x := by
    let ray : ℝ → E := fun a => a • x
    have hray : HasDerivAt ray x 1 := by
      simpa [ray] using (hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).smul_const x
    have hx : ray 1 = x := by
      simp [ray]
    have hF_ray : HasFDerivAt F F' (ray 1) := by
      simpa [hx] using hF
    have hcomp : HasDerivAt (F ∘ ray) (F' x) 1 := by
      simpa [hx] using hF_ray.comp_hasDerivAt 1 hray
    have heq :
        (F ∘ ray) =ᶠ[nhds 1] (fun a => a * F x) := by
      filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
      exact hhom a ha.le x
    have hlinear : HasDerivAt (fun a : ℝ => a * F x) (F x) 1 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).mul_const (F x)
    exact (hcomp.congr_of_eventuallyEq heq.symm).unique hlinear

/-- Thermodynamic component form of Euler's relation once the Fréchet derivative
has the conjugate-variable representation. -/
theorem thermodynamicEuler_of_oneHomogeneous
    {ι : Type*} [Fintype ι]
    (Ufun : (ℝ × ℝ × (ι → ℝ)) → ℝ)
    (S V : ℝ) (N : ι → ℝ) (T P : ℝ) (mu : ι → ℝ)
    (U' : (ℝ × ℝ × (ι → ℝ)) →L[ℝ] ℝ)
    (hhom : OneHomogeneous Ufun)
    (hU : HasFDerivAt Ufun U' (S, V, N))
    (hconj : U' (S, V, N) = T*S - P*V + ∑ i, mu i*N i) :
    EulerRelation (Ufun (S, V, N)) T S P V mu N := by
  unfold EulerRelation
  rw [← hconj]
  symm
  exact euler_of_oneHomogeneous Ufun (S, V, N) U' hhom hU

lemma chemicalPotential_amount_sum_eq_internalEnergy_sub_TS_add_PV {ι : Type*} [Fintype ι]
    {U T S P V : ℝ} {mu N : ι → ℝ} (h : EulerRelation U T S P V mu N) :
    U - T*S + P*V = ∑ i, mu i*N i := by
  unfold EulerRelation at h
  linarith

end ClassicalThermodynamics.Thermodynamics.Extensivity
