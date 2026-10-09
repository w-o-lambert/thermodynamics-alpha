import ClassicalThermodynamics.Models.VanDerWaals.Mixture.Thermodynamics
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open scoped BigOperators

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The van der Waals mixture free energy has a finite-dimensional Frechet
derivative on the nonzero-density and nonzero-free-volume domain. -/
theorem freeEnergy_hasFDerivAt
    (M : Model (ι := ι)) (rho : State (ι := ι))
    (hrho : ∀ i, rho i ≠ 0)
    (hfree : freeVolumeFraction M rho ≠ 0) :
    ∃ D : (ι → ℝ) →L[ℝ] ℝ,
      HasFDerivAt (freeEnergy M) D rho := by
  have hcoordinate (i : ι) :
      HasFDerivAt (fun x : ι → ℝ => x i)
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) rho :=
    hasFDerivAt_apply (𝕜 := ℝ) i rho
  have htotal :
      ∃ D : (ι → ℝ) →L[ℝ] ℝ,
        HasFDerivAt (fun x : ι → ℝ => ∑ i, x i) D rho := by
    refine ⟨∑ i, ContinuousLinearMap.proj i, ?_⟩
    convert HasFDerivAt.sum (u := Finset.univ)
      (fun i _ => hcoordinate i) using 1
    funext x
    simp
  have hoccupied :
      ∃ D : (ι → ℝ) →L[ℝ] ℝ,
        HasFDerivAt
          (fun x : ι → ℝ => ∑ i, M.excludedVolume i * x i) D rho := by
    refine ⟨∑ i, M.excludedVolume i •
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ), ?_⟩
    convert HasFDerivAt.sum (u := Finset.univ)
      (fun i _ => (hcoordinate i).const_mul (M.excludedVolume i)) using 1
    funext x
    simp
  have hfreeVolume :
      ∃ D : (ι → ℝ) →L[ℝ] ℝ,
        HasFDerivAt (fun x : ι → ℝ => freeVolumeFraction M x) D rho := by
    rcases hoccupied with ⟨D, hD⟩
    refine ⟨-D, ?_⟩
    convert (hasFDerivAt_const (x := rho) (1 : ℝ)).sub hD using 1
    funext x
    simp [freeVolumeFraction, occupiedFraction]
    ext y
    simp
  have hentropy (i : ι) :
      ∃ D : (ι → ℝ) →L[ℝ] ℝ,
        HasFDerivAt
          (fun x : ι → ℝ => x i * (Real.log (x i) - 1)) D rho := by
    have hid : HasDerivAt (fun t : ℝ => t) 1 (rho i) :=
      hasDerivAt_id (rho i)
    have hlog := Real.hasDerivAt_log (hrho i)
    have hx := hid.mul (hlog.sub_const 1)
    refine ⟨Real.log (rho i) •
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ), ?_⟩
    convert hx.hasFDerivAt.comp rho (hcoordinate i) using 1
    · simp [Function.comp_def]
    · ext x
      simp
      field_simp [hrho i]
      ring
  have hentropySum :
      ∃ D : (ι → ℝ) →L[ℝ] ℝ,
        HasFDerivAt
          (fun x : ι → ℝ =>
            ∑ i, x i * (Real.log (x i) - 1)) D rho := by
    choose D hD using hentropy
    refine ⟨∑ i, D i, ?_⟩
    convert HasFDerivAt.sum (u := Finset.univ) (fun i _ => hD i) using 1
    funext x
    simp
  have hvolumeLog :
      ∃ D : (ι → ℝ) →L[ℝ] ℝ,
        HasFDerivAt
          (fun x : ι → ℝ => Real.log (freeVolumeFraction M x)) D rho := by
    rcases hfreeVolume with ⟨D, hD⟩
    have hlog := (Real.hasDerivAt_log hfree).hasFDerivAt.comp rho hD
    exact ⟨_, hlog⟩
  have hfreeProduct :
      ∃ D : (ι → ℝ) →L[ℝ] ℝ,
        HasFDerivAt
          (fun x : ι → ℝ =>
            (∑ i, x i) * Real.log (freeVolumeFraction M x)) D rho := by
    rcases htotal with ⟨D₁, hD₁⟩
    rcases hvolumeLog with ⟨D₂, hD₂⟩
    refine ⟨_, hD₁.mul hD₂⟩
  have hpair (i j : ι) :
      ∃ D : (ι → ℝ) →L[ℝ] ℝ,
        HasFDerivAt
          (fun x : ι → ℝ => alpha M i j / 2 * x i * x j) D rho := by
    have hproduct := (hcoordinate i).mul (hcoordinate j)
    have hscaled := hproduct.const_mul (alpha M i j / 2)
    refine ⟨_, hscaled.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (by
        intro x
        simp [Function.comp_def]
        ring))⟩
  have hpairSum :
      ∃ D : (ι → ℝ) →L[ℝ] ℝ,
        HasFDerivAt
          (fun x : ι → ℝ =>
            ∑ i, ∑ j, alpha M i j / 2 * x i * x j) D rho := by
    choose D hD using hpair
    have hinner (i : ι) :
        HasFDerivAt
          (fun x : ι → ℝ => ∑ j, alpha M i j / 2 * x i * x j)
          (∑ j, D i j) rho := by
      convert HasFDerivAt.sum (u := Finset.univ) (fun j _ => hD i j) using 1
      funext x
      simp
    refine ⟨∑ i, ∑ j, D i j, ?_⟩
    convert HasFDerivAt.sum (u := Finset.univ) (fun i _ => hinner i) using 1
    funext x
    simp
  rcases hentropySum with ⟨D₁, hD₁⟩
  rcases hfreeProduct with ⟨D₂, hD₂⟩
  rcases hpairSum with ⟨D₃, hD₃⟩
  refine ⟨D₁ - D₂ - D₃, ?_⟩
  convert (hD₁.sub hD₂).sub hD₃ using 1
  rfl

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
