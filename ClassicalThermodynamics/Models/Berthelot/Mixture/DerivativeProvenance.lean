import ClassicalThermodynamics.Models.Berthelot.Mixture.Thermodynamics
import ClassicalThermodynamics.Thermodynamics.Derivatives.Provenance
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open scoped BigOperators

namespace ClassicalThermodynamics.Models.Berthelot.Mixture

open ClassicalThermodynamics.Thermodynamics.Derivatives

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma totalDensity_coordinatePerturb
    (rho : State (ι := ι)) (j : ι) (t : ℝ) :
    totalDensity (coordinatePerturb rho j t) = totalDensity rho + t := by
  change (∑ i, coordinatePerturb rho j t i) = ∑ i, rho i + t
  simp [coordinatePerturb, ClassicalThermodynamics.Math.Functions.coordinatePerturb,
    Finset.sum_add_distrib]

lemma occupiedFraction_coordinatePerturb
    (M : Model (ι := ι)) (rho : State (ι := ι)) (j : ι) (t : ℝ) :
    occupiedFraction M (coordinatePerturb rho j t) =
      occupiedFraction M rho + M.excludedVolume j * t := by
  simp [occupiedFraction, coordinatePerturb,
    ClassicalThermodynamics.Math.Functions.coordinatePerturb,
    Finset.sum_add_distrib]
  rw [show (∑ i, M.excludedVolume i *
      (rho i + if i = j then t else 0)) =
      ∑ i, (M.excludedVolume i * rho i +
        M.excludedVolume i * (if i = j then t else 0)) by
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq']

lemma freeVolumeFraction_coordinatePerturb
    (M : Model (ι := ι)) (rho : State (ι := ι)) (j : ι) (t : ℝ) :
    freeVolumeFraction M (coordinatePerturb rho j t) =
      freeVolumeFraction M rho - M.excludedVolume j * t := by
  unfold freeVolumeFraction
  rw [occupiedFraction_coordinatePerturb]
  ring

lemma chemicalPotential_coordinatePerturb
    (M : Model (ι := ι)) (temperature : ℝ) (rho : State (ι := ι))
    (i j : ι) (t : ℝ) :
    chemicalPotential M temperature (coordinatePerturb rho j t) i =
      Real.log ((rho i + if i = j then t else 0) /
        (freeVolumeFraction M rho - M.excludedVolume j * t)) +
      M.excludedVolume i * (totalDensity rho + t) /
        (freeVolumeFraction M rho - M.excludedVolume j * t) -
      (∑ k, alpha M temperature i k * rho k) -
        alpha M temperature i j * t := by
  unfold chemicalPotential
  change Real.log ((rho i + if i = j then t else 0) /
      freeVolumeFraction M (coordinatePerturb rho j t)) +
    M.excludedVolume i * totalDensity (coordinatePerturb rho j t) /
      freeVolumeFraction M (coordinatePerturb rho j t) -
      ∑ k, alpha M temperature i k * coordinatePerturb rho j t k = _
  rw [totalDensity_coordinatePerturb, freeVolumeFraction_coordinatePerturb]
  change Real.log ((rho i + if i = j then t else 0) /
      (freeVolumeFraction M rho - M.excludedVolume j * t)) +
    M.excludedVolume i * (totalDensity rho + t) /
      (freeVolumeFraction M rho - M.excludedVolume j * t) -
      (∑ k, alpha M temperature i k * coordinatePerturb rho j t k) = _
  rw [show (∑ k, alpha M temperature i k *
      (coordinatePerturb rho j t) k) =
      (∑ k, alpha M temperature i k * rho k) +
        alpha M temperature i j * t by
    unfold coordinatePerturb ClassicalThermodynamics.Math.Functions.coordinatePerturb
    rw [show (∑ k, alpha M temperature i k *
        (rho k + if k = j then t else 0)) =
        ∑ k, (alpha M temperature i k * rho k +
          alpha M temperature i k * (if k = j then t else 0)) by
      apply Finset.sum_congr rfl
      intro k hk
      ring]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq']]
  ring

private theorem hasDerivAt_covolumeRatio
    (M : Model (ι := ι)) (rho : State (ι := ι)) (temperature : ℝ)
    (i j : ι) (hfree : freeVolumeFraction M rho ≠ 0) :
    HasDerivAt
      (fun t => M.excludedVolume i * (totalDensity rho + t) /
        (freeVolumeFraction M rho - M.excludedVolume j * t))
      (M.excludedVolume i / freeVolumeFraction M rho +
        M.excludedVolume i * M.excludedVolume j * totalDensity rho /
          (freeVolumeFraction M rho)^2) 0 := by
  have hn : HasDerivAt (fun t : ℝ =>
      M.excludedVolume i * (totalDensity rho + t)) (M.excludedVolume i) 0 :=
    by
      convert ((hasDerivAt_const (x := (0 : ℝ)) (totalDensity rho)).add
        (hasDerivAt_id 0)).const_mul (M.excludedVolume i) using 1 <;>
        try { funext t; simp } <;> ring
  have hd : HasDerivAt
      (fun t : ℝ => freeVolumeFraction M rho - M.excludedVolume j * t)
      (-M.excludedVolume j) 0 :=
    by
      convert (hasDerivAt_const (x := (0 : ℝ)) (freeVolumeFraction M rho)).sub
        ((hasDerivAt_id 0).const_mul (M.excludedVolume j)) using 1 <;>
        try { funext t; simp } <;> ring
  convert hn.div hd (by simpa using hfree) using 1 <;>
    field_simp [hfree] <;> ring

theorem chemicalPotential_hasCoordinateDerivative_hessian
    (M : Model (ι := ι)) (temperature : ℝ) (rho : State (ι := ι))
    (hrho : ∀ i, rho i ≠ 0) (hfree : freeVolumeFraction M rho ≠ 0) :
    HessianDerived (chemicalPotential M temperature) (hessian M temperature) rho := by
  intro i j
  rw [show (fun t => chemicalPotential M temperature
      (coordinatePerturb rho j t) i) =
      (fun t => Real.log ((rho i + if i = j then t else 0) /
        (freeVolumeFraction M rho - M.excludedVolume j * t)) +
      M.excludedVolume i * (totalDensity rho + t) /
        (freeVolumeFraction M rho - M.excludedVolume j * t) -
      (∑ k, alpha M temperature i k * rho k) -
        alpha M temperature i j * t) by
    funext t
    exact chemicalPotential_coordinatePerturb M temperature rho i j t]
  have hlog : HasDerivAt
      (fun t => Real.log ((rho i + if i = j then t else 0) /
        (freeVolumeFraction M rho - M.excludedVolume j * t)))
      ((if i = j then 1 else 0) / rho i +
        M.excludedVolume j / freeVolumeFraction M rho) 0 := by
    by_cases hij : i = j
    · subst j
      have hn : HasDerivAt (fun t : ℝ => rho i + t) 1 0 :=
        by
          convert (hasDerivAt_const (x := (0 : ℝ)) (rho i)).add
            (hasDerivAt_id 0) using 1 <;> try { funext t; simp } <;> ring
      have hd : HasDerivAt
          (fun t : ℝ => freeVolumeFraction M rho - M.excludedVolume i * t)
          (-M.excludedVolume i) 0 :=
        by
          convert (hasDerivAt_const (x := (0 : ℝ))
            (freeVolumeFraction M rho)).sub
            ((hasDerivAt_id 0).const_mul (M.excludedVolume i)) using 1
          · funext t
            simp
          · ring
      convert (hn.div hd (by simpa using hfree)).log
        (by simpa [hrho i, hfree]) using 1
      · funext t
        simp
      · norm_num [Function.comp_apply]
        field_simp [hfree, hrho i]
    · have hnum : HasDerivAt (fun _ : ℝ => rho i)
        0 0 := hasDerivAt_const (x := (0 : ℝ)) _
      have hden : HasDerivAt
          (fun t : ℝ => freeVolumeFraction M rho - M.excludedVolume j * t)
          (-M.excludedVolume j) 0 :=
        by
          convert (hasDerivAt_const (x := (0 : ℝ))
            (freeVolumeFraction M rho)).sub
            ((hasDerivAt_id 0).const_mul (M.excludedVolume j)) using 1
          · funext t
            simp
          · ring
      convert (hnum.div hden (by simpa using hfree)).log
        (by simpa [hfree, hrho i]) using 1
      · funext t
        simp [hij]
      · norm_num [Function.comp_apply]
        field_simp [hfree, hrho i]
        simp [hij]
  have hcov := hasDerivAt_covolumeRatio M rho temperature i j hfree
  have hattr : HasDerivAt
      (fun t : ℝ => (∑ k, alpha M temperature i k * rho k) +
        alpha M temperature i j * t) (alpha M temperature i j) 0 :=
    by
      convert (hasDerivAt_const (x := (0 : ℝ))
        (∑ k, alpha M temperature i k * rho k)).add
        ((hasDerivAt_id 0).const_mul (alpha M temperature i j)) using 1 <;>
        try { funext t; simp } <;> ring
  convert (hlog.add hcov).sub hattr using 1
  · funext t
    simp
    ring
  · change (if i = j then (rho i)⁻¹ else 0) +
      (M.excludedVolume i + M.excludedVolume j) /
        freeVolumeFraction M rho +
      M.excludedVolume i * M.excludedVolume j * totalDensity rho /
        (freeVolumeFraction M rho)^2 -
      alpha M temperature i j = _
    by_cases hij : i = j
    · subst j
      simp
      field_simp [hrho i, hfree]
      ring
    · simp [hij]
      field_simp [hrho i, hfree]
      ring

theorem chemicalPotential_hasCoordinateDerivative_hessian_of_physical
    (M : Model (ι := ι)) (temperature : ℝ) (rho : State (ι := ι))
    (hphysical : Physical M rho) :
    HessianDerived (chemicalPotential M temperature) (hessian M temperature) rho := by
  apply chemicalPotential_hasCoordinateDerivative_hessian M temperature rho (fun i => ne_of_gt (hphysical.1 i))
  unfold freeVolumeFraction
  linarith [hphysical.2]

end ClassicalThermodynamics.Models.Berthelot.Mixture
