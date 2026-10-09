import ClassicalThermodynamics.Thermodynamics.Extensivity.Construction
import ClassicalThermodynamics.Thermodynamics.Extensivity.Euler
import ClassicalThermodynamics.Models.VanDerWaals.Pure.DerivativeProvenance

namespace ClassicalThermodynamics.Thermodynamics.Extensivity

open ClassicalThermodynamics.Models.VanDerWaals.Pure

theorem pureVanDerWaals_densityComposition_hasFDerivAt
    (M : Model) {volume amount : ℝ}
    (hvolume : volume ≠ 0) (hrho : amount / volume ≠ 0)
    (hfreeVolume : 1 - M.excludedVolume * (amount / volume) ≠ 0) :
    HasFDerivAt
      (fun x : ℝ × ℝ => freeEnergy M (x.2 / x.1))
      ((ContinuousLinearMap.toSpanSingleton ℝ
          (chemicalPotential M (amount / volume))).comp
        (((-(amount / volume ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
          (volume⁻¹) • ContinuousLinearMap.snd ℝ ℝ ℝ))
      (volume, amount) := by
  have hfree :
      HasDerivAt (freeEnergy M) (chemicalPotential M (amount / volume))
        (amount / volume) :=
    hasDerivAt_freeEnergy M hrho hfreeVolume
  have hquot :
      HasFDerivAt (fun x : ℝ × ℝ => x.2 / x.1)
        ((-(amount / volume ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (volume⁻¹) • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (volume, amount) :=
    scalarDensity_hasFDerivAt hvolume
  convert hfree.hasFDerivAt.comp (volume, amount) hquot using 1
  simp [Function.comp_def]

theorem pureVanDerWaals_extensiveFreeEnergy_hasFDerivAt
    (M : Model) {volume amount : ℝ}
    (hvolume : volume ≠ 0) (hrho : amount / volume ≠ 0)
    (hfreeVolume : 1 - M.excludedVolume * (amount / volume) ≠ 0) :
    ∃ G : (ℝ × ℝ) →L[ℝ] ℝ,
      HasFDerivAt
        (fun x : ℝ × ℝ =>
          if x.1 = 0 then 0 else
            x.1 * freeEnergy M (x.2 / x.1))
        G (volume, amount) := by
  have hcomposition :=
    pureVanDerWaals_densityComposition_hasFDerivAt
      M hvolume hrho hfreeVolume
  have hvolumeDerivative :
      HasFDerivAt (fun x : ℝ × ℝ => x.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (volume, amount) :=
    hasFDerivAt_fst (𝕜 := ℝ)
  exact ⟨
    volume •
        ((ContinuousLinearMap.toSpanSingleton ℝ
            (chemicalPotential M (amount / volume))).comp
          (((-(amount / volume ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
            (volume⁻¹) • ContinuousLinearMap.snd ℝ ℝ ℝ)) +
      freeEnergy M (amount / volume) •
        ContinuousLinearMap.fst ℝ ℝ ℝ,
    extensiveScalarFreeEnergy_hasFDerivAt_of_densityComposition
      (freeEnergy M) hvolume hcomposition hvolumeDerivative⟩

theorem pureVanDerWaals_extensive_conjugate_derivative
    (M : Model) {volume amount : ℝ}
    (hvolume : volume ≠ 0) (hrho : amount / volume ≠ 0)
    (hfreeVolume : 1 - M.excludedVolume * (amount / volume) ≠ 0) :
    ∃ G : (ℝ × ℝ) →L[ℝ] ℝ,
      HasFDerivAt
        (fun x : ℝ × ℝ =>
          if x.1 = 0 then 0 else
            x.1 * freeEnergy M (x.2 / x.1))
        G (volume, amount) ∧
      G (volume, amount) =
        -pressure M (amount / volume) * volume +
          chemicalPotential M (amount / volume) * amount := by
  have hcomposition :=
    pureVanDerWaals_densityComposition_hasFDerivAt
      M hvolume hrho hfreeVolume
  let G : (ℝ × ℝ) →L[ℝ] ℝ :=
    volume •
        ((ContinuousLinearMap.toSpanSingleton ℝ
            (chemicalPotential M (amount / volume))).comp
          (((-(amount / volume ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
            (volume⁻¹) • ContinuousLinearMap.snd ℝ ℝ ℝ)) +
      freeEnergy M (amount / volume) •
        ContinuousLinearMap.fst ℝ ℝ ℝ
  have hvolumeDerivative :
      HasFDerivAt (fun x : ℝ × ℝ => x.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (volume, amount) :=
    hasFDerivAt_fst (𝕜 := ℝ)
  have hG := extensiveScalarFreeEnergy_hasFDerivAt_of_densityComposition
    (freeEnergy M) hvolume hcomposition hvolumeDerivative
  refine ⟨G, ?_, ?_⟩
  · simpa [G] using hG
  · rw [pressure_eq_rho_mul_mu_sub_freeEnergy M (amount / volume) hfreeVolume]
    simp [G, ContinuousLinearMap.comp_apply, div_eq_mul_inv]
    field_simp [hvolume, hrho, hfreeVolume]
    ring

theorem pureVanDerWaals_extensive_pressure_identity
    (M : Model) {volume amount : ℝ}
    (hvolume : volume ≠ 0) (hrho : amount / volume ≠ 0)
    (hfreeVolume : 1 - M.excludedVolume * (amount / volume) ≠ 0) :
    ∃ G : (ℝ × ℝ) →L[ℝ] ℝ,
      HasFDerivAt
        (fun x : ℝ × ℝ =>
          if x.1 = 0 then 0 else
            x.1 * freeEnergy M (x.2 / x.1))
        G (volume, amount) ∧
      pressure M (amount / volume) * volume =
        -(volume * freeEnergy M (amount / volume)) +
          chemicalPotential M (amount / volume) * amount := by
  rcases pureVanDerWaals_extensive_conjugate_derivative
    M hvolume hrho hfreeVolume with ⟨G, hG, hconj⟩
  have hEuler :
      OneHomogeneous (fun x : ℝ × ℝ =>
        if x.1 = 0 then 0 else x.1 * freeEnergy M (x.2 / x.1)) :=
    extensiveScalarFreeEnergy_oneHomogeneous (freeEnergy M)
  have hEulerValue := euler_of_oneHomogeneous
    (fun x : ℝ × ℝ =>
      if x.1 = 0 then 0 else x.1 * freeEnergy M (x.2 / x.1))
    (volume, amount) G hEuler hG
  refine ⟨G, hG, ?_⟩
  calc
    pressure M (amount / volume) * volume =
        -G (volume, amount) +
          chemicalPotential M (amount / volume) * amount := by
      rw [hconj]
      ring
    _ = -(if volume = 0 then 0 else volume * freeEnergy M (amount / volume)) +
          chemicalPotential M (amount / volume) * amount := by
      rw [hEulerValue]
    _ = -(volume * freeEnergy M (amount / volume)) +
          chemicalPotential M (amount / volume) * amount := by
      simp [hvolume]

end ClassicalThermodynamics.Thermodynamics.Extensivity
