import ClassicalThermodynamics.Models.VanDerWaals.Mixture.ProvenanceStatus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open scoped BigOperators

namespace ClassicalThermodynamics.Models.VanDerWaals.Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! Candidate completion of the three multicomponent derivative certificates.
The strategy is to prove scalar coordinate/directional slice identities first and
then apply one-variable `HasDerivAt` combinators. -/

noncomputable def coordinateFreeEnergySlice
    (M : Model (ι := ι)) (rho : State (ι := ι)) (i : ι) (t : ℝ) : ℝ :=
  freeEnergy M rho +
  (rho i + t) * (Real.log (rho i + t) - 1) -
  rho i * (Real.log (rho i) - 1) -
  (totalDensity rho + t) *
    Real.log (freeVolumeFraction M rho - M.excludedVolume i * t) +
  totalDensity rho * Real.log (freeVolumeFraction M rho) -
  t * (∑ j, alpha M i j * rho j) -
  alpha M i i / 2 * t^2

noncomputable def coordinateChemicalPotentialSlice
    (M : Model (ι := ι)) (rho : State (ι := ι))
    (i j : ι) (t : ℝ) : ℝ :=
  Real.log ((rho i + if i = j then t else 0) /
    (freeVolumeFraction M rho - M.excludedVolume j * t)) +
  M.excludedVolume i * (totalDensity rho + t) /
    (freeVolumeFraction M rho - M.excludedVolume j * t) -
  (∑ k, alpha M i k * rho k) - alpha M i j * t

/-- Exact change of the symmetric quadratic attraction under a coordinate perturbation. -/
lemma attractionSum_perturb
    (M : Model (ι := ι)) (rho : State (ι := ι)) (i : ι) (t : ℝ) :
    (∑ j, ∑ k, alpha M j k / 2 *
      perturb rho i t j * perturb rho i t k) =
    (∑ j, ∑ k, alpha M j k / 2 * rho j * rho k) +
      t * (∑ k, alpha M i k * rho k) + alpha M i i / 2 * t^2 := by
  have hs : ∀ j k, alpha M j k = alpha M k j := by
    intro j k
    exact congrFun (congrFun (alpha_isSymm M) k) j
  unfold perturb
  simp only [mul_add, add_mul]
  simp_rw [Finset.sum_add_distrib]
  simp [hs]
  have hcomm :
      (∑ x, alpha M i x / 2 * rho x * t) =
        ∑ x, alpha M i x / 2 * t * rho x := by
    apply Finset.sum_congr rfl
    intro x hx
    ring_nf
  have hscale :
      (∑ x, alpha M i x / 2 * t * rho x) =
        t * (∑ x, alpha M i x * rho x) / 2 := by
    calc
      _ = ∑ x, (t * (alpha M i x * rho x)) / 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (∑ x, t * (alpha M i x * rho x)) / 2 := by
        rw [Finset.sum_div]
      _ = _ := by rw [Finset.mul_sum]
  rw [hcomm]
  rw [hscale]
  ring

/-- The full free energy restricted to coordinate `i` is the scalar slice above. -/
lemma freeEnergy_perturb_eq_coordinateSlice
    (M : Model (ι := ι)) (rho : State (ι := ι)) (i : ι) (t : ℝ) :
    freeEnergy M (perturb rho i t) = coordinateFreeEnergySlice M rho i t := by
  unfold coordinateFreeEnergySlice freeEnergy
  rw [totalDensity_perturb, freeVolumeFraction_perturb, attractionSum_perturb]
  have hideal :
      (∑ x, (rho x + if x = i then t else 0) *
          (Real.log (rho x + if x = i then t else 0) - 1)) =
        (∑ x, rho x * (Real.log (rho x) - 1)) +
          (rho i + t) * (Real.log (rho i + t) - 1) -
          rho i * (Real.log (rho i) - 1) := by
    rw [show (∑ x, (rho x + if x = i then t else 0) *
          (Real.log (rho x + if x = i then t else 0) - 1)) =
        ∑ x, (rho x * (Real.log (rho x) - 1) +
          if x = i then
            ((rho x + t) * (Real.log (rho x + t) - 1) -
              rho x * (Real.log (rho x) - 1)) else 0) by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x = i <;> simp [h] <;> ring]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
    ring
  simp [perturb, hideal]
  ring

/-- The closed chemical potential restricted to coordinate `j` is a scalar slice. -/
lemma chemicalPotential_perturb_eq_coordinateSlice
    (M : Model (ι := ι)) (rho : State (ι := ι))
    (i j : ι) (t : ℝ) :
    chemicalPotential M (perturb rho j t) i =
      coordinateChemicalPotentialSlice M rho i j t := by
  unfold chemicalPotential coordinateChemicalPotentialSlice
  change Real.log ((rho i + if i = j then t else 0) /
      freeVolumeFraction M (perturb rho j t)) +
    M.excludedVolume i * totalDensity (perturb rho j t) /
      freeVolumeFraction M (perturb rho j t) -
      ∑ k, alpha M i k * perturb rho j t k =
    _
  rw [totalDensity_perturb, freeVolumeFraction_perturb]
  have hsum :
      (∑ k, alpha M i k * (rho k + if k = j then t else 0)) =
        (∑ k, alpha M i k * rho k) + alpha M i j * t := by
    rw [show (∑ k, alpha M i k * (rho k + if k = j then t else 0)) =
        ∑ k, (alpha M i k * rho k + alpha M i k *
          (if k = j then t else 0)) by
      apply Finset.sum_congr rfl
      intro k hk
      ring]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [perturb]
  rw [hsum]
  ring

/-- Derivative of the ideal one-component free-energy term. -/
lemma hasDerivAt_idealCoordinateTerm {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun t => (r + t) * (Real.log (r + t) - 1))
      (Real.log r) 0 := by
  have hx' : HasDerivAt (fun t : ℝ => r + t) 1 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) r).add (hasDerivAt_id 0) using 1
    · funext t
      simp
    · ring
  convert hx'.mul ((hx'.log (by simpa using hr)).sub_const 1) using 1 <;>
  field_simp [hr] <;> ring

/-- Derivative of the free-volume contribution along coordinate `i`. -/
lemma hasDerivAt_freeVolumeCoordinateTerm
    (M : Model (ι := ι)) (rho : State (ι := ι)) (i : ι)
    (hfree : freeVolumeFraction M rho ≠ 0) :
    HasDerivAt
      (fun t => -(totalDensity rho + t) *
        Real.log (freeVolumeFraction M rho - M.excludedVolume i * t))
      (-Real.log (freeVolumeFraction M rho) +
        M.excludedVolume i * totalDensity rho / freeVolumeFraction M rho) 0 := by
  have htot : HasDerivAt (fun t : ℝ => totalDensity rho + t) 1 0 :=
    by
      convert ((hasDerivAt_const (x := (0 : ℝ)) (totalDensity rho)).add
        (hasDerivAt_id 0)) using 1
      · funext t
        simp
      · ring
  have hphi : HasDerivAt
      (fun t : ℝ => freeVolumeFraction M rho - M.excludedVolume i * t)
      (-M.excludedVolume i) 0 :=
    by
      convert ((hasDerivAt_const (x := (0 : ℝ)) (freeVolumeFraction M rho)).sub
        ((hasDerivAt_id 0).const_mul (M.excludedVolume i))) using 1
      · funext t
        simp
      · ring
  convert (htot.mul (hphi.log (by simpa using hfree))).neg using 1
  · funext t
    simp
    ring
  · field_simp [hfree]
    ring

/-- Actual free-energy derivative certificate for component `i`. -/
theorem chemicalPotentialDerived
    (M : Model (ι := ι)) (rho : State (ι := ι)) (i : ι)
    (hrho : rho i ≠ 0) (hfree : freeVolumeFraction M rho ≠ 0) :
    ChemicalPotentialDerived M rho i := by
  unfold ChemicalPotentialDerived
  rw [show (fun t => freeEnergy M (perturb rho i t)) =
      coordinateFreeEnergySlice M rho i by
    funext t
    exact freeEnergy_perturb_eq_coordinateSlice M rho i t]
  unfold coordinateFreeEnergySlice
  have hideal := hasDerivAt_idealCoordinateTerm hrho
  have hfv := hasDerivAt_freeVolumeCoordinateTerm M rho i hfree
  have hattr : HasDerivAt
      (fun t : ℝ => -t * (∑ j, alpha M i j * rho j) - alpha M i i / 2 * t^2)
      (-(∑ j, alpha M i j * rho j)) 0 := by
    convert (((hasDerivAt_id 0).const_mul
      (-(∑ j, alpha M i j * rho j))).sub
      ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (alpha M i i / 2))) using 1
    · funext t
      simp
      ring
    · ring
  convert (((hasDerivAt_const (x := (0 : ℝ)) (freeEnergy M rho)).add hideal).sub
      (hasDerivAt_const (x := (0 : ℝ))
        (rho i * (Real.log (rho i) - 1)))).add hfv |>.add
      (hasDerivAt_const (x := (0 : ℝ))
        (totalDensity rho * Real.log (freeVolumeFraction M rho))) |>.add hattr using 1
  · funext t
    simp
    ring
  · unfold chemicalPotential
    rw [Real.log_div hrho hfree]
    ring

/-- Physical states provide every chemical-potential derivative certificate. -/
theorem chemicalPotentialDerived_of_physical
    (M : Model (ι := ι)) (rho : State (ι := ι)) (hphys : Physical M rho) :
    ∀ i, ChemicalPotentialDerived M rho i := by
  intro i
  apply chemicalPotentialDerived M rho i (ne_of_gt (hphys.1 i))
  unfold freeVolumeFraction
  linarith [hphys.2]

/-- Derivative of the logarithmic ratio in a chemical-potential slice. -/
lemma hasDerivAt_logComponentRatio
    (M : Model (ι := ι)) (rho : State (ι := ι)) (i j : ι)
    (hrho : rho i ≠ 0) (hfree : freeVolumeFraction M rho ≠ 0) :
    HasDerivAt
      (fun t => Real.log ((rho i + if i = j then t else 0) /
        (freeVolumeFraction M rho - M.excludedVolume j * t)))
      ((if i = j then (rho i)⁻¹ else 0) +
        M.excludedVolume j / freeVolumeFraction M rho) 0 := by
  have hn : HasDerivAt
      (fun t : ℝ => rho i + if i = j then t else 0)
      (if i = j then 1 else 0) 0 := by
    by_cases h : i = j
    · subst j
      convert ((hasDerivAt_const (x := (0 : ℝ)) (rho i)).add
        (hasDerivAt_id 0)) using 1
      · funext t
        simp
      · norm_num
    · simpa [h] using hasDerivAt_const (x := (0 : ℝ)) (rho i)
  have hd : HasDerivAt
      (fun t : ℝ => freeVolumeFraction M rho - M.excludedVolume j * t)
      (-M.excludedVolume j) 0 :=
    by
      convert ((hasDerivAt_const (x := (0 : ℝ)) (freeVolumeFraction M rho)).sub
        ((hasDerivAt_id 0).const_mul (M.excludedVolume j))) using 1
      · funext t
        simp
      · ring
  convert ((hn.div hd (by simpa using hfree)).log
      (by simpa using (div_ne_zero hrho hfree))) using 1
  · by_cases h : i = j
    · subst j
      simp <;> field_simp [hrho, hfree] <;> ring
    · simp [h]
      field_simp [hrho, hfree] <;> ring
/-- Derivative of the covolume response in a chemical-potential slice. -/
lemma hasDerivAt_covolumeRatio
    (M : Model (ι := ι)) (rho : State (ι := ι)) (i j : ι)
    (hfree : freeVolumeFraction M rho ≠ 0) :
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
        (hasDerivAt_id 0)).const_mul (M.excludedVolume i) using 1
      · funext t
        simp
      · ring
  have hd : HasDerivAt
      (fun t : ℝ => freeVolumeFraction M rho - M.excludedVolume j * t)
      (-M.excludedVolume j) 0 :=
    by
      convert (hasDerivAt_const (x := (0 : ℝ)) (freeVolumeFraction M rho)).sub
        ((hasDerivAt_id 0).const_mul (M.excludedVolume j)) using 1
      · funext t
        simp
      · ring
  convert hn.div hd (by simpa using hfree) using 1 <;>
  field_simp [hfree] <;> ring

/-- Actual Jacobian/Hessian derivative certificate. -/
theorem chemicalPotential_hasCoordinateDerivative_hessian
    (M : Model (ι := ι)) (rho : State (ι := ι))
    (hrho : ∀ i, rho i ≠ 0) (hfree : freeVolumeFraction M rho ≠ 0) :
    HessianDerived M rho := by
  intro i j
  rw [show (fun t => chemicalPotential M (perturb rho j t) i) =
      coordinateChemicalPotentialSlice M rho i j by
    funext t
    exact chemicalPotential_perturb_eq_coordinateSlice M rho i j t]
  unfold coordinateChemicalPotentialSlice
  have hlog := hasDerivAt_logComponentRatio M rho i j (hrho i) hfree
  have hcov := hasDerivAt_covolumeRatio M rho i j hfree
  have hattr : HasDerivAt
      (fun t : ℝ => (∑ k, alpha M i k * rho k) + alpha M i j * t)
      (alpha M i j) 0 :=
    by
      convert (hasDerivAt_const (x := (0 : ℝ)) (∑ k, alpha M i k * rho k)).add
        ((hasDerivAt_id 0).const_mul (alpha M i j)) using 1
      · funext t
        simp
      · ring
  convert (hlog.add hcov).sub hattr using 1
  · funext t
    simp
    ring
  · unfold hessian
    by_cases hij : i = j
    · subst j; simp; ring
    · simp [hij]; ring

/-- Physical states provide the complete Hessian derivative certificate. -/
theorem chemicalPotential_hasCoordinateDerivative_hessian_of_physical
    (M : Model (ι := ι)) (rho : State (ι := ι)) (hphys : Physical M rho) :
    HessianDerived M rho := by
  apply chemicalPotential_hasCoordinateDerivative_hessian M rho (fun i => ne_of_gt (hphys.1 i))
  unfold freeVolumeFraction
  linarith [hphys.2]

@[simp] theorem freeVolumeFraction_directionalState
    (M : Model (ι := ι)) (rho q : State (ι := ι)) (t : ℝ) :
    freeVolumeFraction M (directionalState rho q t) =
      freeVolumeFraction M rho - t * occupiedFraction M q := by
  unfold freeVolumeFraction
  rw [occupiedFraction_directionalState]
  ring_nf

/-- Contraction of the Hessian before differentiation. -/
lemma contracted_hessian_formula
    (M : Model (ι := ι)) (rho q : State (ι := ι)) :
    (∑ i, ∑ j, q i * hessian M rho i j * q j) =
      (∑ i, (q i)^2 / rho i) +
      2 * totalDensity q * occupiedFraction M q / freeVolumeFraction M rho +
      totalDensity rho * (occupiedFraction M q)^2 /
        (freeVolumeFraction M rho)^2 -
      ∑ i, ∑ j, q i * alpha M i j * q j := by
  have hleft (b : ι → ℝ) :
      (∑ i, ∑ j, q i * b i * q j) =
        (∑ i, q i) * (∑ j, b j * q j) := by
    calc
      (∑ i, ∑ j, q i * b i * q j) =
          ∑ i, (q i * b i) * (∑ j, q j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.mul_sum]
      _ = (∑ i, q i * b i) * (∑ j, q j) := by
            rw [← Finset.sum_mul]
      _ = (∑ i, q i) * (∑ j, b j * q j) := by
            rw [show (∑ i, q i * b i) = ∑ i, b i * q i by
              apply Finset.sum_congr rfl
              intro i hi
              ring]
            ring
  have hright (b : ι → ℝ) :
      (∑ i, ∑ j, q i * b i * q j * b j) =
        (∑ i, b i * q i)^2 := by
    calc
      (∑ i, ∑ j, q i * b i * q j * b j) =
          ∑ i, (b i * q i) * (∑ j, b j * q j) := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              ∑ j, q i * b i * q j * b j =
                  ∑ j, (b i * q i) * (b j * q j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = (b i * q i) * (∑ j, b j * q j) := by
                    rw [← Finset.mul_sum]
      _ = (∑ i, b i * q i) * (∑ j, b j * q j) := by
            rw [← Finset.sum_mul]
      _ = (∑ i, b i * q i)^2 := by ring
  have hright' (b : ι → ℝ) :
      (∑ i, ∑ j, q i * q j * b j) =
        (∑ i, q i) * (∑ j, b j * q j) := by
    calc
      (∑ i, ∑ j, q i * q j * b j) =
          ∑ i, q i * (∑ j, b j * q j) := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              ∑ j, q i * q j * b j =
                  ∑ j, q i * (b j * q j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = q i * (∑ j, b j * q j) := by
                    rw [← Finset.mul_sum]
      _ = (∑ i, q i) * (∑ j, b j * q j) := by
            rw [← Finset.sum_mul]
  unfold hessian totalDensity occupiedFraction
  simp_rw [pow_two]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp
  ring_nf
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_add_distrib]
  have htripleLeft :
      (∑ x, ∑ y, (∑ z, (freeVolumeFraction M rho)⁻¹ ^ 2 *
        q x * M.excludedVolume x * M.excludedVolume y * rho z) * q y) =
      (freeVolumeFraction M rho)⁻¹ ^ 2 * (∑ z, rho z) *
        (∑ x, M.excludedVolume x * q x)^2 := by
    calc
      _ = ∑ x, ∑ y, ((freeVolumeFraction M rho)⁻¹ ^ 2 *
          q x * M.excludedVolume x * M.excludedVolume y) *
          (∑ z, rho z) * q y := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        rw [← Finset.mul_sum]
      _ = (freeVolumeFraction M rho)⁻¹ ^ 2 * (∑ z, rho z) *
          (∑ x, ∑ y, q x * M.excludedVolume x * q y * M.excludedVolume y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = (freeVolumeFraction M rho)⁻¹ ^ 2 * (∑ z, rho z) *
          (∑ x, M.excludedVolume x * q x)^2 := by
        rw [hright]
  have htripleRight :
      (∑ x, ∑ y, ∑ z, (freeVolumeFraction M rho)⁻¹ ^ 2 *
        rho x * M.excludedVolume z * q z * M.excludedVolume y * q y) =
      (freeVolumeFraction M rho)⁻¹ ^ 2 * (∑ z, rho z) *
        (∑ x, M.excludedVolume x * q x)^2 := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    calc
      (∑ x_1, ∑ x_2, (freeVolumeFraction M rho)⁻¹ ^ 2 * rho x *
          M.excludedVolume x_2 * q x_2 * M.excludedVolume x_1 * q x_1) =
          (freeVolumeFraction M rho)⁻¹ ^ 2 * rho x *
            (∑ x_1, ∑ x_2, M.excludedVolume x_2 * q x_2 *
              M.excludedVolume x_1 * q x_1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x_1 hx_1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x_2 hx_2
        ring
      _ = (freeVolumeFraction M rho)⁻¹ ^ 2 * rho x *
          (∑ x_1, M.excludedVolume x_1 * q x_1)^2 := by
        have hs :
            (∑ x_1, ∑ x_2, M.excludedVolume x_2 * q x_2 *
              M.excludedVolume x_1 * q x_1) =
              (∑ x_1, M.excludedVolume x_1 * q x_1)^2 := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            hright (fun x => M.excludedVolume x)
        rw [hs]
  have hA :
      (∑ x, ∑ y, q x * M.excludedVolume x *
        (freeVolumeFraction M rho)⁻¹ * q y) =
        (∑ x, q x) * (∑ y, (freeVolumeFraction M rho)⁻¹ *
          M.excludedVolume y * q y) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      hleft (fun x => (freeVolumeFraction M rho)⁻¹ * M.excludedVolume x)
  have hB :
      (∑ x, ∑ y, q x * M.excludedVolume y *
        (freeVolumeFraction M rho)⁻¹ * q y) =
        (∑ x, q x) * (∑ y, (freeVolumeFraction M rho)⁻¹ *
          M.excludedVolume y * q y) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      hright' (fun y => (freeVolumeFraction M rho)⁻¹ * M.excludedVolume y)
  have htripleLeft' :
      (∑ x, ∑ y, (∑ i, q x * (freeVolumeFraction M rho ^ 2)⁻¹ *
        (M.excludedVolume x * M.excludedVolume y * rho i)) * q y) =
      (freeVolumeFraction M rho)⁻¹ ^ 2 * (∑ z, rho z) *
        (∑ x, M.excludedVolume x * q x)^2 := by
    simpa only [inv_pow, mul_assoc, mul_comm, mul_left_comm] using htripleLeft
  have htripleRight' :
      (∑ x, ∑ y, ∑ i, (freeVolumeFraction M rho ^ 2)⁻¹ *
        (rho x * (M.excludedVolume i * q i * M.excludedVolume y * q y))) =
      (freeVolumeFraction M rho)⁻¹ ^ 2 * (∑ z, rho z) *
        (∑ x, M.excludedVolume x * q x)^2 := by
    simpa only [inv_pow, mul_assoc, mul_comm, mul_left_comm] using htripleRight
  have hcross :
      (∑ x, q x) * (∑ y, (freeVolumeFraction M rho)⁻¹ *
        M.excludedVolume y * q y) =
      ∑ x, ∑ y, (freeVolumeFraction M rho)⁻¹ * q y *
        M.excludedVolume x * q x := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (hleft (fun x => (freeVolumeFraction M rho)⁻¹ * M.excludedVolume x)).symm
  rw [hA, hB, htripleLeft', htripleRight']
  rw [hcross]
  try simp only [div_eq_mul_inv]
  ring_nf
  try simp only [← Finset.sum_mul]
  ring_nf

/-- Derivative of the contracted diagonal ideal term. -/
theorem hasDerivAt_contractedIdeal
    (rho q : State (ι := ι)) (hrho : ∀ i, rho i ≠ 0) :
    HasDerivAt
      (fun t => ∑ i, (q i)^2 / (rho i + t * q i))
      (∑ i, -(q i)^3 / (rho i)^2) 0 := by
  convert (HasDerivAt.sum (u := Finset.univ) (fun i _ => by
    have hd : HasDerivAt (fun t : ℝ => rho i + t * q i) (q i) 0 := by
      convert (hasDerivAt_const (x := (0 : ℝ)) (rho i)).add
        ((hasDerivAt_id 0).mul_const (q i)) using 1
      · funext t
        simp
      · ring
    convert (hasDerivAt_const (x := (0 : ℝ)) ((q i)^2)).div hd
      (by simpa using hrho i) using 1
    )) using 1
  · funext t
    simp
  · apply Finset.sum_congr rfl
    intro i hi
    simp [hrho i]
    ring

/-- Actual third-directional-derivative certificate. -/
theorem thirdDirectionalDerivativeDerived
    (M : Model (ι := ι)) (rho q : State (ι := ι))
    (hrho : ∀ i, rho i ≠ 0) (hfree : freeVolumeFraction M rho ≠ 0) :
    ThirdDirectionalDerivativeDerived M rho q := by
  unfold ThirdDirectionalDerivativeDerived
  rw [show (fun t => ∑ i, ∑ j,
      q i * hessian M (directionalState rho q t) i j * q j) =
      fun t =>
        (∑ i, (q i)^2 / (rho i + t * q i)) +
        2 * totalDensity q * occupiedFraction M q /
          (freeVolumeFraction M rho - t * occupiedFraction M q) +
        (totalDensity rho + t * totalDensity q) * (occupiedFraction M q)^2 /
          (freeVolumeFraction M rho - t * occupiedFraction M q)^2 -
        ∑ i, ∑ j, q i * alpha M i j * q j by
    funext t
    rw [contracted_hessian_formula, totalDensity_directionalState,
      freeVolumeFraction_directionalState]
    rfl]
  have hideal := hasDerivAt_contractedIdeal rho q hrho
  have hphi : HasDerivAt
      (fun t : ℝ => freeVolumeFraction M rho - t * occupiedFraction M q)
      (-occupiedFraction M q) 0 :=
    by
      convert (hasDerivAt_const (x := (0 : ℝ)) (freeVolumeFraction M rho)).sub
        ((hasDerivAt_id 0).mul_const (occupiedFraction M q)) using 1
      · funext t
        simp
      · ring
  have hlinear : HasDerivAt
      (fun t : ℝ => 2 * totalDensity q * occupiedFraction M q /
        (freeVolumeFraction M rho - t * occupiedFraction M q))
      (2 * totalDensity q * (occupiedFraction M q)^2 /
        (freeVolumeFraction M rho)^2) 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ))
      (2 * totalDensity q * occupiedFraction M q)).div hphi
      (by simpa using hfree) using 1 <;>
    field_simp [hfree] <;> ring
  have htot : HasDerivAt
      (fun t : ℝ => totalDensity rho + t * totalDensity q)
      (totalDensity q) 0 :=
    by
      convert (hasDerivAt_const (x := (0 : ℝ)) (totalDensity rho)).add
        ((hasDerivAt_id 0).mul_const (totalDensity q)) using 1
      · funext t
        simp
      · ring
  have hquad : HasDerivAt
      (fun t : ℝ => (totalDensity rho + t * totalDensity q) *
        (occupiedFraction M q)^2 /
        (freeVolumeFraction M rho - t * occupiedFraction M q)^2)
      (totalDensity q * (occupiedFraction M q)^2 /
          (freeVolumeFraction M rho)^2 +
       2 * totalDensity rho * (occupiedFraction M q)^3 /
          (freeVolumeFraction M rho)^3) 0 := by
    convert (htot.mul_const ((occupiedFraction M q)^2)).div (hphi.pow 2)
      (by simpa using pow_ne_zero 2 hfree) using 1
    · dsimp
      field_simp [hfree]
      ring_nf
  have hconst : HasDerivAt
      (fun _t : ℝ => ∑ i, ∑ j, q i * alpha M i j * q j) 0 0 :=
    hasDerivAt_const (x := (0 : ℝ)) _
  convert ((hideal.add hlinear).add hquad).sub hconst using 1
  · unfold thirdDirectionalDerivative
    ring_nf

/-- Physical states provide every third-directional derivative certificate. -/
theorem thirdDirectionalDerivativeDerived_of_physical
    (M : Model (ι := ι)) (rho q : State (ι := ι)) (hphys : Physical M rho) :
    ThirdDirectionalDerivativeDerived M rho q := by
  apply thirdDirectionalDerivativeDerived M rho q
    (fun i => ne_of_gt (hphys.1 i))
  unfold freeVolumeFraction
  linarith [hphys.2]

/-- All multicomponent derivative provenance bundled on the physical domain. -/
theorem fullDerivativeProvenance_of_physical
    (M : Model (ι := ι)) (rho : State (ι := ι)) (hphys : Physical M rho) :
    FullDerivativeProvenance M rho := by
  refine fullDerivativeProvenance_of_certificates M rho
    (chemicalPotentialDerived_of_physical M rho hphys)
    (chemicalPotential_hasCoordinateDerivative_hessian_of_physical M rho hphys) ?_
  intro q
  exact thirdDirectionalDerivativeDerived_of_physical M rho q hphys

end ClassicalThermodynamics.Models.VanDerWaals.Mixture
