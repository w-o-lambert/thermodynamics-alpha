import ClassicalThermodynamics.Thermodynamics.Extensivity.Euler
import ClassicalThermodynamics.Thermodynamics.Extensivity.Construction
namespace ClassicalThermodynamics.Thermodynamics.Extensivity
open scoped BigOperators

lemma pressure_freeEnergy_identity {ι : Type*} [Fintype ι]
    {F P V : ℝ} {mu N : ι → ℝ}
    (h : F = -P*V + ∑ i, mu i*N i) : P*V = -F + ∑ i, mu i*N i := by linarith

lemma pressure_of_nonzero_volume {ι : Type*} [Fintype ι]
    {F P V : ℝ} {mu N : ι → ℝ} (hV : V ≠ 0)
    (h : F = -P*V + ∑ i, mu i*N i) :
    P = (-F + ∑ i, mu i*N i) / V := by
  apply (eq_div_iff hV).2; linarith

theorem pressure_freeEnergy_identity_of_oneHomogeneous
    {ι : Type*} [Fintype ι]
    (F : (ℝ × (ι → ℝ)) → ℝ) (V : ℝ) (N : ι → ℝ)
    (P : ℝ) (mu : ι → ℝ)
    (F' : (ℝ × (ι → ℝ)) →L[ℝ] ℝ)
    (hhom : OneHomogeneous F)
    (hF : HasFDerivAt F F' (V, N))
    (hconj : F' (V, N) = -P * V + ∑ i, mu i * N i) :
    P * V = -F (V, N) + ∑ i, mu i * N i := by
  have hEuler : F' (V, N) = F (V, N) :=
    euler_of_oneHomogeneous F (V, N) F' hhom hF
  rw [← hEuler, hconj]
  ring

theorem pressure_density_identity
    {ι : Type*} [Fintype ι]
    {F : (ℝ × (ι → ℝ)) → ℝ} {f : (ι → ℝ) → ℝ}
    {P : ℝ} {N rho mu : ι → ℝ}
    (volume : ℝ) (hvolume : volume ≠ 0)
    (hscale : F (volume, N) = volume * f rho)
    (hamount : N = fun i => volume * rho i)
    (hidentity :
      P * volume = -F (volume, N) + ∑ i, mu i * N i) :
    P = (∑ i, rho i * mu i) - f rho := by
  have hsum :
      (∑ i, mu i * (volume * rho i)) =
        volume * (∑ i, rho i * mu i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hscale, hamount, hsum] at hidentity
  have hresult :
      P * volume = ((∑ i, rho i * mu i) - f rho) * volume := by
    calc
      P * volume = -(volume * f rho) +
          volume * (∑ i, rho i * mu i) := hidentity
      _ = ((∑ i, rho i * mu i) - f rho) * volume := by ring
  exact mul_right_cancel₀ hvolume hresult

theorem extensiveFreeEnergy_pressure_identity_of_conjugate
    {ι : Type*} [Fintype ι] (densityFreeEnergy : (ι → ℝ) → ℝ)
    {volume : ℝ} (hvolume : volume ≠ 0) (amount : ι → ℝ)
    (P : ℝ) (mu : ι → ℝ)
    {G : (ℝ × (ι → ℝ)) →L[ℝ] ℝ}
    (hG :
      HasFDerivAt
        (fun x : ℝ × (ι → ℝ) =>
          extensiveFreeEnergy densityFreeEnergy x.1 x.2)
        G (volume, amount))
    (hconj :
      G (volume, amount) =
        -P * volume + ∑ i, mu i * amount i) :
    P * volume =
      -(volume * densityFreeEnergy (densityState volume amount)) +
        ∑ i, mu i * amount i := by
  have hEuler := euler_of_oneHomogeneous
    (fun x : ℝ × (ι → ℝ) =>
      extensiveFreeEnergy densityFreeEnergy x.1 x.2)
    (volume, amount) G
    (extensiveFreeEnergy_oneHomogeneous densityFreeEnergy) hG
  calc
    P * volume =
        -G (volume, amount) + ∑ i, mu i * amount i := by
      rw [hconj]
      ring
    _ = -extensiveFreeEnergy densityFreeEnergy volume amount +
        ∑ i, mu i * amount i := by
      rw [← hEuler]
    _ = -(volume * densityFreeEnergy (densityState volume amount)) +
        ∑ i, mu i * amount i := by
      rw [extensiveFreeEnergy_eq densityFreeEnergy hvolume amount]
end ClassicalThermodynamics.Thermodynamics.Extensivity
