module

public import SubdiffusiveProcess.MeyersRegularity.Moments

@[expose] public section

/-! Uniform control of the large-scale good-lambda cutoff on nested balls. -/

open MeasureTheory Filter Set Homogenization
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

/-- Scaling of the energy cutoff with the spatial separation. -/
theorem large_scale_cutoff_le {d depth : ℕ} (hd : 0 < d)
    {gap eps D B X Y : ℝ} (hgap : 0 < gap) (heps : 0 < eps)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hXD : X ≤ D^2) (hYD : Y ≤ B^2*D^2) :
    Real.sqrt (((2*((gap/(d : ℝ))/(10*(3 : ℝ)^depth)))^d)⁻¹ * (X+eps⁻¹^2*Y)) ≤
      Real.sqrt ((5*(d : ℝ)*(3 : ℝ)^depth)^d * (1+eps⁻¹^2*B^2)) *
        gap^(-(d : ℝ)/2)*D := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  let c : ℝ := 5*(d : ℝ)*(3 : ℝ)^depth
  have hc : 0 < c := by dsimp only [c]; positivity
  have hden : 0 < 10*(3 : ℝ)^depth := by positivity
  have heq : 2*((gap/(d : ℝ))/(10*(3 : ℝ)^depth)) = gap/c := by
    dsimp only [c]
    field_simp
    ring
  have hgeom : ((2*((gap/(d : ℝ))/(10*(3 : ℝ)^depth)))^d)⁻¹ =
      c^d*gap^(-(d : ℝ)) := by
    rw [heq, div_pow, inv_div, Real.rpow_neg hgap.le, Real.rpow_natCast]
    exact div_eq_mul_inv _ _
  have hgap_pow : (gap^(-(d : ℝ)/2))^2 = gap^(-(d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hgap.le]
    congr 1
    norm_num
  have hconst : 0 ≤ c^d*(1+eps⁻¹^2*B^2) := by positivity
  have hsquare : (Real.sqrt (c^d*(1+eps⁻¹^2*B^2))*gap^(-(d : ℝ)/2)*D)^2 =
      c^d*gap^(-(d : ℝ))*((1+eps⁻¹^2*B^2)*D^2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hconst, hgap_pow]
    ring
  have hcombo : X+eps⁻¹^2*Y ≤ (1+eps⁻¹^2*B^2)*D^2 := by
    calc
      X+eps⁻¹^2*Y ≤ D^2+eps⁻¹^2*(B^2*D^2) :=
        add_le_add hXD (mul_le_mul_of_nonneg_left hYD (sq_nonneg _))
      _ = _ := by ring
  have hinner : 0 ≤ ((2*((gap/(d : ℝ))/(10*(3 : ℝ)^depth)))^d)⁻¹ * (X+eps⁻¹^2*Y) := by
    rw [hgeom]
    positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt hinner]
  change _ ≤ (Real.sqrt (c^d*(1+eps⁻¹^2*B^2))*gap^(-(d : ℝ)/2)*D)^2
  rw [hsquare, hgeom]
  exact mul_le_mul_of_nonneg_left hcombo (by positivity)


/-- The cutoff loss has exactly the spatial exponent required by iteration. -/
theorem scaled_low_moment_eq {d : ℕ} {p M K gap D : ℝ}
    (hp : 2 < p) (hM : 0 ≤ M) (hK : 0 ≤ K) (hgap : 0 < gap) (hD : 0 ≤ D) :
    (M*(2*K*gap^(-(d : ℝ)/2)*D))^(p-2)*D^2 =
      (2*M*K)^(p-2)*gap^(-spatialPower d p)*D^p := by
  have hprod : M*(2*K*gap^(-(d : ℝ)/2)*D) =
      (2*M*K)*gap^(-(d : ℝ)/2)*D := by ring
  rw [hprod, Real.mul_rpow (by positivity) hD,
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hgap.le _),
    ← Real.rpow_mul hgap.le]
  have hexp : (-(d : ℝ)/2)*(p-2) = -spatialPower d p := by
    unfold spatialPower
    ring
  rw [hexp]
  have hDpow : D^(p-2)*D^2 = D^p := by
    rw [mul_comm]
    exact sq_mul_rpow_sub_two hD hp.le
  rw [mul_assoc, hDpow]

end SubdiffusiveProcess.MeyersRegularity
