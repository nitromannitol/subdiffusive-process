module

public import SubdiffusiveProcess.Paper.mass_grid_geometry
public import Mathlib.Tactic

@[expose] public section

open Filter Topology
open scoped Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Choose the mass-grid geometry with gamma fixed before the affine scale threshold.
This preserves the order gamma, then H0, then H1 and the finite shift denominator. -/
theorem mass_grid_geometry_fixed (d : ℕ) (Cd gamma zeta : ℝ)
    (hCd : 0 < Cd) (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1) (hzeta : 0 < zeta)
    (H0 : ℕ) :
    ∃ g : aux_thm_prop_selection_geometry d,
      H0 ≤ g.H1 ∧ g.gamma = gamma ∧ g.zeta = zeta ∧ g.width = Cd := by
  have hpow : Tendsto (fun n : ℕ => (3 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hLg : Tendsto (fun n : ℕ => ((3 : ℝ) ^ n) ^ gamma) atTop atTop :=
    (tendsto_rpow_atTop hgamma.1).comp hpow
  have hsmall : Tendsto (fun n : ℕ => ((3 : ℝ) ^ n) ^ (gamma - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 1 - gamma by linarith [hgamma.2])).comp hpow
    simpa only [neg_sub] using! h
  have hz : Tendsto (fun n : ℕ => ((3 : ℝ) ^ n) ^ (-zeta)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hzeta).comp hpow
  have hweight' : Tendsto (fun n : ℕ =>
      (2 * (d : ℝ) * (Cd + 2)) * ((3 : ℝ) ^ n) ^ (gamma - 1)) atTop (𝓝 0) := by
    simpa using hsmall.const_mul (2 * (d : ℝ) * (Cd + 2))
  have hbig := hLg.const_mul_atTop hCd
  obtain ⟨H1, hH0, hH1, hzsmall, hws, hlarge⟩ :=
    ((eventually_ge_atTop H0).and ((eventually_ge_atTop 1).and
      ((hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 32))).and
        ((hweight'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 32))).and
          (hbig.eventually (eventually_ge_atTop (1 : ℝ))))))).exists
  let b : ℕ := Nat.ceil ((1 - gamma) * (H1 : ℝ))
  have hb0 : 0 < b := by
    apply Nat.ceil_pos.mpr
    exact mul_pos (by linarith [hgamma.2]) (by exact_mod_cast (by omega : 0 < H1))
  have hb : (1 - gamma) * (H1 : ℝ) ≤ (b : ℝ) := Nat.le_ceil _
  have hcop : Nat.Coprime (3 ^ b + 1) (3 ^ H1) := by
    have h3 : Nat.Coprime (3 ^ b + 1) 3 := by
      have h1 : (3 ^ b + 1) % 3 = 1 := by
        have : 3 ∣ 3 ^ b := dvd_pow_self 3 (by omega)
        omega
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      omega
    exact Nat.Coprime.pow_right H1 h3
  have hshift : ((3 ^ b + 1 : ℕ) : ℝ) ^ (-1 : ℝ) ≤
      ((3 : ℝ) ^ H1) ^ (gamma - 1) := by
    rw [Real.rpow_neg_one]
    have hM : (3 : ℝ) ^ b ≤ ((3 ^ b + 1 : ℕ) : ℝ) := by push_cast; linarith
    calc (((3 ^ b + 1 : ℕ) : ℝ))⁻¹ ≤ ((3 : ℝ) ^ b)⁻¹ :=
        inv_anti₀ (by positivity) hM
      _ = (3 : ℝ) ^ (-(b : ℝ)) := by rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
      _ ≤ (3 : ℝ) ^ ((H1 : ℝ) * (gamma - 1)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith
      _ = ((3 : ℝ) ^ H1) ^ (gamma - 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hMm : 2 ≤ 3 ^ b + 1 := by
    have : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
    omega
  refine ⟨⟨H1, 3 ^ b + 1, gamma, zeta, Cd, hH1, hMm, hgamma, hzeta,
    hCd, hcop, hshift, hlarge, ?_⟩, hH0, rfl, rfl, rfl⟩
  linarith

end SubdiffusiveProcess.Paper
