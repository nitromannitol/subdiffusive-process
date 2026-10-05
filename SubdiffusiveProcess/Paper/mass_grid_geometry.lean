module

public import SubdiffusiveProcess.Paper.thm_prop_base

@[expose] public section

/-! Geometry of the affine supplier of `thm_prop`: the mass geometry `aux_thm_prop_selection_geometry`
in the paper's `b`-route (paper `lem-shifts`, `lem-mass`, Step 1 of `thm-prop`):
`Mm = 3^b + 1`, `gamma = (H1 - b)/H1` (so `L^gamma = 3^(H1-b) `, `L^(gamma-1) = 3^-b`), `width = Cd`.
The padding fraction `b` is chosen from the padding constant `Cd` alone (before `L`); `H1` is then any
sufficiently large level (paper: "`L = 3^H1` with `H1 ≥ b + 2`"). -/

open Filter Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Real-power bookkeeping: with `gamma = (H1 - b)/H1`, `(3^H1)^gamma = 3^H1 * 3^(-b)`. -/
theorem aux_mass_grid_geometry_pow (b H1 : ℕ) (hH1 : 1 ≤ H1) :
    ((3 : ℝ) ^ H1) ^ (((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ)) = (3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(b : ℤ)) := by
  have hH1' : (H1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : H1 ≠ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have : (H1 : ℝ) * (((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ)) = (H1 : ℝ) + (-(b : ℝ)) := by
    field_simp
    ring
  rw [this, Real.rpow_add (by norm_num), Real.rpow_natCast, ← Real.rpow_intCast]
  simp

theorem aux_mass_grid_geometry_pow_sub (b H1 : ℕ) (hH1 : 1 ≤ H1) :
    ((3 : ℝ) ^ H1) ^ ((((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ)) - 1) = (3 : ℝ) ^ (-(b : ℤ)) := by
  have hH1' : (H1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : H1 ≠ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have : (H1 : ℝ) * ((((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ)) - 1) = -(b : ℝ) := by
    field_simp
    ring
  rw [this, ← Real.rpow_intCast]
  simp

/-- The padding-loss budget: `b` is chosen from `Cd` (and the dimension) alone. -/
theorem aux_mass_grid_geometry_choose_b (d : ℕ) (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ b : ℕ, 1 ≤ b ∧
      2 * (d : ℝ) * (Cd + 2) * (3 : ℝ) ^ (-(b : ℤ)) ≤ 1 / 32 := by
  have hc : 0 < 2 * (d : ℝ) * (Cd + 2) + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (32 * (2 * (d : ℝ) * (Cd + 2) + 1))
    by positivity) (show (1 / 3 : ℝ) < 1 by norm_num)
  refine ⟨n + 1, by omega, ?_⟩
  have hp : (3 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) ≤ (1 / 3 : ℝ) ^ n := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have hnn : 0 ≤ 2 * (d : ℝ) * (Cd + 2) := by positivity
  calc 2 * (d : ℝ) * (Cd + 2) * (3 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))
      ≤ (2 * (d : ℝ) * (Cd + 2) + 1) * (1 / (32 * (2 * (d : ℝ) * (Cd + 2) + 1))) := by
        apply mul_le_mul (by linarith) (hp.trans hn.le) (by positivity) (by linarith)
    _ = 1 / 32 := by field_simp

/-- Given `b`, all sufficiently large `H1` satisfy the padding/loss budget of the mass geometry
with `gamma = (H1 - b)/H1`, `Mm = 3^b + 1`, `width = Cd`. -/
theorem aux_mass_grid_geometry_choose_H1 (d : ℕ) (Cd zeta : ℝ) (hCd : 0 < Cd)
    (hzeta : 0 < zeta) (b : ℕ) (hb : 1 ≤ b)
    (hbloss : 2 * (d : ℝ) * (Cd + 2) * (3 : ℝ) ^ (-(b : ℤ)) ≤ 1 / 32) (H0 : ℕ) :
    ∃ H1 : ℕ, H0 ≤ H1 ∧ b + 2 ≤ H1 ∧
      ((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 ∧
      1 ≤ Cd * ((3 : ℝ) ^ H1) ^ (((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ)) ∧
      Nat.Coprime (3 ^ b + 1) (3 ^ H1) ∧
      ((3 ^ b + 1 : ℕ) : ℝ) ^ (-1 : ℝ) ≤
        ((3 : ℝ) ^ H1) ^ ((((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ)) - 1) ∧
      (1 / 32 : ℝ) + ((3 : ℝ) ^ H1) ^ (-zeta) +
        (2 * (d : ℝ) * (Cd + 2)) *
          ((3 : ℝ) ^ H1) ^ ((((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ)) - 1) + (1 / 32 : ℝ) ≤ 1 / 8 := by
  have hpow : Tendsto (fun n : ℕ => (3 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hz : Tendsto (fun n : ℕ => ((3 : ℝ) ^ n) ^ (-zeta)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hzeta).comp hpow
  have hbig : Tendsto (fun n : ℕ => Cd * (3 : ℝ) ^ n * (3 : ℝ) ^ (-(b : ℤ))) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => Cd * (3 : ℝ) ^ n) atTop atTop :=
      hpow.const_mul_atTop hCd
    exact h1.atTop_mul_const (by positivity)
  obtain ⟨H1, hH0, hH2, hzsmall, hbigge⟩ :=
    ((eventually_ge_atTop H0).and ((eventually_ge_atTop (b + 2)).and
      ((hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 32))).and
        (hbig.eventually (eventually_ge_atTop (1 : ℝ)))))).exists
  have hH1 : 1 ≤ H1 := by omega
  have hHpos : (0 : ℝ) < (H1 : ℝ) := by exact_mod_cast (by omega : 0 < H1)
  have hbH : (b : ℝ) < (H1 : ℝ) := by exact_mod_cast (by omega : b < H1)
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hLg := aux_mass_grid_geometry_pow_sub b H1 hH1
  refine ⟨H1, hH0, hH2, ⟨div_pos (by linarith) hHpos, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_one hHpos]; linarith
  · rw [aux_mass_grid_geometry_pow b H1 hH1]
    calc (1 : ℝ) ≤ Cd * (3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(b : ℤ)) := hbigge
      _ = Cd * ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(b : ℤ))) := by ring
  · have h3 : Nat.Coprime (3 ^ b + 1) 3 := by
      have h1 : (3 ^ b + 1) % 3 = 1 := by
        have : 3 ∣ 3 ^ b := dvd_pow_self 3 (by omega)
        omega
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      omega
    exact Nat.Coprime.pow_right H1 h3
  · rw [hLg, Real.rpow_neg_one]
    have hM : ((3 : ℝ) ^ b) ≤ ((3 ^ b + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    rw [zpow_neg, zpow_natCast]
    exact inv_anti₀ (by positivity) hM
  · rw [hLg]
    linarith


/-- Geometry of the affine supplier in the paper's order: `b` from `Cd`, then every large `H1`
gives a mass geometry with `Mm = 3^b + 1`, `gamma = (H1-b)/H1`, `width = Cd`. -/
theorem mass_grid_geometry (d : ℕ) (Cd zeta : ℝ) (hCd : 0 < Cd) (hzeta : 0 < zeta) :
    ∃ b : ℕ, 1 ≤ b ∧ 2 * (d : ℝ) * (Cd + 2) * (3 : ℝ) ^ (-(b : ℤ)) ≤ 1 / 32 ∧
      ∀ H0 : ℕ, ∃ g : aux_thm_prop_selection_geometry d,
        H0 ≤ g.H1 ∧ b + 2 ≤ g.H1 ∧ g.Mm = 3 ^ b + 1 ∧
        g.gamma = ((g.H1 : ℝ) - (b : ℝ)) / (g.H1 : ℝ) ∧ g.zeta = zeta ∧ g.width = Cd := by
  obtain ⟨b, hb, hbloss⟩ := aux_mass_grid_geometry_choose_b d Cd hCd
  refine ⟨b, hb, hbloss, fun H0 => ?_⟩
  obtain ⟨H1, hH0, hH2, hgam, hpad, hcop, hshift, hloss⟩ :=
    aux_mass_grid_geometry_choose_H1 d Cd zeta hCd hzeta b hb hbloss H0
  have hMm : 2 ≤ 3 ^ b + 1 := by
    have : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
    omega
  exact ⟨⟨H1, 3 ^ b + 1, ((H1 : ℝ) - (b : ℝ)) / (H1 : ℝ), zeta, Cd, by omega, hMm, hgam, hzeta,
    hCd, hcop, hshift, hpad, hloss⟩, hH0, hH2, rfl, rfl, rfl, rfl⟩

end SubdiffusiveProcess.Paper
end
