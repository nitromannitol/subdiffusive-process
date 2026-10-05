module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.LiouvilleGeometry

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-! ### Machine evidence for the defect -/

/-- **Evidence.**  Any real functional tending to `+∞` satisfies
`liminf … atTop = 0`, because mathlib's `sSup` of a set unbounded above is the
junk value `0`.  Hence the frozen Liouville hypothesis
`e.multifractal.Liouville.power.growth` does not say what the source intends
for rapidly growing `u`. -/
theorem liminf_eq_zero_of_tendsto_atTop {F : ℝ → ℝ}
    (h : Tendsto F atTop atTop) : liminf F atTop = 0 := by
  rw [liminf_eq]
  have hset : {a : ℝ | ∀ᶠ x in atTop, a ≤ F x} = Set.univ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact h.eventually_ge_atTop a
  rw [hset]
  exact Real.sSup_univ

/-! ### The Liouville functional -/

/-- The infimum over constants appearing in the Liouville hypothesis is
nonnegative. -/
theorem sInf_sub_const_nonneg (R : ℝ) (u : Vec d → ℝ) :
    0 ≤ sInf {r : ℝ | ∃ c : ℝ,
      r = normalizedL2On (Metric.ball (0 : Vec d) R) (fun x ↦ u x - c)} := by
  refine le_csInf (nonempty_sub_const_set R u) ?_
  rintro r ⟨c, rfl⟩
  exact normalizedL2On_nonneg _ _

/-- The Liouville functional `R ↦ R^{-γ}·inf_c ‖u-c‖_{L̲²(B_R)}`. -/
def liouvilleFunctional (gamma : ℝ) (u : Vec d → ℝ) (R : ℝ) : ℝ :=
  R ^ (-gamma) *
    sInf {r : ℝ | ∃ c : ℝ,
      r = normalizedL2On (Metric.ball (0 : Vec d) R) (fun x ↦ u x - c)}

/-- The Liouville functional is nonnegative at positive radii. -/
theorem liouvilleFunctional_nonneg {gamma : ℝ} (u : Vec d → ℝ) {R : ℝ}
    (hR : 0 < R) : 0 ≤ liouvilleFunctional gamma u R :=
  mul_nonneg (Real.rpow_nonneg hR.le _) (sInf_sub_const_nonneg R u)

/-- The functional is bounded below along `atTop`: it is nonnegative at every
positive radius. -/
theorem isBoundedUnder_ge_liouvilleFunctional {gamma : ℝ} (u : Vec d → ℝ) :
    IsBoundedUnder (· ≥ ·) atTop (liouvilleFunctional (d := d) gamma u) := by
  refine ⟨0, ?_⟩
  rw [eventually_map]
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact liouvilleFunctional_nonneg u hR

/-- **The extraction, conditionally.**  A vanishing `liminf` gives radii,
arbitrarily large, at which the Liouville functional is arbitrarily small --
*provided* the functional is coboundedly bounded below.  This is
`t.C`.

`hcobdd` is the ingredient the frozen hypothesis does not supply; see the
module docstring and `liminf_eq_zero_of_tendsto_atTop`. -/
theorem exists_radius_ge_and_lt {gamma : ℝ} {u : Vec d → ℝ}
    (hcobdd : IsCoboundedUnder (· ≥ ·) atTop (liouvilleFunctional (d := d) gamma u))
    (hlim : liminf (liouvilleFunctional (d := d) gamma u) atTop = 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (R0 : ℝ) :
    ∃ R : ℝ, R0 ≤ R ∧ liouvilleFunctional (d := d) gamma u R < epsilon := by
  have hlt : liminf (liouvilleFunctional (d := d) gamma u) atTop < epsilon := by
    rw [hlim]; exact hepsilon
  have hfreq : ∃ᶠ R in atTop, liouvilleFunctional (d := d) gamma u R < epsilon :=
    frequently_lt_of_liminf_lt hcobdd hlt
  exact frequently_atTop.1 hfreq R0

/-! ### From a large radius to a large scale -/

/-- The scale selected at a radius `R ≥ 3^N` satisfies `m ≥ N`. -/
theorem le_of_scale_of_le {m N : ℤ} {R : ℝ} (hR : (3 : ℝ) ^ N ≤ R)
    (hupper : 2 * R < (3 : ℝ) ^ (m + 1)) : N ≤ m := by
  by_contra hlt
  push Not at hlt
  have hle : m + 1 ≤ N := by omega
  have hmono : (3 : ℝ) ^ (m + 1) ≤ (3 : ℝ) ^ N :=
    zpow_le_zpow_right₀ (by norm_num) hle
  have hRpos : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  linarith

/-! ### The scaled cube seminorm -/



theorem rpow_neg_mul_intCast (gamma : ℝ) (m : ℤ) :
    (3 : ℝ) ^ (-gamma * (m : ℝ)) = ((3 : ℝ) ^ m) ^ (-gamma) := by
  rw [← Real.rpow_intCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num), mul_comm]

/-- **S8, assembled.**  For every `ε > 0` and every `N`, there is a scale
`m ≥ N` at which the scaled centered cube seminorm is below `ε`.

This is `t.C` in the form the Liouville argument consumes:
the geometry and the `sInf` transfer come from `LiouvilleGeometry`, the radii
from `exists_radius_ge_and_lt`, and the constant
`(3/2)^γ · 3^{d/2}` is absorbed by shrinking `ε`.

Conditional on `hcobdd`, which the frozen hypothesis does not supply. -/
theorem exists_scale_ge_and_lt {gamma : ℝ} {u : Vec d → ℝ}
    (hgamma : 0 < gamma)
    (hcobdd : IsCoboundedUnder (· ≥ ·) atTop (liouvilleFunctional (d := d) gamma u))
    (hlim : liminf (liouvilleFunctional (d := d) gamma u) atTop = 0)
    (huInt : ∀ m : ℤ, IntegrableOn u (cube d m))
    (huSq : ∀ m : ℤ, IntegrableOn (fun x ↦ u x ^ 2) (cube d m))
    (hball : ∀ (R : ℝ) (c : ℝ),
      IntegrableOn (fun x ↦ (u x - c) ^ 2) (Metric.ball (0 : Vec d) R))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (N : ℤ) :
    ∃ m : ℤ, N ≤ m ∧
      (3 : ℝ) ^ (-gamma * (m : ℝ)) *
          normalizedL2On (cube d m)
            (fun x ↦ u x - averageOn (cube d m) u) < epsilon := by
  set K : ℝ := ((3 : ℝ) / 2) ^ gamma * Real.sqrt ((3 : ℝ) ^ d) with hK
  have hKpos : 0 < K := by
    refine mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.sqrt_pos.2 ?_)
    positivity
  -- Shrink `ε` by the constant, and demand a radius past `3^N` and past `0`.
  obtain ⟨R, hRge, hRlt⟩ :=
    exists_radius_ge_and_lt hcobdd hlim (div_pos hepsilon hKpos)
      (max ((3 : ℝ) ^ N) 1)
  have hR3N : (3 : ℝ) ^ N ≤ R := le_trans (le_max_left _ _) hRge
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hRge)
  obtain ⟨m, hlower, hupper⟩ := exists_scale_le_and_lt hRpos
  refine ⟨m, le_of_scale_of_le hR3N hupper, ?_⟩
  -- Combine the scale factor with the `sInf` transfer.
  have hscale : ((3 : ℝ) ^ m) ^ (-gamma) ≤
      ((3 : ℝ) / 2) ^ gamma * R ^ (-gamma) :=
    rpow_neg_scale_le hgamma hRpos hupper
  have htransfer :
      normalizedL2On (cube d m) (fun x ↦ u x - averageOn (cube d m) u) ≤
        Real.sqrt ((3 : ℝ) ^ d) *
          sInf {r : ℝ | ∃ c : ℝ,
            r = normalizedL2On (Metric.ball (0 : Vec d) R) (fun x ↦ u x - c)} :=
    normalizedL2On_cube_le_sInf_ball hlower hupper (huInt m) (huSq m)
      (fun c ↦ hball R c)
  have hprod :
      ((3 : ℝ) ^ m) ^ (-gamma) *
          normalizedL2On (cube d m)
            (fun x ↦ u x - averageOn (cube d m) u) ≤
        K * liouvilleFunctional (d := d) gamma u R := by
    have h1 : (0 : ℝ) ≤ ((3 : ℝ) ^ m) ^ (-gamma) :=
      Real.rpow_nonneg (by positivity) _
    have h2 : (0 : ℝ) ≤
        normalizedL2On (cube d m)
          (fun x ↦ u x - averageOn (cube d m) u) :=
      normalizedL2On_nonneg _ _
    calc ((3 : ℝ) ^ m) ^ (-gamma) *
            normalizedL2On (cube d m)
              (fun x ↦ u x - averageOn (cube d m) u)
        ≤ (((3 : ℝ) / 2) ^ gamma * R ^ (-gamma)) *
            (Real.sqrt ((3 : ℝ) ^ d) *
              sInf {r : ℝ | ∃ c : ℝ,
                r = normalizedL2On (Metric.ball (0 : Vec d) R)
                  (fun x ↦ u x - c)}) :=
          mul_le_mul hscale htransfer h2 (by positivity)
      _ = K * liouvilleFunctional (d := d) gamma u R := by
          rw [hK, liouvilleFunctional]; ring
  rw [rpow_neg_mul_intCast]
  refine lt_of_le_of_lt hprod ?_
  rw [← lt_div_iff₀' hKpos]
  exact hRlt

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
