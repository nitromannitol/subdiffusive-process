module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.VarianceMinimization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows

@[expose] public section

/-!
# Cube/ball geometry for the Liouville argument

The Liouville half of Theorem C converts its hypothesis
`e.multifractal.Liouville.power.growth`, which is
stated on Euclidean balls `B_R`, into a statement on the centered cubes `𝔠_m`
carrying `e.large.scale.Holder.multifractal`.  The tex does this at

> let `m_j` be the largest integer such that `𝔠_{m_j} ⊆ B_{R_j}`. Since
> `3^{m_j} ≃ R_j` and `(u)_{𝔠_{m_j}}` minimizes
> `c ↦ ‖u-c‖_{L̲²(𝔠_{m_j})}`,
> `3^{-γ_reg m_j} ‖u-(u)_{𝔠_{m_j}}‖_{L̲²(𝔠_{m_j})} ⟶ 0`.

Two things make this clean in the formalization.

**The metric is the sup metric.**  `Vec d = Fin d → ℝ` carries the `Pi`
(supremum) metric, so `Metric.ball 0 r` is the open coordinate box of radius
`r`, and the centered paper cube is *exactly* a ball:

`cube d m = Metric.ball 0 (3^m/2)`  (`cube_eq_ball`).

So "the largest `m` with `𝔠_m ⊆ B_R`" is the largest `m` with `3^m/2 ≤ R`, and
the commensurability `3^{m} ≃ R` of the tex is the two-sided bound
`2R/3 < 3^m ≤ 2R` (`exists_scale_le_and_lt`).

**The ball is sandwiched between consecutive cubes.**  At that scale
`𝔠_m ⊆ B_R ⊆ 𝔠_{m+1}`, so the volume ratio `|B_R|/|𝔠_m|` is at most
`|𝔠_{m+1}|/|𝔠_m| = 3^d`, and the ball's own volume never has to be computed.
Combined with `Section6Iteration.normalizedL2On_le_of_subset` and the
minimizing property `sInf_normalizedL2On_sub_const` of
`SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.VarianceMinimization`, this gives the
transfer `normalizedL2On_cube_le_sInf_ball` with the explicit constant `3^{d/2}`.

Naming note: the centred inclusions here are `cube_subset_ball_zero` and
`ball_zero_subset_cube` rather than the shorter names, because
`Section6ExcessDecay.FractionalHolderBridge` already declares a different
`cube_subset_ball` (the diameter version, `cube d m ⊆ Metric.ball p (3^m)` for
any `p` in the cube) and this file opens that namespace.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ### The centered cube is a ball in the supremum metric -/

/-- Membership in a centered ball of `Vec d`, which carries the supremum
metric. -/
theorem mem_ball_zero_iff_forall {r : ℝ} (hr : 0 < r) {x : Vec d} :
    x ∈ Metric.ball (0 : Vec d) r ↔ ∀ i, |x i| < r := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
  simp [Real.norm_eq_abs]

/-- **The centered paper cube is exactly a ball of radius `3^m/2`.**  This is
what makes "the largest `m` with `𝔠_m ⊆ B_R`" a statement about real numbers. -/
theorem cube_eq_ball (d : ℕ) (m : ℤ) :
    cube d m = Metric.ball (0 : Vec d) (1 / 2 * (3 : ℝ) ^ m) := by
  have hr : (0 : ℝ) < 1 / 2 * (3 : ℝ) ^ m := by positivity
  ext x
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff,
    mem_ball_zero_iff_forall hr]
  refine forall_congr' fun i ↦ ?_
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩

/-- A cube sits inside a ball as soon as its radius does. -/
theorem cube_subset_ball_zero {m : ℤ} {R : ℝ} (h : 1 / 2 * (3 : ℝ) ^ m ≤ R) :
    cube d m ⊆ Metric.ball (0 : Vec d) R := by
  rw [cube_eq_ball]
  exact Metric.ball_subset_ball h

/-- A ball sits inside a cube as soon as the cube's radius dominates it. -/
theorem ball_zero_subset_cube {m : ℤ} {R : ℝ} (h : R ≤ 1 / 2 * (3 : ℝ) ^ m) :
    Metric.ball (0 : Vec d) R ⊆ cube d m := by
  rw [cube_eq_ball]
  exact Metric.ball_subset_ball h

/-! ### Selection of the scale, and commensurability -/

/-- **The largest scale whose cube fits in `B_R`.**  For `R > 0` there is an
integer `m` with `3^m ≤ 2R < 3^{m+1}`; equivalently `𝔠_m ⊆ B_R` and
`B_R ⊆ 𝔠_{m+1}`.  The two-sided bound `2R/3 < 3^m ≤ 2R` is the
commensurability `3^m ≃ R`. -/
theorem exists_scale_le_and_lt {R : ℝ} (hR : 0 < R) :
    ∃ m : ℤ, (3 : ℝ) ^ m ≤ 2 * R ∧ 2 * R < (3 : ℝ) ^ (m + 1) := by
  have h2R : (0 : ℝ) < 2 * R := by linarith
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow h2R (by norm_num : (1 : ℝ) < 3)
  exact ⟨m, hm1, hm2⟩

/-- At the selected scale the cube is contained in the ball. -/
theorem cube_subset_ball_of_le {m : ℤ} {R : ℝ} (h : (3 : ℝ) ^ m ≤ 2 * R) :
    cube d m ⊆ Metric.ball (0 : Vec d) R :=
  cube_subset_ball_zero (by linarith)

/-- At the selected scale the ball is contained in the next cube. -/
theorem ball_subset_cube_succ {m : ℤ} {R : ℝ}
    (h : 2 * R < (3 : ℝ) ^ (m + 1)) :
    Metric.ball (0 : Vec d) R ⊆ cube d (m + 1) :=
  ball_zero_subset_cube (by linarith)

/-! ### Volumes -/

/-- The real volume of a centered paper cube. -/
theorem volume_cube_toReal (d : ℕ) (m : ℤ) :
    (volume (cube d m)).toReal = ((3 : ℝ) ^ m) ^ d := by
  rw [cube, Homogenization.volume_openCubeSet_toReal,
    Homogenization.cubeVolume_eq_pow_scale]
  rfl

/-- Cube volumes are finite. -/
theorem volume_cube_ne_top (d : ℕ) (m : ℤ) : volume (cube d m) ≠ ⊤ :=
  (Homogenization.volume_openCubeSet_lt_top _).ne

/-- Cube volumes are positive. -/
theorem volume_cube_toReal_pos (d : ℕ) (m : ℤ) :
    0 < (volume (cube d m)).toReal := by
  rw [volume_cube_toReal]
  positivity

/-- The volume of the ball at the selected scale is at most `3^d` times that of
the cube.  The ball's volume is never computed: it is squeezed by the two
cube inclusions. -/
theorem volume_ball_toReal_le {m : ℤ} {R : ℝ}
    (hupper : 2 * R < (3 : ℝ) ^ (m + 1)) :
    (volume (Metric.ball (0 : Vec d) R)).toReal ≤
      (3 : ℝ) ^ d * (volume (cube d m)).toReal := by
  have hsub : Metric.ball (0 : Vec d) R ⊆ cube d (m + 1) :=
    ball_subset_cube_succ hupper
  have hmono : (volume (Metric.ball (0 : Vec d) R)).toReal ≤
      (volume (cube d (m + 1))).toReal :=
    ENNReal.toReal_mono (volume_cube_ne_top d (m + 1)) (measure_mono hsub)
  refine hmono.trans (le_of_eq ?_)
  rw [volume_cube_toReal, volume_cube_toReal, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
    zpow_one, mul_pow]
  ring

/-- The ball at the selected scale has positive volume. -/
theorem volume_ball_toReal_pos {m : ℤ} {R : ℝ} (hlower : (3 : ℝ) ^ m ≤ 2 * R) :
    0 < (volume (Metric.ball (0 : Vec d) R)).toReal := by
  have hsub : cube d m ⊆ Metric.ball (0 : Vec d) R := cube_subset_ball_of_le hlower
  have hball : volume (cube d m) ≤ volume (Metric.ball (0 : Vec d) R) :=
    measure_mono hsub
  have hfin : volume (Metric.ball (0 : Vec d) R) ≠ ⊤ :=
    (Metric.isBounded_ball).measure_lt_top.ne
  have := ENNReal.toReal_mono hfin hball
  exact lt_of_lt_of_le (volume_cube_toReal_pos d m) this

/-! ### The transfer from the ball to the cube -/

/-- **The transfer.**  At the selected scale, the
centered seminorm on `𝔠_m` is controlled by the infimum over constants on
`B_R`, with the explicit dimensional constant `3^{d/2}`.

Combining `Section6Iteration.normalizedL2On_le_of_subset` on `𝔠_m ⊆ B_R` with
the minimizing property of the window average
(`sInf_normalizedL2On_sub_const`), this is exactly the step that lets the
Liouville hypothesis, stated on balls, be fed into
`e.large.scale.Holder.multifractal`, stated on cubes. -/
theorem normalizedL2On_cube_le_of_scale {m : ℤ} {R : ℝ} {u : Vec d → ℝ} {c : ℝ}
    (hlower : (3 : ℝ) ^ m ≤ 2 * R) (hupper : 2 * R < (3 : ℝ) ^ (m + 1))
    (hint : IntegrableOn (fun x ↦ (u x - c) ^ 2) (Metric.ball (0 : Vec d) R)) :
    normalizedL2On (cube d m) (fun x ↦ u x - c) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        normalizedL2On (Metric.ball (0 : Vec d) R) (fun x ↦ u x - c) := by
  have hsub : cube d m ⊆ Metric.ball (0 : Vec d) R := cube_subset_ball_of_le hlower
  have hBpos : 0 < (volume (Metric.ball (0 : Vec d) R)).toReal :=
    volume_ball_toReal_pos hlower
  have hCpos : 0 < (volume (cube d m)).toReal := volume_cube_toReal_pos d m
  have hstep := normalizedL2On_le_of_subset (f := fun x ↦ u x - c)
    hsub hBpos hCpos hint
  refine hstep.trans (mul_le_mul_of_nonneg_right ?_ (normalizedL2On_nonneg _ _))
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_iff₀ hCpos]
  exact volume_ball_toReal_le hupper

/-- The centered form: the window average on `𝔠_m` is controlled by *any*
constant on `B_R`, hence by the infimum the Liouville hypothesis uses. -/
theorem normalizedL2On_cube_sub_averageOn_le_of_scale {m : ℤ} {R : ℝ}
    {u : Vec d → ℝ} {c : ℝ}
    (hlower : (3 : ℝ) ^ m ≤ 2 * R) (hupper : 2 * R < (3 : ℝ) ^ (m + 1))
    (huInt : IntegrableOn u (cube d m))
    (huSq : IntegrableOn (fun x ↦ u x ^ 2) (cube d m))
    (hint : IntegrableOn (fun x ↦ (u x - c) ^ 2) (Metric.ball (0 : Vec d) R)) :
    normalizedL2On (cube d m) (fun x ↦ u x - averageOn (cube d m) u) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        normalizedL2On (Metric.ball (0 : Vec d) R) (fun x ↦ u x - c) := by
  refine le_trans ?_ (normalizedL2On_cube_le_of_scale hlower hupper hint)
  exact normalizedL2On_sub_averageOn_le c (volume_cube_toReal_pos d m)
    (volume_cube_ne_top d m) huInt huSq

/-! ### The `sInf` form consumed by the Liouville argument -/

/-- The set of constant-shifted seminorms on the ball is nonempty. -/
theorem nonempty_sub_const_set (R : ℝ) (u : Vec d → ℝ) :
    {r : ℝ | ∃ c : ℝ,
      r = normalizedL2On (Metric.ball (0 : Vec d) R) (fun x ↦ u x - c)}.Nonempty :=
  ⟨_, 0, rfl⟩

/-- **The S8 transfer in `sInf` form.**  At the selected scale, the centered
seminorm on `𝔠_m` is bounded by `3^{d/2}` times the infimum over constants on
`B_R` -- which is literally the quantity appearing in the Liouville
hypothesis `e.multifractal.Liouville.power.growth`. -/
theorem normalizedL2On_cube_le_sInf_ball {m : ℤ} {R : ℝ} {u : Vec d → ℝ}
    (hlower : (3 : ℝ) ^ m ≤ 2 * R) (hupper : 2 * R < (3 : ℝ) ^ (m + 1))
    (huInt : IntegrableOn u (cube d m))
    (huSq : IntegrableOn (fun x ↦ u x ^ 2) (cube d m))
    (hint : ∀ c : ℝ,
      IntegrableOn (fun x ↦ (u x - c) ^ 2) (Metric.ball (0 : Vec d) R)) :
    normalizedL2On (cube d m) (fun x ↦ u x - averageOn (cube d m) u) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        sInf {r : ℝ | ∃ c : ℝ,
          r = normalizedL2On (Metric.ball (0 : Vec d) R) (fun x ↦ u x - c)} := by
  have hpos : (0 : ℝ) < Real.sqrt ((3 : ℝ) ^ d) := by
    refine Real.sqrt_pos.2 ?_
    positivity
  rw [← div_le_iff₀' hpos]
  refine le_csInf (nonempty_sub_const_set R u) ?_
  rintro r ⟨c, rfl⟩
  rw [div_le_iff₀' hpos]
  exact normalizedL2On_cube_sub_averageOn_le_of_scale hlower hupper huInt huSq
    (hint c)

/-! ### The commensurability factor -/

/-- **The commensurability `3^m ≃ R`  in the form the
scaling factor needs.**  At the selected scale `2R/3 < 3^m`, so for a positive
exponent the scale factor `(3^m)^{-γ}` is comparable to `R^{-γ}` with the
explicit dimensional-free constant `(3/2)^γ`. -/
theorem rpow_neg_scale_le {m : ℤ} {R : ℝ} {gamma : ℝ} (hgamma : 0 < gamma)
    (hR : 0 < R) (hupper : 2 * R < (3 : ℝ) ^ (m + 1)) :
    ((3 : ℝ) ^ m) ^ (-gamma) ≤ ((3 : ℝ) / 2) ^ gamma * R ^ (-gamma) := by
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hkey : 2 / 3 * R < (3 : ℝ) ^ m := by
    have h : (3 : ℝ) ^ (m + 1) = 3 * (3 : ℝ) ^ m := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]; ring
    rw [h] at hupper; linarith
  have hbase : (0 : ℝ) < 2 / 3 * R := by positivity
  -- `x ↦ x ^ (-γ)` is antitone on the positives.
  have hanti : ((3 : ℝ) ^ m) ^ (-gamma) ≤ (2 / 3 * R) ^ (-gamma) :=
    Real.rpow_le_rpow_of_nonpos hbase hkey.le (by linarith)
  refine hanti.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by norm_num) hR.le,
    show ((2 : ℝ) / 3) ^ (-gamma) = ((3 : ℝ) / 2) ^ gamma by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2 / 3),
        show ((3 : ℝ) / 2) = ((2 : ℝ) / 3)⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2 / 3)]]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
