import SubdiffusiveProcess.Lane3.Subdivision
import Mathlib.Tactic

/-!
# The shifted-root triadic covering catalogue

Builds the concrete "shifted-root" grid catalogue consumed as the `hGridCover` binder by
`candidate_good_event`, `lem_goodext`, `lem_affine`, and other K4 consumers: for every point `x`
within the cell of side `3^{-k}` centred at `z`, and every radius `ρ` up to that side, some
triadic descendant of the tripled root centred at `z` shifted per coordinate by
`rootSide • shiftedRootShift d t` for a label `t : Fin d → Fin 3` has a ball of side at most `9ρ`
containing the `ρ/2`-ball around `x`.

This file is pure deterministic geometry (Mathlib only): it does not use or assert any
probabilistic or PDE content of the paper. `shifted_root_grid_cover` always witnesses its
existential root-factor `e` by `e = 1` (the tripled root); the `e = 0` slot exists only to match
the shape `hGridCover` expects of its callers and is never exercised by this construction.
-/

open Set
noncomputable section
namespace SubdiffusiveProcess
namespace Lane3

/-- The finite shift catalogue `{-1/2, 0, 1/2}^d` (label `t i ∈ Fin 3` ↦ `(t i - 1)/2`). -/
def shiftedRootShift (d : ℕ) (t : Fin d → Fin 3) : SpatialCoordinates d :=
  fun i => (((t i : ℕ) : ℝ) - 1) / 2




/-- The balanced-ternary digit of `n` in `{-1,0,1}`. -/
def balDigit (n : ℤ) : ℤ := (n + 1) % 3 - 1

/-- The balanced-ternary quotient of `n`. -/
def balQuot (n : ℤ) : ℤ := (n + 1) / 3

/-- The balanced-ternary digit always lies in `{-1, 0, 1}`. -/
theorem balDigit_mem (n : ℤ) :
    balDigit n = -1 ∨ balDigit n = 0 ∨ balDigit n = 1 := by
  unfold balDigit; omega

/-- The balanced-ternary quotient and digit reconstruct `n`. -/
theorem balDecomp (n : ℤ) : n = 3 * balQuot n + balDigit n := by
  unfold balQuot balDigit; omega

/-- The balanced-ternary quotient shrinks the representable range by a factor of `3`. -/
theorem balQuot_bound (n h : ℤ) (hn : |n| ≤ 3 * h + 1) : |balQuot n| ≤ h := by
  unfold balQuot
  rw [abs_le] at hn ⊢
  omega

/-- The digit, packaged as a `Fin 3` matching the odd-grid convention
`(k.val : ℤ) - 1`. -/
def balDigitFin (n : ℤ) : Fin 3 :=
  ⟨(balDigit n + 1).toNat, by
    have h := balDigit_mem n
    omega⟩

theorem balDigitFin_eq (n : ℤ) :
    ((balDigitFin n).val : ℤ) - 1 = balDigit n := by
  unfold balDigitFin
  have h := balDigit_mem n
  simp only
  omega

variable {d : ℕ}

/-- Every point of the depth-`D` triadic tree rooted at `(c, S)` with integer
label `N` (coordinatewise, within the representable range) is realized by an
explicit descendant word: the balanced-ternary expansion of `N`. -/
theorem exists_descendant_word_of_offsets (c : SpatialCoordinates d) (S : ℝ) :
    ∀ (D : ℕ) (N : Fin d → ℤ), (∀ i, |N i| ≤ (subdivisionHalfWidth D : ℤ)) →
      ∃ w : Fin D → OddGridIndex d 1,
        ∀ i, descendantCenter 1 c S D w i = c i + S * (N i : ℝ) / 3 ^ D := by
  intro D
  induction D with
  | zero =>
    intro N hN
    refine ⟨finZeroElim, fun i => ?_⟩
    have hsh0 : subdivisionHalfWidth 0 = 0 := by
      unfold subdivisionHalfWidth; norm_num
    have hN0 : N i = 0 := by
      have := hN i
      rw [hsh0] at this
      simpa using this
    simp [descendantCenter, hN0]
  | succ D ih =>
    intro N hN
    set digit : Fin d → Fin 3 := fun i => balDigitFin (N i) with hdigit
    set q : Fin d → ℤ := fun i => balQuot (N i) with hq
    have hqb : ∀ i, |q i| ≤ (subdivisionHalfWidth D : ℤ) := by
      intro i
      have hbound : (subdivisionHalfWidth (D + 1) : ℤ) =
          3 * (subdivisionHalfWidth D : ℤ) + 1 := by
        have h1 := two_mul_subdivisionHalfWidth_add_one D
        have h2 := two_mul_subdivisionHalfWidth_add_one (D + 1)
        have h3 : (3 : ℕ) ^ (D + 1) = 3 * 3 ^ D := by rw [pow_succ]; ring
        zify at h1 h2 h3 ⊢
        omega
      have hNi := hN i
      rw [hbound] at hNi
      exact balQuot_bound (N i) (subdivisionHalfWidth D : ℤ) hNi
    obtain ⟨w', hw'⟩ := ih q hqb
    refine ⟨Fin.snoc w' digit, fun i => ?_⟩
    simp only [descendantCenter]
    have hcomp : (fun j : Fin D => (Fin.snoc w' digit : Fin (D+1) → OddGridIndex d 1) j.castSucc) = w' := by
      funext j; simp
    rw [hcomp, Fin.snoc_last]
    unfold oddGridCenter
    rw [hw' i]
    have hside : descendantSide 1 D S = S / 3 ^ D := by
      unfold descendantSide; norm_num
    rw [hside]
    have hdigit_i : digit i = balDigitFin (N i) := by rw [hdigit]
    have hdig : ((digit i).val : ℝ) - (1 : ℕ) = (balDigit (N i) : ℝ) := by
      rw [hdigit_i]
      have h := balDigitFin_eq (N i)
      exact_mod_cast h
    rw [hdig]
    have hq_i : q i = balQuot (N i) := by rw [hq]
    have h3D : (0:ℝ) < (3:ℝ) ^ D := by positivity
    have hdecomp : (N i : ℝ) = 3 * (q i : ℝ) + (balDigit (N i) : ℝ) := by
      rw [hq_i]
      exact_mod_cast balDecomp (N i)
    rw [pow_succ, hdecomp]
    ring

/-! ### The two-grid (nearest half-integer) trick -/



theorem nearest_half_integer_split (p : ℝ) :
    (∃ N0 : ℤ, |p - (N0 : ℝ)| ≤ 1 / 4) ∨ (∃ N1 : ℤ, |(p - 1 / 2) - (N1 : ℝ)| ≤ 1 / 4) := by
  have hMb : |2 * p - (round (2 * p) : ℝ)| ≤ 1 / 2 := abs_sub_round (2 * p)
  rcases Int.even_or_odd (round (2 * p)) with he | ho
  · obtain ⟨k, hk⟩ := he
    left
    refine ⟨k, ?_⟩
    have : (round (2 * p) : ℝ) = (k : ℝ) + (k : ℝ) := by exact_mod_cast hk
    rw [this] at hMb
    rw [abs_le] at hMb ⊢
    constructor <;> linarith [hMb.1, hMb.2]
  · obtain ⟨k, hk⟩ := ho
    right
    refine ⟨k, ?_⟩
    have : (round (2 * p) : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
    rw [this] at hMb
    rw [abs_le] at hMb ⊢
    constructor <;> linarith [hMb.1, hMb.2]

/-- The same split, rescaled to a lattice of spacing `s`: every real is within
`s/4` of a multiple of `s`, or within `s/4` of a shifted-by-`s/2` multiple of `s`. -/
theorem scale_split (s p : ℝ) (hs : 0 < s) :
    (∃ N0 : ℤ, |p - s * (N0 : ℝ)| ≤ s / 4) ∨ (∃ N1 : ℤ, |p - s / 2 - s * (N1 : ℝ)| ≤ s / 4) := by
  rcases nearest_half_integer_split (p / s) with ⟨N0, h0⟩ | ⟨N1, h1⟩
  · left
    refine ⟨N0, ?_⟩
    have heq : p - s * (N0 : ℝ) = s * (p / s - (N0 : ℝ)) := by field_simp
    rw [heq, abs_mul, abs_of_pos hs]
    calc s * |p / s - (N0 : ℝ)| ≤ s * (1 / 4) := mul_le_mul_of_nonneg_left h0 hs.le
      _ = s / 4 := by ring
  · right
    refine ⟨N1, ?_⟩
    have heq : p - s / 2 - s * (N1 : ℝ) = s * (p / s - 1 / 2 - (N1 : ℝ)) := by field_simp
    rw [heq, abs_mul, abs_of_pos hs]
    calc s * |p / s - 1 / 2 - (N1 : ℝ)| ≤ s * (1 / 4) := mul_le_mul_of_nonneg_left h1 hs.le
      _ = s / 4 := by ring

/-! ### Choosing a label and offset per coordinate -/

/-- Given the depth-`D ≥ 1` mesh `s = R / 3^D` of a root of side `R`, every point
within `R / 6` of the root's own center is within `s / 4` of a lattice point of
one of the three shift-`R`-scaled grids (label `0`: shift `-R/2`; label `1`:
no shift; label `2`: shift `+R/2`), at an offset within `subdivisionHalfWidth D`. -/
theorem exists_label_offset (R s : ℝ) (D : ℕ) (hD1 : 1 ≤ D)
    (hRs : R = s * 3 ^ D) (hs : 0 < s) (p : ℝ) (hp : |p| ≤ R / 6) :
    ∃ (t : Fin 3) (N : ℤ), |N| ≤ (subdivisionHalfWidth D : ℤ) ∧
      |p - R * (((t : ℕ) : ℝ) - 1) / 2 - s * (N : ℝ)| ≤ s / 4 := by
  have h3Dnat : 2 * subdivisionHalfWidth D + 1 = 3 ^ D := two_mul_subdivisionHalfWidth_add_one D
  have h3Dreal : 2 * (subdivisionHalfWidth D : ℝ) + 1 = (3 : ℝ) ^ D := by
    exact_mod_cast h3Dnat
  have h3Dge3 : (3 : ℝ) ≤ (3 : ℝ) ^ D := by
    calc (3 : ℝ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ D := pow_le_pow_right₀ (by norm_num) hD1
  have hRhalf : R / 2 = s * (subdivisionHalfWidth D : ℝ) + s / 2 := by
    rw [hRs]; nlinarith [h3Dreal]
  rcases scale_split s p hs with ⟨N0, h0⟩ | ⟨M0, hM0⟩
  · -- unshifted grid: t = 1
    have hb1 : |s * (N0 : ℝ)| ≤ |p| + s / 4 := by
      have hrev := abs_sub_abs_le_abs_sub (s * (N0 : ℝ)) p
      rw [abs_sub_comm (s * (N0 : ℝ)) p] at hrev
      linarith [h0]
    have hbound : |(N0 : ℝ)| ≤ (subdivisionHalfWidth D : ℝ) := by
      rw [abs_mul, abs_of_pos hs] at hb1
      have hb3 : s * |(N0 : ℝ)| ≤ R / 6 + s / 4 := by linarith [hp]
      rw [hRs] at hb3
      nlinarith [hb3, hs, h3Dreal, h3Dge3]
    refine ⟨1, N0, ?_, ?_⟩
    · exact_mod_cast hbound
    · norm_num; exact h0
  · -- shifted grid: t = 0 or t = 2 depending on the sign of M0
    have h5 : |p - s / 2| ≤ |p| + s / 2 := by
      have h := abs_sub_le p 0 (s / 2)
      simp only [sub_zero, zero_sub, abs_neg] at h
      rwa [abs_of_pos (show (0 : ℝ) < s / 2 by linarith)] at h
    have hb1 : |s * (M0 : ℝ)| ≤ |p - s / 2| + s / 4 := by
      have hrev := abs_sub_abs_le_abs_sub (s * (M0 : ℝ)) (p - s / 2)
      rw [abs_sub_comm (s * (M0 : ℝ)) (p - s / 2)] at hrev
      linarith [hM0]
    have hbound : |(M0 : ℝ)| ≤ (3 : ℝ) ^ D / 6 + 3 / 4 := by
      rw [abs_mul, abs_of_pos hs] at hb1
      have hb3 : s * |(M0 : ℝ)| ≤ R / 6 + s / 2 + s / 4 := by linarith [hp, h5]
      rw [hRs] at hb3
      nlinarith [hb3, hs]
    rw [abs_le] at hbound
    obtain ⟨hboundL, hboundU⟩ := hbound
    rcases le_or_gt 0 M0 with hM0nn | hM0neg
    · -- t = 2
      have hMz : (0 : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hM0nn
      have hcast : |(M0 : ℝ) - (subdivisionHalfWidth D : ℝ)| ≤ (subdivisionHalfWidth D : ℝ) := by
        rw [abs_le]
        constructor <;> nlinarith [hboundL, hboundU, h3Dreal, h3Dge3, hMz]
      refine ⟨2, M0 - (subdivisionHalfWidth D : ℤ), ?_, ?_⟩
      · exact_mod_cast hcast
      · norm_num
        convert hM0 using 2
        rw [hRhalf]; ring
    · -- t = 0
      have hMz : (M0 : ℝ) ≤ -1 := by
        have hmi : M0 ≤ -1 := by omega
        exact_mod_cast hmi
      have hcast : |(M0 : ℝ) + (subdivisionHalfWidth D : ℝ) + 1| ≤ (subdivisionHalfWidth D : ℝ) := by
        rw [abs_le]
        constructor <;> nlinarith [hboundL, hboundU, h3Dreal, h3Dge3, hMz]
      refine ⟨0, M0 + (subdivisionHalfWidth D : ℤ) + 1, ?_, ?_⟩
      · exact_mod_cast hcast
      · norm_num
        convert hM0 using 2
        rw [neg_div, hRhalf]; ring

/-! ### Choosing the depth `D` -/

/-- `descendantSide` at multiplicity `m = 1` is division by the power of `3`. -/
theorem descendantSide_one_eq (D : ℕ) (R : ℝ) : descendantSide 1 D R = R / 3 ^ D := by
  unfold descendantSide; norm_num

/-- Given a root side `R ≥ 3 ρ`, there is a depth `D` at which the descendant
mesh `R / 3^D` lies in `[2ρ, 6ρ)`. -/
theorem choose_depth (R rho : ℝ) (hrho : 0 < rho) (hR3 : 3 * rho ≤ R) :
    ∃ D : ℕ, 2 * rho ≤ R / 3 ^ D ∧ R / 3 ^ D < 6 * rho := by
  classical
  have hex : ∃ D : ℕ, R / 3 ^ D < 2 * rho := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / (2 * rho)) (by norm_num : (1 : ℝ) < 3)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ n)]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * rho)] at hn
    linarith [hn]
  set D1 := Nat.find hex with hD1def
  have hD1spec : R / 3 ^ D1 < 2 * rho := Nat.find_spec hex
  have hD1ne0 : D1 ≠ 0 := by
    intro h
    rw [h] at hD1spec
    simp only [pow_zero, div_one] at hD1spec
    linarith
  obtain ⟨D, hD⟩ := Nat.exists_eq_succ_of_ne_zero hD1ne0
  have hDlt : D < D1 := by omega
  have hDnotpred : ¬ (R / 3 ^ D < 2 * rho) := Nat.find_min hex hDlt
  push_neg at hDnotpred
  refine ⟨D, hDnotpred, ?_⟩
  have hstep : R / 3 ^ D1 = (R / 3 ^ D) / 3 := by rw [hD, pow_succ]; ring
  rw [hstep] at hD1spec
  linarith [hD1spec]

/-! ### Assembly -/

/-- Every point of the closed cell of side `3^{-k}` centred at `z`, at every radius up to the
side, is `9`-covered by a triadic descendant of one of the concentric (factor `0`) or tripled
(factor `1`) roots shifted by `rootSide • shiftedRootShift d t`. -/
theorem shifted_root_grid_cover {d : ℕ} (k : ℕ) (z x : SpatialCoordinates d)
    (hx : x ∈ Metric.closedBall z ((3 : ℝ) ^ (-(k : ℤ)) / 2))
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ (3 : ℝ) ^ (-(k : ℤ))) :
    ∃ (e : Fin 2) (t : Fin d → Fin 3) (D : ℕ) (w : Fin D → OddGridIndex d 1),
      Metric.ball x (rho / 2) ⊆
        Metric.ball
          (descendantCenter 1
            (z + (3 : ℝ) ^ (-((k : ℤ) - (e.val : ℤ))) • shiftedRootShift d t)
            ((3 : ℝ) ^ (-((k : ℤ) - (e.val : ℤ)))) D w)
          (descendantSide 1 D ((3 : ℝ) ^ (-((k : ℤ) - (e.val : ℤ)))) / 2) ∧
      descendantSide 1 D ((3 : ℝ) ^ (-((k : ℤ) - (e.val : ℤ)))) ≤ 9 * rho := by
  set q : ℝ := (3 : ℝ) ^ (-(k : ℤ)) with hqdef
  have hq_pos : 0 < q := by rw [hqdef]; positivity
  set R : ℝ := (3 : ℝ) ^ (-((k : ℤ) - 1)) with hRdef
  have hR_pos : 0 < R := by rw [hRdef]; positivity
  have hRq : R = 3 * q := by
    rw [hRdef, hqdef, show -((k : ℤ) - 1) = -(k : ℤ) + 1 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hR3 : 3 * rho ≤ R := by rw [hRq]; linarith [hrho1]
  obtain ⟨D, hDlow, hDhigh⟩ := choose_depth R rho hrho hR3
  set s : ℝ := descendantSide 1 D R with hsdef0
  have hsdef : s = R / 3 ^ D := by rw [hsdef0]; exact descendantSide_one_eq D R
  have hs_pos : 0 < s := by rw [hsdef]; positivity
  have hDlow' : 2 * rho ≤ s := by rw [hsdef]; exact hDlow
  have hDhigh' : s < 6 * rho := by rw [hsdef]; exact hDhigh
  have hRs : R = s * 3 ^ D := by rw [hsdef]; field_simp
  have hp : ∀ i : Fin d, |x i - z i| ≤ R / 6 := by
    intro i
    have hxz : dist x z ≤ q / 2 := by rwa [Metric.mem_closedBall] at hx
    have hxzi : dist (x i) (z i) ≤ q / 2 := (dist_pi_le_iff (by positivity)).mp hxz i
    have hxzi' : |x i - z i| ≤ q / 2 := by rw [← Real.dist_eq]; exact hxzi
    have hq6 : q / 2 = R / 6 := by rw [hRq]; ring
    linarith [hxzi', hq6]
  have hP : ∀ i : Fin d, ∃ (t : Fin 3) (N : ℤ), |N| ≤ (subdivisionHalfWidth D : ℤ) ∧
      |x i - z i - R * (((t : ℕ) : ℝ) - 1) / 2 - s * (N : ℝ)| ≤ s / 4 := by
    intro i
    rcases Nat.eq_zero_or_pos D with hD0 | hD1
    · refine ⟨1, 0, ?_, ?_⟩
      · rw [hD0]; norm_num [subdivisionHalfWidth]
      · have hs0 : s = R := by rw [hsdef, hD0]; norm_num
        norm_num
        rw [hs0]
        linarith [hp i, hR_pos]
    · exact exists_label_offset R s D hD1 hRs hs_pos (x i - z i) (hp i)
  choose t N hNbound hclose using hP
  obtain ⟨w, hw⟩ := exists_descendant_word_of_offsets
    (z + R • shiftedRootShift d t) R D N hNbound
  refine ⟨1, t, D, w, ?_, ?_⟩
  · show Metric.ball x (rho / 2) ⊆
        Metric.ball (descendantCenter 1 (z + R • shiftedRootShift d t) R D w) (descendantSide 1 D R / 2)
    rw [← hsdef0]
    set centre := descendantCenter 1 (z + R • shiftedRootShift d t) R D w with hcentredef
    have hdist_bound : dist x centre ≤ s / 4 := by
      rw [dist_pi_le_iff (by positivity : (0 : ℝ) ≤ s / 4)]
      intro i
      rw [Real.dist_eq]
      have hzi : (z + R • shiftedRootShift d t) i = z i + R * (((t i : ℕ) : ℝ) - 1) / 2 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, shiftedRootShift]
        ring
      have hcentre_i : centre i = z i + R * (((t i : ℕ) : ℝ) - 1) / 2 + R * (N i : ℝ) / 3 ^ D := by
        rw [hw i, hzi]
      rw [hcentre_i]
      have heq2 : R * (N i : ℝ) / 3 ^ D = s * (N i : ℝ) := by rw [hsdef]; ring
      rw [heq2]
      have hgoal_eq : x i - (z i + R * (((t i : ℕ) : ℝ) - 1) / 2 + s * (N i : ℝ))
          = x i - z i - R * (((t i : ℕ) : ℝ) - 1) / 2 - s * (N i : ℝ) := by ring
      rw [hgoal_eq]
      exact hclose i
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    have htri := dist_triangle y x centre
    linarith [hy, hdist_bound, hDlow']
  · show descendantSide 1 D R ≤ 9 * rho
    rw [← hsdef0]
    linarith [hDhigh', hrho]

end Lane3
end SubdiffusiveProcess
