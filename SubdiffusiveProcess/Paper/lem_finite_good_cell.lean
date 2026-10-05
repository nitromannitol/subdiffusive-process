module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Paper.cell_catalogue
public import SubdiffusiveProcess.Paper.good_event
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.in_deterministic
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.lem_band
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.lem_finite_good_cell_uniform
public import SubdiffusiveProcess.Paper.lem_finite_trace_tests
public import SubdiffusiveProcess.Paper.lem_local_normalizations
public import SubdiffusiveProcess.Paper.lem_witness
public import SubdiffusiveProcess.Paper.prop_growth
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.primitive_scores
public import Mathlib.Algebra.BigOperators.Fin
public import SubdiffusiveProcess.Paper.chart_coords_measurable
public import SubdiffusiveProcess.Paper.lem_crossing
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualFMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualPrawMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualRMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldTransport
public import SubdiffusiveProcess.Paper.primitive_scores_finite
public import SubdiffusiveProcess.Paper.lfgc_layer_tail
public import SubdiffusiveProcess.Paper.lfgc_draw_sure
public import SubdiffusiveProcess.Paper.lfgc_draw_carrier
public import SubdiffusiveProcess.Paper.lfgc_family_cover
public import SubdiffusiveProcess.Paper.lfgc_root_stat
public import SubdiffusiveProcess.Paper.lfgc_root_near
public import SubdiffusiveProcess.Paper.lfgc_root_bridge
public import SubdiffusiveProcess.Paper.lfgc_rhs_bridge
public import SubdiffusiveProcess.Paper.lfgc_tail_cover
public import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison
public import SubdiffusiveProcess.Paper.lfgc_clause1_assembly

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper






theorem aux_lem_finite_good_cell_gap_pos (alpha beta : ℝ) (hba : beta < alpha) :
    0 < alpha - beta := by
  linarith



theorem aux_lem_finite_good_cell_choose_trivial_constants :
    ∃ eps cell lam lamDet cdet : ℝ,
      eps ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < cell ∧ cell ≤ 1 / 2 ∧ 0 < lam ∧ lam < lamDet ∧
        lamDet < 1 ∧ 0 < cdet := by
  refine ⟨1/2, 1/2, 1/2, 3/4, 1, ?_, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩
  constructor <;> norm_num

/-- Given any positive gap below `1/2` (the case `gap = alpha - beta` with
`1/2 < beta` and `alpha < 1`, so `gap < 1/2`) and any disorder-absorbing
constant `Cc ≥ 1`, a small disorder discount `sigma ∈ (0,1)` and a matching
correction `tau2 > 0` can be chosen so that `Cc*(sigma+tau2)` stays below
the gap: "choose sigma, then tau2, so that
`C(d,p1)(sigma+tau2) < alpha1-alpha`". Packaging `sigma ∈ Set.Ioo 0 1`
into the conclusion (rather than stating it as a separate consequence of
the witness formula) lets a consumer use this lemma without unfolding the
concrete witness. -/
theorem aux_lem_finite_good_cell_matching_choice (gap Cc : ℝ) (hgap : 0 < gap)
    (hgap1 : gap < 1 / 2) (hCc : 1 ≤ Cc) :
    ∃ sigma tau2 : ℝ,
      sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < tau2 ∧ Cc * (sigma + tau2) < gap := by
  have hCc0 : 0 < Cc := by linarith
  have h4Cc0 : (0 : ℝ) < 4 * Cc := by positivity
  refine ⟨gap / (4 * Cc), gap / (4 * Cc), ⟨by positivity, ?_⟩, by positivity, ?_⟩
  · rw [div_lt_one h4Cc0]
    nlinarith
  · have heq : Cc * (gap / (4 * Cc) + gap / (4 * Cc)) = gap / 2 := by
      field_simp
      ring
    rw [heq]
    linarith



theorem aux_lem_finite_good_cell_choose_parameters
    (alpha beta Cc : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < alpha)
    (halpha : alpha < 1) (hCc : 1 ≤ Cc) :
    ∃ sigma eps cell lam lamDet cdet tau2 : ℝ,
      sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ eps ∈ Set.Ioo (0 : ℝ) 1 ∧
      0 < cell ∧ 0 < lam ∧ lam < lamDet ∧ lamDet < 1 ∧ 0 < cdet ∧
      0 < tau2 ∧ Cc * (sigma + tau2) < alpha - beta := by
  have hgap : 0 < alpha - beta := aux_lem_finite_good_cell_gap_pos alpha beta hba
  have hgap1 : alpha - beta < 1 / 2 := by linarith
  obtain ⟨sigma, tau2, hsig_mem, htau_pos, hmatch⟩ :=
    aux_lem_finite_good_cell_matching_choice (alpha - beta) Cc hgap hgap1 hCc
  obtain ⟨eps, cell, lam, lamDet, cdet, heps_mem, hcell, _hcellSmall, hlam, hlamlt, hlamDet1,
      hcdet⟩ := aux_lem_finite_good_cell_choose_trivial_constants
  exact ⟨sigma, eps, cell, lam, lamDet, cdet, tau2, hsig_mem, heps_mem, hcell, hlam, hlamlt,
    hlamDet1, hcdet, htau_pos, hmatch⟩








theorem aux_lem_finite_good_cell_L_gt_one (H1 : ℕ) (hH1 : 0 < H1) :
    (1 : ℝ) < (3 : ℝ) ^ H1 := by
  exact (one_lt_pow_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 3) hH1.ne').mpr (by norm_num)

/-- The exact real identity linking `mgrid = subdivisionHalfWidth H1` to
`L = 3^H1`, the cast of `SubdiffusiveProcess.ResponseMoments.two_mul_subdivisionHalfWidth_add_one` to `ℝ`.
`oddGridCenter`'s defining `2*m+1` division is literally `L` once `m` is
`mgrid`. -/
theorem aux_lem_finite_good_cell_mgrid_cast (H1 : ℕ) :
    2 * ((subdivisionHalfWidth H1 : ℕ) : ℝ) + 1 = (3 : ℝ) ^ H1 := by
  exact_mod_cast two_mul_subdivisionHalfWidth_add_one H1



theorem aux_lem_finite_good_cell_descendantSide_le (D : ℕ) (X : ℝ) (hX : 0 ≤ X) :
    descendantSide 1 D X ≤ X := by
  unfold descendantSide
  have hbase : (2 * ((1 : ℕ) : ℝ) + 1) = (3 : ℝ) := by norm_num
  rw [hbase]
  exact div_le_self hX (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))



theorem aux_lem_finite_good_cell_L_mgrid_facts (H1 : ℕ) (hH1 : 0 < H1) :
    let L : ℝ := (3 : ℝ) ^ H1
    let mgrid := subdivisionHalfWidth H1
    1 < L ∧ 2 * (mgrid : ℝ) + 1 = L ∧
      ∀ (D : ℕ) (X : ℝ), 0 ≤ X → descendantSide 1 D X ≤ X := by
  intro L mgrid
  refine ⟨aux_lem_finite_good_cell_L_gt_one H1 hH1, ?_, ?_⟩
  · exact aux_lem_finite_good_cell_mgrid_cast H1
  · intro D X hX
    exact aux_lem_finite_good_cell_descendantSide_le D X hX






/-- `alpha1 := (alpha+1)/2` lies strictly between `alpha` and `1` whenever
`alpha < 1`: the paper's "a strictly larger exponent alpha1 ∈ (alpha,1)". -/
theorem aux_lem_finite_good_cell_exists_alpha1 (alpha : ℝ) (halpha : alpha < 1) :
    ∃ alpha1 : ℝ, alpha1 ∈ Set.Ioo alpha 1 := by
  refine ⟨(alpha + 1) / 2, ?_, ?_⟩
  · linarith
  · linarith

/-- A Morrey/Sobolev exponent `p1 > 0` with `1-d/p1>alpha1` can always be
found once `alpha1 < 1`: the paper's "Choose p1 with 1-d/p1>alpha1". -/
theorem aux_lem_finite_good_cell_exists_p1 (d : ℕ) (hd : 2 ≤ d) (alpha1 : ℝ)
    (h1 : alpha1 < 1) :
    ∃ p1 : ℝ, 0 < p1 ∧ alpha1 < 1 - (d : ℝ) / p1 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (by omega : 0 < d)
  have h1a : (0 : ℝ) < 1 - alpha1 := by linarith
  refine ⟨2 * (d : ℝ) / (1 - alpha1), by positivity, ?_⟩
  have hsimp : (d : ℝ) / (2 * (d : ℝ) / (1 - alpha1)) = (1 - alpha1) / 2 := by
    field_simp
  rw [hsimp]
  linarith

/-- Both matching powers  (the energy power `alpha1-alpha`
and the source power `2-alpha`) are positive once `alpha1 ∈ (alpha,1)` and
`alpha<1`: the paper's "Both powers remain positive." -/
theorem aux_lem_finite_good_cell_powers_pos (alpha alpha1 : ℝ) (hlt : alpha < alpha1)
    (halpha : alpha < 1) :
    0 < alpha1 - alpha ∧ 0 < 2 - alpha := by
  constructor
  · linarith
  · linarith



theorem aux_lem_finite_good_cell_choose_exponents (d : ℕ) (hd : 2 ≤ d) (alpha beta : ℝ)
    (_hba : beta < alpha) (halpha : alpha < 1) :
    ∃ alpha1 p1 : ℝ, alpha1 ∈ Set.Ioo alpha 1 ∧ 0 < p1 ∧ alpha1 < 1 - (d : ℝ) / p1 ∧
      0 < alpha1 - alpha ∧ 0 < 2 - alpha := by
  obtain ⟨alpha1, halpha1⟩ := aux_lem_finite_good_cell_exists_alpha1 alpha halpha
  obtain ⟨p1, hp1pos, hp1⟩ := aux_lem_finite_good_cell_exists_p1 d hd alpha1 halpha1.2
  obtain ⟨hpow1, hpow2⟩ := aux_lem_finite_good_cell_powers_pos alpha alpha1 halpha1.1 halpha
  exact ⟨alpha1, p1, halpha1, hp1pos, hp1, hpow1, hpow2⟩








theorem aux_lem_finite_good_cell_pad_exists (L : ℝ) (hL1 : 1 < L) (D : ℕ)
    (hD : 1 < (3 : ℝ) ^ D) :
    ∃ pad : ℝ, 1 < pad ∧ pad < L ∧ pad ≤ (3 : ℝ) ^ D := by
  refine ⟨(1 + min L ((3 : ℝ) ^ D)) / 2, ?_, ?_, ?_⟩
  · have hmin := lt_min hL1 hD; linarith
  · have hminL := min_le_left L ((3 : ℝ) ^ D); have hmin := lt_min hL1 hD; linarith
  · have hminR := min_le_right L ((3 : ℝ) ^ D); have hmin := lt_min hL1 hD; linarith



theorem aux_lem_finite_good_cell_trivial_positive_constants :
    ∃ delta0 Cfin Aext : ℝ, 0 < delta0 ∧ 0 < Cfin ∧ 0 < Aext := by
  exact ⟨1, 1, 1, by norm_num, by norm_num, by norm_num⟩

/-- `(3:ℝ)^D > 1` for any positive depth `D` (the padding depth
`enDepth padRoot`, analogous to
`aux_lem_finite_good_cell_L_gt_one` for the unrelated subdivision exponent
`H1`): needed to discharge `aux_lem_finite_good_cell_pad_exists`'s `hD`
hypothesis once a positive padding depth has been fixed. -/
theorem aux_lem_finite_good_cell_pad_depth_pos (D : ℕ) (hD0 : 0 < D) :
    (1 : ℝ) < (3 : ℝ) ^ D := by
  exact (one_lt_pow_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) hD0.ne').mpr (by norm_num)



theorem aux_lem_finite_good_cell_choose_second_block (L : ℝ) (hL1 : 1 < L) (D : ℕ)
    (hD0 : 0 < D) :
    ∃ delta0 Cfin Aext pad : ℝ, 0 < delta0 ∧ 0 < Cfin ∧ 0 < Aext ∧
      ∃ _hpad : 1 < pad, pad < L ∧ pad ≤ (3 : ℝ) ^ D := by
  obtain ⟨delta0, Cfin, Aext, hd, hc, ha⟩ := aux_lem_finite_good_cell_trivial_positive_constants
  have hD : 1 < (3 : ℝ) ^ D := aux_lem_finite_good_cell_pad_depth_pos D hD0
  obtain ⟨pad, hpad1, hpadL, hpadD⟩ := aux_lem_finite_good_cell_pad_exists L hL1 D hD
  exact ⟨delta0, Cfin, Aext, pad, hd, hc, ha, hpad1, hpadL, hpadD⟩

/-! ### Balanced-ternary digit extraction (peels one digit via division by 3). -/

def aux_lem_finite_good_cell_balDigit (n : ℤ) : ℤ := (n + 1) % 3 - 1
def aux_lem_finite_good_cell_balQuot (n : ℤ) : ℤ := (n + 1) / 3

theorem aux_lem_finite_good_cell_balDigit_mem (n : ℤ) :
    aux_lem_finite_good_cell_balDigit n = -1 ∨ aux_lem_finite_good_cell_balDigit n = 0 ∨
      aux_lem_finite_good_cell_balDigit n = 1 := by
  unfold aux_lem_finite_good_cell_balDigit; omega

theorem aux_lem_finite_good_cell_balDecomp (n : ℤ) :
    n = 3 * aux_lem_finite_good_cell_balQuot n + aux_lem_finite_good_cell_balDigit n := by
  unfold aux_lem_finite_good_cell_balQuot aux_lem_finite_good_cell_balDigit; omega

theorem aux_lem_finite_good_cell_balQuot_bound (n h : ℤ) (hn : |n| ≤ 3 * h + 1) :
    |aux_lem_finite_good_cell_balQuot n| ≤ h := by
  unfold aux_lem_finite_good_cell_balQuot
  rw [abs_le] at hn ⊢
  omega

/-- The digit, packaged as a `Fin 3` matching the odd-grid convention
`(k.val : ℤ) - 1`. -/
def aux_lem_finite_good_cell_balDigitFin (n : ℤ) : Fin 3 :=
  ⟨(aux_lem_finite_good_cell_balDigit n + 1).toNat, by
    have h := aux_lem_finite_good_cell_balDigit_mem n
    omega⟩

theorem aux_lem_finite_good_cell_balDigitFin_eq (n : ℤ) :
    ((aux_lem_finite_good_cell_balDigitFin n).val : ℤ) - 1 =
      aux_lem_finite_good_cell_balDigit n := by
  unfold aux_lem_finite_good_cell_balDigitFin
  have h := aux_lem_finite_good_cell_balDigit_mem n
  simp only
  omega

variable {d : ℕ}

/-- Every point of the depth-`D` triadic tree rooted at `(c, S)` with integer
label `N` (coordinatewise, within the representable range) is realized by an
explicit descendant word: the balanced-ternary expansion of `N`, built one
digit at a time via `aux_lem_finite_good_cell_balQuot`/`balDigit`. -/
theorem aux_lem_finite_good_cell_descendant_exists (c : SpatialCoordinates d) (S : ℝ) :
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
    set digit : Fin d → Fin 3 := fun i => aux_lem_finite_good_cell_balDigitFin (N i) with hdigit
    set q : Fin d → ℤ := fun i => aux_lem_finite_good_cell_balQuot (N i) with hq
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
      exact aux_lem_finite_good_cell_balQuot_bound (N i) (subdivisionHalfWidth D : ℤ) hNi
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
    have hdigit_i : digit i = aux_lem_finite_good_cell_balDigitFin (N i) := by rw [hdigit]
    have hdig : ((digit i).val : ℝ) - (1 : ℕ) = (aux_lem_finite_good_cell_balDigit (N i) : ℝ) := by
      rw [hdigit_i]
      have h := aux_lem_finite_good_cell_balDigitFin_eq (N i)
      exact_mod_cast h
    rw [hdig]
    have hq_i : q i = aux_lem_finite_good_cell_balQuot (N i) := by rw [hq]
    have h3D : (0:ℝ) < (3:ℝ) ^ D := by positivity
    have hdecomp : (N i : ℝ) = 3 * (q i : ℝ) + (aux_lem_finite_good_cell_balDigit (N i) : ℝ) := by
      rw [hq_i]
      exact_mod_cast aux_lem_finite_good_cell_balDecomp (N i)
    rw [pow_succ, hdecomp]
    ring

/-! ### The two-grid (adjacent systems) trick, avoiding boundary alignment. -/

theorem aux_lem_finite_good_cell_two_grid_split (p : ℝ) :
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

theorem aux_lem_finite_good_cell_subdivisionHalfWidth_real (n : ℕ) :
    (subdivisionHalfWidth n : ℝ) = ((3:ℝ) ^ n - 1) / 2 := by
  have h := two_mul_subdivisionHalfWidth_add_one n
  have h2 : ((2 * subdivisionHalfWidth n + 1 : ℕ) : ℝ) = ((3 ^ n : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h2
  linarith

/-- Per-coordinate two-grid covering: a point of the reference cube is either
close to a lattice point of the unshifted depth-`D'+1` grid rooted at `0`, or
close to a lattice point of the same-size grid rooted at `27/6` (shift chosen
so that the two grids' fine-scale phases are exactly complementary, since
`3^D'` is odd for every `D'`). -/
theorem aux_lem_finite_good_cell_per_coord (x : ℝ) (hx : |x| ≤ 1 / 2) (D' : ℕ) :
    (∃ N0 : ℤ, |N0| ≤ (subdivisionHalfWidth (D' + 1) : ℤ) ∧
        |x - 27 * (N0 : ℝ) / 3 ^ (D' + 1)| ≤ (27 / 3 ^ (D' + 1)) / 4) ∨
    (∃ N1 : ℤ, |N1| ≤ (subdivisionHalfWidth (D' + 1) : ℤ) ∧
        |x - (9 / 2 + 27 * (N1 : ℝ) / 3 ^ (D' + 1))| ≤ (27 / 3 ^ (D' + 1)) / 4) := by
  have h3D' : (0:ℝ) < (3:ℝ) ^ D' := by positivity
  have h3D'1 : (0:ℝ) < (3:ℝ) ^ (D' + 1) := by positivity
  have hpowsucc : (3:ℝ) ^ (D' + 1) = 3 * 3 ^ D' := by rw [pow_succ]; ring
  have hSHWD' : (subdivisionHalfWidth D' : ℝ) = ((3:ℝ) ^ D' - 1) / 2 :=
    aux_lem_finite_good_cell_subdivisionHalfWidth_real D'
  have hSHWD'1 : (subdivisionHalfWidth (D' + 1) : ℝ) = ((3:ℝ) ^ (D' + 1) - 1) / 2 :=
    aux_lem_finite_good_cell_subdivisionHalfWidth_real (D' + 1)
  have hxle := hx
  rw [abs_le] at hxle
  have h2 : (0:ℝ) < 27 / 3 ^ (D'+1) := by positivity
  have hnorm : |(27:ℝ) / 3 ^ (D'+1)| = 27 / 3 ^ (D'+1) := abs_of_pos h2
  rcases aux_lem_finite_good_cell_two_grid_split (x * 3 ^ (D' + 1) / 27) with
    ⟨N0, hN0⟩ | ⟨N1, hN1⟩
  · left
    refine ⟨N0, ?_, ?_⟩
    · have hN0' := hN0
      rw [abs_le] at hN0'
      rw [abs_le]
      have key : (-((subdivisionHalfWidth (D' + 1):ℤ):ℝ) ≤ (N0:ℝ)) ∧
          ((N0:ℝ) ≤ ((subdivisionHalfWidth (D' + 1):ℤ):ℝ)) := by
        have hcast : ((subdivisionHalfWidth (D' + 1) : ℤ) : ℝ) = (subdivisionHalfWidth (D'+1) : ℝ) := by
          push_cast; ring
        rw [hcast, hSHWD'1]
        constructor <;> nlinarith [hN0'.1, hN0'.2, hxle.1, hxle.2, h3D'1]
      exact_mod_cast key
    · have heq : x - 27 * (N0 : ℝ) / 3 ^ (D' + 1) =
          (27 / 3 ^ (D'+1)) * (x * 3 ^ (D'+1) / 27 - (N0:ℝ)) := by
        field_simp
      rw [heq, abs_mul, hnorm]
      calc 27 / 3 ^ (D'+1) * |x * 3 ^ (D' + 1) / 27 - (N0:ℝ)|
          ≤ 27 / 3 ^ (D'+1) * (1/4) := mul_le_mul_of_nonneg_left hN0 (le_of_lt h2)
        _ = 27 / 3 ^ (D'+1) / 4 := by ring
  · right
    refine ⟨N1 - (subdivisionHalfWidth D' : ℤ), ?_, ?_⟩
    · have hN1' := hN1
      rw [abs_le] at hN1'
      rw [abs_le]
      have hcast : ((N1 - (subdivisionHalfWidth D':ℤ) : ℤ):ℝ) =
          (N1:ℝ) - (subdivisionHalfWidth D' : ℝ) := by push_cast; ring
      have key : (-((subdivisionHalfWidth (D' + 1):ℤ):ℝ) ≤ ((N1 - (subdivisionHalfWidth D':ℤ) : ℤ):ℝ)) ∧
          (((N1 - (subdivisionHalfWidth D':ℤ) : ℤ):ℝ) ≤ ((subdivisionHalfWidth (D' + 1):ℤ):ℝ)) := by
        have hcast2 : ((subdivisionHalfWidth (D' + 1) : ℤ) : ℝ) = (subdivisionHalfWidth (D'+1) : ℝ) := by
          push_cast; ring
        rw [hcast, hcast2, hSHWD'1, hSHWD']
        constructor <;> nlinarith [hN1'.1, hN1'.2, hxle.1, hxle.2, h3D', h3D'1, hpowsucc]
      exact_mod_cast key
    · have heq : x - (9 / 2 + 27 * ((N1 - (subdivisionHalfWidth D':ℤ) : ℤ):ℝ) / 3 ^ (D' + 1)) =
          (27 / 3 ^ (D'+1)) * ((x * 3 ^ (D'+1) / 27 - 1 / 2) - (N1:ℝ)) := by
        have hcast : ((N1 - (subdivisionHalfWidth D':ℤ) : ℤ):ℝ) =
            (N1:ℝ) - (subdivisionHalfWidth D' : ℝ) := by push_cast; ring
        rw [hcast, hSHWD', hpowsucc]
        field_simp
        ring
      rw [heq, abs_mul, hnorm]
      calc 27 / 3 ^ (D'+1) * |x * 3 ^ (D' + 1) / 27 - 1 / 2 - (N1:ℝ)|
          ≤ 27 / 3 ^ (D'+1) * (1/4) := mul_le_mul_of_nonneg_left hN1 (le_of_lt h2)
        _ = 27 / 3 ^ (D'+1) / 4 := by ring

/-- Choose a triadic scale `27/3^D` sandwiched between `2ρ` and `9ρ`. -/
theorem aux_lem_finite_good_cell_choose_D (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ∃ D : ℕ, (27 : ℝ) / 3 ^ D ≤ 9 * rho ∧ 2 * rho ≤ (27 : ℝ) / 3 ^ D := by
  classical
  have hex : ∃ k, (1 / 3 : ℝ) ^ k < rho :=
    exists_pow_lt_of_lt_one hrho (show (1 / 3 : ℝ) < 1 by norm_num)
  set k := Nat.find hex with hkdef
  have hk_spec : (1 / 3 : ℝ) ^ k < rho := Nat.find_spec hex
  refine ⟨k + 1, ?_, ?_⟩
  · have h3k : (0:ℝ) < (3:ℝ) ^ k := by positivity
    rw [pow_succ]
    rw [div_le_iff₀ (by positivity)]
    have heq : (1 / 3 : ℝ) ^ k = 1 / 3 ^ k := by rw [div_pow]; norm_num
    rw [heq] at hk_spec
    rw [div_lt_iff₀ h3k] at hk_spec
    nlinarith [hk_spec]
  · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0]
      norm_num
      linarith
    · have hnot : ¬ (1 / 3 : ℝ) ^ (k - 1) < rho := Nat.find_min hex (by omega)
      push Not at hnot
      have hkeq : k - 1 + 1 = k := by omega
      have hpow : (1 / 3 : ℝ) ^ (k - 1) * (1 / 3) = (1 / 3 : ℝ) ^ k := by
        rw [← pow_succ, hkeq]
      have h3k : (0:ℝ) < (3:ℝ) ^ k := by positivity
      rw [pow_succ]
      rw [le_div_iff₀ (by positivity)]
      have heq2 : (1 / 3 : ℝ) ^ k = 1 / 3 ^ k := by rw [div_pow]; norm_num
      rw [heq2] at hpow
      have hstep : rho * (1 / 3) ≤ 1 / 3 ^ k := by
        rw [← hpow]
        exact mul_le_mul_of_nonneg_right hnot (by norm_num)
      rw [le_div_iff₀ h3k] at hstep
      nlinarith [hstep]

/-- The fixed enlargement schedule: `self` at depth `0` (the reference cell
itself), a fresh `coarse` root at depth `3` (side `27`, generous enough to
contain the reference cell's whole `9ρ`-neighbourhood for every `ρ ≤ 1`
before any shift), and `padRoot` at a FIXED depth `1` (side `3`, unrelated to
the covering, decoupled from `H1` because `in_deterministic`'s own
padded enlargement is a fixed factor-`3` enlargement of the reference cell,
not one that scales with the L-adic parent depth `H1`, so `padRoot`'s depth
must not vary with `H1` either). `H1` remains a parameter of this `def` only
because `self`/`coarse` share its argument position with `padRoot`; it is
otherwise unused by this branch. -/
def aux_lem_finite_good_cell_enDepth (_H1 : ℕ) (e : Fin 3) : ℕ :=
  if e = 0 then 0 else if e = 1 then 3 else 1

/-- The `2^d` translations of the `coarse` root: coordinate `i` is shifted by
`0` or by `1/6` of the root's own side (so the absolute shift is `27/6 = 9/2`),
chosen independently per coordinate via the `Fin d → Fin 2` pattern under
`finFunctionFinEquiv`. The zero pattern is `selfShift`. -/
def aux_lem_finite_good_cell_shift (d : ℕ) : Fin (2 ^ d) → SpatialCoordinates d :=
  fun t i => if (finFunctionFinEquiv.symm t : Fin d → Fin 2) i = 1 then (1 / 6 : ℝ) else 0

theorem aux_lem_finite_good_cell_shift_zero (d : ℕ) :
    aux_lem_finite_good_cell_shift d (finFunctionFinEquiv (fun _ : Fin d => (0 : Fin 2))) = 0 := by
  funext i
  unfold aux_lem_finite_good_cell_shift
  rw [Equiv.symm_apply_apply]
  simp



theorem aux_lem_finite_good_cell_hGridCover (H1 : ℕ) :
    ∀ x : SpatialCoordinates d, x ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2) →
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        ∃ (U : Fin 3 × Fin (2 ^ d)) (D : ℕ) (w : Fin D → OddGridIndex d 1),
          Metric.ball x (rho / 2) ⊆
            Metric.ball (descendantCenter 1
              (((3 : ℝ) ^ aux_lem_finite_good_cell_enDepth H1 U.1) •
                aux_lem_finite_good_cell_shift d U.2)
              ((3 : ℝ) ^ aux_lem_finite_good_cell_enDepth H1 U.1) D w)
              (descendantSide 1 D ((3 : ℝ) ^ aux_lem_finite_good_cell_enDepth H1 U.1) / 2) ∧
          descendantSide 1 D ((3 : ℝ) ^ aux_lem_finite_good_cell_enDepth H1 U.1) ≤ 9 * rho := by
  intro x hx rho hrho hrho1
  have hxi : ∀ i, |x i| ≤ 1 / 2 := by
    intro i
    rw [Metric.mem_closedBall] at hx
    rw [dist_pi_le_iff (by norm_num)] at hx
    have hi := hx i
    rw [Real.dist_eq] at hi
    simpa using hi
  obtain ⟨D, hD1, hD2⟩ := aux_lem_finite_good_cell_choose_D rho hrho hrho1
  have hDne : D ≠ 0 := by
    intro h
    rw [h] at hD1
    norm_num at hD1
    linarith
  obtain ⟨D', hDeq⟩ := Nat.exists_eq_succ_of_ne_zero hDne
  subst hDeq
  simp only [Nat.succ_eq_add_one] at hD1 hD2
  have hchoice : ∀ i : Fin d, ∃ (b : Fin 2) (n : ℤ),
      |n| ≤ (subdivisionHalfWidth (D' + 1) : ℤ) ∧
      |x i - ((if b = 1 then (9 / 2 : ℝ) else 0) + 27 * (n : ℝ) / 3 ^ (D' + 1))| ≤
        (27 / 3 ^ (D' + 1)) / 4 := by
    intro i
    rcases aux_lem_finite_good_cell_per_coord (x i) (hxi i) D' with
      ⟨N0, hN0b, hN0d⟩ | ⟨N1, hN1b, hN1d⟩
    · exact ⟨0, N0, hN0b, by simpa using hN0d⟩
    · exact ⟨1, N1, hN1b, by simpa using hN1d⟩
  choose β N hNb hNd using hchoice
  set c : SpatialCoordinates d := fun i => if β i = 1 then (9 / 2 : ℝ) else 0 with hcdef
  obtain ⟨w, hw⟩ := aux_lem_finite_good_cell_descendant_exists c 27 (D' + 1) N hNb
  have henD : aux_lem_finite_good_cell_enDepth H1 ((1 : Fin 3), finFunctionFinEquiv β).1 = 3 := by
    unfold aux_lem_finite_good_cell_enDepth
    norm_num
  have h27 : (3 : ℝ) ^ (3:ℕ) = 27 := by norm_num
  refine ⟨((1 : Fin 3), finFunctionFinEquiv β), D' + 1, w, ?_, ?_⟩
  · have hcentre : (((3 : ℝ) ^ aux_lem_finite_good_cell_enDepth H1
        ((1 : Fin 3), finFunctionFinEquiv β).1) •
          aux_lem_finite_good_cell_shift d ((1 : Fin 3), finFunctionFinEquiv β).2) = c := by
      rw [henD, h27]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      unfold aux_lem_finite_good_cell_shift
      rw [Equiv.symm_apply_apply]
      rw [hcdef]
      by_cases hbi : β i = 1 <;> simp [hbi] ; norm_num
    rw [hcentre, henD, h27]
    have hdistc : dist x (descendantCenter 1 c 27 (D' + 1) w) ≤ (27 / 3 ^ (D' + 1)) / 4 := by
      rw [dist_pi_le_iff (by positivity)]
      intro i
      rw [Real.dist_eq, hw i]
      exact hNd i
    apply Metric.ball_subset_ball'
    have hside : (27:ℝ) / 3 ^ (D' + 1) = descendantSide 1 (D' + 1) 27 := by
      unfold descendantSide
      norm_num
    rw [hside] at hdistc
    linarith [hdistc, hD2]
  · rw [henD, h27]
    have hside : descendantSide 1 (D' + 1) (27:ℝ) = 27 / 3 ^ (D' + 1) := by
      unfold descendantSide
      norm_num
    rw [hside]
    exact hD1

/-- The `cell_catalogue` instantiation for the repaired three-root catalogue
(`en = 3`: `self` at depth `0`, `coarse` at depth `3`, `padRoot` at depth
`H1`), `nc = 1`, single zero-shift comparison cell: the same construction as
the (correct) degenerate two-root version, with one more enlargement level.
Every clause is either independent of `en`'s size, or (the two enlargement
containment clauses) uses only that `factor e : ℕ` for the non-`self` case,
regardless of its specific value. -/
theorem aux_lem_finite_good_cell_gap_catalogue (d : ℕ) (_hd : 2 ≤ d) (H1 : ℕ) :
    _root_.SubdiffusiveProcess.Paper.cell_catalogue d (Fin 3) (Fin 1)
      (fun k z => Metric.ball z ((3 : ℝ) ^ (-(k : ℤ)) / 2))
      (fun k z e => Metric.ball z
        (((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ (aux_lem_finite_good_cell_enDepth H1 e)) / 2))
      (fun k z (_c : Fin 1) => Metric.ball
        (z + (3 : ℝ) ^ (-(k : ℤ)) • (0 : SpatialCoordinates d))
        (((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ (-(0 : ℤ))) / 2))
      (0 : Fin 3) (fun (_k : ℕ) (_z : SpatialCoordinates d) => (0 : Fin 1)) := by
  classical
  let factor : Fin 3 → ℕ := aux_lem_finite_good_cell_enDepth H1
  let shifts : Finset (SpatialCoordinates d) := {0}
  let roots : ℕ → SpatialCoordinates d → Fin 3 → Finset (SpatialCoordinates d) :=
    fun _ _ _ => ∅
  let Cd : ℝ := 1
  let bigSide : ℕ → Fin 3 → ℝ := fun k e => (3 : ℝ) ^ (-(k : ℝ)) * (3 : ℝ) ^ (factor e)
  let shiftedCentre : ℕ → SpatialCoordinates d → Fin 3 → SpatialCoordinates d →
      SpatialCoordinates d := fun k z e t => z + bigSide k e • t
  let centres : ℕ → SpatialCoordinates d → Fin 3 → ℕ → Finset (SpatialCoordinates d) :=
    fun k z e D =>
      (Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
        (descendantCenter 1 z (bigSide k e) D)
  let catalogue : ℕ → SpatialCoordinates d → Set (Set (SpatialCoordinates d)) := fun k z =>
    {V | ∃ (e : Fin 3) (t : SpatialCoordinates d), t ∈ shifts ∧
      ∃ (D : ℕ) (word : Fin D → OddGridIndex d 1),
        V = Metric.ball
          (descendantCenter 1 (shiftedCentre k z e t) (bigSide k e) D word)
          (descendantSide 1 D (bigSide k e) / 2)}
  refine ⟨1 / 2, 1 / 2, 0, factor, shifts, roots, Cd, centres, catalogue, ?_⟩
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, rfl, ?_, by norm_num, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [shifts]
  · intro k z e; simp [roots, Cd]
  · intro k z; simp [Real.rpow_neg_natCast]
  · intro k z e; simp [factor, Real.rpow_neg_natCast]
  · intro k z c
    refine ⟨⟨(0 : Fin 3), 0, by simp [shifts], 0, (Fin.elim0 ·), ?_⟩, (0 : Fin 3), ?_⟩
    · simp [shiftedCentre, bigSide, factor, aux_lem_finite_good_cell_enDepth, descendantCenter,
        descendantSide, Real.rpow_neg_natCast]
    · simp [aux_lem_finite_good_cell_enDepth]
  · intro k z
    refine ⟨⟨(0 : Fin 3), 0, by simp [shifts], 0, (Fin.elim0 ·), ?_⟩, (0 : Fin 3), ?_⟩
    · simp [shiftedCentre, bigSide, factor, aux_lem_finite_good_cell_enDepth, descendantCenter,
        descendantSide, Real.rpow_neg_natCast]
    · simp [aux_lem_finite_good_cell_enDepth]
  · intro k z V
    rfl
  · intro k z e D w
    simp [centres, roots, bigSide, Finset.mem_image, eq_comm]
  · intro k z e D
    dsimp only [centres, Cd]
    have hcardFin : Fintype.card (Fin D → OddGridIndex d 1) = 3 ^ (d * D) := by
      rw [Fintype.card_pi]
      simp [OddGridIndex, pow_mul]
    have hcard : ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
        (descendantCenter 1 z (bigSide k e) D)).card ≤ 3 ^ (d * D) := by
      refine le_trans Finset.card_image_le ?_
      simpa using hcardFin.le
    have hcardR : (((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
        (descendantCenter 1 z (bigSide k e) D)).card : ℝ) ≤ (3 : ℝ) ^ (d * D) := by
      exact_mod_cast hcard
    have heq : ((3 : ℝ) ^ (d * D) : ℝ) = (3 : ℝ) ^ ((d : ℝ) * (D : ℝ)) := by
      rw [← Real.rpow_natCast (3 : ℝ) (d * D)]
      norm_num
    rw [heq] at hcardR
    have hpos : (0 : ℝ) < (3 : ℝ) ^ ((d : ℝ) * (D : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    nlinarith [hcardR, hpos]
  · intro k z
    simp [aux_lem_finite_good_cell_enDepth]
  · intro k z e
    by_cases he : e = (0 : Fin 3)
    · simp [he, aux_lem_finite_good_cell_enDepth]
    · apply Metric.ball_subset_ball
      have h3fe : (1 : ℝ) ≤ (3 : ℝ) ^ (factor e) := one_le_pow₀ (by norm_num)
      have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
      nlinarith
  · intro k z
    apply Metric.ball_subset_ball
    have hstep : (3 : ℝ) ^ (-((k : ℤ) + 1)) ≤ (3 : ℝ) ^ (-(k : ℤ)) := by
      apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
    have hcast : (-(((k : ℕ) + 1 : ℕ) : ℤ)) = -((k : ℤ) + 1) := by push_cast; ring
    rw [hcast]
    linarith

/--  cardinality bound on
`lem_finite_good_cell`'s actual centre catalogue `centres U D` (root
translates ∪ comparison translates ∪ depth-`D` descendants), for ARBITRARY
translation maps: general fact about `Finset.image`/`Fintype.card`, no
probability content, reusable at any instantiation of `rootMap`/`cmpMap`.
Discharges `good_event`'s cardinality conjunct at `good_char`/`RHS`'s own
`centres` — one of the six deterministic conjuncts `aux_good_event_neg_reduce`
below needs supplied. -/
theorem aux_lem_finite_good_cell_tail_card
    (d en nc ns : ℕ) (D : ℕ)
    (rootMap : Fin en × Fin ns → SpatialCoordinates d)
    (cmpMap : Fin nc → SpatialCoordinates d)
    (descMap : (Fin D → OddGridIndex d 1) → SpatialCoordinates d) :
    (((Finset.univ : Finset (Fin en × Fin ns)).image rootMap ∪
        (Finset.univ : Finset (Fin nc)).image cmpMap ∪
        (Finset.univ : Finset (Fin D → OddGridIndex d 1)).image descMap).card : ℝ) ≤
      ((en * ns + nc + 1 : ℕ) : ℝ) * (3 : ℝ) ^ ((d : ℝ) * (D : ℝ)) := by
  have hcardFin : Fintype.card (Fin D → OddGridIndex d 1) = 3 ^ (d * D) := by
    rw [Fintype.card_pi]; simp [OddGridIndex, pow_mul]
  have h1 : ((Finset.univ : Finset (Fin en × Fin ns)).image rootMap).card ≤ en * ns := by
    calc ((Finset.univ : Finset (Fin en × Fin ns)).image rootMap).card
        ≤ (Finset.univ : Finset (Fin en × Fin ns)).card := Finset.card_image_le
      _ = en * ns := by simp
  have h2 : ((Finset.univ : Finset (Fin nc)).image cmpMap).card ≤ nc := by
    calc ((Finset.univ : Finset (Fin nc)).image cmpMap).card
        ≤ (Finset.univ : Finset (Fin nc)).card := Finset.card_image_le
      _ = nc := by simp
  have h3 : ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image descMap).card ≤
      3 ^ (d * D) := by
    calc ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image descMap).card
        ≤ (Finset.univ : Finset (Fin D → OddGridIndex d 1)).card := Finset.card_image_le
      _ = 3 ^ (d * D) := by rw [Finset.card_univ, hcardFin]
  have hunion : ((Finset.univ : Finset (Fin en × Fin ns)).image rootMap ∪
      (Finset.univ : Finset (Fin nc)).image cmpMap ∪
      (Finset.univ : Finset (Fin D → OddGridIndex d 1)).image descMap).card ≤
      en * ns + nc + 3 ^ (d * D) := by
    calc ((Finset.univ : Finset (Fin en × Fin ns)).image rootMap ∪
        (Finset.univ : Finset (Fin nc)).image cmpMap ∪
        (Finset.univ : Finset (Fin D → OddGridIndex d 1)).image descMap).card
        ≤ ((Finset.univ : Finset (Fin en × Fin ns)).image rootMap ∪
            (Finset.univ : Finset (Fin nc)).image cmpMap).card +
          ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image descMap).card :=
          Finset.card_union_le _ _
      _ ≤ (((Finset.univ : Finset (Fin en × Fin ns)).image rootMap).card +
            ((Finset.univ : Finset (Fin nc)).image cmpMap).card) + 3 ^ (d * D) := by
          gcongr
          exact Finset.card_union_le _ _
      _ ≤ (en * ns + nc) + 3 ^ (d * D) := by
          gcongr
  have hcast : ((en * ns + nc + 3 ^ (d * D) : ℕ) : ℝ) ≤
      ((en * ns + nc + 1 : ℕ) : ℝ) * (3 : ℝ) ^ ((d : ℝ) * (D : ℝ)) := by
    have heq : ((3 : ℝ) ^ (d * D) : ℝ) = (3 : ℝ) ^ ((d : ℝ) * (D : ℝ)) := by
      rw [← Real.rpow_natCast (3 : ℝ) (d * D)]
      norm_num
    push_cast
    rw [heq]
    have hpow_pos : (0:ℝ) < (3:ℝ) ^ ((d:ℝ) * (D:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hpow_ge : (1:ℝ) ≤ (3:ℝ) ^ ((d:ℝ) * (D:ℝ)) := by
      rw [← heq]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    have hAnonneg : (0:ℝ) ≤ (en : ℝ) * (ns : ℝ) + (nc : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hpow_ge hAnonneg]
  calc (((Finset.univ : Finset (Fin en × Fin ns)).image rootMap ∪
      (Finset.univ : Finset (Fin nc)).image cmpMap ∪
      (Finset.univ : Finset (Fin D → OddGridIndex d 1)).image descMap).card : ℝ)
      ≤ ((en * ns + nc + 3 ^ (d * D) : ℕ) : ℝ) := by exact_mod_cast hunion
    _ ≤ ((en * ns + nc + 1 : ℕ) : ℝ) * (3 : ℝ) ^ ((d : ℝ) * (D : ℝ)) := hcast

/--  pure propositional
reduction, no probability content: given `good_event`'s SIX deterministic
conjuncts (the constants block `0 < lam ∧ lam < 1 ∧ 0 < cell ∧ 0 < epshom ∧
0 < cdet ∧ 0 < c0`, the centre-catalogue cardinality bound, and
`lam < lamDet`) — which at `lem_finite_good_cell`'s own instantiation are
ALWAYS true, never ω-dependent failures — its negation collapses to a
disjunction of the negations of the five remaining, genuinely ω-dependent
conjuncts (the prefix-sum test, ellipticity, the affine matrix bound,
`coarseErr`, and `refRatio`). This separates the `hTailCover` engineering
(supplied below) — which only has to cover these five failure modes —
from the six conjuncts that are fixed constants and can never fail, at
whatever `Roots`/`Enl`/`Cmp` instantiation the caller uses. -/
theorem aux_good_event_neg_reduce
    {Om : Type} {d : ℕ} {Roots Enl Cmp : Type}
    [Fintype Enl] [Fintype Cmp]
    (centres : Roots → ℕ → Finset (Fin d → ℝ))
    (pre : Roots → ℕ → (Fin d → ℝ) → Finset ℤ)
    (Z Dsc : ℤ → (Fin d → ℝ) → Om → ℝ)
    (ellipMin ellipMax : Enl → Om → ℝ)
    (AE : Enl → Om → Matrix (Fin d) (Fin d) ℝ)
    (coarseErr refRatio : Cmp → Om → ℝ) (chosen : Cmp)
    (c0 Cd cell lam lamDet epshom cdet : ℝ) (k0 : ℕ) (ω : Om)
    (hlam : 0 < lam) (hlam1 : lam < 1) (hcell : 0 < cell)
    (hepshom : 0 < epshom) (hcdet : 0 < cdet) (hc0 : 0 < c0)
    (hcard : ∀ (U : Roots) (D : ℕ),
      ((centres U D).card : ℝ) ≤ Cd * (3 : ℝ) ^ ((d : ℝ) * (D : ℝ)))
    (hlamDet : lam < lamDet) :
    ¬ good_event Om d Roots Enl Cmp centres pre Z Dsc ellipMin ellipMax AE
        coarseErr refRatio chosen c0 Cd cell lam lamDet epshom cdet k0 ω ↔
    (¬ (∀ (U : Roots) (D : ℕ), k0 ≤ D → ∀ w ∈ centres U D,
          (∑ j ∈ pre U D w, Z j w ω) < lam * (D : ℝ) ∧
            (∑ j ∈ pre U D w, Dsc j w ω) < lam * (D : ℝ))) ∨
    (¬ (∀ e : Enl, cell ≤ ellipMin e ω ∧ ellipMax e ω ≤ cell⁻¹)) ∨
    (¬ (∀ (e : Enl) (x : Fin d → ℝ),
          c0 * Matrix.trace (AE e ω) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (AE e ω).mulVec x)) ∨
    (¬ (coarseErr chosen ω ≤ epshom * cdet)) ∨
    (¬ (∀ cq : Cmp, refRatio cq ω ∈ Set.Icc (1 / 2 : ℝ) 2)) := by
  unfold good_event
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := hc
    exact h ⟨hlam, hlam1, hcell, hepshom, hcdet, hc0, hcard, hc1, hlamDet, hc2, hc3, hc4, hc5⟩
  · intro h hgood
    obtain ⟨_, _, _, _, _, _, _, hP1, _, hP2, hP3, hP4, hP5⟩ := hgood
    rcases h with h | h | h | h | h
    · exact h hP1
    · exact h hP2
    · exact h hP3
    · exact h hP4
    · exact h hP5



def aux_lem_finite_good_cell_good_char
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (_Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sobolev : SobolevFoundationalInput d hd)
    (_MeyersMorrey : SmallPerturbationInput d)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (Cresp : ℝ) (_hCresp : 0 < Cresp)
    (alpha beta rate : ℝ) (_hbeta : 1 / 2 < beta)
    (_hba : beta < alpha) (_halpha : alpha < 1) (_hrate : 0 < rate)
    (H1 : ℕ) (_hH1 : 0 < H1)
    (eps cell lam lamDet cdet : ℝ)
    (_heps : eps ∈ Set.Ioo (0 : ℝ) 1) (_hcell : 0 < cell) (_hlam : 0 < lam)
    (_hlamlt : lam < lamDet) (_hlamDet1 : lamDet < 1) (_hcdet : 0 < cdet)
    (en nc ns : ℕ) (_self padRoot : Fin en) (chosen : Fin nc) (_selfShift : Fin ns)
    (enDepth : Fin en → ℕ) (cmpDepth : Fin nc → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d)
    (shift : Fin ns → SpatialCoordinates d)
    (cmpRoot : Fin nc → Fin en × Fin ns)
    (_cmpWord : (c : Fin nc) →
      Fin (enDepth (cmpRoot c).1 + cmpDepth c) → OddGridIndex d 1)
    (buffer k0 : ℕ) (_hbuffer : 0 < buffer)
    (sigma : ℝ)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (F Praw _Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (_rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (Good : ℕ → ℕ → SpatialCoordinates d → Set (BilateralField d))
    (Carrier : Set (BilateralField d)) : Prop :=
      (∀ (m k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d),
        omega ∈ Carrier →
        let N := m + k
        let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
        let rootSide : Fin en × Fin ns → ℝ :=
          fun U => r * (3 : ℝ) ^ enDepth U.1
        let rootCentre : Fin en × Fin ns → SpatialCoordinates d :=
          fun U => z + rootSide U • shift U.2
        let centres : (Fin en × Fin ns) → ℕ → Finset (SpatialCoordinates d) :=
          fun U D => by
            classical
            exact ((Finset.univ : Finset (Fin en × Fin ns)).image rootCentre) ∪
              ((Finset.univ : Finset (Fin nc)).image (fun c => z + r • cmpShift c)) ∪
              ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
                (descendantCenter 1 (rootCentre U) (rootSide U) D))
        let pre : (Fin en × Fin ns) → ℕ → SpatialCoordinates d → Finset ℤ :=
          fun U D _ =>
            Finset.Icc ((k : ℤ) - enDepth U.1 - buffer)
              (min (N : ℤ) ((k : ℤ) - enDepth U.1 + D + buffer))
        let Zphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
          if 0 ≤ (N : ℤ) - j then Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om else 0
        let Dphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
          if 0 ≤ (N : ℤ) - j then
            (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om).toReal else 0
        omega ∈ Good m k z ↔
          (∀ e D, ∀ w ∈ centres e D, ∀ j ∈ pre e D w,
            0 ≤ (N : ℤ) - j →
              Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega ≠ ⊤) ∧
          (∀ t : Fin ns,
            F N (m + enDepth padRoot)
              ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 1 ∧
            Praw N (m + enDepth padRoot)
              ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 12) ∧
          ∀ infrared : Bool,
            let Hused := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
            let kappa := fun J : ℕ =>
              Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
                SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
            let retained := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
              if 0 ≤ j then ∑ i ∈ Finset.Ico (0 : ℤ) j, om (-i) w
              else -∑ i ∈ Finset.Ico j (0 : ℤ), om (-i) w
            let reference := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
              kappa ((N : ℤ) - j).toNat / kappa N *
                Real.exp (Hused om w + retained j w om)
            let rEn := rootSide
            let zEn := rootCentre
            let hrEn : ∀ U : Fin en × Fin ns, 0 < rEn U := by
              intro U; dsimp [rEn, rootSide, r]; positivity
            let aEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
              cutoffPositiveCoefficient model Hused om N (zEn U) (hrEn U)
            let refEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
              reference ((k : ℤ) - enDepth U.1) (zEn U) om
            let zCmp := fun c : Fin nc => z + r • cmpShift c
            let rCmp := fun c : Fin nc => r * (3 : ℝ) ^ (-(cmpDepth c : ℤ))
            let hrCmp : ∀ c, 0 < rCmp c := by intro c; dsimp [rCmp, r]; positivity
            let aCmp := fun (c : Fin nc) (om : BilateralField d) =>
              cutoffPositiveCoefficient model Hused om N (zCmp c) (hrCmp c)
            let refCmp := fun (c : Fin nc) (om : BilateralField d) =>
              reference ((k : ℤ) + cmpDepth c) (zCmp c) om
            good_event (BilateralField d) d (Fin en × Fin ns) (Fin en × Fin ns) (Fin nc)
              centres pre Zphys Dphys
              (fun e om => I.lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
              (fun e om => I.Lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
              (fun e om i j =>
                (Homogenization.Book.Ch02.sigmaCoarse
                  (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                  ((I.chart (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e)).coeffOn
                    (Homogenization.originCube d 0))) i j / refEn e om)
              (fun c om => I.err (zCmp c) (rCmp c) (hrCmp c) (aCmp c om)
                (zCmp c) (rCmp c) (refCmp c om) sigma 2)
              (fun c om => reference (k : ℤ) z om / refCmp c om)
              chosen ((2 * (d : ℝ))⁻¹) ((en * ns + nc + 1 : ℕ) : ℝ) cell lam lamDet eps cdet k0 omega)

/-- The disorder discount `sigma`, the disorder threshold `delta0`, the
Holder/extension constants `Cfin, Aext`, and a padding scalar `pad`
strictly between `1` and `(3:ℝ)^H1`, and separately `≤ 3` (since the padding root now sits at the FIXED depth
`1`, `enDepth padRoot = 1` independent of `H1`, so the bound the call site
needs is `pad ≤ (3:ℝ)^1 = 3`, not `pad ≤ (3:ℝ)^H1`): the purely algebraic
half of the paper's parameter-choice paragraph preceding
("Choose sigma, then tau2... a small discount sigma>0"), reusing the
already-proved `aux_lem_finite_good_cell_choose_second_block` at the fixed
padding depth `D := 1`. Easiest step: pure real arithmetic, no
probabilistic or Sobolev content. -/
theorem aux_lem_finite_good_cell_h_constants (H1 : ℕ) (hH1 : 0 < H1) :
    ∃ sigma delta0 Cfin Aext pad : ℝ,
      sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < delta0 ∧ 0 < Cfin ∧ 0 < Aext ∧
      ∃ _hpad : 1 < pad, pad < (3 : ℝ) ^ H1 ∧ pad ≤ 3 := by
  obtain ⟨delta0, Cfin, Aext, pad, hd, hc, ha, hpad, hpadL, hpadD⟩ :=
    aux_lem_finite_good_cell_choose_second_block ((3 : ℝ) ^ H1)
      (aux_lem_finite_good_cell_L_gt_one H1 hH1) 1 (by norm_num)
  refine ⟨1/2, delta0, Cfin, Aext, pad, ?_, hd, hc, ha, hpad, hpadL, ?_⟩
  · exact ⟨by norm_num, by norm_num⟩
  · simpa using hpadD



theorem aux_lem_finite_good_cell_h_good_event_witness
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Sobolev : SobolevFoundationalInput d hd)
    (MeyersMorrey : SmallPerturbationInput d)
    (Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (alpha beta rate : ℝ) (hbeta : 1 / 2 < beta)
    (hba : beta < alpha) (halpha : alpha < 1) (hrate : 0 < rate)
    (H1 : ℕ) (hH1 : 0 < H1)
    (eps cell lam lamDet cdet : ℝ)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (hcell : 0 < cell) (hlam : 0 < lam)
    (hlamlt : lam < lamDet) (hlamDet1 : lamDet < 1) (hcdet : 0 < cdet)
    (en nc ns : ℕ) (self padRoot : Fin en) (chosen : Fin nc) (selfShift : Fin ns)
    (enDepth : Fin en → ℕ) (cmpDepth : Fin nc → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d)
    (shift : Fin ns → SpatialCoordinates d)
    (cmpRoot : Fin nc → Fin en × Fin ns)
    (cmpWord : (c : Fin nc) →
      Fin (enDepth (cmpRoot c).1 + cmpDepth c) → OddGridIndex d 1)
    (buffer k0 : ℕ) (hbuffer : 0 < buffer)
    (sigma delta0 : ℝ) (_hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) (_hdelta0 : 0 < delta0)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (response : _root_.SubdiffusiveProcess.Paper.in_responses d model)
    (_hresponse : response.C ≤ Cresp)
    (regularity : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
    (_iteration : _root_.SubdiffusiveProcess.Paper.in_iteration d model I regularity)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hInfra : InfraredCharacterization model H)
    (_hdelta : model.delta ≤ delta0)
    (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (_heta : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N i x,
      eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x))
    (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (_hprim : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N,
      primitive_scores d model sigma eps (eta N omega)
        (fun m z => F N m z omega) (fun m z => Praw N m z omega)
        (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
        (fun m z => Z N m z omega) (fun m z => rawGood N m z omega))
    :
    ∃ Good : ℕ → ℕ → SpatialCoordinates d → Set (BilateralField d),
    let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
    ∃ Carrier : Set (BilateralField d), MeasurableSet Carrier ∧ P Carrierᶜ = 0 ∧
      aux_lem_finite_good_cell_good_char d hd I Poincare Extension Sobolev MeyersMorrey Step Cresp hCresp alpha beta rate hbeta hba halpha hrate H1 hH1 eps cell lam lamDet cdet heps hcell hlam hlamlt hlamDet1 hcdet en nc ns self padRoot chosen selfShift enDepth cmpDepth cmpShift shift cmpRoot cmpWord buffer k0 hbuffer sigma model H F Praw Rraw Draw Z rawGood Good Carrier := by
  let Good : ℕ → ℕ → SpatialCoordinates d → Set (BilateralField d) := fun m k z omega =>
    let N := m + k
    let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
    let rootSide : Fin en × Fin ns → ℝ :=
      fun U => r * (3 : ℝ) ^ enDepth U.1
    let rootCentre : Fin en × Fin ns → SpatialCoordinates d :=
      fun U => z + rootSide U • shift U.2
    let centres : (Fin en × Fin ns) → ℕ → Finset (SpatialCoordinates d) :=
      fun U D => by
        classical
        exact ((Finset.univ : Finset (Fin en × Fin ns)).image rootCentre) ∪
          ((Finset.univ : Finset (Fin nc)).image (fun c => z + r • cmpShift c)) ∪
          ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
            (descendantCenter 1 (rootCentre U) (rootSide U) D))
    let pre : (Fin en × Fin ns) → ℕ → SpatialCoordinates d → Finset ℤ :=
      fun U D _ =>
        Finset.Icc ((k : ℤ) - enDepth U.1 - buffer)
          (min (N : ℤ) ((k : ℤ) - enDepth U.1 + D + buffer))
    let Zphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
      if 0 ≤ (N : ℤ) - j then Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om else 0
    let Dphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
      if 0 ≤ (N : ℤ) - j then
        (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om).toReal else 0
    (∀ e D, ∀ w ∈ centres e D, ∀ j ∈ pre e D w,
      0 ≤ (N : ℤ) - j →
        Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega ≠ ⊤) ∧
    (∀ t : Fin ns,
      F N (m + enDepth padRoot)
        ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 1 ∧
        Praw N (m + enDepth padRoot)
          ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 12) ∧
    ∀ infrared : Bool,
      let Hused := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
      let kappa := fun J : ℕ =>
        Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
      let retained := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
        if 0 ≤ j then ∑ i ∈ Finset.Ico (0 : ℤ) j, om (-i) w
        else -∑ i ∈ Finset.Ico j (0 : ℤ), om (-i) w
      let reference := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
        kappa ((N : ℤ) - j).toNat / kappa N *
          Real.exp (Hused om w + retained j w om)
      let rEn := rootSide
      let zEn := rootCentre
      let hrEn : ∀ U : Fin en × Fin ns, 0 < rEn U := by
        intro U; dsimp [rEn, rootSide, r]; positivity
      let aEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
        cutoffPositiveCoefficient model Hused om N (zEn U) (hrEn U)
      let refEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
        reference ((k : ℤ) - enDepth U.1) (zEn U) om
      let zCmp := fun c : Fin nc => z + r • cmpShift c
      let rCmp := fun c : Fin nc => r * (3 : ℝ) ^ (-(cmpDepth c : ℤ))
      let hrCmp : ∀ c, 0 < rCmp c := by intro c; dsimp [rCmp, r]; positivity
      let aCmp := fun (c : Fin nc) (om : BilateralField d) =>
        cutoffPositiveCoefficient model Hused om N (zCmp c) (hrCmp c)
      let refCmp := fun (c : Fin nc) (om : BilateralField d) =>
        reference ((k : ℤ) + cmpDepth c) (zCmp c) om
      good_event (BilateralField d) d (Fin en × Fin ns) (Fin en × Fin ns) (Fin nc)
        centres pre Zphys Dphys
        (fun e om => I.lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
        (fun e om => I.Lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
        (fun e om i j =>
          (Homogenization.Book.Ch02.sigmaCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e)).coeffOn
              (Homogenization.originCube d 0))) i j / refEn e om)
        (fun c om => I.err (zCmp c) (rCmp c) (hrCmp c) (aCmp c om)
          (zCmp c) (rCmp c) (refCmp c om) sigma 2)
        (fun c om => reference (k : ℤ) z om / refCmp c om)
        chosen ((2 * (d : ℝ))⁻¹) ((en * ns + nc + 1 : ℕ) : ℝ) cell lam lamDet eps cdet k0 omega
  refine ⟨Good, ?_⟩
  refine ⟨Set.univ, ?_⟩
  have hMeas : MeasurableSet (Set.univ : Set (BilateralField d)) := MeasurableSet.univ
  have hProb : (chaosSampleLaw model).toMeasure (Set.univ : Set (BilateralField d))ᶜ = 0 := by
    simp
  have hChar : aux_lem_finite_good_cell_good_char d hd I Poincare Extension Sobolev MeyersMorrey Step Cresp hCresp alpha beta rate hbeta hba halpha hrate H1 hH1 eps cell lam lamDet cdet heps hcell hlam hlamlt hlamDet1 hcdet en nc ns self padRoot chosen selfShift enDepth cmpDepth cmpShift shift cmpRoot cmpWord buffer k0 hbuffer sigma model H F Praw Rraw Draw Z rawGood Good Set.univ := by
    intro m k z omega h
    rfl
  exact ⟨hMeas, hProb, hChar⟩

/-- Pointwise supremum over a separable index space of a family that is continuous in the index
and measurable in the parameter is measurable. (Real `⨆` is `0` when unbounded; the dense
countable subset has the same supremum and the same boundedness, by continuity.)

Used below for `hCondMeas`'s `normOn`/`J` sub-pieces (the sup-over-a-window content of
`primitive_scores`'s `Fsc/Psc/Rsc/Dsc`). -/
theorem aux_lem_finite_good_cell_measurable_iSup_of_continuous
    {X K : Type*} [MeasurableSpace X] [TopologicalSpace K] [SeparableSpace K]
    (f : X → K → ℝ) (hcont : ∀ x, Continuous (f x))
    (hmeas : ∀ k, Measurable (fun x => f x k)) :
    Measurable (fun x => ⨆ k, f x k) := by
  by_cases h_ne : Nonempty K
  · -- K is nonempty: use the countable dense sequence
    let D := denseSeq K
    have hD : DenseRange D := denseRange_denseSeq K
    have h_eq : ∀ x, ⨆ k, f x k = ⨆ n, f x (D n) := by
      intro x
      by_cases hbdd : BddAbove (Set.range (fun n : ℕ => f x (D n)))
      · set M := ⨆ n, f x (D n) with hM
        have hM_le_dense : ∀ n, f x (D n) ≤ M := by
          intro n
          exact le_ciSup hbdd n
        have hM_le_all : ∀ k, f x k ≤ M := by
          intro k
          refine hD.induction_on k (isClosed_le (hcont x) continuous_const) hM_le_dense
        have hbdd_full : BddAbove (Set.range (f x)) := by
          refine ⟨M, ?_⟩
          rintro y ⟨k, rfl⟩
          exact hM_le_all k
        apply le_antisymm
        · exact ciSup_le hM_le_all
        · apply ciSup_le
          intro n
          exact le_ciSup hbdd_full (D n)
      · -- the dense-range values are unbounded above, so both iSups are 0
        have hbdd_full : ¬ BddAbove (Set.range (f x)) := by
          intro h
          apply hbdd
          exact h.mono (Set.range_comp_subset_range D (f x))
        rw [Real.iSup_of_not_bddAbove hbdd, Real.iSup_of_not_bddAbove hbdd_full]
    have h_meas : Measurable (fun x => ⨆ n, f x (D n)) :=
      Measurable.iSup (fun n => hmeas (D n))
    simpa [h_eq] using h_meas
  · -- K is empty: the iSup over an empty type is 0
    have : IsEmpty K := not_nonempty_iff.mp h_ne
    simp

section CondMeas
/-! Measurability of the primitive-score formulas in the sample:
on the carrier the raw scores are these formulas at the canonical relabelled sample. -/
open MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess
open scoped ENNReal Topology

/-- Public copy of the proved `PrefixActualFMeas.prefixF_spatial_sup_meas` (private there). -/
theorem aux_condmeas_spatial_sup_meas {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {W : Set (Vec d)} (hWopen : IsOpen W)
    (F : Ω → Vec d → ENNReal)
    (hcont : ∀ omega, Continuous (F omega))
    (hmeas : ∀ x, Measurable (fun omega => F omega x)) :
    Measurable (fun omega => sSup {v : ENNReal | ∃ x ∈ W, v = F omega x}) := by
  obtain ⟨Q, hQcount, hQdense⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  have : Countable ↥(W ∩ Q) :=
    (hQcount.mono Set.inter_subset_right).to_subtype
  have heq : ∀ omega,
      sSup {v : ENNReal | ∃ x ∈ W, v = F omega x} =
        ⨆ x : ↥(W ∩ Q), F omega x := by
    intro omega
    apply le_antisymm
    · refine sSup_le ?_
      rintro v ⟨x, hx, rfl⟩
      let c : ENNReal := ⨆ y : ↥(W ∩ Q), F omega y
      have hc : IsClosed {y : Vec d | F omega y ≤ c} :=
        isClosed_le (hcont omega) continuous_const
      have hsub : W ∩ Q ⊆ {y : Vec d | F omega y ≤ c} := by
        intro y hy
        exact le_iSup (fun y : ↥(W ∩ Q) => F omega y) ⟨y, hy⟩
      have hdense : W ⊆ closure (W ∩ Q) :=
        hQdense.open_subset_closure_inter hWopen
      exact hc.closure_subset_iff.mpr hsub (hdense hx)
    · refine iSup_le fun y => ?_
      exact le_sSup ⟨y.1, y.2.1, rfl⟩
  simp_rw [heq]
  exact Measurable.iSup (fun y => hmeas y)

/-- Dsc, term 2 (the shell-block tests), measurable in the sample. -/
theorem aux_condmeas_Dsc_block_meas {d : ℕ} (s : ℝ) (k : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            w = ENNReal.ofReal |shellBlock k j omega x|}}) := by
  have hinner : ∀ j : ℕ, Measurable (fun omega : PotentialSample d =>
      sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
        w = ENNReal.ofReal |shellBlock k j omega x|}) := by
    intro j
    apply aux_condmeas_spatial_sup_meas
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.isOpen_translatedCube d k z)
    · intro omega
      exact ENNReal.continuous_ofReal.comp
        ((SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_shellBlock k j omega).abs)
    · intro x
      exact (continuous_abs.measurable.comp
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.measurable_shellBlock_eval k j x)).ennreal_ofReal
  have hterm : ∀ j : ℕ, Measurable (fun omega : PotentialSample d =>
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
        sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
          w = ENNReal.ofReal |shellBlock k j omega x|}) := by
    intro j
    exact Measurable.const_mul (hinner j) _
  have heq : (fun omega : PotentialSample d =>
      sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            w = ENNReal.ofReal |shellBlock k j omega x|}}) =
      (fun omega => ⨆ j : {j : ℕ // j ≤ k},
        ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            w = ENNReal.ofReal |shellBlock k j omega x|}) := by
    funext omega
    apply le_antisymm
    · refine sSup_le ?_
      rintro v ⟨j, hj, rfl⟩
      exact le_iSup_of_le ⟨j, hj⟩ le_rfl
    · refine iSup_le fun j => ?_
      exact le_sSup ⟨j.1, j.2, rfl⟩
  rw [heq]
  exact Measurable.iSup (fun (j : {j : ℕ // j ≤ k}) => hterm j.1)

/-- Dsc, term 3 (the base layer), measurable in the sample. -/
theorem aux_condmeas_Dsc_base_meas {d : ℕ} (s : ℝ) (k : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
        sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
          w = ENNReal.ofReal |omega 0 x|}) := by
  have hinner : Measurable (fun omega : PotentialSample d =>
      sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
        w = ENNReal.ofReal |omega 0 x|}) := by
    apply aux_condmeas_spatial_sup_meas
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.isOpen_translatedCube d k z)
    · intro omega
      exact ENNReal.continuous_ofReal.comp
        ((_root_.SubdiffusiveProcess.Model.PotentialField.contDiff_one (omega 0)).continuous.abs)
    · intro x
      exact ((continuous_abs.measurable.comp ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
        (measurable_potentialCoordinate 0))).ennreal_ofReal)
  exact Measurable.const_mul hinner _

/-- Dsc, term 4 (the high-gradient series), measurable in the sample. -/
theorem aux_condmeas_Dsc_grad_meas {d : ℕ} (k : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      ∑' j : ℕ, (if k ≤ j then
        ENNReal.ofReal ((3 : ℝ) ^ k) *
          sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            w = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|}
        else 0)) := by
  have hinner : ∀ j : ℕ, Measurable (fun omega : PotentialSample d =>
      sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
        w = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|}) := by
    intro j
    apply aux_condmeas_spatial_sup_meas
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.isOpen_translatedCube d k z)
    · intro omega
      exact ENNReal.continuous_ofReal.comp
        ((SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_euclideanNorm.comp
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_shellGradient
            (omega j))).abs)
    · intro x
      exact ((continuous_abs.measurable.comp
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_euclideanNorm.measurable.comp
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.measurable_shellGradient_eval x j)))).ennreal_ofReal
  apply Measurable.tsum
  intro j
  split_ifs
  · exact Measurable.const_mul (hinner j) _
  · exact measurable_const

/-- The eramp bad score `Z` (clause (7)) is measurable in the sample. -/
theorem aux_condmeas_Z_meas {d : ℕ} [NeZero d] (M : GMCModel d) (s eps : ℝ) (m : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      (min (1 : ENNReal)
          ((sSup {v : ENNReal | ∃ j : ℕ,
              v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
                ∑ i ∈ Finset.Icc (m - j) (m + j),
                  sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
                    w = ENNReal.ofReal |(|omega i x| + (3 : ℝ) ^ (i : ℝ) *
                      Homogenization.euclideanNorm (shellGradient (omega i) x))|}} -
              ENNReal.ofReal (eps / 2)) / ENNReal.ofReal (eps - eps / 2))).toReal +
      (min (1 : ENNReal)
          ((sSup {v : ENNReal | ∃ j : ℕ,
              v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
                sSup {w : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (m + 1 + j) z ∧
                  w = (∏ i ∈ Finset.Icc (m - j) (m + j),
                        ENNReal.ofReal (Real.exp |omega i x|)) +
                      sSup {u : ENNReal | ∃ K : ℕ,
                        u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
                          ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))}}} -
              ENNReal.ofReal 6) / ENNReal.ofReal (12 - 6))).toReal +
      (min (1 : ENNReal)
          ((sSup {v : ENNReal | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧ ∃ x : Vec d,
              OnTriadicGrid n (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
              v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
                sSup {u : ENNReal | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
                  u = ENNReal.ofReal (section6Response M n n omega x e)}} -
              ENNReal.ofReal (eps ^ 2 / 4)) / ENNReal.ofReal (eps ^ 2 - eps ^ 2 / 4))).toReal) := by
  have heramp (a b : ℝ) {X : PotentialSample d → ENNReal} (hX : Measurable X) :
      Measurable (fun x => (min (1 : ENNReal) ((X x - ENNReal.ofReal a) /
        ENNReal.ofReal (b - a))).toReal) := by
    exact ENNReal.measurable_toReal.comp
      (measurable_const.min ((hX.sub measurable_const).div measurable_const))
  have hF := aux_lem_prefix_limit_actual_Fsc_meas s m z
  have hP := aux_lem_prefix_limit_actual_Psc_meas s m z
  have hR := aux_lem_prefix_limit_actual_Rsc_meas M s m z
  exact ((heramp (eps / 2) eps hF).add (heramp 6 12 hP)).add
    (heramp (eps ^ 2 / 4) (eps ^ 2) hR)

/-- The canonical relabelled sample is measurable, and agrees with any `eta` satisfying the
relabelling identity at `ω`. -/
theorem aux_condmeas_eta_canon {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (N : ℕ) :
    Measurable (fun omega : BilateralField d => fun i : ℕ =>
      aux_lem_crossing_unforget (SubdiffusiveProcess.layerScaling d (N : ℤ)
        (omega ((i : ℤ) - (N : ℤ))))) ∧
    ∀ (eta : BilateralField d → PotentialSample d) (omega : BilateralField d),
      (∀ (i : ℕ) (y : Vec d), eta omega i y = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      eta omega = fun i : ℕ => aux_lem_crossing_unforget (SubdiffusiveProcess.layerScaling d (N : ℤ)
        (omega ((i : ℤ) - (N : ℤ)))) := by
  constructor
  · refine measurable_pi_iff.mpr fun i =>
      aux_lem_crossing_measurable_unforget.comp
        ((SubdiffusiveProcess.layerScaling d (N : ℤ)).continuous.measurable.comp
          (measurable_pi_apply ((i : ℤ) - (N : ℤ))))
  · intro eta omega h
    funext i
    have hf : SubdiffusiveProcess.layerScaling d (N : ℤ)
        (omega ((i : ℤ) - (N : ℤ))) = aux_lem_crossing_forget (eta omega i) := by
      apply ContinuousMap.ext
      intro y
      simpa [SubdiffusiveProcess.layerScaling, aux_lem_crossing_forget] using
        (h i y).symm
    calc
      eta omega i = aux_lem_crossing_unforget (aux_lem_crossing_forget (eta omega i)) := by
        rw [aux_lem_crossing_unforget_forget]
      _ = aux_lem_crossing_unforget (SubdiffusiveProcess.layerScaling d (N : ℤ)
        (omega ((i : ℤ) - (N : ℤ)))) := by rw [hf]

/-- Measurability and positivity of the good-event reference scalar. -/
theorem aux_condmeas_reference {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHm : Measurable Hused)
    (N : ℕ) (j : ℤ) (w : SpatialCoordinates d) :
    let kappa := fun J : ℕ =>
      Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
    let retained := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
      if 0 ≤ j then ∑ i ∈ Finset.Ico (0 : ℤ) j, om (-i) w
      else -∑ i ∈ Finset.Ico j (0 : ℤ), om (-i) w
    Measurable (fun om : BilateralField d =>
      kappa ((N : ℤ) - j).toNat / kappa N * Real.exp (Hused om w + retained j w om)) ∧
    ∀ om, 0 < kappa ((N : ℤ) - j).toNat / kappa N * Real.exp (Hused om w + retained j w om) := by
  intro kappa retained
  constructor
  · -- measurability
    have hHused_meas : Measurable (fun (om : BilateralField d) => Hused om w) :=
      (continuous_eval_const w).measurable.comp hHm
    have hretained_meas : Measurable (retained j w) := by
      unfold retained
      split_ifs with hj
      · refine Finset.measurable_sum _ (fun i hi => ?_)
        exact (continuous_eval_const w).measurable.comp (measurable_pi_apply (-i))
      · refine Measurable.neg (Finset.measurable_sum _ (fun i hi => ?_))
        exact (continuous_eval_const w).measurable.comp (measurable_pi_apply (-i))
    have h_exp_meas : Measurable (fun (om : BilateralField d) => Real.exp (Hused om w + retained j w om)) :=
      Real.measurable_exp.comp (hHused_meas.add hretained_meas)
    have hkappa_meas : Measurable (fun (_ : BilateralField d) => kappa ((N : ℤ) - j).toNat / kappa N) :=
      measurable_const
    exact hkappa_meas.mul h_exp_meas
  · -- positivity
    intro om
    have hkappa_pos : ∀ J : ℕ, 0 < kappa J := by
      intro J
      unfold kappa
      refine mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model J)
    have h_num_pos : 0 < kappa ((N : ℤ) - j).toNat := hkappa_pos _
    have h_den_pos : 0 < kappa N := hkappa_pos _
    have h_ratio_pos : 0 < kappa ((N : ℤ) - j).toNat / kappa N :=
      div_pos h_num_pos h_den_pos
    have h_exp_pos : 0 < Real.exp (Hused om w + retained j w om) :=
      Real.exp_pos _
    exact mul_pos h_ratio_pos h_exp_pos

end CondMeas



def aux_lem_finite_good_cell_rhs (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (sigma eps cell lam lamDet cdet : ℝ) (en nc ns : ℕ) (padRoot : Fin en) (chosen : Fin nc)
    (enDepth : Fin en → ℕ) (cmpDepth : Fin nc → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d) (shift : Fin ns → SpatialCoordinates d)
    (buffer k0 : ℕ)
    (F Praw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (m k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) : Prop :=
  let N := m + k
  let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  let rootSide : Fin en × Fin ns → ℝ :=
    fun U => r * (3 : ℝ) ^ enDepth U.1
  let rootCentre : Fin en × Fin ns → SpatialCoordinates d :=
    fun U => z + rootSide U • shift U.2
  let centres : (Fin en × Fin ns) → ℕ → Finset (SpatialCoordinates d) :=
    fun U D => by
      classical
      exact ((Finset.univ : Finset (Fin en × Fin ns)).image rootCentre) ∪
        ((Finset.univ : Finset (Fin nc)).image (fun c => z + r • cmpShift c)) ∪
        ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
          (descendantCenter 1 (rootCentre U) (rootSide U) D))
  let pre : (Fin en × Fin ns) → ℕ → SpatialCoordinates d → Finset ℤ :=
    fun U D _ =>
      Finset.Icc ((k : ℤ) - enDepth U.1 - buffer)
        (min (N : ℤ) ((k : ℤ) - enDepth U.1 + D + buffer))
  let Zphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
    if 0 ≤ (N : ℤ) - j then Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om else 0
  let Dphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
    if 0 ≤ (N : ℤ) - j then
      (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om).toReal else 0
  (∀ e D, ∀ w ∈ centres e D, ∀ j ∈ pre e D w,
    0 ≤ (N : ℤ) - j →
      Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega ≠ ⊤) ∧
  (∀ t : Fin ns,
    F N (m + enDepth padRoot)
      ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 1 ∧
    Praw N (m + enDepth padRoot)
      ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 12) ∧
  ∀ infrared : Bool,
    let Hused := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
    let kappa := fun J : ℕ =>
      Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
    let retained := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
      if 0 ≤ j then ∑ i ∈ Finset.Ico (0 : ℤ) j, om (-i) w
      else -∑ i ∈ Finset.Ico j (0 : ℤ), om (-i) w
    let reference := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
      kappa ((N : ℤ) - j).toNat / kappa N *
        Real.exp (Hused om w + retained j w om)
    let rEn := rootSide
    let zEn := rootCentre
    let hrEn : ∀ U : Fin en × Fin ns, 0 < rEn U := by
      intro U; dsimp [rEn, rootSide, r]; positivity
    let aEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
      cutoffPositiveCoefficient model Hused om N (zEn U) (hrEn U)
    let refEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
      reference ((k : ℤ) - enDepth U.1) (zEn U) om
    let zCmp := fun c : Fin nc => z + r • cmpShift c
    let rCmp := fun c : Fin nc => r * (3 : ℝ) ^ (-(cmpDepth c : ℤ))
    let hrCmp : ∀ c, 0 < rCmp c := by intro c; dsimp [rCmp, r]; positivity
    let aCmp := fun (c : Fin nc) (om : BilateralField d) =>
      cutoffPositiveCoefficient model Hused om N (zCmp c) (hrCmp c)
    let refCmp := fun (c : Fin nc) (om : BilateralField d) =>
      reference ((k : ℤ) + cmpDepth c) (zCmp c) om
    good_event (BilateralField d) d (Fin en × Fin ns) (Fin en × Fin ns) (Fin nc)
      centres pre Zphys Dphys
      (fun e om => I.lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
      (fun e om => I.Lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
      (fun e om i j =>
        (Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e)).coeffOn
            (Homogenization.originCube d 0))) i j / refEn e om)
      (fun c om => I.err (zCmp c) (rCmp c) (hrCmp c) (aCmp c om)
        (zCmp c) (rCmp c) (refCmp c om) sigma 2)
      (fun c om => reference (k : ℤ) z om / refCmp c om)
      chosen ((2 * (d : ℝ))⁻¹) ((en * ns + nc + 1 : ℕ) : ℝ) cell lam lamDet eps cdet k0 omega

/-- `RHS` reads the four score families only at its own sample. -/
theorem aux_lem_finite_good_cell_rhs_congr (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (sigma eps cell lam lamDet cdet : ℝ) (en nc ns : ℕ) (padRoot : Fin en) (chosen : Fin nc)
    (enDepth : Fin en → ℕ) (cmpDepth : Fin nc → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d) (shift : Fin ns → SpatialCoordinates d)
    (buffer k0 : ℕ)
    (F Praw Draw F' Praw' Draw' : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z Z' : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (m k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d)
    (hF : ∀ n y, F (m + k) n y omega = F' (m + k) n y omega)
    (hP : ∀ n y, Praw (m + k) n y omega = Praw' (m + k) n y omega)
    (hD : ∀ n y, Draw (m + k) n y omega = Draw' (m + k) n y omega)
    (hZ : ∀ n y, Z (m + k) n y omega = Z' (m + k) n y omega) :
    aux_lem_finite_good_cell_rhs d I model H sigma eps cell lam lamDet cdet en nc ns padRoot chosen
        enDepth cmpDepth cmpShift shift buffer k0 F Praw Draw Z m k z omega ↔
      aux_lem_finite_good_cell_rhs d I model H sigma eps cell lam lamDet cdet en nc ns padRoot chosen
        enDepth cmpDepth cmpShift shift buffer k0 F' Praw' Draw' Z' m k z omega := by
  unfold aux_lem_finite_good_cell_rhs good_event
  simp only [hF, hP, hD, hZ]

/-- `RHS` is a measurable event once the four score families are measurable (at level `m + k`). -/
theorem aux_lem_finite_good_cell_rhs_meas (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (sigma eps cell lam lamDet cdet : ℝ) (en nc ns : ℕ) (padRoot : Fin en) (chosen : Fin nc)
    (enDepth : Fin en → ℕ) (cmpDepth : Fin nc → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d) (shift : Fin ns → SpatialCoordinates d)
    (buffer k0 : ℕ)
    (hHm : Measurable H) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (F Praw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (m k : ℕ) (z : SpatialCoordinates d)
    (hF : ∀ n y, Measurable (F (m + k) n y)) (hP : ∀ n y, Measurable (Praw (m + k) n y))
    (hD : ∀ n y, Measurable (Draw (m + k) n y)) (hZ : ∀ n y, Measurable (Z (m + k) n y)) :
    MeasurableSet {omega | aux_lem_finite_good_cell_rhs d I model H sigma eps cell lam lamDet cdet
      en nc ns padRoot chosen enDepth cmpDepth cmpShift shift buffer k0 F Praw Draw Z m k z omega} := by
  classical
  -- finite-set universal quantifiers over a non-countable carrier type
  have hfin : ∀ {β : Type} (S : Finset β) (Q : β → BilateralField d → Prop),
      (∀ w, Measurable (Q w)) → Measurable (fun omega => ∀ w ∈ S, Q w omega) := by
    intro β S Q hQ
    have hrw : (fun omega => ∀ w ∈ S, Q w omega) = fun omega => ∀ w : S, Q w omega := by
      funext omega; simp
    rw [hrw]
    exact Measurable.forall fun w => hQ w
  unfold aux_lem_finite_good_cell_rhs
  apply Measurable.setOf
  dsimp only
  refine Measurable.and ?_ (Measurable.and ?_ ?_)
  · refine Measurable.forall fun e => Measurable.forall fun D => ?_
    refine hfin _ _ fun w => hfin _ _ fun j => ?_
    refine Measurable.imp measurable_const ?_
    exact Measurable.not (measurableSet_setOfPred.mp ((hD _ _) (measurableSet_singleton ⊤)))
  · refine Measurable.forall fun t => Measurable.and ?_ ?_
    · exact measurableSet_setOfPred.mp (measurableSet_le (hF _ _) measurable_const)
    · exact measurableSet_setOfPred.mp (measurableSet_le (hP _ _) measurable_const)
  · refine Measurable.forall fun infrared => ?_
    have hHu : Measurable (if infrared then H
        else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) := by
      cases infrared
      · exact measurable_const
      · exact hHm
    refine measurableSet_setOfPred.mp (aux_goodev_measurableSet (BilateralField d) d _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    · intro j w
      by_cases hj : (0 : ℤ) ≤ ((m + k : ℕ) : ℤ) - j
      · simp only [hj, ↓reduceIte]; exact hZ _ _
      · simp only [hj, ↓reduceIte]; exact measurable_const
    · intro j w
      by_cases hj : (0 : ℤ) ≤ ((m + k : ℕ) : ℤ) - j
      · simp only [hj, ↓reduceIte]; exact (hD _ _).ennreal_toReal
      · simp only [hj, ↓reduceIte]; exact measurable_const
    · intro e
      exact (aux_core_lam_measurable_HOLE_gen hd I model _ hHu (m + k) _ _ _ sigma hsigma).div
        (aux_condmeas_reference model _ hHu (m + k) _ _).1
    · intro e
      exact (aux_core_Lam_measurable_HOLE_gen hd I model _ hHu (m + k) _ _ _ sigma hsigma).div
        (aux_condmeas_reference model _ hHu (m + k) _ _).1
    · intro e i j
      exact (aux_core_sigmaCoarse_measurable_HOLE_gen hd I model _ hHu (m + k) _ _ _ i j).div
        (aux_condmeas_reference model _ hHu (m + k) _ _).1
    · exact aux_core_err_measurable_HOLE_gen hd I model _ hHu (m + k) _ _ _ sigma hsigma _
        (aux_condmeas_reference model _ hHu (m + k) _ _).1
        (aux_condmeas_reference model _ hHu (m + k) _ _).2
    · intro c
      exact (aux_condmeas_reference model _ hHu (m + k) _ _).1.div
        (aux_condmeas_reference model _ hHu (m + k) _ _).1



theorem aux_lem_finite_good_cell_rhs_of_parts (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (sigma eps cell lam lamDet cdet : ℝ) (en nc ns : ℕ) (padRoot : Fin en) (chosen : Fin nc)
    (enDepth : Fin en → ℕ) (cmpDepth : Fin nc → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d) (shift : Fin ns → SpatialCoordinates d)
    (buffer k0 : ℕ)
    (F Praw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (m k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (heps : 0 < eps) (hcell : 0 < cell)
    (hcell2 : cell ≤ 1 / 2) (hlam : 0 < lam) (hlamlt : lam < lamDet) (hlamDet1 : lamDet < 1)
    (hcdet : 0 < cdet) (self : Fin en) (selfShift : Fin ns) (hself : enDepth self = 0)
    (hselfShift : shift selfShift = 0) (hcmpShift : ∀ c, cmpShift c = 0)
    (hcmpDepth : ∀ c, cmpDepth c = 0) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθd : θ ≤ 1 / (4 * d))
    (hθe : θ ≤ eps * cdet)
    (hDraw : aux_lfgc_rhs_bridge_rhsDrawOK en nc ns enDepth cmpShift shift buffer Draw m k z omega)
    (hFP : aux_lfgc_rhs_bridge_rhsFPOK en ns padRoot enDepth shift F Praw m k z omega)
    (hP1 : aux_lfgc_rhs_bridge_rhsP1OK en nc ns enDepth cmpShift shift buffer k0 lam Draw Z m k z omega)
    (hnH : aux_lfgc_root_stat_nearAll I model H sigma (en * ns) (aux_lfgc_rhs_bridge_lfgcOffset enDepth)
      (aux_lfgc_rhs_bridge_lfgcShift enDepth shift) (m + k) (k : ℤ) z θ omega)
    (hn0 : aux_lfgc_root_stat_nearAll I model 0 sigma (en * ns) (aux_lfgc_rhs_bridge_lfgcOffset enDepth)
      (aux_lfgc_rhs_bridge_lfgcShift enDepth shift) (m + k) (k : ℤ) z θ omega) :
    aux_lem_finite_good_cell_rhs d I model H sigma eps cell lam lamDet cdet en nc ns
      padRoot chosen enDepth cmpDepth cmpShift shift buffer k0 F Praw Draw Z m k z omega := by
  unfold aux_lem_finite_good_cell_rhs
  intro N r rootSide rootCentre centres pre Zphys Dphys
  refine ⟨hDraw, hFP, fun infrared => ?_⟩
  have hnU : aux_lfgc_root_stat_nearAll I model (if infrared then H else 0) sigma (en * ns)
      (aux_lfgc_rhs_bridge_lfgcOffset enDepth) (aux_lfgc_rhs_bridge_lfgcShift enDepth shift)
      (m + k) (k : ℤ) z θ omega := by
    cases infrared
    · exact hn0
    · exact hnH
  intro Hused kappa retained reference rEn zEn hrEn aEn refEn zCmp rCmp hrCmp aCmp refCmp
  unfold _root_.SubdiffusiveProcess.Paper.good_event
  have h2 : (2 : ℝ) ≤ cell⁻¹ := by
    rw [← one_div, le_div_iff₀ hcell]; linarith
  refine ⟨hlam, hlamlt.trans hlamDet1, hcell, heps, hcdet, by positivity, ?_, hP1, hlamlt,
    ?_, ?_, ?_, ?_⟩
  · intro U D
    exact aux_lem_finite_good_cell_tail_card d en nc ns D rootCentre
      (fun c => z + r • cmpShift c) (descendantCenter 1 (rootCentre U) (rootSide U) D)
  · intro e
    obtain ⟨t1, t2, -, -⟩ := lfgc_root_bridge hd I model Hused sigma hsigma omega N (zEn e) (rEn e)
      (hrEn e) ((k : ℤ) - (enDepth e.1 : ℤ)) (aux_lfgc_rhs_bridge_lfgc_side_eq k (enDepth e.1))
      (refEn e omega) rfl hθ0 hθd (lfgc_rhs_bridge I model Hused sigma θ enDepth shift N k z omega hnU e)
    exact ⟨by linarith, by linarith⟩
  · intro e x
    obtain ⟨-, -, t3, -⟩ := lfgc_root_bridge hd I model Hused sigma hsigma omega N (zEn e) (rEn e)
      (hrEn e) ((k : ℤ) - (enDepth e.1 : ℤ)) (aux_lfgc_rhs_bridge_lfgc_side_eq k (enDepth e.1))
      (refEn e omega) rfl hθ0 hθd (lfgc_rhs_bridge I model Hused sigma θ enDepth shift N k z omega hnU e)
    exact t3 x
  · have hzc : zCmp chosen = z := by
      show z + r • cmpShift chosen = z
      rw [hcmpShift, smul_zero, add_zero]
    have hrc : rCmp chosen = (3 : ℝ) ^ (-(k : ℤ)) := by
      show r * (3 : ℝ) ^ (-(cmpDepth chosen : ℤ)) = _
      rw [hcmpDepth]
      simp only [Nat.cast_zero, neg_zero, zpow_zero, mul_one]
      rfl
    have href : refCmp chosen omega =
        _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference model Hused N (k : ℤ) (zCmp chosen) omega := by
      show reference ((k : ℤ) + (cmpDepth chosen : ℤ)) (zCmp chosen) omega = _
      rw [hcmpDepth]
      simp only [Nat.cast_zero, add_zero]
      rfl
    have hn := lfgc_rhs_bridge I model Hused sigma θ enDepth shift N k z omega hnU (self, selfShift)
    simp only [hself, hselfShift, Nat.cast_zero, sub_zero, smul_zero, add_zero] at hn
    rw [← hzc] at hn
    obtain ⟨-, -, -, t4⟩ := lfgc_root_bridge hd I model Hused sigma hsigma omega N (zCmp chosen)
      (rCmp chosen) (hrCmp chosen) (k : ℤ) hrc (refCmp chosen omega) href hθ0 hθd hn
    exact t4.trans hθe
  · intro c
    have hc : refCmp c omega = reference (k : ℤ) z omega := by
      show reference ((k : ℤ) + (cmpDepth c : ℤ)) (z + r • cmpShift c) omega = _
      rw [hcmpDepth, hcmpShift]
      simp only [Nat.cast_zero, add_zero, smul_zero]
    have hpos : 0 < reference (k : ℤ) z omega :=
      _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference_pos model Hused N (k : ℤ) z omega
    show reference (k : ℤ) z omega / refCmp c omega ∈ Set.Icc (1 / 2 : ℝ) 2
    rw [hc, div_self hpos.ne']
    constructor <;> norm_num

/-- Carrier, measurable good event and tail cover (`\label{mfd:lem-finite-good-cell}`, clause (i),
and the pointwise facts on the carrier that Clause 1 reads off).

`Good` and `Carrier` are built together so that `Good m k z` is measurable for EVERY `omega`:
`S` is the full-measure set where the two a.e. pins (`eta` reindexing and `primitive_scores`) hold
pointwise together with the sure finiteness of `Draw` and the infrared limit; `Carrier :=
(toMeasurable P Sᶜ)ᶜ` is a measurable probability-one subset of `S`; `Good m k z := Carrierᶜ ∪
(Carrier ∩ {omega | RHS m k z omega})`, where `RHS` is the literal condition of `good_char`.
Measurability of `Carrier ∩ RHS` is `aux_lem_finite_good_cell_rhs_meas` (chart-coordinate
measurability, `aux_condmeas_*`, `aux_lem_finite_good_cell_measurable_iSup_of_continuous`); the
window cover `(Good m k z)ᶜ ⊆ ⋃ h, W h` with `P (W h) ≤ exp(-rate h)` is `lfgc_tail_cover`
(band estimate of `lem_band` + Markov, the `lfgc_*` fine nodes); the carrier facts are
`lfgc_draw_carrier`, `lfgc_draw_sure`, `lfgc_rhs_bridge`. -/

theorem aux_lem_finite_good_cell_h_measurability_tail
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Sobolev : SobolevFoundationalInput d hd)
    (MeyersMorrey : SmallPerturbationInput d)
    (Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (Dbase : _root_.SubdiffusiveProcess.Paper.sum_errors_baseline_input d)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (alpha beta rate : ℝ) (hbeta : 1 / 2 < beta)
    (hba : beta < alpha) (halpha : alpha < 1) (hrate : 0 < rate)
    (H1 : ℕ) (hH1 : 0 < H1)
    (eps cell lam lamDet cdet : ℝ)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (hcell : 0 < cell) (hcellSmall : cell ≤ 1 / 2)
    (hlam : 0 < lam)
    (hlamlt : lam < lamDet) (hlamDet1 : lamDet < 1) (hcdet : 0 < cdet)
    (en nc ns : ℕ) (self padRoot : Fin en) (chosen : Fin nc) (selfShift : Fin ns)
    (enDepth : Fin en → ℕ) (cmpDepth : Fin nc → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d)
    (shift : Fin ns → SpatialCoordinates d)
    (cmpRoot : Fin nc → Fin en × Fin ns)
    (cmpWord : (c : Fin nc) →
      Fin (enDepth (cmpRoot c).1 + cmpDepth c) → OddGridIndex d 1)
    (buffer k0 : ℕ) (hbuffer : 0 < buffer)
    (hself : enDepth self = 0) (hselfShift : shift selfShift = 0)
    (hcmpShift : ∀ c, cmpShift c = 0) (hcmpDepth : ∀ c, cmpDepth c = 0)
    (hdepthle : ∀ e, enDepth e ≤ 3) (hpadDep : enDepth padRoot = 1) (hk0 : 1 ≤ k0)
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (response : _root_.SubdiffusiveProcess.Paper.in_responses d model)
      (_hresponse : response.C ≤ Cresp)
      (regularity : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
      (_iteration : _root_.SubdiffusiveProcess.Paper.in_iteration d model I regularity)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ delta0 →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d),
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N i x,
          eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N,
          primitive_scores d model sigma eps (eta N omega)
            (fun m z => F N m z omega) (fun m z => Praw N m z omega)
            (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
            (fun m z => Z N m z omega) (fun m z => rawGood N m z omega)) →
      ∃ Good : ℕ → ℕ → SpatialCoordinates d → Set (BilateralField d),
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      ∃ Carrier : Set (BilateralField d), MeasurableSet Carrier ∧ P Carrierᶜ = 0 ∧
        aux_lem_finite_good_cell_good_char d hd I Poincare Extension Sobolev MeyersMorrey Step Cresp hCresp alpha beta rate hbeta hba halpha hrate H1 hH1 eps cell lam lamDet cdet heps hcell hlam hlamlt hlamDet1 hcdet en nc ns self padRoot chosen selfShift enDepth cmpDepth cmpShift shift cmpRoot cmpWord buffer k0 hbuffer sigma model H F Praw Rraw Draw Z rawGood Good Carrier ∧
        (∀ (m k : ℕ) (z : SpatialCoordinates d),
          MeasurableSet (Good m k z) ∧ ∃ W : ℕ+ → Set (BilateralField d),
            (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
              ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).domRestrict)
              (inferInstance : MeasurableSpace
                ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
                  C(SpatialCoordinates d, ℝ)))] (W h)) ∧
            (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-rate * (h : ℝ)))) ∧
            (Good m k z)ᶜ ⊆ ⋃ h : ℕ+, W h) ∧
        (∀ omega ∈ Carrier,
          (∀ (N i : ℕ) (x : SpatialCoordinates d),
            eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x)) ∧
          (∀ N, primitive_scores d model sigma eps (eta N omega)
            (fun m z => F N m z omega) (fun m z => Praw N m z omega)
            (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
            (fun m z => Z N m z omega) (fun m z => rawGood N m z omega)) ∧
          Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)) ∧
          (∀ (N n : ℕ) (y : SpatialCoordinates d), Draw N n y omega ≠ ⊤)) := by
  obtain ⟨θ0lo, hθ0pos, hθ0_4d, hθ0_epscdet, hθ0_8⟩ :
      ∃ θ0 : ℝ, 0 < θ0 ∧ θ0 ≤ 1 / (4 * (d : ℝ)) ∧ θ0 ≤ eps * cdet ∧ θ0 ≤ 1 / 8 := by
    refine ⟨min (1 / (4 * (d : ℝ))) (eps * cdet), lt_min (by positivity) (mul_pos heps.1 hcdet),
      min_le_left _ _, min_le_right _ _, ?_⟩
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h8 : (8 : ℝ) ≤ 4 * (d : ℝ) := by nlinarith
    exact (min_le_left _ _).trans (one_div_le_one_div_of_le (by norm_num) h8)
  obtain ⟨delta0, hdelta0pos, hlfgc⟩ :=
    lfgc_tail_cover hd I Poincare Extension MeyersMorrey Sobolev D Dbase Cresp hCresp sigma
      ⟨hsigma.1, hsigma.2.le⟩ eps heps lam hlam hθ0pos hθ0_8 en nc ns padRoot enDepth hdepthle
      hpadDep cmpShift shift buffer k0 hk0 hrate
  refine ⟨delta0, hdelta0pos, ?_⟩
  · intro model response hresponse regularity iteration H hInfra hdelta
      eta heta F Praw Rraw Draw Z rawGood hprim
    set P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure with hPdef
    set S : Set (BilateralField d) := {omega | (∀ N i x,
        eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x)) ∧
        (∀ N, primitive_scores d model sigma eps (eta N omega)
          (fun m z => F N m z omega) (fun m z => Praw N m z omega)
          (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
          (fun m z => Z N m z omega) (fun m z => rawGood N m z omega)) ∧
        (∀ (N k : ℕ) (z' : Fin d → ℤ),
          (∑' j : ℕ, _root_.SubdiffusiveProcess.Paper.aux_psf_Dmaj4 (k + 1) (fun i => (z' i : ℝ)) j
            (_root_.SubdiffusiveProcess.Paper.aux_lfgc_layer_tail_canonEta N omega)) ≠ ⊤) ∧
        Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))} with hSdef
    have hSmem : ∀ᵐ omega ∂P, omega ∈ S := by
      filter_upwards [heta, hprim, lfgc_draw_sure model, hInfra.2] with omega h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    have hSnull : P Sᶜ = 0 := MeasureTheory.ae_iff.mp hSmem
    set Carrier : Set (BilateralField d) := (toMeasurable P Sᶜ)ᶜ with hCarrierDef
    have hCarrierMeas : MeasurableSet Carrier := (measurableSet_toMeasurable P Sᶜ).compl
    have hCarrierNull : P Carrierᶜ = 0 := by
      rw [hCarrierDef, compl_compl, measure_toMeasurable]
      exact hSnull
    have hCarrierSubS : Carrier ⊆ S := by
      have h1 : Sᶜ ⊆ toMeasurable P Sᶜ := subset_toMeasurable P Sᶜ
      have h2 := Set.compl_subset_compl.mpr h1
      rw [compl_compl] at h2
      exact h2
    have hC1 : ∀ omega ∈ Carrier, ∀ (N i : ℕ) (x : SpatialCoordinates d),
        eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x) :=
      fun omega homega => (hCarrierSubS homega).1
    have hC2 : ∀ omega ∈ Carrier, ∀ N, primitive_scores d model sigma eps (eta N omega)
        (fun m z => F N m z omega) (fun m z => Praw N m z omega)
        (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
        (fun m z => Z N m z omega) (fun m z => rawGood N m z omega) :=
      fun omega homega => (hCarrierSubS homega).2.1
    have hClat : ∀ omega ∈ Carrier, ∀ (N k : ℕ) (z' : Fin d → ℤ),
        (∑' j : ℕ, _root_.SubdiffusiveProcess.Paper.aux_psf_Dmaj4 (k + 1) (fun i => (z' i : ℝ)) j
          (_root_.SubdiffusiveProcess.Paper.aux_lfgc_layer_tail_canonEta N omega)) ≠ ⊤ :=
      fun omega homega => (hCarrierSubS homega).2.2.1
    have hC4 : ∀ omega ∈ Carrier, Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)) :=
      fun omega homega => (hCarrierSubS homega).2.2.2
    have hC3 : ∀ omega ∈ Carrier, ∀ (N n : ℕ) (y : SpatialCoordinates d), Draw N n y omega ≠ ⊤ :=
      fun omega homega => lfgc_draw_carrier model sigma eps hsigma.1 eta F Praw Rraw Draw Z rawGood
        omega (hC1 omega homega) (hC2 omega homega) (hClat omega homega)
    let RHS : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop :=
      fun m k z omega =>
        let N := m + k
        let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
        let rootSide : Fin en × Fin ns → ℝ :=
          fun U => r * (3 : ℝ) ^ enDepth U.1
        let rootCentre : Fin en × Fin ns → SpatialCoordinates d :=
          fun U => z + rootSide U • shift U.2
        let centres : (Fin en × Fin ns) → ℕ → Finset (SpatialCoordinates d) :=
          fun U D => by
            classical
            exact ((Finset.univ : Finset (Fin en × Fin ns)).image rootCentre) ∪
              ((Finset.univ : Finset (Fin nc)).image (fun c => z + r • cmpShift c)) ∪
              ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
                (descendantCenter 1 (rootCentre U) (rootSide U) D))
        let pre : (Fin en × Fin ns) → ℕ → SpatialCoordinates d → Finset ℤ :=
          fun U D _ =>
            Finset.Icc ((k : ℤ) - enDepth U.1 - buffer)
              (min (N : ℤ) ((k : ℤ) - enDepth U.1 + D + buffer))
        let Zphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
          if 0 ≤ (N : ℤ) - j then Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om else 0
        let Dphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
          if 0 ≤ (N : ℤ) - j then
            (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om).toReal else 0
        (∀ e D, ∀ w ∈ centres e D, ∀ j ∈ pre e D w,
          0 ≤ (N : ℤ) - j →
            Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega ≠ ⊤) ∧
        (∀ t : Fin ns,
          F N (m + enDepth padRoot)
            ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 1 ∧
          Praw N (m + enDepth padRoot)
            ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 12) ∧
        ∀ infrared : Bool,
          let Hused := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
          let kappa := fun J : ℕ =>
            Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
          let retained := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
            if 0 ≤ j then ∑ i ∈ Finset.Ico (0 : ℤ) j, om (-i) w
            else -∑ i ∈ Finset.Ico j (0 : ℤ), om (-i) w
          let reference := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
            kappa ((N : ℤ) - j).toNat / kappa N *
              Real.exp (Hused om w + retained j w om)
          let rEn := rootSide
          let zEn := rootCentre
          let hrEn : ∀ U : Fin en × Fin ns, 0 < rEn U := by
            intro U; dsimp [rEn, rootSide, r]; positivity
          let aEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
            cutoffPositiveCoefficient model Hused om N (zEn U) (hrEn U)
          let refEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
            reference ((k : ℤ) - enDepth U.1) (zEn U) om
          let zCmp := fun c : Fin nc => z + r • cmpShift c
          let rCmp := fun c : Fin nc => r * (3 : ℝ) ^ (-(cmpDepth c : ℤ))
          let hrCmp : ∀ c, 0 < rCmp c := by intro c; dsimp [rCmp, r]; positivity
          let aCmp := fun (c : Fin nc) (om : BilateralField d) =>
            cutoffPositiveCoefficient model Hused om N (zCmp c) (hrCmp c)
          let refCmp := fun (c : Fin nc) (om : BilateralField d) =>
            reference ((k : ℤ) + cmpDepth c) (zCmp c) om
          good_event (BilateralField d) d (Fin en × Fin ns) (Fin en × Fin ns) (Fin nc)
            centres pre Zphys Dphys
            (fun e om => I.lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
            (fun e om => I.Lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
            (fun e om i j =>
              (Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                ((I.chart (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e)).coeffOn
                  (Homogenization.originCube d 0))) i j / refEn e om)
            (fun c om => I.err (zCmp c) (rCmp c) (hrCmp c) (aCmp c om)
              (zCmp c) (rCmp c) (refCmp c om) sigma 2)
            (fun c om => reference (k : ℤ) z om / refCmp c om)
            chosen ((2 * (d : ℝ))⁻¹) ((en * ns + nc + 1 : ℕ) : ℝ) cell lam lamDet eps cdet k0 omega
    let Good : ℕ → ℕ → SpatialCoordinates d → Set (BilateralField d) :=
      fun m k z => Carrierᶜ ∪ (Carrier ∩ {omega | RHS m k z omega})
    refine ⟨Good, Carrier, hCarrierMeas, hCarrierNull, ?_, ?_, fun omega homega =>
      ⟨hC1 omega homega, hC2 omega homega, hC4 omega homega, hC3 omega homega⟩⟩
    · intro m k z omega hmem
      show (omega ∈ Carrierᶜ ∪ (Carrier ∩ {omega | RHS m k z omega})) ↔ RHS m k z omega
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, mem_ofPred_eq]
      tauto
    · intro m k z
      have hCondMeas : MeasurableSet (Carrier ∩ {omega | RHS m k z omega}) := by
        have hRHS : ∀ omega, RHS m k z omega = aux_lem_finite_good_cell_rhs d I model H sigma eps cell
            lam lamDet cdet en nc ns padRoot chosen enDepth cmpDepth cmpShift shift buffer k0
            F Praw Draw Z m k z omega := fun _ => rfl
        obtain ⟨hηmeas, hηeq⟩ := aux_condmeas_eta_canon (d := d) (m + k)
        set η : BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d := fun omega i =>
          aux_lem_crossing_unforget (SubdiffusiveProcess.layerScaling d ((m + k : ℕ) : ℤ)
            (omega ((i : ℤ) - ((m + k : ℕ) : ℤ)))) with hηdef
        -- the primitive-score formulas at the canonical sample (clauses (2)-(5),(7))
        let Fc : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal := fun _ n y om =>
          sSup {v : ENNReal | ∃ j : ℕ,
            v = ENNReal.ofReal ((3 : ℝ) ^ (-(sigma * (j : ℝ) / 8))) *
              ∑ i ∈ Finset.Icc (n - j) (n + j),
                sSup {w : ENNReal | ∃ x : SpatialCoordinates d, x ∈ SubdiffusiveProcess.CoarseGrainingVocab.translatedCube d (n + 1 + j) y ∧
                  w = ENNReal.ofReal |(|η om i x| + (3 : ℝ) ^ (i : ℝ) *
                    Homogenization.euclideanNorm (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (η om i) x))|}}
        let Pc : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal := fun _ n y om =>
          sSup {v : ENNReal | ∃ j : ℕ,
            v = ENNReal.ofReal ((3 : ℝ) ^ (-(sigma * (j : ℝ) / 8))) *
              sSup {w : ENNReal | ∃ x : SpatialCoordinates d, x ∈ SubdiffusiveProcess.CoarseGrainingVocab.translatedCube d (n + 1 + j) y ∧
                w = (∏ i ∈ Finset.Icc (n - j) (n + j), ENNReal.ofReal (Real.exp |η om i x|)) +
                    sSup {u : ENNReal | ∃ K : ℕ,
                      u = ∏ i ∈ Finset.Icc (n + j) (n + j + K),
                        ENNReal.ofReal (Real.exp (4 * |η om i x - η om i y|))}}}
        let Rc : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal := fun _ n y om =>
          sSup {v : ENNReal | ∃ j l : ℕ, j ≤ n ∧ l + 2 ≤ j ∧ ∃ x : SpatialCoordinates d,
            SubdiffusiveProcess.CoarseGrainingVocab.OnTriadicGrid l (x - y) ∧
            x - y ∈ SubdiffusiveProcess.CoarseGrainingVocab.cube d j \ SubdiffusiveProcess.CoarseGrainingVocab.cube d (j - 1) ∧
            v = ENNReal.ofReal ((3 : ℝ) ^ (-(sigma * ((n : ℝ) - (l : ℝ)) / 8))) *
              sSup {u : ENNReal | ∃ e : SpatialCoordinates d, Homogenization.vecNormSq e = 1 ∧
                u = ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.section6Response model l l (η om) x e)}}
        let Dc : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal := fun _ n y om =>
          sSup {v : ENNReal | ∃ j l : ℕ, j ≤ n ∧ l ≤ n ∧ l + 2 ≤ j ∧ ∃ x : SpatialCoordinates d,
              SubdiffusiveProcess.CoarseGrainingVocab.OnTriadicGrid l (x - y) ∧
              x - y ∈ SubdiffusiveProcess.CoarseGrainingVocab.cube d j \ SubdiffusiveProcess.CoarseGrainingVocab.cube d (j - 1) ∧
              v = ENNReal.ofReal ((3 : ℝ) ^ (-(sigma / 2) * ((n : ℝ) - (l : ℝ)))) *
                (min (sSup {u : ENNReal | ∃ e : SpatialCoordinates d, Homogenization.vecNormSq e = 1 ∧
                  u = ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.section6Response model l l (η om) x e)}) 1) ^
                  (1 / 2 : ℝ)} +
            sSup {v : ENNReal | ∃ j : ℕ, j ≤ n ∧
              v = ENNReal.ofReal ((3 : ℝ) ^ (-(sigma / 8) * ((n : ℝ) - (j : ℝ)))) *
                sSup {w : ENNReal | ∃ x : SpatialCoordinates d, x ∈ SubdiffusiveProcess.CoarseGrainingVocab.translatedCube d n y ∧
                  w = ENNReal.ofReal |SubdiffusiveProcess.CoarseGrainingVocab.shellBlock n j (η om) x|}} +
            ENNReal.ofReal ((3 : ℝ) ^ (-(sigma / 8) * (n : ℝ))) *
              sSup {w : ENNReal | ∃ x : SpatialCoordinates d, x ∈ SubdiffusiveProcess.CoarseGrainingVocab.translatedCube d n y ∧
                w = ENNReal.ofReal |η om 0 x|} +
            ∑' j : ℕ, (if n ≤ j then
              ENNReal.ofReal ((3 : ℝ) ^ n) *
                sSup {w : ENNReal | ∃ x : SpatialCoordinates d, x ∈ SubdiffusiveProcess.CoarseGrainingVocab.translatedCube d n y ∧
                  w = ENNReal.ofReal |Homogenization.euclideanNorm
                    (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (η om j) x)|}
              else 0)
        let Zc : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ := fun N n y om =>
          (min (1 : ENNReal) ((Fc N n y om - ENNReal.ofReal (eps / 2)) /
            ENNReal.ofReal (eps - eps / 2))).toReal +
          (min (1 : ENNReal) ((Pc N n y om - ENNReal.ofReal 6) / ENNReal.ofReal (12 - 6))).toReal +
          (min (1 : ENNReal) ((Rc N n y om - ENNReal.ofReal (eps ^ 2 / 4)) /
            ENNReal.ofReal (eps ^ 2 - eps ^ 2 / 4))).toReal
        have hscores : ∀ om ∈ Carrier,
            (∀ n y, F (m + k) n y om = Fc (m + k) n y om) ∧
            (∀ n y, Praw (m + k) n y om = Pc (m + k) n y om) ∧
            (∀ n y, Draw (m + k) n y om = Dc (m + k) n y om) ∧
            (∀ n y, Z (m + k) n y om = Zc (m + k) n y om) := by
          intro om hom
          obtain ⟨heta_om, hprim_om, -, -⟩ := hCarrierSubS hom
          have hη_om : eta (m + k) om = η om :=
            hηeq (eta (m + k)) om (fun i y => heta_om (m + k) i y)
          have hp := hprim_om (m + k)
          rw [hη_om] at hp
          obtain ⟨-, -, -, -, h2, h3, h4, h5, -, h7, -⟩ := hp
          have hF2 : ∀ n y, F (m + k) n y om = Fc (m + k) n y om := fun n y => h2 n y
          have hP2 : ∀ n y, Praw (m + k) n y om = Pc (m + k) n y om := fun n y => h3 n y
          have hR2 : ∀ n y, Rraw (m + k) n y om = Rc (m + k) n y om := fun n y => h4 n y
          refine ⟨hF2, hP2, fun n y => h5 n y, fun n y => ?_⟩
          refine ((h7 n y).1).trans ?_
          show (min (1 : ENNReal) ((F (m + k) n y om - ENNReal.ofReal (eps / 2)) /
              ENNReal.ofReal (eps - eps / 2))).toReal +
            (min (1 : ENNReal) ((Praw (m + k) n y om - ENNReal.ofReal 6) /
              ENNReal.ofReal (12 - 6))).toReal +
            (min (1 : ENNReal) ((Rraw (m + k) n y om - ENNReal.ofReal (eps ^ 2 / 4)) /
              ENNReal.ofReal (eps ^ 2 - eps ^ 2 / 4))).toReal = _
          rw [hF2, hP2, hR2]
        have hset : Carrier ∩ {omega | RHS m k z omega} =
            Carrier ∩ {omega | aux_lem_finite_good_cell_rhs d I model H sigma eps cell lam lamDet
              cdet en nc ns padRoot chosen enDepth cmpDepth cmpShift shift buffer k0
              Fc Pc Dc Zc m k z omega} := by
          ext om
          simp only [Set.mem_inter_iff, mem_ofPred_eq]
          constructor
          · rintro ⟨hC, hR⟩
            obtain ⟨hF', hP', hD', hZ'⟩ := hscores om hC
            exact ⟨hC, (aux_lem_finite_good_cell_rhs_congr d I model H sigma eps cell lam lamDet cdet
              en nc ns padRoot chosen enDepth cmpDepth cmpShift shift buffer k0 F Praw Draw Fc Pc Dc
              Z Zc m k z om hF' hP' hD' hZ').1 ((hRHS om) ▸ hR)⟩
          · rintro ⟨hC, hR⟩
            obtain ⟨hF', hP', hD', hZ'⟩ := hscores om hC
            exact ⟨hC, (hRHS om).symm ▸ (aux_lem_finite_good_cell_rhs_congr d I model H sigma eps
              cell lam lamDet cdet en nc ns padRoot chosen enDepth cmpDepth cmpShift shift buffer k0
              F Praw Draw Fc Pc Dc Z Zc m k z om hF' hP' hD' hZ').2 hR⟩
        rw [hset]
        refine hCarrierMeas.inter (aux_lem_finite_good_cell_rhs_meas hd I model H sigma eps cell lam
          lamDet cdet en nc ns padRoot chosen enDepth cmpDepth cmpShift shift buffer k0 hInfra.1
          ⟨hsigma.1, hsigma.2.le⟩ Fc Pc Dc Zc m k z ?_ ?_ ?_ ?_)
        · intro n y
          exact (aux_lem_prefix_limit_actual_Fsc_meas sigma n y).comp hηmeas
        · intro n y
          exact (aux_lem_prefix_limit_actual_Psc_meas sigma n y).comp hηmeas
        · intro n y
          exact ((((aux_lem_prefix_limit_actual_Dsc_first_meas model sigma n y).add
            (aux_condmeas_Dsc_block_meas sigma n y)).add (aux_condmeas_Dsc_base_meas sigma n y)).add
            (aux_condmeas_Dsc_grad_meas n y)).comp hηmeas
        · intro n y
          exact (aux_condmeas_Z_meas model sigma eps n y).comp hηmeas
      have hTail : ∃ W : ℕ+ → Set (BilateralField d),
          (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
            ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).domRestrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
                C(SpatialCoordinates d, ℝ)))] (W h)) ∧
          (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-rate * (h : ℝ)))) ∧
          Carrier ∩ {omega | ¬ RHS m k z omega} ⊆ ⋃ h : ℕ+, W h := by
        obtain ⟨W, hWmeas, hWprob, hWcover⟩ :=
          hlfgc model hdelta response hresponse regularity iteration H hInfra eta heta
            F Praw Rraw Draw Z rawGood hprim Carrier hCarrierNull hC1 hC2 hC3 hC4 m k z
        refine ⟨W, hWmeas, hWprob, ?_⟩
        rintro omega ⟨homega, hnotRHS⟩
        refine hWcover ⟨homega, ?_⟩
        rintro ⟨hD, hFtest, hP1', hnH, hn0⟩
        exact hnotRHS (aux_lem_finite_good_cell_rhs_of_parts hd I model H sigma eps cell lam
          lamDet cdet en nc ns padRoot chosen enDepth cmpDepth cmpShift shift buffer k0 F Praw
          Draw Z m k z omega ⟨hsigma.1, hsigma.2.le⟩ heps.1 hcell hcellSmall hlam hlamlt hlamDet1
          hcdet self selfShift hself hselfShift hcmpShift hcmpDepth hθ0pos.le hθ0_4d hθ0_epscdet
          hD hFtest hP1' hnH hn0)
      obtain ⟨W, hWmeas, hWprob, hWcover⟩ := hTail
      refine ⟨?_, W, hWmeas, hWprob, ?_⟩
      · show MeasurableSet (Carrierᶜ ∪ (Carrier ∩ {omega | RHS m k z omega}))
        exact hCarrierMeas.compl.union hCondMeas
      · have hgc : (Good m k z)ᶜ = Carrier ∩ {omega | ¬ RHS m k z omega} := by
          show (Carrierᶜ ∪ (Carrier ∩ {omega | RHS m k z omega}))ᶜ =
            Carrier ∩ {omega | ¬ RHS m k z omega}
          ext omega
          simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff, mem_ofPred_eq]
          tauto
        rw [hgc]
        exact hWcover

/- The response estimate exports a disorder threshold; unrestricted constants would permit the counterexample `Cfin = 0`. The estimate is proved inside `gap_main`. -/


/-- Repaired `h_constants`: `sigma` now depends on `beta` and is small enough for
`in_deterministic`'s own `s ≤ 1/32` applicability bound AND strictly below
`lem_extension`'s required ellipticity exponent `(beta - 1/2)/4` (with room to spare,
since hDet's Clause 2 needs strict `<`). -/
theorem aux_lem_finite_good_cell_h_constants_v2 (H1 : ℕ) (hH1 : 0 < H1)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ sigma delta0 Cfin Aext pad : ℝ,
      sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ sigma ≤ 1 / 32 ∧ sigma < (beta - 1 / 2) / 4 ∧
      0 < delta0 ∧ 0 < Cfin ∧ 0 < Aext ∧
      ∃ _hpad : 1 < pad, pad < (3 : ℝ) ^ H1 ∧ pad ≤ 3 := by
  obtain ⟨delta0, Cfin, Aext, pad, hd, hc, ha, hpad, hpadL, hpadD⟩ :=
    aux_lem_finite_good_cell_choose_second_block ((3 : ℝ) ^ H1)
      (aux_lem_finite_good_cell_L_gt_one H1 hH1) 1 (by norm_num)
  refine ⟨min (1 / 32) ((beta - 1 / 2) / 8), delta0, Cfin, Aext, pad,
    ⟨?_, ?_⟩, ?_, ?_, hd, hc, ha, hpad, hpadL, ?_⟩
  · exact lt_min (by norm_num) (by linarith [hbeta.1])
  · calc min (1 / 32 : ℝ) ((beta - 1 / 2) / 8) ≤ 1 / 32 := min_le_left _ _
    _ < 1 := by norm_num
  · exact min_le_left _ _
  · calc min (1 / 32 : ℝ) ((beta - 1 / 2) / 8) ≤ (beta - 1 / 2) / 8 := min_le_right _ _
    _ < (beta - 1 / 2) / 4 := by linarith [hbeta.1]
  · simpa using hpadD

/-- A choice of geometric constants with pad = 2. For positive H1 and
1/2 < beta < 1, the conclusion includes 2 ≤ pad together with all the
displayed positivity and range bounds. -/
theorem aux_lem_finite_good_cell_h_constants_v3 (H1 : ℕ) (hH1 : 0 < H1)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ sigma delta0 Cfin Aext pad : ℝ,
      sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ sigma ≤ 1 / 32 ∧ sigma < (beta - 1 / 2) / 4 ∧
      0 < delta0 ∧ 0 < Cfin ∧ 0 < Aext ∧
      ∃ _hpad : 1 < pad, pad < (3 : ℝ) ^ H1 ∧ pad ≤ 3 ∧ (2 : ℝ) ≤ pad := by
  have hL3 : (3 : ℝ) ≤ (3 : ℝ) ^ H1 := by
    calc (3 : ℝ) = (3 : ℝ) ^ 1 := (pow_one 3).symm
    _ ≤ (3 : ℝ) ^ H1 := pow_le_pow_right₀ (by norm_num) hH1
  refine ⟨min (1 / 32) ((beta - 1 / 2) / 8), 1, 1, 1, 2,
    ⟨?_, ?_⟩, ?_, ?_, one_pos, one_pos, one_pos, by norm_num, by linarith, by norm_num,
    le_refl 2⟩
  · exact lt_min (by norm_num) (by linarith [hbeta.1])
  · calc min (1 / 32 : ℝ) ((beta - 1 / 2) / 8) ≤ 1 / 32 := min_le_left _ _
    _ < 1 := by norm_num
  · exact min_le_left _ _
  · calc min (1 / 32 : ℝ) ((beta - 1 / 2) / 8) ≤ (beta - 1 / 2) / 8 := min_le_right _ _
    _ < (beta - 1 / 2) / 4 := by linarith [hbeta.1]

open Homogenization.Book.Ch02 (LambdaSq LambdaSq_antitone MultiscaleExponent) in
/-- hDet Clause 2 ("trace/Dirichlet response") of `aux_lem_finite_good_cell_gap_main`'s
`hDet` obligation, given an ellipticity upper bound at some `outerSigma` strictly below the
exponent `lem_extension` actually needs, transferred via `LambdaSq_antitone`. `Aext` is
delivered as an external constant so the caller can weaken it against whatever value
`h_constants_v2` independently supplies. -/
theorem aux_lem_finite_good_cell_clause2_of_ellipticity
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_Ext : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_S : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    -- `C`/`hCpos`/`hbh` are now taken as explicit
    -- hypotheses (the `aux_lem_extension_boundary_half` witness), not re-derived internally, so
    -- the caller can reuse the SAME `C` it already fixed `Aext := C * cell⁻¹` against early in
    -- `gap_main` (before `model`) — avoiding a second, non-defeq `obtain` on the same `∃`.
    (C : ℝ) (hCpos : 0 < C)
    (hbh : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr)) (G : SpatialCoordinates d → ℝ)
        (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        (((b : SobolevData (centeredCube z r hr)).1) =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] G) →
        dirichletResponse (killedResponseSpace hP) a b ≤
          C * I.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ beta * holderSeminorm beta (frontier (centeredCube z r hr :
              Set (SpatialCoordinates d))) G) ^ 2)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (a : PositiveCoefficient (centeredCube z r hr))
    (outerSigma s cell : ℝ) (houter : outerSigma ∈ Set.Ioc (0 : ℝ) 1)
    (houterSmall : outerSigma < (beta - 1 / 2) / 4) (hcell : 0 < cell) (hs : 0 < s)
    (hEll : I.Lam z r hr a z r outerSigma 2 ≤ cell⁻¹ * s) :
    ∃ Aext : ℝ, Aext = C * cell⁻¹ ∧ 0 < Aext ∧
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (b : weakSobolevGraph (centeredCube z r hr)) (G : SpatialCoordinates d → ℝ),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        (((b : SobolevData (centeredCube z r hr)).1) =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] G) →
        ∀ c : ℝ,
        dirichletResponse (killedResponseSpace hP) a b ≤
          Aext * r ^ ((d : ℝ) - 2) * s *
            (cAlphaNorm beta
              (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
              (fun x => G (z + r • x) - c)) ^ 2 := by
  refine ⟨C * cell⁻¹, rfl, mul_pos hCpos (inv_pos.mpr hcell), ?_⟩
  intro hP b G hGcont hGhol htie c
  have htarget : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨by linarith [hbeta.1], by linarith [hbeta.2]⟩
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)) := Set.Subset.refl _
  have hLamEq1 := I.Lam_eq z r hr a z r hr hsub outerSigma houter (2 : ℝ≥0∞) (by norm_num)
  have hLamEq2 := I.Lam_eq z r hr a z r hr hsub ((beta - 1 / 2) / 4) htarget (2 : ℝ≥0∞) (by norm_num)
  have h2ne : ¬ (2 : ℝ≥0∞) = ⊤ := by norm_num
  have h2real : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [ite_eq_right h2ne, h2real] at hLamEq1 hLamEq2
  have hantitone : LambdaSq (Homogenization.originCube d 0) ((beta - 1 / 2) / 4)
      (MultiscaleExponent.finite 2) (I.chart z r hr a z r) ≤
      LambdaSq (Homogenization.originCube d 0) outerSigma
        (MultiscaleExponent.finite 2) (I.chart z r hr a z r) :=
    LambdaSq_antitone (q := MultiscaleExponent.finite 2) (Homogenization.originCube d 0)
      (I.chart z r hr a z r) houter.1 houterSmall (by norm_num)
  have hmono : I.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 ≤ I.Lam z r hr a z r outerSigma 2 := by
    rw [hLamEq1, hLamEq2]; exact hantitone
  have hLamBound : I.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 ≤ cell⁻¹ * s := hmono.trans hEll
  have hrd : (0:ℝ) ≤ r ^ ((d : ℝ) - 2) := Real.rpow_nonneg hr.le _
  have hbase := hbh z r hr hr1 hP a G b hGcont hGhol htie
  set Sq : Set (SpatialCoordinates d) := frontier (centeredCube z r hr : Set (SpatialCoordinates d))
    with hSqdef
  have hbase2 : dirichletResponse (killedResponseSpace hP) a b ≤
      C * (cell⁻¹ * s) * r ^ ((d : ℝ) - 2) * (r ^ beta * holderSeminorm beta Sq G) ^ 2 := by
    refine hbase.trans ?_
    have hrest : (0:ℝ) ≤ r ^ ((d:ℝ)-2) * (r ^ beta * holderSeminorm beta Sq G) ^ 2 :=
      mul_nonneg hrd (sq_nonneg _)
    calc C * I.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
        (r ^ beta * holderSeminorm beta Sq G) ^ 2
        = C * (I.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 *
            (r ^ ((d:ℝ)-2) * (r ^ beta * holderSeminorm beta Sq G) ^ 2)) := by ring
      _ ≤ C * ((cell⁻¹ * s) * (r ^ ((d:ℝ)-2) * (r ^ beta * holderSeminorm beta Sq G) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLamBound hrest) hCpos.le
      _ = C * (cell⁻¹ * s) * r ^ ((d : ℝ) - 2) * (r ^ beta * holderSeminorm beta Sq G) ^ 2 := by
          ring
  set unitFrontier : Set (SpatialCoordinates d) :=
    frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
    with huFdef
  have hTeq : (fun x => G (z + r • x)) = (fun x => G (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x)) := by
    funext x
    congr 1
    funext i
    simp [_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation, smul_eq_mul]
  have hdil : r ^ beta * holderSeminorm beta Sq G =
      holderSeminorm beta unitFrontier (fun x => G (z + r • x)) := by
    rw [hTeq, hSqdef, huFdef]
    exact (aux_lem_extension_holderSeminorm_dilation z r hr beta G).symm
  have hshift : holderSeminorm beta unitFrontier (fun x => G (z + r • x)) =
      holderSeminorm beta unitFrontier (fun x => G (z + r • x) - c) := by
    unfold holderSeminorm
    rw [SubdiffusiveProcess.FiniteStopping.holderRatioSet_sub_const]
  have hlhs_nonneg : (0:ℝ) ≤ r ^ beta * holderSeminorm beta Sq G := by
    rw [hdil, hshift]
    exact aux_lem_extension_holderSeminorm_nonneg beta unitFrontier _
  have hle : r ^ beta * holderSeminorm beta Sq G ≤
      cAlphaNorm beta unitFrontier (fun x => G (z + r • x) - c) := by
    rw [hdil, hshift]
    unfold cAlphaNorm
    have h0 : (0:ℝ) ≤
        sSup {v : ℝ | ∃ x ∈ unitFrontier, v = |(fun x => G (z + r • x) - c) x|} :=
      SubdiffusiveProcess.FiniteStopping.sSup_nonneg_of_forall_nonneg
        (by rintro v ⟨x, -, rfl⟩; exact abs_nonneg _)
    linarith
  have hsq : (r ^ beta * holderSeminorm beta Sq G) ^ 2 ≤
      (cAlphaNorm beta unitFrontier (fun x => G (z + r • x) - c)) ^ 2 :=
    pow_le_pow_left₀ hlhs_nonneg hle 2
  refine hbase2.trans ?_
  have hfin : (0:ℝ) ≤ C * (cell⁻¹ * s) * r ^ ((d:ℝ)-2) := by positivity
  calc C * (cell⁻¹ * s) * r ^ ((d : ℝ) - 2) * (r ^ beta * holderSeminorm beta Sq G) ^ 2
      ≤ C * (cell⁻¹ * s) * r ^ ((d : ℝ) - 2) *
          (cAlphaNorm beta unitFrontier (fun x => G (z + r • x) - c)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hfin
    _ = C * cell⁻¹ * r ^ ((d : ℝ) - 2) * s *
          (cAlphaNorm beta unitFrontier (fun x => G (z + r • x) - c)) ^ 2 := by ring

/-- Clause 2 ("trace/Dirichlet response") of `hDet`, Takes the ellipticity fact `h10` (good_event's clause 10, the `∀ e, cell ≤ ellipMin e ω ∧
ellipMax e ω ≤ cell⁻¹` conjunct, in its own self-contained catalogue-formula form) plus the
`self`/`selfShift` root identification data, and does the whole derivation: extract the bound at
`e := (self, selfShift)`, transport it to `z, r` via `hself`/`hselfShift`, clear the denominator,
and apply `aux_lem_finite_good_cell_clause2_of_ellipticity`. -/
theorem aux_lem_finite_good_cell_clause2_extract
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I) (Sobolev : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta1 : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (CExt : ℝ) (hCExtPos : 0 < CExt)
    (hbhExt : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr)) (G : SpatialCoordinates d → ℝ)
        (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        (((b : SobolevData (centeredCube z r hr)).1) =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] G) →
        dirichletResponse (killedResponseSpace hP) a b ≤
          CExt * I.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ beta * holderSeminorm beta (frontier (centeredCube z r hr :
              Set (SpatialCoordinates d))) G) ^ 2)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (omega : BilateralField d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ))
    (m k : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hrle1 : r ≤ 1)
    (sigma cell : ℝ) (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) (hsigmaEll : sigma < (beta - 1 / 2) / 4)
    (hcell : 0 < cell)
    (en ns : ℕ) (self : Fin en) (selfShift : Fin ns)
    (enDepth : Fin en → ℕ) (shift : Fin ns → SpatialCoordinates d)
    (hself : enDepth self = 0) (hselfShift : shift selfShift = 0)
    (h10 :
      let kappa := fun J : ℕ =>
        Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
      let retained := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
        if 0 ≤ j then ∑ i ∈ Finset.Ico (0 : ℤ) j, om (-i) w
        else -∑ i ∈ Finset.Ico j (0 : ℤ), om (-i) w
      let reference := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
        kappa ((m + k : ℤ) - j).toNat / kappa (m + k) * Real.exp (Hused om w + retained j w om)
      ∀ e : Fin en × Fin ns,
        let rS := r * (3 : ℝ) ^ enDepth e.1
        let rC := z + rS • shift e.2
        cell ≤ I.lam rC rS (by positivity) (cutoffPositiveCoefficient model Hused omega (m + k) rC
              (by positivity)) rC rS sigma 2 / reference ((k : ℤ) - (enDepth e.1 : ℤ)) rC omega ∧
          I.Lam rC rS (by positivity) (cutoffPositiveCoefficient model Hused omega (m + k) rC
              (by positivity)) rC rS sigma 2 / reference ((k : ℤ) - (enDepth e.1 : ℤ)) rC omega ≤
            cell⁻¹) :
    ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (b : weakSobolevGraph (centeredCube z r hr)) (G : SpatialCoordinates d → ℝ),
      ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      (((b : SobolevData (centeredCube z r hr)).1) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] G) →
      ∀ c : ℝ,
      dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient model Hused omega (m + k) z hr) b ≤
        CExt * cell⁻¹ * r ^ ((d : ℝ) - 2) *
          (Real.exp (((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom model m /
            (Real.exp (((m + k : ℕ) + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom model (m + k)) *
              Real.exp (Hused omega z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)) *
          (cAlphaNorm beta
            (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
            (fun x => G (z + r • x) - c)) ^ 2 := by
  have hEllMax := (h10 (self, selfShift)).2
  dsimp only at hEllMax
  have hretained_eq : (∑ i ∈ Finset.Ico (0 : ℤ) (k : ℤ), omega (-i) z) =
        ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z := by
    rw [show (Finset.Ico (0 : ℤ) (k : ℤ)) = (Finset.range k).map
        ⟨(Nat.cast : ℕ → ℤ), Nat.cast_injective⟩ by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨h0, hj⟩
        exact ⟨x.toNat, by omega, by omega⟩
      · rintro ⟨y, hy, rfl⟩
        omega]
    rw [Finset.sum_map]
    simp
  have hTransport : ∀ (z1 : SpatialCoordinates d) (r1 : ℝ) (hr1 : 0 < r1), z1 = z → r1 = r →
      I.Lam z1 r1 hr1 (cutoffPositiveCoefficient model Hused omega (m + k) z1 hr1) z1 r1 sigma 2 =
        I.Lam z r hr (cutoffPositiveCoefficient model Hused omega (m + k) z hr) z r sigma 2 := by
    intro z1 r1 hr1 hz hr'
    subst hz; subst hr'
    rfl
  have hrProof : r * (3 : ℝ) ^ enDepth self = r := by rw [hself]; simp
  have hzProof : z + (r * (3 : ℝ) ^ enDepth self) • shift selfShift = z := by
    rw [hselfShift]; simp
  rw [hTransport _ _ _ hzProof hrProof] at hEllMax
  rw [hzProof] at hEllMax
  have hkEq : (k : ℤ) - (enDepth self : ℤ) = (k : ℤ) := by rw [hself]; simp
  rw [hkEq] at hEllMax
  have hNkEq : (m : ℤ) + (k : ℤ) - (k : ℤ) = (m : ℤ) := by ring
  rw [hNkEq] at hEllMax
  have hkpos : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  simp only [Int.toNat_natCast, ite_eq_left hkpos, hretained_eq] at hEllMax
  have hden_pos : 0 < Real.exp (((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model m /
        (Real.exp (((m + k : ℕ) + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model (m + k)) *
      Real.exp (Hused omega z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z) := by
    have hkm : 0 < Real.exp (((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model m :=
      mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model m)
    have hkN : 0 < Real.exp (((m + k : ℕ) + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model (m + k) :=
      mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model (m + k))
    positivity
  rw [div_le_iff₀ hden_pos] at hEllMax
  have hEllCell : I.Lam z r hr (cutoffPositiveCoefficient model Hused omega (m + k) z hr) z r
      sigma 2 ≤ cell⁻¹ * (Real.exp (((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model m /
          (Real.exp (((m + k : ℕ) + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model (m + k)) *
        Real.exp (Hused omega z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)) := hEllMax
  obtain ⟨Aext', hAextEq, hAextPos', hConcl⟩ :=
    aux_lem_finite_good_cell_clause2_of_ellipticity d hd I Extension Sobolev beta hbeta1
      CExt hCExtPos hbhExt z r hr hrle1
      (cutoffPositiveCoefficient model Hused omega (m + k) z hr) sigma
      (Real.exp (((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model m /
          (Real.exp (((m + k : ℕ) + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model (m + k)) *
        Real.exp (Hused omega z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z))
      cell ⟨hsigma.1, hsigma.2.le⟩ hsigmaEll hcell hden_pos hEllCell
  rw [hAextEq] at hConcl
  exact hConcl



theorem aux_lfgc_below_osc_hpad_check
    (en ns : ℕ) (padRoot : Fin en) (selfShift : Fin ns)
    (enDepth : Fin en → ℕ) (shift : Fin ns → SpatialCoordinates d)
    (hpadDepth : enDepth padRoot = 1) (hselfShiftZero : shift selfShift = 0)
    (buffer : ℕ) (hbuffer : 0 < buffer)
    (r : ℝ) (z : SpatialCoordinates d) (N : ℕ)
    (omega : BilateralField d)
    (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (lam : ℝ)
    (pword : Fin 1 → OddGridIndex d 1)
    (hFin : ∀ (e : Fin en × Fin ns) (D : ℕ),
      ∀ w ∈ ((Finset.univ : Finset (Fin en × Fin ns)).image
              (fun U : Fin en × Fin ns => z + (r * (3 : ℝ) ^ enDepth U.1) • shift U.2))
            ∪ (∅ : Finset (SpatialCoordinates d))
            ∪ ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
                (descendantCenter 1 (z + (r * (3 : ℝ) ^ enDepth e.1) • shift e.2)
                  (r * (3 : ℝ) ^ enDepth e.1) D)),
        ∀ j ∈ Finset.Icc ((N : ℤ) - enDepth e.1 - buffer)
                (min (N : ℤ) ((N : ℤ) - enDepth e.1 + D + buffer)),
          0 ≤ (N : ℤ) - j → Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega ≠ ⊤)
    (hPrefix : ∀ (e : Fin en × Fin ns) (D : ℕ), (1 : ℕ) ≤ D →
      ∀ w ∈ ((Finset.univ : Finset (Fin en × Fin ns)).image
              (fun U : Fin en × Fin ns => z + (r * (3 : ℝ) ^ enDepth U.1) • shift U.2))
            ∪ (∅ : Finset (SpatialCoordinates d))
            ∪ ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
                (descendantCenter 1 (z + (r * (3 : ℝ) ^ enDepth e.1) • shift e.2)
                  (r * (3 : ℝ) ^ enDepth e.1) D)),
        (∑ j ∈ Finset.Icc ((N : ℤ) - enDepth e.1 - buffer)
                (min (N : ℤ) ((N : ℤ) - enDepth e.1 + D + buffer)),
          (if 0 ≤ (N : ℤ) - j then
            (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega).toReal else 0)) < lam * (D : ℝ)) :
    Draw N 0 (((3 : ℝ) ^ N) • descendantCenter 1 z (3 * r) 1 pword) omega ≠ ⊤ ∧
    (Draw N 0 (((3 : ℝ) ^ N) • descendantCenter 1 z (3 * r) 1 pword) omega).toReal ≤ lam := by
  have hU1 : (padRoot, selfShift).1 = padRoot := rfl
  have hU2 : (padRoot, selfShift).2 = selfShift := rfl
  have hrootSideU : r * (3 : ℝ) ^ enDepth (padRoot, selfShift).1 = 3 * r := by
    rw [hU1, hpadDepth]; ring
  have hrootCentreU : z + (3 * r) • shift (padRoot, selfShift).2 = z := by
    rw [hU2, hselfShiftZero]; simp
  set w : SpatialCoordinates d := descendantCenter 1 z (3 * r) 1 pword with hw
  have hwmem : w ∈
      ((Finset.univ : Finset (Fin en × Fin ns)).image
        (fun U : Fin en × Fin ns => z + (r * (3 : ℝ) ^ enDepth U.1) • shift U.2))
      ∪ (∅ : Finset (SpatialCoordinates d))
      ∪ ((Finset.univ : Finset (Fin 1 → OddGridIndex d 1)).image
          (descendantCenter 1
            (z + (r * (3 : ℝ) ^ enDepth (padRoot, selfShift).1) •
              shift (padRoot, selfShift).2)
            (r * (3 : ℝ) ^ enDepth (padRoot, selfShift).1) 1)) := by
    apply Finset.mem_union_right
    rw [hrootSideU, hrootCentreU]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ pword)
  have henD : (enDepth (padRoot, selfShift).1 : ℤ) = 1 := by
    rw [hU1, hpadDepth]; norm_num
  have hNmem : (N : ℤ) ∈ Finset.Icc
      ((N : ℤ) - enDepth (padRoot, selfShift).1 - buffer)
      (min (N : ℤ) ((N : ℤ) - enDepth (padRoot, selfShift).1 + (1 : ℕ) + buffer)) := by
    rw [henD]
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · have : (0 : ℤ) < (buffer : ℤ) := by exact_mod_cast hbuffer
      linarith
    · refine le_min (le_refl _) ?_
      have : (0 : ℤ) ≤ (buffer : ℤ) := by positivity
      push_cast
      linarith
  have hFinAt := hFin (padRoot, selfShift) 1 w hwmem N hNmem (by simp)
  have hPrefixAt := hPrefix (padRoot, selfShift) 1 (le_refl 1) w hwmem
  have hnonneg : ∀ j ∈ Finset.Icc
      ((N : ℤ) - enDepth (padRoot, selfShift).1 - buffer)
      (min (N : ℤ) ((N : ℤ) - enDepth (padRoot, selfShift).1 + (1 : ℕ) + buffer)),
      (0 : ℝ) ≤ if 0 ≤ (N : ℤ) - j then
        (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega).toReal else 0 := by
    intro j _
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_refl 0
  have hterm := Finset.single_le_sum hnonneg hNmem
  have hcond : (0 : ℤ) ≤ (N : ℤ) - (N : ℤ) := by omega
  have hsimp : ((N : ℤ) - (N : ℤ)).toNat = 0 := by simp
  rw [ite_eq_left hcond, hsimp] at hterm
  rw [hsimp] at hFinAt
  have hlt : (Draw N 0 (((3 : ℝ) ^ N) • w) omega).toReal < lam := by
    have hcombine := lt_of_le_of_lt hterm hPrefixAt
    simpa using hcombine
  exact ⟨hFinAt, hlt.le⟩

/-- Same as `aux_lfgc_below_osc_hpad_check` but with the word length left as a fresh variable
`n` (with `n = 1` as a side hypothesis) rather than the literal `1` — this is the shape actually
needed to instantiate `aux_in_deterministic_onestep_sub_osc`'s `hpad` field, whose word type is
the compound `Fin (N - k + 1)`, not `Fin 1` up to a defeq Lean will not find on its own (`N - k`
does not reduce for symbolic `N, k` even when a hypothesis gives `N = k`); using a fresh `n` lets
`subst` discharge the cast for free instead of fighting a dependent rewrite. -/
theorem aux_lfgc_below_osc_hpad_check_gen
    (en ns : ℕ) (padRoot : Fin en) (selfShift : Fin ns)
    (enDepth : Fin en → ℕ) (shift : Fin ns → SpatialCoordinates d)
    (hpadDepth : enDepth padRoot = 1) (hselfShiftZero : shift selfShift = 0)
    (buffer : ℕ) (hbuffer : 0 < buffer)
    (r : ℝ) (z : SpatialCoordinates d) (N : ℕ)
    (omega : BilateralField d)
    (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (lam : ℝ)
    (hFin : ∀ (e : Fin en × Fin ns) (D : ℕ),
      ∀ w ∈ ((Finset.univ : Finset (Fin en × Fin ns)).image
              (fun U : Fin en × Fin ns => z + (r * (3 : ℝ) ^ enDepth U.1) • shift U.2))
            ∪ (∅ : Finset (SpatialCoordinates d))
            ∪ ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
                (descendantCenter 1 (z + (r * (3 : ℝ) ^ enDepth e.1) • shift e.2)
                  (r * (3 : ℝ) ^ enDepth e.1) D)),
        ∀ j ∈ Finset.Icc ((N : ℤ) - enDepth e.1 - buffer)
                (min (N : ℤ) ((N : ℤ) - enDepth e.1 + D + buffer)),
          0 ≤ (N : ℤ) - j → Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega ≠ ⊤)
    (hPrefix : ∀ (e : Fin en × Fin ns) (D : ℕ), (1 : ℕ) ≤ D →
      ∀ w ∈ ((Finset.univ : Finset (Fin en × Fin ns)).image
              (fun U : Fin en × Fin ns => z + (r * (3 : ℝ) ^ enDepth U.1) • shift U.2))
            ∪ (∅ : Finset (SpatialCoordinates d))
            ∪ ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
                (descendantCenter 1 (z + (r * (3 : ℝ) ^ enDepth e.1) • shift e.2)
                  (r * (3 : ℝ) ^ enDepth e.1) D)),
        (∑ j ∈ Finset.Icc ((N : ℤ) - enDepth e.1 - buffer)
                (min (N : ℤ) ((N : ℤ) - enDepth e.1 + D + buffer)),
          (if 0 ≤ (N : ℤ) - j then
            (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega).toReal else 0)) < lam * (D : ℝ))
    (n : ℕ) (hn : n = 1) (pword : Fin n → OddGridIndex d 1) :
    Draw N 0 (((3 : ℝ) ^ N) • descendantCenter 1 z (3 * r) n pword) omega ≠ ⊤ ∧
    (Draw N 0 (((3 : ℝ) ^ N) • descendantCenter 1 z (3 * r) n pword) omega).toReal ≤ lam := by
  subst hn
  exact aux_lfgc_below_osc_hpad_check en ns padRoot selfShift enDepth shift hpadDepth
    hselfShiftZero buffer hbuffer r z N omega Draw lam pword hFin hPrefix

/-- Clause 1 of `gap_main` at one good cell, split out for the elaboration budget: the
good-event characterization read at the cell, on the pinned carrier, feeds
`lfgc_clause1_assembly` (eq:mfd-finite-good-holder). -/
theorem aux_lem_finite_good_cell_clause1_extract
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha sigma eps cell lam lamDet cdet Cfin delta1 : ℝ)
    (hLH : aux_lfgc_clause1_spec d I alpha sigma cell eps lam Cfin delta1)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (response : _root_.SubdiffusiveProcess.Paper.in_responses d model)
    (hdelta : model.delta ≤ delta1)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (en nc ns : ℕ) (self padRoot : Fin en) (chosen : Fin nc) (selfShift : Fin ns)
    (enDepth : Fin en → ℕ) (cmpDepth : Fin nc → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d)
    (shift : Fin ns → SpatialCoordinates d)
    (hself : enDepth self = 0) (hselfShift : shift selfShift = 0)
    (hpadDepth : enDepth padRoot = 1)
    (buffer k0 : ℕ) (hbuffer1 : buffer = 1) (hk01 : k0 = 1)
    (omega : BilateralField d)
    (hCar : (∀ (N i : ℕ) (x : SpatialCoordinates d),
        eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x)) ∧
      (∀ N, primitive_scores d model sigma eps (eta N omega)
        (fun m z => F N m z omega) (fun m z => Praw N m z omega)
        (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
        (fun m z => Z N m z omega) (fun m z => rawGood N m z omega)) ∧
      Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)) ∧
      (∀ (N n : ℕ) (y : SpatialCoordinates d), Draw N n y omega ≠ ⊤))
    (m k : ℕ) (z : SpatialCoordinates d) (infrared : Bool)
    (hGE :
      let N := m + k
      let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
      let rootSide : Fin en × Fin ns → ℝ :=
        fun U => r * (3 : ℝ) ^ enDepth U.1
      let rootCentre : Fin en × Fin ns → SpatialCoordinates d :=
        fun U => z + rootSide U • shift U.2
      let centres : (Fin en × Fin ns) → ℕ → Finset (SpatialCoordinates d) :=
        fun U D => by
          classical
          exact ((Finset.univ : Finset (Fin en × Fin ns)).image rootCentre) ∪
            ((Finset.univ : Finset (Fin nc)).image (fun c => z + r • cmpShift c)) ∪
            ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
              (descendantCenter 1 (rootCentre U) (rootSide U) D))
      let pre : (Fin en × Fin ns) → ℕ → SpatialCoordinates d → Finset ℤ :=
        fun U D _ =>
          Finset.Icc ((k : ℤ) - enDepth U.1 - buffer)
            (min (N : ℤ) ((k : ℤ) - enDepth U.1 + D + buffer))
      let Zphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
        if 0 ≤ (N : ℤ) - j then Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om else 0
      let Dphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
        if 0 ≤ (N : ℤ) - j then
          (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om).toReal else 0
      (∀ e D, ∀ w ∈ centres e D, ∀ j ∈ pre e D w,
        0 ≤ (N : ℤ) - j →
          Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega ≠ ⊤) ∧
      (∀ t : Fin ns,
        F N (m + enDepth padRoot)
          ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 1 ∧
        Praw N (m + enDepth padRoot)
          ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 12) ∧
      ∀ infrared : Bool,
        let Hused := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        let kappa := fun J : ℕ =>
          Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
        let retained := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
          if 0 ≤ j then ∑ i ∈ Finset.Ico (0 : ℤ) j, om (-i) w
          else -∑ i ∈ Finset.Ico j (0 : ℤ), om (-i) w
        let reference := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
          kappa ((N : ℤ) - j).toNat / kappa N *
            Real.exp (Hused om w + retained j w om)
        let rEn := rootSide
        let zEn := rootCentre
        let hrEn : ∀ U : Fin en × Fin ns, 0 < rEn U := by
          intro U; dsimp [rEn, rootSide, r]; positivity
        let aEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
          cutoffPositiveCoefficient model Hused om N (zEn U) (hrEn U)
        let refEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
          reference ((k : ℤ) - enDepth U.1) (zEn U) om
        let zCmp := fun c : Fin nc => z + r • cmpShift c
        let rCmp := fun c : Fin nc => r * (3 : ℝ) ^ (-(cmpDepth c : ℤ))
        let hrCmp : ∀ c, 0 < rCmp c := by intro c; dsimp [rCmp, r]; positivity
        let aCmp := fun (c : Fin nc) (om : BilateralField d) =>
          cutoffPositiveCoefficient model Hused om N (zCmp c) (hrCmp c)
        let refCmp := fun (c : Fin nc) (om : BilateralField d) =>
          reference ((k : ℤ) + cmpDepth c) (zCmp c) om
        good_event (BilateralField d) d (Fin en × Fin ns) (Fin en × Fin ns) (Fin nc)
          centres pre Zphys Dphys
          (fun e om => I.lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
          (fun e om => I.Lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
          (fun e om i j =>
            (Homogenization.Book.Ch02.sigmaCoarse
              (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
              ((I.chart (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e)).coeffOn
                (Homogenization.originCube d 0))) i j / refEn e om)
          (fun c om => I.err (zCmp c) (rCmp c) (hrCmp c) (aCmp c om)
            (zCmp c) (rCmp c) (refCmp c om) sigma 2)
          (fun c om => reference (k : ℤ) z om / refCmp c om)
          chosen ((2 * (d : ℝ))⁻¹) ((en * ns + nc + 1 : ℕ) : ℝ) cell lam lamDet eps cdet k0 omega)
    (H1 : ℕ) (zP : SpatialCoordinates d) (hLr : 0 < (3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ)))
    (hsub0 : Metric.closedBall z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2) ⊆
      (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr : Set (SpatialCoordinates d))) :
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), Measurable F → 0 ≤ Kf →
      (∀ x ∈ centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr, |F x| ≤ Kf) →
      ∀ u : weakSobolevGraph (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr),
        (∀ psi : killedSobolevGraph (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr),
          @sobolevCoefficientForm d (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr)
            (cutoffPositiveCoefficient model
              (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
              omega (m + k) zP hLr)
            (u : SobolevData (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr)) (psi : SobolevData (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr)) =
            ∫ x in (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr : Set (SpatialCoordinates d)),
              F x * (psi : SobolevData (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr)).1 x) →
        ∃ (U : SpatialCoordinates d → ℝ) (c : ℝ),
          ContinuousOn U (closedCube z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
            Set (SpatialCoordinates d)) ∧
          ((fun x => (u : SobolevData (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr)).1 x) =ᵐ[volume.restrict
            (centeredCube z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
              Set (SpatialCoordinates d))] U) ∧
          @IsHolderOn d alpha
            (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
            (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - c) ∧
          @cAlphaNorm d alpha
            (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
            (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - c) ≤
            Cfin * ((3 : ℝ) ^ (-(k : ℤ))) ^ (((2 : ℝ) - (d : ℝ)) / 2) *
                (Real.exp (((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom model m /
                  (Real.exp ((((m + k : ℕ) : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom model (m + k)) *
                  Real.exp (((if infrared then H else
                    (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega) z +
                    ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)) ^ (-(1 : ℝ) / 2) *
                Real.sqrt (@sobolevCoefficientForm d (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr)
                  (cutoffPositiveCoefficient model
                    (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
                    omega (m + k) zP hLr)
                  (u : SobolevData (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr))
                  (u : SobolevData (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-(k : ℤ))) hLr))) +
              Cfin * ((3 : ℝ) ^ (-(k : ℤ))) ^ (2 : ℝ) *
                (Real.exp (((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom model m /
                  (Real.exp ((((m + k : ℕ) : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom model (m + k)) *
                  Real.exp (((if infrared then H else
                    (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega) z +
                    ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z))⁻¹ * Kf := by
  obtain ⟨_hR1, hR2, hR3⟩ := hGE
  obtain ⟨_g1, _g2, _g3, _g4, _g5, _g6, _g7, h8, _g9, h10, _g11, _g12, _g13⟩ := hR3 infrared
  obtain ⟨hC1, hC2, hC4, hC3⟩ := hCar
  exact lfgc_clause1_assembly d I alpha sigma cell eps lam Cfin delta1 hLH model response
    hdelta H eta F Praw Rraw Draw Z rawGood omega hC1 hC2 hC4 hC3 en ns self padRoot
    selfShift enDepth shift hself hselfShift hpadDepth buffer k0 hbuffer1 hk01 m k z infrared
    (hR2 selfShift).1
    (fun DA dword hDA => h8 (self, selfShift) DA hDA _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ dword))))
    (fun D pword hD => (h8 (padRoot, selfShift) D hD _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ pword)))).2)
    _ _ _ _ (h10 (padRoot, selfShift)).1 rfl rfl rfl zP _ hLr hsub0

/-- The padded enlargement: `3` as soon as the parent is at least nine cells wide, `2` otherwise. -/
theorem aux_lem_finite_good_cell_pad_choice (H1 : ℕ) (hH1 : 0 < H1) :
    1 < (if 2 ≤ H1 then (3 : ℝ) else 2) ∧ (if 2 ≤ H1 then (3 : ℝ) else 2) < (3 : ℝ) ^ H1 ∧
      (if 2 ≤ H1 then (3 : ℝ) else 2) ≤ 3 := by
  by_cases h : 2 ≤ H1
  · rw [ite_eq_left h]
    have h9 : (9 : ℝ) ≤ (3 : ℝ) ^ H1 := by
      calc (9 : ℝ) = (3 : ℝ) ^ 2 := by norm_num
        _ ≤ (3 : ℝ) ^ H1 := pow_le_pow_right₀ (by norm_num) h
    exact ⟨by norm_num, by linarith only [h9], le_rfl⟩
  · rw [ite_eq_right h]
    have hH : H1 = 1 := by omega
    subst hH
    exact ⟨by norm_num, by norm_num, by norm_num⟩



theorem aux_lem_finite_good_cell_choose_small_constants (t0 : ℝ) (ht0 : 0 < t0) :
    ∃ eps lam lamDet : ℝ, eps ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < lam ∧ lam < lamDet ∧ lamDet < 1 ∧
      eps ≤ t0 ∧ lamDet ≤ t0 := by
  have hm : 0 < min (1 / 2 : ℝ) t0 := lt_min (by norm_num) ht0
  have hm1 : min (1 / 2 : ℝ) t0 < 1 := (min_le_left _ _).trans_lt (by norm_num)
  exact ⟨min (1 / 2) t0, min (1 / 2) t0 / 2, min (1 / 2) t0, ⟨hm, hm1⟩, by positivity,
    half_lt_self hm, hm1, min_le_right _ _, min_le_right _ _⟩

/-- The paper's deterministic/analytic core of `\label{mfd:lem-finite-good-cell}` : given the
exponent hypotheses, the fixed suppliers `I, Poincare, Extension, Sobolev, MeyersMorrey, Step`, and the
(already fixed) threshold constants `eps, cell, lam, lamDet, cdet` and catalogue data (`en = 2`,
`self = 0`, `padRoot = 1` at depth `H1`, `nc = ns = 1`, zero shift), produce the discount `sigma`, the
disorder threshold `delta0`, the Hölder/extension constants `Cfin, Aext`, the padding scalar `pad`, and
(for every model with `model.delta ≤ delta0`) the finite-cutoff good event `Good`, its probability-one
carrier, its `good_event` characterization, its measurability and exponential-tail bound
(`aux_lem_finite_good_cell_h_measurability_tail`), and the estimates for every good sample.
Clause 1 (Parent/Hölder + energy bound, `eq:mfd-finite-good-holder`) is gated by `4 ≤ H1 →`
 and is
closed by `lem_finite_good_cell_local_holder` through `lfgc_clause1_assembly`; Clause 2 (trace/Dirichlet
response) by `aux_lem_finite_good_cell_clause2_of_ellipticity`. -/
theorem aux_lem_finite_good_cell_gap_main
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Sobolev : SobolevFoundationalInput d hd)
    (MeyersMorrey : SmallPerturbationInput d)
    (_Cp : CampanatoInput d)
    (Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (Dbase : _root_.SubdiffusiveProcess.Paper.sum_errors_baseline_input d)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (alpha beta rate : ℝ) (hbeta : 1 / 2 < beta)
    (hba : beta < alpha) (halpha : alpha < 1) (hrate : 0 < rate)
    (H1 : ℕ) (hH1 : 0 < H1)
    (eps cell lam lamDet cdet : ℝ)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (hcell : 0 < cell) (hcellSmall : cell ≤ 1 / 2)
    (hlam : 0 < lam)
    (hlamlt : lam < lamDet) (hlamDet1 : lamDet < 1) (hcdet : 0 < cdet)
    (en nc ns : ℕ) (self padRoot : Fin en) (chosen : Fin nc) (selfShift : Fin ns)
    (enDepth : Fin en → ℕ) (cmpDepth : Fin nc → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d)
    (shift : Fin ns → SpatialCoordinates d)
    (cmpRoot : Fin nc → Fin en × Fin ns)
    (cmpWord : (c : Fin nc) →
      Fin (enDepth (cmpRoot c).1 + cmpDepth c) → OddGridIndex d 1)
    (buffer k0 : ℕ) (hbuffer : 0 < buffer) (hpadDepth : enDepth padRoot = 1)
    (hself : enDepth self = 0) (hselfShift : shift selfShift = 0)
    (hcmpShift : ∀ c, cmpShift c = 0) (hcmpDepth : ∀ c, cmpDepth c = 0)
    (hdepthle : ∀ e, enDepth e ≤ 3) (hk0 : 1 ≤ k0)
    (hbuffer1 : buffer = 1) (hk01 : k0 = 1)
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) (hsigmaEll : sigma < (beta - 1 / 2) / 4)
    (Cfin delta1 : ℝ) (hCfin : 0 < Cfin) (hdelta1 : 0 < delta1)
    (hLH : aux_lfgc_clause1_spec d I alpha sigma cell eps lam Cfin delta1) :
    ∃ sigma delta0 Cfin Aext pad : ℝ,
      sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < delta0 ∧ 0 < Cfin ∧ 0 < Aext ∧
      ∃ hpad : 1 < pad, pad < (3 : ℝ) ^ H1 ∧
      pad ≤ 3 ∧
      pad ≤ (3 : ℝ) ^ enDepth padRoot ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (response : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (_hresponse : response.C ≤ Cresp)
        (regularity : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
        (_iteration : _root_.SubdiffusiveProcess.Paper.in_iteration d model I regularity)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ delta0 →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d),
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N i x,
          eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N,
          primitive_scores d model sigma eps (eta N omega)
            (fun m z => F N m z omega) (fun m z => Praw N m z omega)
            (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
            (fun m z => Z N m z omega) (fun m z => rawGood N m z omega)) →
      ∃ Good : ℕ → ℕ → SpatialCoordinates d → Set (BilateralField d),
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      ∃ Carrier : Set (BilateralField d), MeasurableSet Carrier ∧ P Carrierᶜ = 0 ∧
      (∀ (m k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d),
        omega ∈ Carrier →
        let N := m + k
        let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
        let rootSide : Fin en × Fin ns → ℝ :=
          fun U => r * (3 : ℝ) ^ enDepth U.1
        let rootCentre : Fin en × Fin ns → SpatialCoordinates d :=
          fun U => z + rootSide U • shift U.2
        let centres : (Fin en × Fin ns) → ℕ → Finset (SpatialCoordinates d) :=
          fun U D => by
            classical
            exact ((Finset.univ : Finset (Fin en × Fin ns)).image rootCentre) ∪
              ((Finset.univ : Finset (Fin nc)).image (fun c => z + r • cmpShift c)) ∪
              ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
                (descendantCenter 1 (rootCentre U) (rootSide U) D))
        let pre : (Fin en × Fin ns) → ℕ → SpatialCoordinates d → Finset ℤ :=
          fun U D _ =>
            Finset.Icc ((k : ℤ) - enDepth U.1 - buffer)
              (min (N : ℤ) ((k : ℤ) - enDepth U.1 + D + buffer))
        let Zphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
          if 0 ≤ (N : ℤ) - j then Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om else 0
        let Dphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
          if 0 ≤ (N : ℤ) - j then
            (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om).toReal else 0
        omega ∈ Good m k z ↔
          (∀ e D, ∀ w ∈ centres e D, ∀ j ∈ pre e D w,
            0 ≤ (N : ℤ) - j →
              Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega ≠ ⊤) ∧
          (∀ t : Fin ns,
            F N (m + enDepth padRoot)
              ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 1 ∧
            Praw N (m + enDepth padRoot)
              ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 12) ∧
          ∀ infrared : Bool,
            let Hused := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
            let kappa := fun J : ℕ =>
              Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
                SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
            let retained := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
              if 0 ≤ j then ∑ i ∈ Finset.Ico (0 : ℤ) j, om (-i) w
              else -∑ i ∈ Finset.Ico j (0 : ℤ), om (-i) w
            let reference := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
              kappa ((N : ℤ) - j).toNat / kappa N *
                Real.exp (Hused om w + retained j w om)
            let rEn := rootSide
            let zEn := rootCentre
            let hrEn : ∀ U : Fin en × Fin ns, 0 < rEn U := by
              intro U; dsimp [rEn, rootSide, r]; positivity
            let aEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
              cutoffPositiveCoefficient model Hused om N (zEn U) (hrEn U)
            let refEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
              reference ((k : ℤ) - enDepth U.1) (zEn U) om
            let zCmp := fun c : Fin nc => z + r • cmpShift c
            let rCmp := fun c : Fin nc => r * (3 : ℝ) ^ (-(cmpDepth c : ℤ))
            let hrCmp : ∀ c, 0 < rCmp c := by intro c; dsimp [rCmp, r]; positivity
            let aCmp := fun (c : Fin nc) (om : BilateralField d) =>
              cutoffPositiveCoefficient model Hused om N (zCmp c) (hrCmp c)
            let refCmp := fun (c : Fin nc) (om : BilateralField d) =>
              reference ((k : ℤ) + cmpDepth c) (zCmp c) om
            good_event (BilateralField d) d (Fin en × Fin ns) (Fin en × Fin ns) (Fin nc)
              centres pre Zphys Dphys
              (fun e om => I.lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
              (fun e om => I.Lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
              (fun e om i j =>
                (Homogenization.Book.Ch02.sigmaCoarse
                  (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                  ((I.chart (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e)).coeffOn
                    (Homogenization.originCube d 0))) i j / refEn e om)
              (fun c om => I.err (zCmp c) (rCmp c) (hrCmp c) (aCmp c om)
                (zCmp c) (rCmp c) (refCmp c om) sigma 2)
              (fun c om => reference (k : ℤ) z om / refCmp c om)
              chosen ((2 * (d : ℝ))⁻¹) ((en * ns + nc + 1 : ℕ) : ℝ) cell lam lamDet eps cdet k0 omega) ∧
      (∀ (m k : ℕ) (z : SpatialCoordinates d),
        MeasurableSet (Good m k z) ∧ ∃ W : ℕ+ → Set (BilateralField d),
          (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
            ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).domRestrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
                C(SpatialCoordinates d, ℝ)))] (W h)) ∧
          (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-rate * (h : ℝ)))) ∧
          (Good m k z)ᶜ ⊆ ⋃ h : ℕ+, W h) ∧
      (∀ (omega : BilateralField d), omega ∈ Carrier →
        ∀ (m k : ℕ) (z : SpatialCoordinates d),
        omega ∈ Good m k z → ∀ infrared : Bool,
        let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
        let hr : 0 < r := by positivity
        let hLr : 0 < (3 : ℝ) ^ H1 * r := mul_pos (pow_pos (by norm_num) H1) hr
        let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
        let closedQ : Set (SpatialCoordinates d) := closedCube z r hr
        let unitClosed : Set (SpatialCoordinates d) := closedCube (0 : SpatialCoordinates d) 1 one_pos
        let T : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
        let Hused : BilateralField d → C(SpatialCoordinates d, ℝ) := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        let N := m + k
        let kappa : ℕ → ℝ := fun J =>
          Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
        let s : ℝ := (kappa m / kappa (m + k)) *
          Real.exp ((Hused omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)
        (4 ≤ H1 → ∀ (zP : SpatialCoordinates d) (idx : OddGridIndex d (subdivisionHalfWidth H1)),
          z = oddGridCenter zP ((3 : ℝ) ^ H1 * r) (subdivisionHalfWidth H1) idx →
          (closedCube z (pad * r) (mul_pos (lt_trans zero_lt_one hpad) hr) : Set (SpatialCoordinates d)) ⊆
            (centeredCube zP ((3 : ℝ) ^ H1 * r) hLr : Set (SpatialCoordinates d)) →
          let Parent : Opens (SpatialCoordinates d) := centeredCube zP ((3 : ℝ) ^ H1 * r) hLr
          let aP : PositiveCoefficient Parent := cutoffPositiveCoefficient model Hused omega N zP hLr
          ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            Measurable F → 0 ≤ Kf → (∀ x ∈ Parent, |F x| ≤ Kf) →
            ∀ u : weakSobolevGraph Parent,
              (∀ psi : killedSobolevGraph Parent,
                @sobolevCoefficientForm d Parent aP (u : SobolevData Parent) (psi : SobolevData Parent) =
                  ∫ x in (Parent : Set (SpatialCoordinates d)), F x * (psi : SobolevData Parent).1 x) →
              ∃ (U : SpatialCoordinates d → ℝ) (c : ℝ),
                ContinuousOn U closedQ ∧
                ((fun x => (u : SobolevData Parent).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                @IsHolderOn d alpha unitClosed (fun x => U (T x) - c) ∧
                @cAlphaNorm d alpha unitClosed (fun x => U (T x) - c) ≤
                  Cfin * r ^ (((2 : ℝ) - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) *
                    Real.sqrt (@sobolevCoefficientForm d Parent aP
                      (u : SobolevData Parent) (u : SobolevData Parent)) +
                  Cfin * r ^ (2 : ℝ) * s⁻¹ * Kf) ∧
        (let aQ : PositiveCoefficient Q := cutoffPositiveCoefficient model Hused omega N z hr
         ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
             ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
           ∀ (b : weakSobolevGraph Q) (G : SpatialCoordinates d → ℝ),
             ContinuousOn G closedQ → @IsHolderOn d beta (frontier (Q : Set (SpatialCoordinates d))) G →
             ((fun x => (b : SobolevData Q).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] G) → ∀ c : ℝ,
             @dirichletResponse d Q (@killedResponseSpace d Q hP) aQ b ≤
               Aext * r ^ ((d : ℝ) - 2) * s *
                 (@cAlphaNorm d beta
                   (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
                   (fun x => G (T x) - c)) ^ (2 : ℕ))) := by
  -- `sigma` and the Clause-1 constant `Cfin` (with its disorder
  -- threshold `delta1`) are supplied by the principal from `lem_finite_good_cell_local_holder`
  -- (via `aux_lfgc_clause1_spec_exists`), before the thresholds `eps, lam, lamDet`; the padded
  -- enlargement is `pad = 3` whenever `2 ≤ H1` (so on the gated branch `4 ≤ H1`).
  obtain ⟨pad, hpadDef⟩ : ∃ pad : ℝ, pad = if 2 ≤ H1 then (3 : ℝ) else 2 := ⟨_, rfl⟩
  have hpadC := aux_lem_finite_good_cell_pad_choice H1 hH1
  rw [← hpadDef] at hpadC
  obtain ⟨hpad, hpadL, hpad3⟩ := hpadC
  -- `Aext` is no longer `h_constants`' own
  -- arbitrary placeholder — it is computed here as `clause2_of_ellipticity`'s own witness
  -- `CExt * cell⁻¹`, using only `d, hd, I, Extension, Sobolev, beta` (all available before
  -- `model`), so it is fixed early exactly like the rest of the existential block, and hDet's
  -- proof below discharges Clause 2 by supplying `outerSigma := sigma` (now `< (beta-1/2)/4` via
  -- `hsigmaEll`) to the SAME `aux_lem_extension_boundary_half` call, so the two `C`s agree by
  -- `rfl`/definitional unfolding of `Aext`'s `have`.
  obtain ⟨CExt, hCExtPos, hbhExt⟩ :=
    aux_lem_extension_boundary_half d hd I Extension Sobolev beta ⟨hbeta, hba.trans halpha⟩
  have hAext : 0 < CExt * cell⁻¹ := mul_pos hCExtPos (inv_pos.mpr hcell)
  set Aext : ℝ := CExt * cell⁻¹ with hAextDef
  -- `h_measurability_tail` now CHOOSES
  -- its own disorder threshold `delta0Tail` (existential, depending on
  -- `rate, sigma, eps, cell, lam, lamDet, cdet, H1, Cresp`) instead of receiving an arbitrary
  -- universal one — see that theorem's docstring for the counterexample this removes. `gap_main`
  -- combines it with `h_constants`' own `delta0Const` (currently unconsumed by anything but kept,
  -- per the general's instruction, for forward compatibility with a future real threshold from
  -- `Cfin/Aext/pad`'s `in_deterministic`/Meyers-Morrey smallness requirement) via `min`:
  -- `model.delta ≤ min delta0Const delta0Tail` implies both `model.delta ≤ delta0Const` and
  -- `model.delta ≤ delta0Tail`, so nothing downstream loses information versus the old
  -- (mistakenly non-existential) wiring.
  obtain ⟨delta0Tail, hdelta0Tail, hmainTail⟩ :=
    aux_lem_finite_good_cell_h_measurability_tail d hd I Poincare Extension Sobolev MeyersMorrey Step Dbase D Cresp hCresp alpha beta rate hbeta hba halpha hrate H1 hH1 eps cell lam lamDet cdet heps hcell hcellSmall hlam hlamlt hlamDet1 hcdet en nc ns self padRoot chosen selfShift enDepth cmpDepth cmpShift shift cmpRoot cmpWord buffer k0 hbuffer hself hselfShift hcmpShift hcmpDepth hdepthle hpadDepth hk0
      sigma hsigma
  refine ⟨sigma, min delta1 delta0Tail, Cfin, Aext, pad, hsigma,
    lt_min hdelta1 hdelta0Tail, hCfin, hAext, hpad, hpadL, hpad3, ?_, ?_⟩
  · rw [hpadDepth, pow_one]; exact hpad3
  · intro model response hresponse regularity iteration H hInfra hdelta
      eta heta F Praw Rraw Draw Z rawGood hprim
    -- the old two-step plan (h_good_event_witness with
    -- `Carrier := Set.univ`, then a separate h_measurability_tail about that
    -- SAME `Good`) cannot give literal `MeasurableSet (Good m k z)` for every
    -- `omega` (the a.e. pins `heta`/`hprim` only hold up to a null set, so the
    -- naive `Good` need not be exactly measurable there). The repaired
    -- `h_measurability_tail` builds `Good`/`Carrier` TOGETHER instead (see its
    -- docstring); `h_good_event_witness` is no longer called here.
    have hdeltaTail : model.delta ≤ delta0Tail := hdelta.trans (min_le_right _ _)
    have hdeltaLH : model.delta ≤ delta1 := hdelta.trans (min_le_left _ _)
    obtain ⟨Good, Carrier, hMeas, hNull, hChar, hTail, hCarProps⟩ :=
      hmainTail model response hresponse regularity iteration H hInfra hdeltaTail
        eta heta F Praw Rraw Draw Z rawGood hprim
    refine ⟨Good, Carrier, hMeas, hNull, hChar, hTail, ?_⟩
    
    
    
    
    
    
    
    
    have hDet :
        ∀ (omega : BilateralField d), omega ∈ Carrier →
        ∀ (m k : ℕ) (z : SpatialCoordinates d),
        omega ∈ Good m k z → ∀ infrared : Bool,
        let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
        let hr : 0 < r := by positivity
        let hLr : 0 < (3 : ℝ) ^ H1 * r := mul_pos (pow_pos (by norm_num) H1) hr
        let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
        let closedQ : Set (SpatialCoordinates d) := closedCube z r hr
        let unitClosed : Set (SpatialCoordinates d) := closedCube (0 : SpatialCoordinates d) 1 one_pos
        let T : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
        let Hused : BilateralField d → C(SpatialCoordinates d, ℝ) := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        let N := m + k
        let kappa : ℕ → ℝ := fun J =>
          Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
        let s : ℝ := (kappa m / kappa (m + k)) *
          Real.exp ((Hused omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)
        (4 ≤ H1 → ∀ (zP : SpatialCoordinates d) (idx : OddGridIndex d (subdivisionHalfWidth H1)),
          z = oddGridCenter zP ((3 : ℝ) ^ H1 * r) (subdivisionHalfWidth H1) idx →
          (closedCube z (pad * r) (mul_pos (lt_trans zero_lt_one hpad) hr) : Set (SpatialCoordinates d)) ⊆
            (centeredCube zP ((3 : ℝ) ^ H1 * r) hLr : Set (SpatialCoordinates d)) →
          let Parent : Opens (SpatialCoordinates d) := centeredCube zP ((3 : ℝ) ^ H1 * r) hLr
          let aP : PositiveCoefficient Parent := cutoffPositiveCoefficient model Hused omega N zP hLr
          ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            Measurable F → 0 ≤ Kf → (∀ x ∈ Parent, |F x| ≤ Kf) →
            ∀ u : weakSobolevGraph Parent,
              (∀ psi : killedSobolevGraph Parent,
                @sobolevCoefficientForm d Parent aP (u : SobolevData Parent) (psi : SobolevData Parent) =
                  ∫ x in (Parent : Set (SpatialCoordinates d)), F x * (psi : SobolevData Parent).1 x) →
              ∃ (U : SpatialCoordinates d → ℝ) (c : ℝ),
                ContinuousOn U closedQ ∧
                ((fun x => (u : SobolevData Parent).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                @IsHolderOn d alpha unitClosed (fun x => U (T x) - c) ∧
                @cAlphaNorm d alpha unitClosed (fun x => U (T x) - c) ≤
                  Cfin * r ^ (((2 : ℝ) - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) *
                    Real.sqrt (@sobolevCoefficientForm d Parent aP
                      (u : SobolevData Parent) (u : SobolevData Parent)) +
                  Cfin * r ^ (2 : ℝ) * s⁻¹ * Kf) ∧
        (let aQ : PositiveCoefficient Q := cutoffPositiveCoefficient model Hused omega N z hr
         ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
             ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
           ∀ (b : weakSobolevGraph Q) (G : SpatialCoordinates d → ℝ),
             ContinuousOn G closedQ → @IsHolderOn d beta (frontier (Q : Set (SpatialCoordinates d))) G →
             ((fun x => (b : SobolevData Q).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] G) → ∀ c : ℝ,
             @dirichletResponse d Q (@killedResponseSpace d Q hP) aQ b ≤
               Aext * r ^ ((d : ℝ) - 2) * s *
                 (@cAlphaNorm d beta
                   (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
                   (fun x => G (T x) - c)) ^ (2 : ℕ)) := by
      intro omega hCarOmega m k z hGoodMkz infrared
      extract_lets r hr hLr Q closedQ unitClosed T Hused N kappa s
      refine ⟨?_, ?_⟩
      · -- Clause 1, `4 ≤ H1`: the good-event tests at the cell on the
        -- pinned carrier feed `lfgc_clause1_assembly` (eq:mfd-finite-good-holder through
        -- `lem_finite_good_cell_local_holder`); the padded cube `pad * r = 3 r` lies in `Parent`.
        intro h4 zP idx _hzEq hsub
        have hpadEq : pad = 3 := hpadDef.trans (ite_eq_left (by omega))
        have hsub0 : Metric.closedBall z (pad * r / 2) ⊆
            (centeredCube zP ((3 : ℝ) ^ H1 * r) hLr : Set (SpatialCoordinates d)) := hsub
        rw [hpadEq] at hsub0
        exact aux_lem_finite_good_cell_clause1_extract d I alpha sigma eps cell lam lamDet cdet Cfin
          delta1 hLH model response hdeltaLH H eta F Praw Rraw Draw Z rawGood en nc ns self padRoot
          chosen selfShift enDepth cmpDepth cmpShift shift hself hselfShift hpadDepth buffer k0
          hbuffer1 hk01 omega (hCarProps omega hCarOmega) m k z infrared
          ((hChar m k z omega hCarOmega).mp hGoodMkz) H1 zP hLr hsub0
      · -- Clause 2 ("trace/Dirichlet response"): fully proved via
        -- `aux_lem_finite_good_cell_clause2_of_ellipticity`, feeding it `outerSigma := sigma`
        -- (now `< (beta-1/2)/4` via `hsigmaEll`) and the ellipticity bound extracted from
        -- `hChar`/`good_event`'s own clause 10 (`∀ e, cell ≤ ellipMin e ω ∧ ellipMax e ω ≤
        -- cell⁻¹`) at the self root `e := (self, selfShift)`, identified against `z, r, aQ, s`
        -- via `hself : enDepth self = 0` and `hselfShift : shift selfShift = 0` (gap_main's own
        -- catalogue hypotheses) — matches `aux_lem_finite_good_cell_clause2_of_ellipticity`'s
        -- catalogue formula.
        intro hP b G hGcont hGhol htie c
        have hGE := (hChar m k z omega hCarOmega).mp hGoodMkz
        obtain ⟨_hR1, _hR2, hR3⟩ := hGE
        have hGoodEv := hR3 infrared
        obtain ⟨_h1, _h2, _h3, _h4, _h5, _h6, _h7, _h8, _h9, h10, _h11, _h12, _h13⟩ := hGoodEv
        have hrle1 : r ≤ 1 := by
          have hk3 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
          have hreq : r = ((3 : ℝ) ^ k)⁻¹ := by
            show (3 : ℝ) ^ (-(k : ℤ)) = ((3 : ℝ) ^ k)⁻¹
            rw [zpow_neg, zpow_natCast]
          rw [hreq]
          exact inv_le_one_of_one_le₀ hk3
        exact aux_lem_finite_good_cell_clause2_extract d hd I Extension Sobolev beta
          ⟨hbeta, hba.trans halpha⟩ CExt hCExtPos hbhExt model omega Hused m k z r hr hrle1
          sigma cell hsigma hsigmaEll hcell en ns self selfShift enDepth shift hself hselfShift
          h10 hP b G hGcont hGhol htie c
    exact hDet


/--
- Good is identified on a common measurable probability-one
  carrier with the actual finite-prefix good_event and the extra F/P root tests.
  All thresholds and catalogue geometry precede disorder. Zphys/Dphys use the
  physical-to-cutoff reindexing; Draw finiteness is required before toReal.
  Ellipticity, affine matrices, errors and reference ratios use the same
  cutoffPositiveCoefficient and its root reference, for both infrared variants.
- The finite translated grids, distinguished zero shift, actual comparison
  descendant words, and normalized hGridCover conclusion are chosen before
  disorder. Roots are Fin en × Fin ns throughout the prefix/finiteness and
  coarse ellipticity/matrix tests. Each centre catalogue includes all root
  centres, all comparison centres, and that root's depth-D descendants.
  This is the catalogue  and the hGridCover interface of
  in_deterministic, not a new regularity hypothesis. The fixed padded F/P
  tests are imposed at each translated padded root. 
- Geometry: q has side r=3^{-k}; p is its actual L-adic parent of side Lr through oddGridCenter, with the fixed padded enlargement contained in p.
- Parent energy: the right-hand side is the diagonal coefficient form of u on p, exactly Gamma(u)(p), while the norm and reference scalar remain at q.
- Concrete carriers: the law, cutoff coefficient, weak solution, bounded source, continuous representative, and reference scalar are pinned; no arbitrary norm, datum, energy, or band is left free.
- Interval witnesses: the actual bilateral layer restriction has indices [-k-2h,-k+h], corresponding to gamma_{-j}, k-h≤j≤k+2h; one rate for every remaining cutoff m.
- Constants: alpha, beta, rate and geometry precede the disorder threshold; Aext is fixed before any finite test family or its tolerance.
- Every solution: all bounded sources and weak solutions are quantified after the good event; recentering constant and representative are conclusions.
- Infrared variants: H or zero is selected inside the concrete coefficient and root reference, on the same event.
- Coarse objects and deterministic inequalities: I, Poincare and Extension carry in_J, in_poincare  and in_extension. These are the standing inputs consumed by lem_band, in_deterministic and lem_extension, not their conclusions.
- Fractional trace/embedding facts: Sobolev carries the published SobolevFoundationalInput used by lem_extension  and in_deterministic; the Besov ingredient is written. No Lean witness; frozen on the author's deferral of published inputs, Stein (1970), Ch. VI; Lions-Magenes (1972), Ch. 1; the Besov seminorm of the paper and `e.nabla.u.detach`.
- Below-wavelength supplier: MeyersMorrey carries SmallPerturbationInput, the published interior W1p estimate and Morrey inequality explicitly used in prop_growth's PROOF  and again here. prop_growth's displayed Dirichlet conclusion alone does not supply the local weak-solution estimate. No Lean witness; frozen on the author's deferral of published inputs, Meyers (1963), gradient Lp estimate, and Morrey embedding.
- Cutoff one-step supplier: Step is cutoff_good_scale_input, the published M l.cutoff.regularity.good.scale.estimates, consumed by in_deterministic. It does not assume the iterated or finite-good-cell conclusions.
- Finite response moments and regularity: response, regularity and iteration are in_responses, in_6_16  and in_iteration, on the SAME model. Cresp bounds the response input's dimensional constant before delta0 is selected, as in lem_band; every moment order is chosen in the proof before disorder.
- Interval suppliers: lem_witness and lem_band conclude the interval mechanism after their input hypotheses are discharged. No band, witness, prefix, or local regularity estimate has been added as a hypothesis.
- Matching estimate: Applies the calculation in prop_growth  to obtain the energy factor a^(alpha1-alpha) and source factor a^(2-alpha). lem_finite_good_cell_uniform only absorbs powers AFTER those bounds have been established; it is not their supplier.
- Response and normalization suppliers: lem_extension gives the trace bound after condition (a) of good_event; lem_local_normalizations identifies the root scalar. All original conclusion bytes and witness scopes are retained.
-/
theorem lem_finite_good_cell
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Sobolev : SobolevFoundationalInput d hd)
    (MeyersMorrey : SmallPerturbationInput d)
    (Cp : CampanatoInput d)
    (Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Dbase : _root_.SubdiffusiveProcess.Paper.sum_errors_baseline_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (alpha beta rate : ℝ) (hbeta : 1 / 2 < beta)
    (hba : beta < alpha) (halpha : alpha < 1) (hrate : 0 < rate)
    (H1 : ℕ) (hH1 : 0 < H1) :
    let L : ℝ := (3 : ℝ) ^ H1
    let mgrid := subdivisionHalfWidth H1
    ∃ sigma eps cell lam lamDet cdet : ℝ,
    ∃ en nc ns : ℕ, ∃ self padRoot : Fin en, ∃ chosen : Fin nc,
    ∃ selfShift : Fin ns,
    ∃ (enDepth : Fin en → ℕ) (cmpDepth : Fin nc → ℕ)
      (cmpShift : Fin nc → SpatialCoordinates d)
      (shift : Fin ns → SpatialCoordinates d)
      (cmpRoot : Fin nc → Fin en × Fin ns)
      (cmpWord : (c : Fin nc) →
        Fin (enDepth (cmpRoot c).1 + cmpDepth c) → OddGridIndex d 1)
      (buffer k0 : ℕ),
      sigma ∈ Set.Ioo (0 : ℝ) 1 ∧ eps ∈ Set.Ioo (0 : ℝ) 1 ∧
      0 < cell ∧ 0 < lam ∧ lam < lamDet ∧ lamDet < 1 ∧ 0 < cdet ∧
      enDepth self = 0 ∧ shift selfShift = 0 ∧ 0 < buffer ∧
      (∀ c : Fin nc,
        cmpShift c = descendantCenter 1
          (((3 : ℝ) ^ enDepth (cmpRoot c).1) • shift (cmpRoot c).2)
          ((3 : ℝ) ^ enDepth (cmpRoot c).1)
          (enDepth (cmpRoot c).1 + cmpDepth c) (cmpWord c)) ∧
      (∀ x : SpatialCoordinates d,
        x ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2) →
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          ∃ (U : Fin en × Fin ns) (D : ℕ) (w : Fin D → OddGridIndex d 1),
            Metric.ball x (rho / 2) ⊆
              Metric.ball (descendantCenter 1
                (((3 : ℝ) ^ enDepth U.1) • shift U.2)
                ((3 : ℝ) ^ enDepth U.1) D w)
                (descendantSide 1 D ((3 : ℝ) ^ enDepth U.1) / 2) ∧
            descendantSide 1 D ((3 : ℝ) ^ enDepth U.1) ≤ 9 * rho) ∧
      cell_catalogue d (Fin en) (Fin nc)
        (fun k z => Metric.ball z ((3 : ℝ) ^ (-(k : ℤ)) / 2))
        (fun k z e => Metric.ball z
          (((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth e) / 2))
        (fun k z c => Metric.ball
          (z + (3 : ℝ) ^ (-(k : ℤ)) • cmpShift c)
          (((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ (-(cmpDepth c : ℤ))) / 2))
        self (fun _ _ => chosen) ∧
    ∃ delta0 Cfin Aext pad : ℝ,
      0 < delta0 ∧ 0 < Cfin ∧ 0 < Aext ∧ ∃ hpad : 1 < pad, pad < L ∧
      pad ≤ 3 ∧
      pad ≤ (3 : ℝ) ^ enDepth padRoot ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (response : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (_hresponse : response.C ≤ Cresp)
        (regularity : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
        (_iteration : _root_.SubdiffusiveProcess.Paper.in_iteration d model I regularity)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ delta0 →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d),
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N i x,
          eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N,
          primitive_scores d model sigma eps (eta N omega)
            (fun m z => F N m z omega) (fun m z => Praw N m z omega)
            (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
            (fun m z => Z N m z omega) (fun m z => rawGood N m z omega)) →
      ∃ Good : ℕ → ℕ → SpatialCoordinates d → Set (BilateralField d),
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      ∃ Carrier : Set (BilateralField d), MeasurableSet Carrier ∧ P Carrierᶜ = 0 ∧
      (∀ (m k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d),
        omega ∈ Carrier →
        let N := m + k
        let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
        let rootSide : Fin en × Fin ns → ℝ :=
          fun U => r * (3 : ℝ) ^ enDepth U.1
        let rootCentre : Fin en × Fin ns → SpatialCoordinates d :=
          fun U => z + rootSide U • shift U.2
        let centres : (Fin en × Fin ns) → ℕ → Finset (SpatialCoordinates d) :=
          fun U D => by
            classical
            exact ((Finset.univ : Finset (Fin en × Fin ns)).image rootCentre) ∪
              ((Finset.univ : Finset (Fin nc)).image (fun c => z + r • cmpShift c)) ∪
              ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
                (descendantCenter 1 (rootCentre U) (rootSide U) D))
        let pre : (Fin en × Fin ns) → ℕ → SpatialCoordinates d → Finset ℤ :=
          fun U D _ =>
            Finset.Icc ((k : ℤ) - enDepth U.1 - buffer)
              (min (N : ℤ) ((k : ℤ) - enDepth U.1 + D + buffer))
        let Zphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
          if 0 ≤ (N : ℤ) - j then Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om else 0
        let Dphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
          if 0 ≤ (N : ℤ) - j then
            (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om).toReal else 0
        omega ∈ Good m k z ↔
          (∀ e D, ∀ w ∈ centres e D, ∀ j ∈ pre e D w,
            0 ≤ (N : ℤ) - j →
              Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega ≠ ⊤) ∧
          (∀ t : Fin ns,
            F N (m + enDepth padRoot)
              ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 1 ∧
            Praw N (m + enDepth padRoot)
              ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 12) ∧
          ∀ infrared : Bool,
            let Hused := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
            let kappa := fun J : ℕ =>
              Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
                SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
            let retained := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
              if 0 ≤ j then ∑ i ∈ Finset.Ico (0 : ℤ) j, om (-i) w
              else -∑ i ∈ Finset.Ico j (0 : ℤ), om (-i) w
            let reference := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
              kappa ((N : ℤ) - j).toNat / kappa N *
                Real.exp (Hused om w + retained j w om)
            let rEn := rootSide
            let zEn := rootCentre
            let hrEn : ∀ U : Fin en × Fin ns, 0 < rEn U := by
              intro U; dsimp [rEn, rootSide, r]; positivity
            let aEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
              cutoffPositiveCoefficient model Hused om N (zEn U) (hrEn U)
            let refEn := fun (U : Fin en × Fin ns) (om : BilateralField d) =>
              reference ((k : ℤ) - enDepth U.1) (zEn U) om
            let zCmp := fun c : Fin nc => z + r • cmpShift c
            let rCmp := fun c : Fin nc => r * (3 : ℝ) ^ (-(cmpDepth c : ℤ))
            let hrCmp : ∀ c, 0 < rCmp c := by intro c; dsimp [rCmp, r]; positivity
            let aCmp := fun (c : Fin nc) (om : BilateralField d) =>
              cutoffPositiveCoefficient model Hused om N (zCmp c) (hrCmp c)
            let refCmp := fun (c : Fin nc) (om : BilateralField d) =>
              reference ((k : ℤ) + cmpDepth c) (zCmp c) om
            good_event (BilateralField d) d (Fin en × Fin ns) (Fin en × Fin ns) (Fin nc)
              centres pre Zphys Dphys
              (fun e om => I.lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
              (fun e om => I.Lam (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e) sigma 2 / refEn e om)
              (fun e om i j =>
                (Homogenization.Book.Ch02.sigmaCoarse
                  (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
                  ((I.chart (zEn e) (rEn e) (hrEn e) (aEn e om) (zEn e) (rEn e)).coeffOn
                    (Homogenization.originCube d 0))) i j / refEn e om)
              (fun c om => I.err (zCmp c) (rCmp c) (hrCmp c) (aCmp c om)
                (zCmp c) (rCmp c) (refCmp c om) sigma 2)
              (fun c om => reference (k : ℤ) z om / refCmp c om)
              chosen ((2 * (d : ℝ))⁻¹) ((en * ns + nc + 1 : ℕ) : ℝ) cell lam lamDet eps cdet k0 omega) ∧
      (∀ (m k : ℕ) (z : SpatialCoordinates d),
        MeasurableSet (Good m k z) ∧ ∃ W : ℕ+ → Set (BilateralField d),
          (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
            ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).domRestrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
                C(SpatialCoordinates d, ℝ)))] (W h)) ∧
          (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-rate * (h : ℝ)))) ∧
          (Good m k z)ᶜ ⊆ ⋃ h : ℕ+, W h) ∧
      (∀ (omega : BilateralField d), omega ∈ Carrier →
        ∀ (m k : ℕ) (z : SpatialCoordinates d),
        omega ∈ Good m k z → ∀ infrared : Bool,
        let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
        let hr : 0 < r := by positivity
        let hLr : 0 < L * r := mul_pos (pow_pos (by norm_num) H1) hr
        let Q : Opens (SpatialCoordinates d) := centeredCube z r hr
        let closedQ : Set (SpatialCoordinates d) := closedCube z r hr
        let unitClosed : Set (SpatialCoordinates d) := closedCube (0 : SpatialCoordinates d) 1 one_pos
        let T : SpatialCoordinates d → SpatialCoordinates d := fun x => z + r • x
        let Hused : BilateralField d → C(SpatialCoordinates d, ℝ) := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        let N := m + k
        let kappa : ℕ → ℝ := fun J =>
          Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
        let s : ℝ := (kappa m / kappa (m + k)) *
          Real.exp ((Hused omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)
        (4 ≤ H1 → ∀ (zP : SpatialCoordinates d) (idx : OddGridIndex d mgrid),
          z = oddGridCenter zP (L * r) mgrid idx →
          (closedCube z (pad * r) (mul_pos (lt_trans zero_lt_one hpad) hr) : Set (SpatialCoordinates d)) ⊆
            (centeredCube zP (L * r) hLr : Set (SpatialCoordinates d)) →
          let Parent : Opens (SpatialCoordinates d) := centeredCube zP (L * r) hLr
          let aP : PositiveCoefficient Parent := cutoffPositiveCoefficient model Hused omega N zP hLr
          ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
            Measurable F → 0 ≤ Kf → (∀ x ∈ Parent, |F x| ≤ Kf) →
            ∀ u : weakSobolevGraph Parent,
              (∀ psi : killedSobolevGraph Parent,
                @sobolevCoefficientForm d Parent aP (u : SobolevData Parent) (psi : SobolevData Parent) =
                  ∫ x in (Parent : Set (SpatialCoordinates d)), F x * (psi : SobolevData Parent).1 x) →
              ∃ (U : SpatialCoordinates d → ℝ) (c : ℝ),
                ContinuousOn U closedQ ∧
                ((fun x => (u : SobolevData Parent).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                @IsHolderOn d alpha unitClosed (fun x => U (T x) - c) ∧
                @cAlphaNorm d alpha unitClosed (fun x => U (T x) - c) ≤
                  Cfin * r ^ (((2 : ℝ) - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) *
                    Real.sqrt (@sobolevCoefficientForm d Parent aP
                      (u : SobolevData Parent) (u : SobolevData Parent)) +
                  Cfin * r ^ (2 : ℝ) * s⁻¹ * Kf) ∧
        (let aQ : PositiveCoefficient Q := cutoffPositiveCoefficient model Hused omega N z hr
         ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
             ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
           ∀ (b : weakSobolevGraph Q) (G : SpatialCoordinates d → ℝ),
             ContinuousOn G closedQ → @IsHolderOn d beta (frontier (Q : Set (SpatialCoordinates d))) G →
             ((fun x => (b : SobolevData Q).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] G) → ∀ c : ℝ,
             @dirichletResponse d Q (@killedResponseSpace d Q hP) aQ b ≤
               Aext * r ^ ((d : ℝ) - 2) * s *
                 (@cAlphaNorm d beta
                   (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
                   (fun x => G (T x) - c)) ^ (2 : ℕ))) := by
  intro L mgrid
  -- paper order. `sigma` first; then the Clause-1 constants of
  -- `lem_finite_good_cell_local_holder` at `sigma` and `cell = 1/2`; then the thresholds
  -- `eps, lam, lamDet` below its level `t0`.
  obtain ⟨sigma, _, _, _, _, hsigma, hsigma32, hsigmaEll, -⟩ :=
    aux_lem_finite_good_cell_h_constants_v2 H1 hH1 beta ⟨hbeta, hba.trans halpha⟩
  obtain ⟨CfinLH, t0, delta1, hCfinLH, ht0, hdelta1, hLHall⟩ :=
    aux_lfgc_clause1_spec_exists d hd I Poincare MeyersMorrey D alpha sigma (1 / 2)
      ⟨by linarith only [hbeta, hba], halpha⟩ ⟨hsigma.1, hsigma.2.le⟩ hsigma32 (by norm_num)
  obtain ⟨eps, lam, lamDet, heps, hlam, hlamlt, hlamDet1, hepst, hlamDett⟩ :=
    aux_lem_finite_good_cell_choose_small_constants t0 ht0
  have hLH := hLHall eps lam lamDet heps hepst hlam.le hlamlt.le hlamDett
  let cell : ℝ := 1 / 2
  let cdet : ℝ := 1
  have hcell : 0 < cell := by norm_num
  have hcellSmall : cell ≤ 1 / 2 := le_rfl
  have hcdet : 0 < cdet := one_pos
  let en : ℕ := 3
  let nc : ℕ := 1
  let ns : ℕ := 2 ^ d
  let self : Fin en := (0 : Fin 3)
  let padRoot : Fin en := (2 : Fin 3)
  let chosen : Fin nc := (0 : Fin 1)
  let selfShift : Fin ns := finFunctionFinEquiv (fun _ : Fin d => (0 : Fin 2))
  let enDepth : Fin en → ℕ := aux_lem_finite_good_cell_enDepth H1
  let cmpDepth : Fin nc → ℕ := fun _ => 0
  let cmpShift : Fin nc → SpatialCoordinates d := fun _ => 0
  let shift : Fin ns → SpatialCoordinates d := aux_lem_finite_good_cell_shift d
  let cmpRoot : Fin nc → Fin en × Fin ns := fun _ => (self, selfShift)
  have hcmpRootDepth : ∀ c : Fin nc, enDepth (cmpRoot c).1 + cmpDepth c = 0 := by
    intro c
    simp [enDepth, cmpDepth, cmpRoot, self, aux_lem_finite_good_cell_enDepth]
  let cmpWord : (c : Fin nc) → Fin (enDepth (cmpRoot c).1 + cmpDepth c) → OddGridIndex d 1 :=
    fun c i => (Fin.cast (hcmpRootDepth c) i).elim0
  let buffer : ℕ := 1
  let k0 : ℕ := 1
  have hbuffer : 0 < buffer := by norm_num
  have hpadDepth : enDepth padRoot = 1 := by
    simp [enDepth, padRoot, aux_lem_finite_good_cell_enDepth]
  have hself : enDepth self = 0 := by simp [enDepth, self, aux_lem_finite_good_cell_enDepth]
  have hselfShift : shift selfShift = 0 := by
    show shift selfShift = 0
    simp [shift, selfShift, aux_lem_finite_good_cell_shift_zero]
  have hcmpShift : ∀ c : Fin nc, cmpShift c = 0 := fun _ => rfl
  have hcmpDepth : ∀ c : Fin nc, cmpDepth c = 0 := fun _ => rfl
  have hdepthle : ∀ e : Fin en, enDepth e ≤ 3 := by
    intro e
    show aux_lem_finite_good_cell_enDepth H1 e ≤ 3
    unfold aux_lem_finite_good_cell_enDepth
    split_ifs <;> norm_num
  have hk0 : 1 ≤ k0 := le_refl 1
  obtain ⟨sigma, delta0, Cfin, Aext, pad, hsigma, hdelta0, hCfin, hAext, hpad, hpadL, hpad3, hpadEnD, hbig⟩ :=
    aux_lem_finite_good_cell_gap_main d hd I Poincare Extension Sobolev MeyersMorrey Cp Step Dbase D
      Cresp hCresp alpha beta rate hbeta hba halpha hrate H1 hH1 eps cell lam lamDet cdet heps hcell
      hcellSmall hlam hlamlt hlamDet1 hcdet en nc ns self padRoot chosen selfShift enDepth cmpDepth
      cmpShift shift cmpRoot cmpWord buffer k0 hbuffer hpadDepth hself hselfShift hcmpShift hcmpDepth
      hdepthle hk0 rfl rfl sigma hsigma hsigmaEll CfinLH delta1 hCfinLH hdelta1 hLH
  refine ⟨sigma, eps, cell, lam, lamDet, cdet, en, nc, ns, self, padRoot, chosen, selfShift,
    enDepth, cmpDepth, cmpShift, shift, cmpRoot, cmpWord, buffer, k0,
    hsigma, heps, hcell, hlam, hlamlt, hlamDet1, hcdet, ?_, ?_, hbuffer, ?_, ?_, ?_,
    delta0, Cfin, Aext, pad, hdelta0, hCfin, hAext, hpad, hpadL, hpad3, hpadEnD, hbig⟩
  · simp [enDepth, self, aux_lem_finite_good_cell_enDepth]
  · show shift selfShift = 0
    simp [shift, selfShift, aux_lem_finite_good_cell_shift_zero]
  · have hdescendant_zero : ∀ (n : ℕ) (hn : n = 0) (z : SpatialCoordinates d) (S : ℝ)
        (w : Fin n → OddGridIndex d 1), descendantCenter 1 z S n w = z := by
      intro n hn
      subst hn
      intro z S w
      rfl
    intro c
    rw [hdescendant_zero (enDepth (cmpRoot c).1 + cmpDepth c) (hcmpRootDepth c)]
    have hshift0 : shift (cmpRoot c).2 = 0 := by
      show shift selfShift = 0
      simp [shift, selfShift, aux_lem_finite_good_cell_shift_zero]
    rw [hshift0, smul_zero]
  · show ∀ x ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2), ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      ∃ (U : Fin en × Fin ns) (D : ℕ) (w : Fin D → OddGridIndex d 1),
        Metric.ball x (rho / 2) ⊆
          Metric.ball (descendantCenter 1
            (((3 : ℝ) ^ aux_lem_finite_good_cell_enDepth H1 U.1) •
              aux_lem_finite_good_cell_shift d U.2)
            ((3 : ℝ) ^ aux_lem_finite_good_cell_enDepth H1 U.1) D w)
            (descendantSide 1 D ((3 : ℝ) ^ aux_lem_finite_good_cell_enDepth H1 U.1) / 2) ∧
        descendantSide 1 D ((3 : ℝ) ^ aux_lem_finite_good_cell_enDepth H1 U.1) ≤ 9 * rho
    exact aux_lem_finite_good_cell_hGridCover H1
  · show _root_.SubdiffusiveProcess.Paper.cell_catalogue d (Fin en) (Fin nc)
      (fun k z => Metric.ball z ((3 : ℝ) ^ (-(k : ℤ)) / 2))
      (fun k z e => Metric.ball z
        (((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ (aux_lem_finite_good_cell_enDepth H1 e)) / 2))
      (fun k z (_c : Fin nc) => Metric.ball
        (z + (3 : ℝ) ^ (-(k : ℤ)) • (0 : SpatialCoordinates d))
        (((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ (-(0 : ℤ))) / 2))
      self (fun _ _ => chosen)
    exact aux_lem_finite_good_cell_gap_catalogue d hd H1

end SubdiffusiveProcess.Paper
