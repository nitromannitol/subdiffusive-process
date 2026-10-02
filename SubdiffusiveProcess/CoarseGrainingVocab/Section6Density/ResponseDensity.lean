import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ResponseScore
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ExponentialSequenceArithmetic
import Mathlib.Data.Int.NatAbs

/-!
# Density adapter for the discounted response event

This file first closes the deterministic annular separation needed by the
finite-range response score.  The probabilistic normalization and literal
event reduction follow below.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open Filter MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The headline logarithm is paid by the manuscript's `|log delta|`
budget throughout the model range `delta ≤ 1/2`. -/
theorem log_two_add_le_four_abs_log
    {delta p : ℝ} (hdelta : 0 < delta) (hhalf : delta ≤ 1 / 2)
    (hp0 : 0 ≤ p) (hp : p ≤ (delta ^ 2)⁻¹) :
    Real.log (2 + p) ≤ 4 * |Real.log delta| := by
  have hdeltaOne : delta ≤ 1 := hhalf.trans (by norm_num)
  have hlogNonpos : Real.log delta ≤ 0 :=
    Real.log_nonpos hdelta.le hdeltaOne
  have hdeltaSqPos : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hdeltaSqLe : delta ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - delta)]
  have hinvOne : 1 ≤ (delta ^ 2)⁻¹ := by
    rw [one_le_inv₀ hdeltaSqPos]
    exact hdeltaSqLe
  have harg : 2 + p ≤ 3 * (delta ^ 2)⁻¹ := by nlinarith
  have hlogArg : Real.log (2 + p) ≤ Real.log (3 * (delta ^ 2)⁻¹) :=
    Real.log_le_log (by linarith) harg
  have hdeltaLog : Real.log delta ≤ Real.log (1 / 2 : ℝ) :=
    Real.log_le_log hdelta hhalf
  have hhalfLog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  have hlogTwoLe : Real.log 2 ≤ |Real.log delta| := by
    rw [abs_of_nonpos hlogNonpos]
    rw [hhalfLog] at hdeltaLog
    linarith
  have hlogThree : Real.log 3 ≤ 2 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (by norm_num : (3 : ℝ) ≤ 4)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    norm_num at h ⊢
    exact h
  calc
    Real.log (2 + p) ≤ Real.log (3 * (delta ^ 2)⁻¹) := hlogArg
    _ = Real.log 3 - 2 * Real.log delta := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
        (inv_ne_zero hdeltaSqPos.ne'), Real.log_inv, Real.log_pow]
      ring
    _ ≤ 4 * |Real.log delta| := by
      rw [abs_of_nonpos hlogNonpos]
      nlinarith

/-- A deliberately generous dimension-only spacing for concentric response
annuli. -/
def responseScoreRange (d : ℕ) : ℕ := d + 8

theorem responseScoreRange_pos (d : ℕ) : 0 < responseScoreRange d := by
  unfold responseScoreRange
  omega

private theorem abs_apply_sub_apply_lt_of_dist_lt {d : ℕ}
    {x y : Vec d} {epsilon : ℝ} (hxy : dist x y < epsilon) (i : Fin d) :
    |x i - y i| < epsilon := by
  have hcoord : |(x - y) i| ≤ ‖x - y‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) i
  exact hcoord.trans_lt (by simpa only [dist_eq_norm] using hxy)

private theorem cubeSet_origin_coordinate_bounds {d : ℕ} {m : ℤ}
    {x : Vec d} (hx : x ∈ cubeSet (originCube d m)) (i : Fin d) :
    -(3 : ℝ) ^ m / 2 ≤ x i ∧ x i < (3 : ℝ) ^ m / 2 := by
  have hi := hx i
  simp only [originCube, Pi.zero_apply, Int.cast_zero, cubeScaleFactor,
    zero_sub] at hi
  have hpow : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  constructor <;> nlinarith

private theorem cubeSet_descendant_coordinate_bounds {d : ℕ} {m n : ℤ}
    {R : TriadicCube d} (hnm : n ≤ m)
    (hR : R ∈ descendantsAtScale (originCube d m) n)
    {x : Vec d} (hx : x ∈ cubeSet R) (i : Fin d) :
    -(3 : ℝ) ^ m / 2 ≤ x i ∧ x i < (3 : ℝ) ^ m / 2 := by
  exact cubeSet_origin_coordinate_bounds
    (cubeSet_subset_of_mem_descendantsAtScale hnm hR hx) i

private theorem annulus_center_coordinate {d j : ℕ}
    {R : TriadicCube d}
    (hann : triadicCubeShift R ∉ cube d ((j : ℤ) - 1)) :
    ∃ i : Fin d,
      triadicCubeShift R i ≤ -(3 : ℝ) ^ ((j : ℤ) - 1) / 2 ∨
      (3 : ℝ) ^ ((j : ℤ) - 1) / 2 ≤ triadicCubeShift R i := by
  unfold cube at hann
  simp only [openCubeSet, Set.mem_setOf_eq, originCube, triadicCubeShift,
    cubeScaleFactor, not_forall, not_and_or, not_lt] at hann
  rcases hann with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simp only [Pi.zero_apply, Int.cast_zero, zero_sub] at hi
  change ((R.index i : ℝ) * (3 : ℝ) ^ R.scale ≤
      -(3 : ℝ) ^ ((j : ℤ) - 1) / 2 ∨
    (3 : ℝ) ^ ((j : ℤ) - 1) / 2 ≤
      (R.index i : ℝ) * (3 : ℝ) ^ R.scale)
  have hpow : 0 < (3 : ℝ) ^ ((j : ℤ) - 1) := zpow_pos (by norm_num) _
  rcases hi with hi | hi
  · left
    nlinarith
  · right
    nlinarith

private theorem cubePoint_near_shift_coordinate {d : ℕ} {n : ℤ}
    {R : TriadicCube d} (hscale : R.scale = n)
    {x : Vec d} (hx : x ∈ cubeSet R) (i : Fin d) :
    triadicCubeShift R i - (3 : ℝ) ^ n / 2 ≤ x i ∧
      x i < triadicCubeShift R i + (3 : ℝ) ^ n / 2 := by
  have hi := hx i
  simp only [triadicCubeShift, cubeScaleFactor, hscale] at hi ⊢
  have hpow : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  constructor <;> nlinarith

private theorem responseAnnulusReadRegion_outer_coordinate {d j : ℕ}
    {x : Vec d} (hx : x ∈ responseAnnulusReadRegion d j) :
    ∃ n : ℕ, ∃ _hnj : n + 2 ≤ j, ∃ i : Fin d,
      x i < -(3 : ℝ) ^ ((j : ℤ) - 1) / 2 + (3 : ℝ) ^ n / 2 +
          responseRestrictionBridgeRadius d ∨
      (3 : ℝ) ^ ((j : ℤ) - 1) / 2 - (3 : ℝ) ^ n / 2 -
          responseRestrictionBridgeRadius d < x i := by
  unfold responseAnnulusReadRegion at hx
  obtain ⟨n, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨R, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨x0, hx0, hdist⟩ := Metric.mem_thickening_iff.mp hx
  obtain ⟨i, hi | hi⟩ := annulus_center_coordinate R.2.2
  · refine ⟨n.1, n.2, i, Or.inl ?_⟩
    have hscale : R.1.scale = (n.1 : ℤ) :=
      scale_eq_of_mem_descendantsAtScale R.2.1
    have hcell := (cubePoint_near_shift_coordinate hscale hx0 i).2
    rw [zpow_natCast] at hcell
    have hpert := abs_apply_sub_apply_lt_of_dist_lt hdist i
    rw [abs_lt] at hpert
    nlinarith
  · refine ⟨n.1, n.2, i, Or.inr ?_⟩
    have hscale : R.1.scale = (n.1 : ℤ) :=
      scale_eq_of_mem_descendantsAtScale R.2.1
    have hcell := (cubePoint_near_shift_coordinate hscale hx0 i).1
    rw [zpow_natCast] at hcell
    have hpert := abs_apply_sub_apply_lt_of_dist_lt hdist i
    rw [abs_lt] at hpert
    nlinarith

private theorem responseAnnulusReadRegion_coordinate_bounds {d j : ℕ}
    {x : Vec d} (hx : x ∈ responseAnnulusReadRegion d j) (i : Fin d) :
    -(3 : ℝ) ^ j / 2 - responseRestrictionBridgeRadius d < x i ∧
      x i < (3 : ℝ) ^ j / 2 + responseRestrictionBridgeRadius d := by
  unfold responseAnnulusReadRegion at hx
  obtain ⟨n, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨R, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨x0, hx0, hdist⟩ := Metric.mem_thickening_iff.mp hx
  have hparent := cubeSet_descendant_coordinate_bounds
    (show (n.1 : ℤ) ≤ (j : ℤ) by exact_mod_cast (show n.1 ≤ j by omega))
    R.2.1 hx0 i
  rw [zpow_natCast] at hparent
  have hpert := abs_apply_sub_apply_lt_of_dist_lt hdist i
  rw [abs_lt] at hpert
  constructor <;> nlinarith

private theorem nat_succ_le_three_pow : ∀ d : ℕ, d + 1 ≤ 3 ^ d
  | 0 => by norm_num
  | d + 1 => by
      calc
        d + 1 + 1 ≤ 3 * (d + 1) := by omega
        _ ≤ 3 * 3 ^ d := Nat.mul_le_mul_left 3 (nat_succ_le_three_pow d)
        _ = 3 ^ (d + 1) := by rw [pow_succ]; ring

private theorem sqrt_nat_le_three_pow (d : ℕ) :
    Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ d := by
  have hsqrt : Real.sqrt (d : ℝ) ≤ (d : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg (d : ℝ)]
  exact hsqrt.trans (by exact_mod_cast nat_succ_le_three_pow d)

private theorem responseRestrictionBridgeRadius_lt_quarter (d : ℕ) [NeZero d] :
    responseRestrictionBridgeRadius d < 1 / 4 := by
  rw [responseRestrictionBridgeRadius, inv_eq_one_div]
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ((d : ℝ) + 1))]
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  nlinarith

private theorem response_annulus_numeric_gap {d a b n : ℕ} [NeZero d]
    (hab : a + responseScoreRange d ≤ b) (hnb : n + 2 ≤ b) :
    Real.sqrt (d : ℝ) * (3 : ℝ) ^ (a - 2) ≤
      (3 : ℝ) ^ ((b : ℤ) - 1) / 2 - (3 : ℝ) ^ n / 2 -
        ((3 : ℝ) ^ a / 2 + 2 * responseRestrictionBridgeRadius d) := by
  have hb2 : 2 ≤ b := by unfold responseScoreRange at hab; omega
  have hnle : n ≤ b - 2 := by omega
  have hable : a + d + 6 ≤ b - 2 := by
    unfold responseScoreRange at hab
    omega
  have hpowN : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (b - 2) :=
    pow_le_pow_right₀ (by norm_num) hnle
  have hpowBig : (3 : ℝ) ^ (a + d + 6) ≤ (3 : ℝ) ^ (b - 2) :=
    pow_le_pow_right₀ (by norm_num) hable
  have hpowB : (3 : ℝ) ^ ((b : ℤ) - 1) =
      3 * (3 : ℝ) ^ (b - 2) := by
    rw [show (b : ℤ) - 1 = ((b - 2 : ℕ) : ℤ) + 1 by omega,
      zpow_add₀ (by norm_num), zpow_natCast]
    ring
  have hpowAD : (3 : ℝ) ^ (a + d + 6) =
      (3 : ℝ) ^ a * (3 : ℝ) ^ d * 729 := by
    rw [pow_add, pow_add]
    norm_num
  have hP : 1 ≤ (3 : ℝ) ^ a := one_le_pow₀ (by norm_num)
  have hQ : 1 ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hsqrt := sqrt_nat_le_three_pow d
  have hpowSub : (3 : ℝ) ^ (a - 2) ≤ (3 : ℝ) ^ a :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le a 2)
  have htarget : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (a - 2) ≤
      (3 : ℝ) ^ a * (3 : ℝ) ^ d := by
    have hmul := mul_le_mul hsqrt hpowSub
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    simpa only [mul_comm] using hmul
  have heps := responseRestrictionBridgeRadius_lt_quarter d
  rw [hpowB]
  have hlarge : (3 : ℝ) ^ a * (3 : ℝ) ^ d * 729 ≤
      (3 : ℝ) ^ (b - 2) := by simpa only [hpowAD] using hpowBig
  have hroom : (3 : ℝ) ^ a * (3 : ℝ) ^ d +
      (3 : ℝ) ^ a / 2 + 1 / 2 ≤ (3 : ℝ) ^ (b - 2) := by
    calc
      _ ≤ (3 : ℝ) ^ a * (3 : ℝ) ^ d * 729 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hQ)]
      _ ≤ _ := hlarge
  nlinarith

private theorem abs_apply_le_vecNorm {d : ℕ} (v : Vec d) (i : Fin d) :
    |v i| ≤ Ch02.vecNorm v := by
  rw [← sq_le_sq₀ (abs_nonneg _) (Ch02.vecNorm_nonneg _), sq_abs,
    Ch02.vecNorm_sq_eq_vecNormSq]
  exact sq_apply_le_vecNormSq v i

theorem responseAnnulusReadRegion_separated_of_add_range_le
    {d a b : ℕ} [NeZero d]
    (hab : a + responseScoreRange d ≤ b) :
    ∀ x y : Vec d,
      x ∈ responseAnnulusReadRegion d b →
      y ∈ responseAnnulusReadRegion d a →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ (a - 2) ≤ Ch02.vecNorm (x - y) := by
  intro x y hx hy
  obtain ⟨n, hnb, i, hi⟩ := responseAnnulusReadRegion_outer_coordinate hx
  have hyi := responseAnnulusReadRegion_coordinate_bounds hy i
  have hgap := response_annulus_numeric_gap (d := d) hab hnb
  have hthreshold0 : 0 ≤ Real.sqrt (d : ℝ) * (3 : ℝ) ^ (a - 2) := by
    positivity
  have habs : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (a - 2) ≤ |(x - y) i| := by
    simp only [Pi.sub_apply]
    rcases hi with hi | hi
    · rw [abs_of_neg]
      · nlinarith
      · nlinarith
    · rw [abs_of_pos]
      · nlinarith
      · nlinarith
  exact habs.trans (abs_apply_le_vecNorm (x - y) i)

private theorem vecNorm_sub_comm {d : ℕ} (x y : Vec d) :
    Ch02.vecNorm (x - y) = Ch02.vecNorm (y - x) := by
  unfold Ch02.vecNorm
  rw [show (WithLp.toLp 2 (x - y) : EuclideanSpace ℝ (Fin d)) =
      -(WithLp.toLp 2 (y - x) : EuclideanSpace ℝ (Fin d)) by
    ext i
    simp]
  exact norm_neg _

theorem responseScoreArray_annulus_separation {d : ℕ} [NeZero d] :
    ∀ b : ℤ,
      Pairwise fun i j :
          {q : ℤ // 0 ≤ q * (responseScoreRange d : ℤ) + b} =>
        ∀ {x y : Vec d},
          x ∈ responseAnnulusReadRegion d
            (i.1 * (responseScoreRange d : ℤ) + b).toNat →
          y ∈ responseAnnulusReadRegion d
            (j.1 * (responseScoreRange d : ℤ) + b).toNat →
          Real.sqrt (d : ℝ) *
              (3 : ℝ) ^ min
                ((i.1 * (responseScoreRange d : ℤ) + b).toNat - 2)
                ((j.1 * (responseScoreRange d : ℤ) + b).toNat - 2) ≤
            Ch02.vecNorm (x - y) := by
  intro b i j hij x y hx hy
  let A := (i.1 * (responseScoreRange d : ℤ) + b).toNat
  let B := (j.1 * (responseScoreRange d : ℤ) + b).toNat
  have hAi : (A : ℤ) = i.1 * (responseScoreRange d : ℤ) + b := by
    exact Int.toNat_of_nonneg i.2
  have hBj : (B : ℤ) = j.1 * (responseScoreRange d : ℤ) + b := by
    exact Int.toNat_of_nonneg j.2
  have hijVal : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
  rcases lt_or_gt_of_ne hijVal with hijlt | hjilt
  · have hAB : A + responseScoreRange d ≤ B := by
      have hz : (A : ℤ) + responseScoreRange d ≤ (B : ℤ) := by
        rw [hAi, hBj]
        have hstep : i.1 + 1 ≤ j.1 := by omega
        have hr0 : (0 : ℤ) ≤ responseScoreRange d := by positivity
        nlinarith
      exact_mod_cast hz
    have hsep := responseAnnulusReadRegion_separated_of_add_range_le
      (d := d) hAB y x hy hx
    have hAle : A ≤ B := hAB.trans' (Nat.le_add_right A _)
    rw [min_eq_left (Nat.sub_le_sub_right hAle 2)]
    exact hsep.trans_eq (vecNorm_sub_comm y x)
  · have hBA : B + responseScoreRange d ≤ A := by
      have hz : (B : ℤ) + responseScoreRange d ≤ (A : ℤ) := by
        rw [hAi, hBj]
        have hstep : j.1 + 1 ≤ i.1 := by omega
        have hr0 : (0 : ℤ) ≤ responseScoreRange d := by positivity
        nlinarith
      exact_mod_cast hz
    have hsep := responseAnnulusReadRegion_separated_of_add_range_le
      (d := d) hBA x y hx hy
    have hBle : B ≤ A := hBA.trans' (Nat.le_add_right B _)
    rw [min_eq_right (Nat.sub_le_sub_right hBle 2)]
    exact hsep

/-- The response score really is finite-range: separated residue columns read
disjoint local coefficient sigma-fields. -/
theorem columnsIndep_responseScoreArray {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s epsilon K : ℝ) :
    SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      (responseScoreArray M s epsilon K) (responseScoreRange d) :=
  columnsIndep_responseScoreArray_of_separated M s epsilon K
    (responseScoreRange d) responseScoreArray_annulus_separation

theorem triadicCubeShift_eq_of_onTriadicGrid_of_mem_cubeSet
    {d n : ℕ} {z : Vec d} {R : TriadicCube d}
    (hscale : R.scale = (n : ℤ)) (hz : OnTriadicGrid n z)
    (hzR : z ∈ cubeSet R) : triadicCubeShift R = z := by
  funext i
  obtain ⟨k, hk⟩ := hz i
  have hcell := hzR i
  simp only [triadicCubeShift, cubeScaleFactor, hscale, zpow_natCast] at hcell ⊢
  rw [hk] at hcell ⊢
  have hpow : 0 < (3 : ℝ) ^ n := by positivity
  have hindex : R.index i = k := by
    exact_mod_cast (by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : (R.index i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlt
        nlinarith
      · have : (k : ℝ) + 1 ≤ (R.index i : ℝ) := by exact_mod_cast hgt
        nlinarith)
  rw [hindex]
  ring

/-- One common full-measure set dominates every unit direction.  The only
null-set choice is the finite quarter-net representative, so no uncountable
intersection over directions is taken. -/
theorem ae_forall_section6Response_le_two_mul_localNet
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ n : ℕ, ∀ R : TriadicCube d,
      R.scale = (n : ℤ) → ∀ e : Vec d, vecNormSq e = 1 →
        ENNReal.ofReal
            (section6Response M n n omega (triadicCubeShift R) e) ≤
          2 * localNormalizedResponseQuarterNetMax M n R omega := by
  rw [ae_all_iff]
  intro n
  rw [ae_all_iff]
  intro R
  filter_upwards [normalizedResponseQuarterNetMax_ae_eq_local M n R] with omega heq
  intro hscale e he
  calc
    ENNReal.ofReal (section6Response M n n omega (triadicCubeShift R) e) ≤
        normalizedDefect M n (Ch02.cubeDomain R) omega :=
      ofReal_section6Response_shift_le_normalizedDefect M n R hscale e he omega
    _ ≤ 2 * normalizedResponseQuarterNetMax M n (Ch02.cubeDomain R) omega :=
      normalizedDefect_le_two_mul_quarterNetMax M n (Ch02.cubeDomain R) omega
    _ = 2 * localNormalizedResponseQuarterNetMax M n R omega := by rw [heq]

theorem localNormalizedResponseQuarterNetMax_ne_top
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (R : TriadicCube d)
    (omega : Sample d) : localNormalizedResponseQuarterNetMax M n R omega ≠ ∞ := by
  unfold localNormalizedResponseQuarterNetMax
  rw [Finset.sup'_apply]
  apply ne_of_lt
  rw [Finset.sup'_lt_iff]
  exact fun _ _ => ENNReal.ofReal_lt_top

theorem localResponseScaleAtom_ne_top {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j n : ℕ) (omega : Sample d) :
    localResponseScaleAtom M j n omega ≠ ∞ := by
  unfold localResponseScaleAtom
  split_ifs
  · dsimp only [localResponseAnnulusMax]
    apply ne_of_lt
    rw [Finset.sup'_lt_iff]
    intro R _
    by_cases hann : triadicCubeShift R ∉ cube d ((j : ℤ) - 1)
    · rw [if_pos hann]
      exact (localNormalizedResponseQuarterNetMax_ne_top M n R omega).lt_top
    · rw [if_neg hann]
      simp
  · simp

theorem localResponseScore_ne_top {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s epsilon K : ℝ) (j : ℕ)
    (omega : Sample d) : localResponseScore M s epsilon K j omega ≠ ∞ := by
  unfold localResponseScore
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  rw [ENNReal.sum_ne_top]
  intro n hn
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (localResponseScaleAtom_ne_top M j n omega)

theorem responseScoreArray_nonneg {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s epsilon K : ℝ)
    (m j : ℤ) (omega : Sample d) :
    0 ≤ responseScoreArray M s epsilon K m j omega := by
  unfold responseScoreArray
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem summable_responseScoreArray_row {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s epsilon K : ℝ)
    (m : ℕ) (omega : Sample d) :
    Summable fun j : ℤ => SubdiffusiveProcess.Concentration.wt s (m : ℤ) j *
      responseScoreArray M s epsilon K (m : ℤ) j omega := by
  refine summable_of_ne_finset_zero
    (s := Finset.Icc (0 : ℤ) (m : ℤ)) fun j hj => ?_
  simp only [Finset.mem_Icc, not_and_or] at hj
  unfold responseScoreArray
  have hinactive : ¬(0 ≤ (m : ℤ) ∧ 0 ≤ j ∧ j ≤ (m : ℤ)) := by omega
  rw [if_neg hinactive]
  simp

private theorem idist_natCast_eq_sub {m j : ℕ} (hjm : j ≤ m) :
    SubdiffusiveProcess.Concentration.idist (m : ℤ) (j : ℤ) = ((m - j : ℕ) : ℝ) := by
  unfold SubdiffusiveProcess.Concentration.idist
  change |(m : ℝ) - (j : ℝ)| = ((m - j : ℕ) : ℝ)
  have hcast : (m : ℝ) - (j : ℝ) = ((m - j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hjm]
  rw [hcast, abs_of_nonneg (Nat.cast_nonneg _)]

theorem measurable_responseScoreArray {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s epsilon K : ℝ) (m j : ℤ) :
    Measurable (responseScoreArray M s epsilon K m j) := by
  unfold responseScoreArray
  split_ifs
  · exact ENNReal.measurable_toReal.comp
      ((measurable_localResponseScore M s epsilon K j.toNat).mono
        (aCutoffPotentialLocalSigma_le_borel _) le_rfl)
  · exact measurable_const

theorem lintegral_responseScoreArray_rpow_le_one_of_norm
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s epsilon K p : ℝ}
    (hp : 1 ≤ p)
    (hnorm : ∀ j : ℕ,
      paperENNRealLpNorm M.P.toMeasure p (localResponseScore M s epsilon K j) ≤ 1) :
    ∀ m j : ℤ,
      ∫⁻ omega, ENNReal.ofReal ((responseScoreArray M s epsilon K m j omega) ^ p)
        ∂M.P.toMeasure ≤ 1 := by
  intro m j
  unfold responseScoreArray
  split_ifs with hactive
  · have hp0 : 0 < p := zero_lt_one.trans_le hp
    have hraw := hnorm j.toNat
    unfold paperENNRealLpNorm at hraw
    have hinv : 0 < p⁻¹ := inv_pos.mpr hp0
    have hmoment :
        ∫⁻ omega, (localResponseScore M s epsilon K j.toNat omega) ^ p
          ∂M.P.toMeasure ≤ 1 := by
      rw [← ENNReal.one_rpow p⁻¹] at hraw
      exact (ENNReal.rpow_le_rpow_iff hinv).mp hraw
    have heq : (fun omega => ENNReal.ofReal
        (((localResponseScore M s epsilon K j.toNat omega).toReal) ^ p)) =
        fun omega => (localResponseScore M s epsilon K j.toNat omega) ^ p := by
      funext omega
      calc
        ENNReal.ofReal (((localResponseScore M s epsilon K j.toNat omega).toReal) ^ p) =
            ENNReal.ofReal
              ((localResponseScore M s epsilon K j.toNat omega ^ p).toReal) :=
          congrArg ENNReal.ofReal (ENNReal.toReal_rpow _ _)
        _ = _ := ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg hp0.le
          (localResponseScore_ne_top M s epsilon K j.toNat omega))
    rw [heq]
    exact hmoment
  · rw [Real.zero_rpow (zero_lt_one.trans_le hp).ne']
    simp

private theorem response_descendant_card_rpow_eq
    {d j n : ℕ} {p : ℝ} (hnj : n ≤ j) (hp : 0 < p) :
    ((descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹ =
      ENNReal.ofReal ((3 : ℝ) ^ (((d : ℝ) / p) * ((j : ℝ) - (n : ℝ)))) := by
  have hscale : (n : ℤ) ≤ (originCube d (j : ℤ)).scale := by
    change (n : ℤ) ≤ (j : ℤ)
    exact_mod_cast hnj
  have hcard :
      (descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)).card =
        (3 ^ d) ^ (j - n) := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d (j : ℤ)) hscale]
    have hdepth : Int.toNat ((originCube d (j : ℤ)).scale - (n : ℤ)) =
        j - n := by simp only [originCube]; omega
    rw [hdepth, descendantsAtDepth_card]
  rw [hcard, ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr hp.le)]
  apply congrArg ENNReal.ofReal
  rw [Nat.cast_pow, Nat.cast_pow]
  norm_num only [Nat.cast_ofNat]
  rw [← Real.rpow_natCast (3 : ℝ) d]
  change Real.rpow ((Real.rpow 3 (d : ℝ)) ^ (j - n)) p⁻¹ = _
  rw [← Real.rpow_natCast (Real.rpow 3 (d : ℝ)) (j - n)]
  calc
    Real.rpow (Real.rpow (Real.rpow 3 (d : ℝ)) ((j - n : ℕ) : ℝ)) p⁻¹ =
        Real.rpow (Real.rpow 3 ((d : ℝ) * ((j - n : ℕ) : ℝ))) p⁻¹ := by
      congr 1
      exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) _ _).symm
    _ = Real.rpow 3 (((d : ℝ) * ((j - n : ℕ) : ℝ)) * p⁻¹) :=
      (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) _ _).symm
    _ = _ := by
      congr 1
      rw [Nat.cast_sub hnj]
      field_simp [hp.ne']

/-- The descendant count costs at most half of the geometric response
discount once `p ≥ 2d/s`. -/
theorem responseScore_geometric_sum_le
    {d j : ℕ} {s p : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hp : 0 < p)
    (hdim : 2 * (d : ℝ) * s⁻¹ ≤ p) :
    ∑ n ∈ Finset.range (j - 1),
        ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
          ((descendantsAtScale
            (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹ ≤
      ENNReal.ofReal (4 / s) := by
  have hdp : (d : ℝ) / p ≤ s / 2 := by
    have hsInv : 0 < s⁻¹ := inv_pos.mpr hs
    have h := mul_le_mul_of_nonneg_right hdim (inv_nonneg.mpr hp.le)
    field_simp [hp.ne', hs.ne'] at h ⊢
    nlinarith
  have hsumReal :
      ∑ n ∈ Finset.range (j - 1),
          (3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ))) ≤ 4 / s := by
    have hsummable := SubdiffusiveProcess.Concentration.summable_wt_half hs hs1 (j : ℤ)
    have hfinite := hsummable.sum_le_tsum
      (s := (Finset.range (j - 1)).map
        ⟨Int.ofNat, Int.ofNat_injective⟩)
      (fun q _ => SubdiffusiveProcess.Concentration.wt_nonneg (s / 2) (j : ℤ) q)
    have hbound := SubdiffusiveProcess.Concentration.sum_wt_half_le hs hs1 (j : ℤ)
    apply le_trans _ hbound
    rw [Finset.sum_map] at hfinite
    apply (Finset.sum_le_sum fun n hn => ?_).trans hfinite
    simp only [Function.Embedding.coeFn_mk, SubdiffusiveProcess.Concentration.wt,
      SubdiffusiveProcess.Concentration.idist_eq]
    have hnj : n ≤ j := by
      have : n < j - 1 := Finset.mem_range.mp hn
      omega
    have habs : ((j : ℤ) - Int.ofNat n).natAbs = j - n := by
      simpa only [Int.ofNat_eq_natCast] using
        Int.natAbs_natCast_sub_natCast_of_ge hnj
    rw [habs, Nat.cast_sub hnj]
    ring_nf
    exact le_rfl
  calc
    ∑ n ∈ Finset.range (j - 1),
        ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
          ((descendantsAtScale
            (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹ ≤
        ∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((j : ℝ) - (n : ℝ)))) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnj : n ≤ j := by
        have : n < j - 1 := Finset.mem_range.mp hn
        omega
      rw [response_descendant_card_rpow_eq hnj hp,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ))
      have hgap : 0 ≤ (j : ℝ) - (n : ℝ) :=
        sub_nonneg.mpr (by exact_mod_cast hnj)
      nlinarith [mul_le_mul_of_nonneg_right hdp hgap]
    _ ≤ _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => Real.rpow_nonneg (by norm_num) _)]
      exact ENNReal.ofReal_le_ofReal hsumReal

/-- The manuscript's scalar response budget implies the unit score moment
required by `concentration_for_scales`. -/
theorem localResponseScore_norm_le_one_of_numeric
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {s epsilon K C p : ℝ} (j : ℕ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hepsilon : 0 < epsilon)
    (hK : 0 < K) (hC : 0 < C) (hp : 1 ≤ p)
    (hdim : 2 * (d : ℝ) * s⁻¹ ≤ p)
    (hmoment :
      paperENNRealLpNorm M.P.toMeasure p
          (localResponseScore M s epsilon K j) ≤
        ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
          ∑ n ∈ Finset.range (j - 1),
            ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
              ((descendantsAtScale
                (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹ *
              ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2))
    (hnumeric :
      8 * K * C * p * Real.log (2 + p) * M.delta ^ 2 ≤
        s ^ 2 * epsilon ^ 2) :
    paperENNRealLpNorm M.P.toMeasure p
        (localResponseScore M s epsilon K j) ≤ 1 := by
  have hsum := responseScore_geometric_sum_le (j := j) hs hs1
    (zero_lt_one.trans_le hp) hdim
  have hA0 : 0 ≤ C * p * Real.log (2 + p) * M.delta ^ 2 := by
    have hlog : 0 ≤ Real.log (2 + p) :=
      Real.log_nonneg (by linarith)
    positivity
  have hcoef0 : 0 ≤ 2 * K * s⁻¹ * (epsilon ^ 2)⁻¹ := by positivity
  have hsdiv0 : 0 ≤ 4 / s := by positivity
  have hfactor :
      (∑ n ∈ Finset.range (j - 1),
        ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
          ((descendantsAtScale
            (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹ *
          ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2)) =
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹) *
          ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2) := by
    exact (Finset.sum_mul (s := Finset.range (j - 1))
        (f := fun n =>
          ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹)
        (ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2))).symm
  calc
    paperENNRealLpNorm M.P.toMeasure p
        (localResponseScore M s epsilon K j) ≤
        ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
          ∑ n ∈ Finset.range (j - 1),
            ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
              ((descendantsAtScale
                (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹ *
              ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2) := hmoment
    _ = ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹) *
          ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2) := by
      rw [hfactor]
      ring
    _ ≤ ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
        ENNReal.ofReal (4 / s) *
          ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (zero_le _)) (zero_le _)
    _ = ENNReal.ofReal ((2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
        (4 / s) * (C * p * Real.log (2 + p) * M.delta ^ 2)) := by
      rw [← ENNReal.ofReal_mul hcoef0,
        ← ENNReal.ofReal_mul (mul_nonneg hcoef0 hsdiv0)]
    _ ≤ 1 := by
      rw [ENNReal.ofReal_le_one]
      have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
      have heps2 : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
      field_simp [hs.ne', hepsilon.ne']
      nlinarith

theorem not_goodResponse_imp_lt_Yk_responseScoreArray
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (omega : Sample d)
    {t epsilon K : ℝ} (ht : 0 < t) (hepsilon : 0 < epsilon) (hK : 0 < K)
    (hall : ∀ n : ℕ, ∀ R : TriadicCube d,
      R.scale = (n : ℤ) → ∀ e : Vec d, vecNormSq e = 1 →
        ENNReal.ofReal
            (section6Response M n n omega (triadicCubeShift R) e) ≤
          2 * localNormalizedResponseQuarterNetMax M n R omega)
    (m : ℕ) (hbad : ¬ GoodResponse M none m 0 epsilon (8 * t) omega) :
    K * t⁻¹ < SubdiffusiveProcess.Concentration.Yk
      (responseScoreArray M t epsilon K) t (m : ℤ) omega := by
  unfold GoodResponse at hbad
  push_neg at hbad
  obtain ⟨j, n, hjm, hnj, z, hzgrid, hzann, e, he, hresponse⟩ := hbad
  have hzparent : z ∈ cubeSet (originCube d (j : ℤ)) :=
    openCubeSet_subset_cubeSet _ (by simpa only [sub_zero] using hzann.1)
  have hcover := cubeSet_subset_iUnion_descendantsAtScale
    (originCube d (j : ℤ))
    (show (n : ℤ) ≤ (originCube d (j : ℤ)).scale by
      change (n : ℤ) ≤ (j : ℤ)
      exact_mod_cast (show n ≤ j by omega)) hzparent
  obtain ⟨R, hR, hzR⟩ := Set.mem_iUnion₂.1 hcover
  have hscale : R.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hR
  have hshift : triadicCubeShift R = z :=
    triadicCubeShift_eq_of_onTriadicGrid_of_mem_cubeSet hscale
      (by simpa only [sub_zero] using hzgrid) hzR
  have hannR : triadicCubeShift R ∉ cube d ((j : ℤ) - 1) := by
    rw [hshift]
    simpa only [sub_zero] using hzann.2
  have hnetAtom : localNormalizedResponseQuarterNetMax M n R omega ≤
      localResponseScaleAtom M j n omega := by
    unfold localResponseScaleAtom
    rw [dif_pos hnj]
    dsimp only [localResponseAnnulusMax]
    calc
      localNormalizedResponseQuarterNetMax M n R omega =
          (if triadicCubeShift R ∉ cube d ((j : ℤ) - 1) then
            localNormalizedResponseQuarterNetMax M n R omega else 0) := by
        rw [if_pos hannR]
      _ ≤ _ := Finset.le_sup' (fun Q =>
        if triadicCubeShift Q ∉ cube d ((j : ℤ) - 1) then
          localNormalizedResponseQuarterNetMax M n Q omega else 0) hR
  have hresponseLocal : ENNReal.ofReal
      (section6Response M n n omega z e) ≤
        2 * localResponseScaleAtom M j n omega := by
    rw [← hshift]
    exact (hall n R hscale e he).trans
      (mul_le_mul_of_nonneg_left hnetAtom (by norm_num))
  have hresponse0 : 0 < section6Response M n n omega z e := by
    have hleft : 0 ≤ epsilon ^ 2 *
        (3 : ℝ) ^ (((8 * t) * ((m : ℝ) - (n : ℝ))) / 8) := by
      positivity
    exact hleft.trans_lt (by simpa using hresponse)
  have hlocalReal : section6Response M n n omega z e ≤
      2 * (localResponseScaleAtom M j n omega).toReal := by
    have htop : 2 * localResponseScaleAtom M j n omega ≠ ∞ :=
      ENNReal.mul_ne_top (by norm_num) (localResponseScaleAtom_ne_top M j n omega)
    have := ENNReal.toReal_mono htop hresponseLocal
    simpa only [ENNReal.toReal_ofReal hresponse0.le, ENNReal.toReal_ofNat,
      ENNReal.toReal_mul, localResponseScaleAtom_ne_top] using this
  have hjRange : j ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
  have hnRange : n ∈ Finset.range (j - 1) := Finset.mem_range.2 (by omega)
  have hscoreTerm :
      ENNReal.ofReal (2 * K * t⁻¹ * (epsilon ^ 2)⁻¹) *
          (ENNReal.ofReal ((3 : ℝ) ^ (-t * ((j : ℝ) - (n : ℝ)))) *
            localResponseScaleAtom M j n omega) ≤
        localResponseScore M t epsilon K j omega := by
    unfold localResponseScore
    apply mul_le_mul_right
    exact Finset.single_le_sum
      (f := fun q : ℕ => ENNReal.ofReal
        ((3 : ℝ) ^ (-t * ((j : ℝ) - (q : ℝ)))) *
          localResponseScaleAtom M j q omega)
      (fun _ _ => bot_le) hnRange
  have hscoreReal := ENNReal.toReal_mono (localResponseScore_ne_top M t epsilon K j omega)
    hscoreTerm
  have hcoef0 : 0 ≤ 2 * K * t⁻¹ * (epsilon ^ 2)⁻¹ := by positivity
  have hweight0 : 0 ≤ (3 : ℝ) ^ (-t * ((j : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hcoef0, ENNReal.toReal_ofReal hweight0] at hscoreReal
  have hexponent : (8 * t) * ((m : ℝ) - (n : ℝ)) / 8 =
      t * ((m : ℝ) - (n : ℝ)) := by ring
  have hnone : min n ((none : Option ℕ).getD n) = n := by simp
  rw [hnone] at hresponse
  have hresponse' : epsilon ^ 2 *
      (3 : ℝ) ^ (t * ((m : ℝ) - (n : ℝ))) <
        section6Response M n n omega z e := by
    simpa only [hexponent] using hresponse
  have hatom : epsilon ^ 2 *
      (3 : ℝ) ^ (t * ((m : ℝ) - (n : ℝ))) <
        2 * (localResponseScaleAtom M j n omega).toReal :=
    hresponse'.trans_le hlocalReal
  have hlocalScore : K * t⁻¹ *
      (3 : ℝ) ^ (t * ((m : ℝ) - (j : ℝ))) <
        (localResponseScore M t epsilon K j omega).toReal := by
    calc
      K * t⁻¹ * (3 : ℝ) ^ (t * ((m : ℝ) - (j : ℝ))) =
          (2 * K * t⁻¹ * (epsilon ^ 2)⁻¹) *
            (3 : ℝ) ^ (-t * ((j : ℝ) - (n : ℝ))) *
              (epsilon ^ 2 *
                (3 : ℝ) ^ (t * ((m : ℝ) - (n : ℝ))) / 2) := by
        field_simp [ht.ne', hepsilon.ne']
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring
      _ < (2 * K * t⁻¹ * (epsilon ^ 2)⁻¹) *
            (3 : ℝ) ^ (-t * ((j : ℝ) - (n : ℝ))) *
              (localResponseScaleAtom M j n omega).toReal := by
        apply mul_lt_mul_of_pos_left
        · nlinarith
        · positivity
      _ ≤ _ := by simpa only [mul_assoc] using hscoreReal
  have hrow := (summable_responseScoreArray_row M t epsilon K m omega).le_tsum
    (j : ℤ) (fun q _ => mul_nonneg (SubdiffusiveProcess.Concentration.wt_nonneg _ _ _)
      (responseScoreArray_nonneg M t epsilon K _ _ omega))
  have hjInt : (j : ℤ) ≤ (m : ℤ) := by exact_mod_cast hjm
  have hterm : SubdiffusiveProcess.Concentration.wt t (m : ℤ) (j : ℤ) *
      (localResponseScore M t epsilon K j omega).toReal ≤
        SubdiffusiveProcess.Concentration.Yk (responseScoreArray M t epsilon K) t (m : ℤ) omega := by
    unfold SubdiffusiveProcess.Concentration.Yk
    simpa only [responseScoreArray, Int.natCast_nonneg, hjInt, and_self, if_true,
      Int.toNat_natCast] using hrow
  apply lt_of_lt_of_le _ hterm
  unfold SubdiffusiveProcess.Concentration.wt
  rw [idist_natCast_eq_sub hjm]
  have hweightPos : 0 < (3 : ℝ) ^ (-(t * ((m - j : ℕ) : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc
    K * t⁻¹ = (3 : ℝ) ^ (-(t * ((m - j : ℕ) : ℝ))) *
        (K * t⁻¹ * (3 : ℝ) ^ (t * ((m : ℝ) - (j : ℝ)))) := by
      have hcast : ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := by
        exact Nat.cast_sub hjm
      rw [hcast]
      rw [show (3 : ℝ) ^ (-(t * ((m : ℝ) - (j : ℝ)))) *
          (K * t⁻¹ * (3 : ℝ) ^ (t * ((m : ℝ) - (j : ℝ)))) =
        K * t⁻¹ * ((3 : ℝ) ^ (-(t * ((m : ℝ) - (j : ℝ)))) *
          (3 : ℝ) ^ (t * ((m : ℝ) - (j : ℝ)))) by ring]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      norm_num
    _ < _ := mul_lt_mul_of_pos_left hlocalScore hweightPos

/-- The literal response failure is dominated by the response score on the
single common full-measure set supplied by the finite quarter net. -/
theorem ae_not_goodResponse_imp_lt_Yk_responseScoreArray
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {t epsilon K : ℝ} (ht : 0 < t) (hepsilon : 0 < epsilon) (hK : 0 < K) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ m : ℕ,
      ¬ GoodResponse M none m 0 epsilon (8 * t) omega →
        K * t⁻¹ < SubdiffusiveProcess.Concentration.Yk
          (responseScoreArray M t epsilon K) t (m : ℤ) omega := by
  filter_upwards [ae_forall_section6Response_le_two_mul_localNet M] with omega hall
  intro m hbad
  exact not_goodResponse_imp_lt_Yk_responseScoreArray
    M omega ht hepsilon hK hall m hbad

/-- Response-event density concentration after exposing the score-moment and
scalar threshold normalizations. -/
theorem measure_goodResponse_badDensity_le_of_parameters
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {t epsilon theta K p : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hepsilon : 0 < epsilon)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hK : 0 < K) (hp : 1 ≤ p) (htp : 1 ≤ t * p)
    (hthreshold : 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
        (theta / 2) ^ (-1 / p) < K * t⁻¹)
    (hnorm : ∀ j : ℕ,
      paperENNRealLpNorm M.P.toMeasure p
        (localResponseScore M t epsilon K j) ≤ 1)
    (m0 window : ℕ) :
    M.P.toMeasure {omega | theta ≤ intervalEventDensity
        (fun m => {omega : Sample d |
          GoodResponse M none m 0 epsilon (8 * t) omega}ᶜ)
        m0 window omega} ≤
      ENNReal.ofReal (Real.exp
        (-(t * p * (theta / 2)) /
          (16 * (responseScoreRange d : ℝ)) * ((window : ℝ) + 1))) := by
  have hconc := SubdiffusiveProcess.Concentration.concentration_for_scales_Cstar
    M.P.toMeasure (responseScoreArray M t epsilon K) hp ht ht1 htp
    (responseScoreRange_pos d)
    (measurable_responseScoreArray M t epsilon K)
    (responseScoreArray_nonneg M t epsilon K)
    (lintegral_responseScoreArray_rpow_le_one_of_norm M hp hnorm)
    (columnsIndep_responseScoreArray M t epsilon K)
    (m0 : ℤ) window (theta / 2) (by positivity) (by linarith)
  let CE : Set (Sample d) := {omega | theta / 2 < (1 / ((window : ℝ) + 1)) *
      ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
        (if 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
            (theta / 2) ^ (-1 / p) <
              SubdiffusiveProcess.Concentration.Yk (responseScoreArray M t epsilon K)
                t k omega then (1 : ℝ) else 0)}
  have hreduce := ae_not_goodResponse_imp_lt_Yk_responseScoreArray
    M ht hepsilon hK
  have hmono : {omega | theta ≤ intervalEventDensity
        (fun m => {omega : Sample d |
          GoodResponse M none m 0 epsilon (8 * t) omega}ᶜ)
        m0 window omega} ≤ᶠ[ae M.P.toMeasure] CE := by
    filter_upwards [hreduce] with omega hreduce homega
    unfold intervalEventDensity at homega
    change theta / 2 < (1 / ((window : ℝ) + 1)) *
      ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
        (if 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
            (theta / 2) ^ (-1 / p) <
              SubdiffusiveProcess.Concentration.Yk (responseScoreArray M t epsilon K)
                t k omega then (1 : ℝ) else 0)
    have hcount :
        ∑ k ∈ Finset.Icc m0 (m0 + window),
            (if omega ∈ {omega : Sample d |
                GoodResponse M none k 0 epsilon (8 * t) omega}ᶜ
              then (1 : ℝ) else 0) ≤
          ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
            (if 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
                (theta / 2) ^ (-1 / p) <
                  SubdiffusiveProcess.Concentration.Yk (responseScoreArray M t epsilon K)
                    t k omega then (1 : ℝ) else 0) := by
      let natToInt : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
      rw [show Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)) =
          (Finset.Icc m0 (m0 + window)).map natToInt by
        ext z
        simp only [Finset.mem_Icc, Finset.mem_map]
        constructor
        · intro hz
          have hz0 : 0 ≤ z := (show (0 : ℤ) ≤ m0 by omega).trans hz.1
          have hzEq : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
          refine ⟨z.toNat, ?_, ?_⟩
          · constructor
            · have hzLower : (m0 : ℤ) ≤ (z.toNat : ℤ) := by
                simpa only [hzEq] using hz.1
              omega
            · have hzUpper : (z.toNat : ℤ) ≤ ((m0 + window : ℕ) : ℤ) := by
                simpa only [hzEq, Nat.cast_add] using hz.2
              omega
          · simp only [natToInt, Function.Embedding.coeFn_mk]
            exact hzEq
        · rintro ⟨k, hk, rfl⟩
          simp only [natToInt, Function.Embedding.coeFn_mk]
          constructor
          · simpa only [Int.ofNat_eq_natCast] using
              (show (m0 : ℤ) ≤ (k : ℤ) by exact_mod_cast hk.1)
          · simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
              (show (k : ℤ) ≤ ((m0 + window : ℕ) : ℤ) by
                exact_mod_cast hk.2),
        Finset.sum_map]
      apply Finset.sum_le_sum
      intro k hk
      by_cases hbad : omega ∈ {omega : Sample d |
          GoodResponse M none k 0 epsilon (8 * t) omega}ᶜ
      · rw [if_pos hbad]
        have hy := hreduce k (by simpa only [Set.mem_compl_iff,
          Set.mem_setOf_eq, not_not] using hbad)
        have hscore : 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
            (theta / 2) ^ (-1 / p) <
              SubdiffusiveProcess.Concentration.Yk (responseScoreArray M t epsilon K)
                t (k : ℤ) omega := hthreshold.trans hy
        rw [if_pos (by simpa only [natToInt, Function.Embedding.coeFn_mk] using hscore)]
      · rw [if_neg hbad]
        split_ifs <;> norm_num
    have hcount' :
        (∑ m ∈ Finset.Icc m0 (m0 + window),
          eventIndicator
            ((fun m => {omega : Sample d |
              GoodResponse M none m 0 epsilon (8 * t) omega}ᶜ) m) omega) ≤
          ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
            (if 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
                (theta / 2) ^ (-1 / p) <
                  SubdiffusiveProcess.Concentration.Yk (responseScoreArray M t epsilon K)
                    t k omega then (1 : ℝ) else 0) := by
      convert hcount using 1;
        simp only [eventIndicator, Set.mem_compl_iff, Set.mem_setOf_eq]
    have havg := homega.trans
      (div_le_div_of_nonneg_right hcount' (by positivity))
    have havg' : theta ≤ (1 / ((window : ℝ) + 1)) *
        ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
          (if 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
              (theta / 2) ^ (-1 / p) <
                SubdiffusiveProcess.Concentration.Yk (responseScoreArray M t epsilon K)
                  t k omega then (1 : ℝ) else 0) := by
      calc
        theta ≤ (∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
            (if 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
                (theta / 2) ^ (-1 / p) <
                  SubdiffusiveProcess.Concentration.Yk (responseScoreArray M t epsilon K)
                    t k omega then (1 : ℝ) else 0)) /
              ((window : ℝ) + 1) := havg
        _ = _ := by ring
    exact (by linarith : theta / 2 < theta).trans_le havg'
  exact (MeasureTheory.measure_mono_ae hmono).trans (by
    simpa only [CE] using hconc)

private theorem responseMoment_le_headlineRange
    {t epsilon D C delta L : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hD : 0 < D) (hC : 0 < C) (hDC : C ≤ D)
    (hdelta : 0 < delta) (hL : 0 < L) :
    t ^ 2 * epsilon ^ 2 / (D * (delta ^ 2 * L)) ≤
      C⁻¹ * (delta ^ 2)⁻¹ * L⁻¹ := by
  have htSq : t ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ ht0 ht1 2
  have heSq : epsilon ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ he0 he1 2
  have hprod : t ^ 2 * epsilon ^ 2 ≤ 1 := by
    simpa only [one_pow, one_mul] using
      mul_le_mul htSq heSq (sq_nonneg epsilon) (by norm_num : (0 : ℝ) ≤ 1 ^ 2)
  have hInv : D⁻¹ ≤ C⁻¹ := (inv_le_inv₀ hD hC).2 hDC
  calc
    t ^ 2 * epsilon ^ 2 / (D * (delta ^ 2 * L)) =
        (t ^ 2 * epsilon ^ 2) * D⁻¹ * (delta ^ 2)⁻¹ * L⁻¹ := by
      field_simp [hD.ne', hdelta.ne', hL.ne']
    _ ≤ 1 * C⁻¹ * (delta ^ 2)⁻¹ * L⁻¹ := by gcongr
    _ = _ := by rw [one_mul]

private theorem responseMoment_le_deltaInv
    {t epsilon D delta L : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hD : 0 < D) (hdelta : 0 < delta) (hL : 0 < L)
    (hDL : 1 ≤ D * L) :
    t ^ 2 * epsilon ^ 2 / (D * (delta ^ 2 * L)) ≤ (delta ^ 2)⁻¹ := by
  have htSq : t ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ ht0 ht1 2
  have heSq : epsilon ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ he0 he1 2
  have hprod : t ^ 2 * epsilon ^ 2 ≤ 1 := by
    simpa only [one_pow, one_mul] using
      mul_le_mul htSq heSq (sq_nonneg epsilon) (by norm_num : (0 : ℝ) ≤ 1 ^ 2)
  have hInv : (D * L)⁻¹ ≤ 1 := (inv_le_one₀ (mul_pos hD hL)).2 hDL
  calc
    t ^ 2 * epsilon ^ 2 / (D * (delta ^ 2 * L)) =
        (t ^ 2 * epsilon ^ 2) * (D * L)⁻¹ * (delta ^ 2)⁻¹ := by
      field_simp [hD.ne', hdelta.ne', hL.ne']
    _ ≤ 1 * 1 * (delta ^ 2)⁻¹ := by gcongr
    _ = _ := by norm_num

private theorem responseMoment_numeric
    {A C D t epsilon delta L p : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hD : 0 < D)
    (ht : 0 < t) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hL : 0 < L)
    (hp : p = t ^ 2 * epsilon ^ 2 / (D * (delta ^ 2 * L)))
    (hlog : Real.log (2 + p) ≤ 4 * L)
    (hDlarge : 32 * A * C ≤ D) :
    8 * A * C * p * Real.log (2 + p) * delta ^ 2 ≤
      t ^ 2 * epsilon ^ 2 := by
  have hfac : 0 ≤ 8 * A * C * p * delta ^ 2 := by
    rw [hp]
    positivity
  calc
    8 * A * C * p * Real.log (2 + p) * delta ^ 2 =
        (8 * A * C * p * delta ^ 2) * Real.log (2 + p) := by ring
    _ ≤ (8 * A * C * p * delta ^ 2) * (4 * L) :=
      mul_le_mul_of_nonneg_left hlog hfac
    _ = (32 * A * C / D) * (t ^ 2 * epsilon ^ 2) := by
      rw [hp]
      field_simp [hD.ne', hdelta.ne', hL.ne']
      ring
    _ ≤ t ^ 2 * epsilon ^ 2 := by
      have hratio : 32 * A * C / D ≤ 1 := (div_le_one hD).2 hDlarge
      exact mul_le_of_le_one_left
        (mul_nonneg (sq_nonneg t) (sq_nonneg epsilon)) hratio

private theorem response_threshold_scaled
    {t theta p A : ℝ} (ht : 0 < t)
    (h : 6 * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
      (theta / 2) ^ (-1 / p) < A) :
    6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
      (theta / 2) ^ (-1 / p) < A * t⁻¹ := by
  have hmul := mul_lt_mul_of_pos_right h (inv_pos.mpr ht)
  convert hmul using 1
  all_goals ring

private theorem response_one_le_tp_of_dim {d : ℕ} [NeZero d]
    {t p : ℝ} (ht : 0 < t) (hdim : 2 * (d : ℝ) * t⁻¹ ≤ p) :
    1 ≤ t * p := by
  have hmul := mul_le_mul_of_nonneg_right hdim ht.le
  have hcancel : 2 * (d : ℝ) * t⁻¹ * t = 2 * (d : ℝ) := by
    field_simp [ht.ne']
  rw [hcancel] at hmul
  have hd : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (NeZero.one_le : 1 ≤ d)
  calc
    1 ≤ 2 * (d : ℝ) := by linarith only [hd]
    _ ≤ t * p := by simpa only [mul_comm] using hmul

private theorem response_rate_compare
    {t p theta epsilon D C0 delta L r : ℝ}
    (ht : 0 < t) (hepsilon : 0 < epsilon) (htheta : 0 < theta)
    (hD : 0 < D) (hC0 : 0 < C0) (hdelta : 0 < delta)
    (hL : 0 < L) (hr : 0 < r)
    (hp : p = t ^ 2 * epsilon ^ 2 / (D * (delta ^ 2 * L)))
    (hC0rate : 32 * D * r ≤ C0) :
    t * p * (theta / 2) / (16 * r) ≥
      t ^ 3 * epsilon ^ 2 * theta / (C0 * delta ^ 2 * L) := by
  rw [hp]
  field_simp [hD.ne', hC0.ne', hdelta.ne', hL.ne', hr.ne']
  nlinarith [hC0rate]

private theorem exists_responseMoment_parameters {d : ℕ}
    {A C D C0 t theta epsilon delta : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hD : 0 < D) (_hC0 : 0 < C0)
    (ht : 0 < t) (ht1 : t ≤ 1) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hbudget : C0 * (delta ^ 2 * |Real.log delta|) ≤
      theta * t ^ 3 * epsilon ^ 2)
    (hC0D : 2 * D ≤ C0) (hC0dD : 2 * (d : ℝ) * D ≤ C0)
    (hDgeC : C ≤ D) (hDlog : 1 ≤ D * |Real.log delta|)
    (hDlarge : 32 * A * C ≤ D) :
    ∃ p : ℝ,
      p = t ^ 2 * epsilon ^ 2 /
        (D * (delta ^ 2 * |Real.log delta|)) ∧
      1 ≤ p ∧ 2 / theta ≤ p ∧
      2 * (d : ℝ) * t⁻¹ ≤ p ∧
      p ≤ C⁻¹ * (delta ^ 2)⁻¹ * |Real.log delta|⁻¹ ∧
      8 * A * C * p * Real.log (2 + p) * delta ^ 2 ≤
        t ^ 2 * epsilon ^ 2 := by
  let p : ℝ := t ^ 2 * epsilon ^ 2 /
    (D * (delta ^ 2 * |Real.log delta|))
  have hlogNeg : Real.log delta < 0 :=
    Real.log_neg hdelta (hdeltaHalf.trans_lt (by norm_num))
  have hL : 0 < |Real.log delta| := abs_pos.mpr hlogNeg.ne
  have hdeltaLog : 0 < delta ^ 2 * |Real.log delta| :=
    mul_pos (sq_pos_of_pos hdelta) hL
  have hp0 : 0 < p := by dsimp only [p]; positivity
  have hpTheta : 2 / theta ≤ p := by
    rw [div_le_iff₀ htheta]
    dsimp only [p]
    rw [show t ^ 2 * epsilon ^ 2 /
        (D * (delta ^ 2 * |Real.log delta|)) * theta =
      (t ^ 2 * epsilon ^ 2 * theta) /
        (D * (delta ^ 2 * |Real.log delta|)) by ring]
    rw [le_div_iff₀ (mul_pos hD hdeltaLog)]
    have hleft : 2 * D * (delta ^ 2 * |Real.log delta|) ≤
        C0 * (delta ^ 2 * |Real.log delta|) :=
      mul_le_mul_of_nonneg_right hC0D hdeltaLog.le
    have htCubeLeSq : t ^ 3 ≤ t ^ 2 := by nlinarith [sq_nonneg t]
    calc
      2 * (D * (delta ^ 2 * |Real.log delta|)) =
          2 * D * (delta ^ 2 * |Real.log delta|) := by ring
      _ ≤ C0 * (delta ^ 2 * |Real.log delta|) := hleft
      _ ≤ theta * t ^ 3 * epsilon ^ 2 := hbudget
      _ ≤ t ^ 2 * epsilon ^ 2 * theta := by
        nlinarith [mul_le_mul_of_nonneg_right htCubeLeSq
          (mul_nonneg htheta.le (sq_nonneg epsilon))]
  have hp : 1 ≤ p := by
    have : 1 ≤ 2 / theta := by
      rw [le_div_iff₀ htheta]
      linarith
    exact this.trans hpTheta
  have hdim : 2 * (d : ℝ) * t⁻¹ ≤ p := by
    rw [show 2 * (d : ℝ) * t⁻¹ = (2 * (d : ℝ)) / t by ring,
      div_le_iff₀ ht]
    dsimp only [p]
    rw [show t ^ 2 * epsilon ^ 2 /
        (D * (delta ^ 2 * |Real.log delta|)) * t =
      (t ^ 2 * epsilon ^ 2 * t) /
        (D * (delta ^ 2 * |Real.log delta|)) by ring]
    rw [le_div_iff₀ (mul_pos hD hdeltaLog)]
    have hleft : 2 * (d : ℝ) * D * (delta ^ 2 * |Real.log delta|) ≤
        C0 * (delta ^ 2 * |Real.log delta|) :=
      mul_le_mul_of_nonneg_right hC0dD hdeltaLog.le
    have hbudgetOne : C0 * (delta ^ 2 * |Real.log delta|) ≤
        t ^ 3 * epsilon ^ 2 := hbudget.trans (by
      have hm := mul_le_mul_of_nonneg_right htheta1
        (mul_nonneg (pow_nonneg ht.le 3) (sq_nonneg epsilon))
      nlinarith)
    calc
      2 * (d : ℝ) * (D * (delta ^ 2 * |Real.log delta|)) =
          2 * (d : ℝ) * D * (delta ^ 2 * |Real.log delta|) := by ring
      _ ≤ C0 * (delta ^ 2 * |Real.log delta|) := hleft
      _ ≤ t ^ 3 * epsilon ^ 2 := hbudgetOne
      _ = t ^ 2 * epsilon ^ 2 * t := by ring
  have hsmall : p ≤ C⁻¹ * (delta ^ 2)⁻¹ * |Real.log delta|⁻¹ :=
    responseMoment_le_headlineRange ht.le ht1 hepsilon.le hepsilon1
      hD hC hDgeC hdelta hL
  have hpDelta : p ≤ (delta ^ 2)⁻¹ :=
    responseMoment_le_deltaInv ht.le ht1 hepsilon.le hepsilon1
      hD hdelta hL hDlog
  have hlog := log_two_add_le_four_abs_log hdelta hdeltaHalf hp0.le hpDelta
  have hnumeric := responseMoment_numeric hA hC hD ht hepsilon hdelta hL
    (p := p) rfl hlog hDlarge
  exact ⟨p, rfl, hp, hpTheta, hdim, hsmall, hnumeric⟩

/-- Public numerical selector for response-density arguments sharing the
manuscript's scalar budget. -/
theorem exists_responseMoment_parameters_of_budget {d : ℕ}
    {A C D C0 t theta epsilon delta : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hD : 0 < D) (hC0 : 0 < C0)
    (ht : 0 < t) (ht1 : t ≤ 1) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hbudget : C0 * (delta ^ 2 * |Real.log delta|) ≤
      theta * t ^ 3 * epsilon ^ 2)
    (hC0D : 2 * D ≤ C0) (hC0dD : 2 * (d : ℝ) * D ≤ C0)
    (hDgeC : C ≤ D) (hDlog : 1 ≤ D * |Real.log delta|)
    (hDlarge : 32 * A * C ≤ D) :
    ∃ p : ℝ,
      p = t ^ 2 * epsilon ^ 2 /
        (D * (delta ^ 2 * |Real.log delta|)) ∧
      1 ≤ p ∧ 2 / theta ≤ p ∧
      2 * (d : ℝ) * t⁻¹ ≤ p ∧
      p ≤ C⁻¹ * (delta ^ 2)⁻¹ * |Real.log delta|⁻¹ ∧
      8 * A * C * p * Real.log (2 + p) * delta ^ 2 ≤
        t ^ 2 * epsilon ^ 2 := by
  exact exists_responseMoment_parameters hA hC hD hC0 ht ht1 htheta
    htheta1 hepsilon hepsilon1 hdelta hdeltaHalf hbudget hC0D hC0dD
    hDgeC hDlog hDlarge

/-- Source-form response density estimate (`l.discounted.J.local`).  The
constant absorbs the finite annular dependence range and all scalar choices
in the manuscript's moment `p`. -/
theorem exists_measure_goodResponse_badDensity_le (d : ℕ) [NeZero d] :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (t theta epsilon : ℝ),
        t ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 →
        epsilon ∈ Set.Ioc 0 1 →
        C0 * t ^ (-3 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
            |Real.log M.delta| ≤ theta →
        ∀ m0 window : ℕ,
          M.P.toMeasure {omega | theta ≤ intervalEventDensity
              (fun m => {omega : Sample d |
                GoodResponse M none m 0 epsilon (8 * t) omega}ᶜ)
              m0 window omega} ≤
            ENNReal.ofReal (Real.exp
              (-(t ^ 3 * epsilon ^ 2 * theta /
                (C0 * M.delta ^ 2 * |Real.log M.delta|)) *
                  ((window : ℝ) + 1))) := by
  obtain ⟨c, C, hc, hC, hheadline⟩ :=
    SubdiffusiveProcess.Frozen.Section4.coarse_grained_bound (d := d)
  let A : ℝ := expSequenceAmplitude
  let D : ℝ := 2 + C + 32 * A * C
  let Q : ℝ := 1 + 2 * D + 2 * (d : ℝ) * D
  let C0 : ℝ := 1 + Q + 32 * D * (responseScoreRange d : ℝ)
  have hA : 0 < A := zero_lt_one.trans expSequenceAmplitude_gt_one
  have hD : 0 < D := by dsimp only [D]; positivity
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hC0 : 0 < C0 := by dsimp only [C0]; positivity
  refine ⟨C0, hC0, ?_⟩
  intro M t theta epsilon ht htheta hepsilon hsource m0 window
  have ht0 := ht.1
  have ht1 := ht.2
  have htheta0 := htheta.1
  have htheta1 := htheta.2
  have hepsilon0 := hepsilon.1
  have hepsilon1 := hepsilon.2
  have hdelta := M.shellPrefix.delta_pos
  have hdeltaHalf := M.shellPrefix.delta_le_half
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg hdelta (hdeltaHalf.trans_lt (by norm_num))
  have hL : 0 < |Real.log M.delta| := abs_pos.mpr hlogNeg.ne
  have hdeltaLog : 0 < M.delta ^ 2 * |Real.log M.delta| :=
    mul_pos (sq_pos_of_pos hdelta) hL
  have hbudget : C0 * (M.delta ^ 2 * |Real.log M.delta|) ≤
      theta * t ^ 3 * epsilon ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hsource
      (mul_nonneg (pow_nonneg ht0.le 3) (sq_nonneg epsilon))
    calc
      C0 * (M.delta ^ 2 * |Real.log M.delta|) =
          (C0 * t ^ (-3 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
            |Real.log M.delta|) * (t ^ 3 * epsilon ^ 2) := by
        rw [zpow_neg]
        field_simp [ht0.ne', hepsilon0.ne']
      _ ≤ theta * (t ^ 3 * epsilon ^ 2) := hmul
      _ = theta * t ^ 3 * epsilon ^ 2 := by ring
  have hC0D : 2 * D ≤ C0 := by
    dsimp only [C0, Q]
    have hr : 0 ≤ (responseScoreRange d : ℝ) := by positivity
    nlinarith
  have hC0dD : 2 * (d : ℝ) * D ≤ C0 := by
    dsimp only [C0, Q]
    have hr : 0 ≤ (responseScoreRange d : ℝ) := by positivity
    nlinarith
  have hDgeC : C ≤ D := by
    change C ≤ 2 + C + 32 * A * C
    have hAC : 0 ≤ 32 * A * C := by positivity
    linarith
  have hlogHalf : (1 : ℝ) / 2 ≤ |Real.log M.delta| := by
    have hmono : Real.log M.delta ≤ Real.log (1 / 2 : ℝ) :=
      Real.log_le_log hdelta hdeltaHalf
    have heq : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
      simp
    rw [heq] at hmono
    rw [abs_of_neg hlogNeg]
    linarith [Real.log_two_gt_d9]
  have hDtwo : 2 ≤ D := by
    change 2 ≤ 2 + C + 32 * A * C
    have hAC : 0 ≤ 32 * A * C := by positivity
    linarith
  have hDlog : 1 ≤ D * |Real.log M.delta| := by
    calc
      1 = 2 * ((1 : ℝ) / 2) := by norm_num
      _ ≤ D * |Real.log M.delta| :=
        mul_le_mul hDtwo hlogHalf (by norm_num) (by positivity)
  have hDlarge : 32 * A * C ≤ D := by
    change 32 * A * C ≤ 2 + C + 32 * A * C
    linarith [hC]
  obtain ⟨p, hpDef, hp, hpTheta, hdim, hsmall, hnumeric⟩ :=
    exists_responseMoment_parameters (d := d) hA hC hD hC0 ht0 ht1
      htheta0 htheta1 hepsilon0 hepsilon1 hdelta hdeltaHalf hbudget
      hC0D hC0dD hDgeC hDlog hDlarge
  have hnorm : ∀ j : ℕ,
      paperENNRealLpNorm M.P.toMeasure p
        (localResponseScore M t epsilon A j) ≤ 1 := by
    intro j
    exact localResponseScore_norm_le_one_of_numeric M j ht0 ht1 hepsilon0
      hA hC hp hdim (hheadline M p hp hsmall j |>.1 |> fun hcenter =>
        localResponseScore_moment_le_of_center M t epsilon A j hp
          (ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2))
          (fun n => hheadline M p hp hsmall n |>.1)) hnumeric
  have hthresholdBase :
      6 * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
          (theta / 2) ^ (-1 / p) < A := by
    exact expSequence_threshold_lt_amplitude htheta0 htheta1 hpTheta
  have hthreshold :
      6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
          (theta / 2) ^ (-1 / p) < A * t⁻¹ := by
    exact response_threshold_scaled ht0 hthresholdBase
  have htp : 1 ≤ t * p := response_one_le_tp_of_dim ht0 hdim
  have hraw := measure_goodResponse_badDensity_le_of_parameters
    M ht0 ht1 hepsilon0 htheta0 htheta1 hA hp htp hthreshold hnorm m0 window
  refine hraw.trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have hC0rate : 32 * D * (responseScoreRange d : ℝ) ≤ C0 := by
    change 32 * D * (responseScoreRange d : ℝ) ≤
      1 + Q + 32 * D * (responseScoreRange d : ℝ)
    exact le_add_of_nonneg_left (by linarith only [hQ] : 0 ≤ 1 + Q)
  have hden0 : 0 < M.delta ^ 2 * |Real.log M.delta| := hdeltaLog
  have hrate : t * p * (theta / 2) /
        (16 * (responseScoreRange d : ℝ)) ≥
      t ^ 3 * epsilon ^ 2 * theta /
        (C0 * M.delta ^ 2 * |Real.log M.delta|) := by
    have hrpos : 0 < (responseScoreRange d : ℝ) := by exact_mod_cast responseScoreRange_pos d
    exact response_rate_compare ht0 hepsilon0 htheta0 hD hC0 hdelta hL hrpos
      hpDef hC0rate
  have hw : 0 ≤ (window : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hrate hw
  convert neg_le_neg hmul using 1 <;> ring



theorem exists_measure_goodResponse_badDensity_le_all (d : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (t theta epsilon : ℝ),
        t ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 →
        epsilon ∈ Set.Ioc 0 1 →
        C0 * t ^ (-3 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
            |Real.log M.delta| ≤ theta →
        ∀ m0 window : ℕ,
          M.P.toMeasure {omega | theta ≤ intervalEventDensity
              (fun m => {omega : Sample d |
                GoodResponse M none m 0 epsilon (8 * t) omega}ᶜ)
              m0 window omega} ≤
            ENNReal.ofReal (Real.exp
              (-(t ^ 3 * epsilon ^ 2 * theta /
                (C0 * M.delta ^ 2 * |Real.log M.delta|)) *
                  ((window : ℝ) + 1))) := by
  by_cases hd : d = 0
  · subst d
    refine ⟨1, by norm_num, ?_⟩
    intro M t theta epsilon _ht htheta _hepsilon _hsmall m0 window
    have hgood : ∀ (omega : Sample 0) (m : ℕ),
        GoodResponse M none m 0 epsilon (8 * t) omega := by
      intro omega m
      unfold GoodResponse
      intro j n hjm hnj z hzgrid hzann e he
      have he0 : e = 0 := Subsingleton.elim _ _
      subst e
      simp [Homogenization.vecNormSq, vecDot] at he
    have hevent : {omega | theta ≤ intervalEventDensity
          (fun m => {omega : Sample 0 |
            GoodResponse M none m 0 epsilon (8 * t) omega}ᶜ)
          m0 window omega} = ∅ := by
      ext omega
      constructor
      · intro homega
        simp only [Set.mem_setOf_eq] at homega
        unfold intervalEventDensity eventIndicator at homega
        simp only [hgood, Set.mem_compl_iff, Set.mem_setOf_eq,
          not_true_eq_false, if_false, Finset.sum_const_zero, zero_div] at homega
        linarith [htheta.1]
      · intro hempty
        exact (Set.notMem_empty omega hempty).elim
    rw [hevent, measure_empty]
    exact bot_le
  · letI : NeZero d := ⟨hd⟩
    exact exists_measure_goodResponse_badDensity_le d

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
