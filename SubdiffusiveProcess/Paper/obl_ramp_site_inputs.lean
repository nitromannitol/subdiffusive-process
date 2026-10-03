module

public import SubdiffusiveProcess.Paper.product_threshold_good_scale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.LongRatioEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.RatioCollapse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.SubunitTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.NormalizerSwap
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffEllipticityCaps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepWeightedEnergyComparison
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators

namespace Paper

private theorem aux_obl_ramp_site_inputs_zero_mem_cube (d m : ℕ) :
    (0 : Vec d) ∈ cube d (m : ℤ) := by
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hp : (0 : ℝ) < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
  constructor <;> simp only [Pi.zero_apply] <;> nlinarith

private theorem aux_obl_ramp_site_inputs_abs_bdd_cube
    {d : ℕ} (r : ℕ) {f : Vec d → ℝ} (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ cube d (r : ℤ), a = |f x|} := by
  let Q := originCube d (r : ℤ)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      ((continuous_abs.comp hf).continuousOn)
  refine ⟨max 0 C, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hC x hx'
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using
    h.trans (le_max_right _ _)

private theorem aux_obl_ramp_site_inputs_abs_bdd_translated
    {d : ℕ} (r : ℤ) (z : Vec d) {f : Vec d → ℝ} (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ translatedCube d r z, a = |f x|} := by
  let Q := originCube d r
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall z (cubeRadius Q)).exists_bound_of_continuousOn
      ((continuous_abs.comp hf).continuousOn)
  refine ⟨max 0 C, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  rcases hx with ⟨y, hy, rfl⟩
  have hyball : y ∈ Metric.ball (cubeCenter Q) (cubeRadius Q) := by
    rw [ball_cubeCenter_eq_openCubeSet]
    exact hy
  have hcenter : cubeCenter Q = (0 : Vec d) := by
    ext i
    simp [Q, cubeCenter, originCube]
  have hxball : z + y ∈ Metric.closedBall z (cubeRadius Q) := by
    apply Metric.ball_subset_closedBall
    rw [Metric.mem_ball, dist_eq_norm, hcenter] at hyball
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hyball
  have h := hC (z + y) hxball
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using
    h.trans (le_max_right _ _)

private theorem aux_obl_ramp_site_inputs_shell_finite_product
    {d : ℕ} {m n : ℕ} (hnm : n ≤ m)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    Real.exp |shellBlock m n omega x| ≤
      ∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)), Real.exp |omega i x| := by
  unfold shellBlock
  calc
    Real.exp |∑ i ∈ Finset.Icc (n + 1) m, omega i x| ≤
        Real.exp (∑ i ∈ Finset.Icc (n + 1) m, |omega i x|) :=
      Real.exp_le_exp.mpr (Finset.abs_sum_le_sum_abs _ _)
    _ = ∏ i ∈ Finset.Icc (n + 1) m, Real.exp |omega i x| := by
      rw [Real.exp_sum]
    _ ≤ ∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
        Real.exp |omega i x| := by
      let u := Finset.Icc (n + 1) m
      let v := Finset.Icc (m - (m - n)) (m + (m - n))
      have huv : u ⊆ v := by
        intro i hi
        simp only [u, v, Finset.mem_Icc] at hi ⊢
        omega
      have hleft : 0 ≤ ∏ i ∈ u, Real.exp |omega i x| := by positivity
      have hrest : 1 ≤ ∏ i ∈ v \ u, Real.exp |omega i x| := by
        induction v \ u using Finset.induction_on with
        | empty => simp
        | @insert a w haw ih =>
            rw [Finset.prod_insert haw]
            exact one_le_mul_of_one_le_of_one_le
              (Real.one_le_exp (abs_nonneg _)) ih
      change (∏ i ∈ u, Real.exp |omega i x|) ≤
        ∏ i ∈ v, Real.exp |omega i x|
      calc
        (∏ i ∈ u, Real.exp |omega i x|) =
            1 * ∏ i ∈ u, Real.exp |omega i x| := by rw [one_mul]
        _ ≤ (∏ i ∈ v \ u, Real.exp |omega i x|) *
            ∏ i ∈ u, Real.exp |omega i x| :=
          mul_le_mul_of_nonneg_right hrest hleft
        _ = ∏ i ∈ v, Real.exp |omega i x| := Finset.prod_sdiff huv

private theorem aux_obl_ramp_site_inputs_tail_one
    {d : ℕ} (m q : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x y : Vec d) :
    1 ≤ ∏' i : ℕ, if m + q ≤ i then
      Real.exp (4 * |omega i x - omega i y|) else 1 := by
  let f : ℕ → ℝ := fun i => if m + q ≤ i then
    Real.exp (4 * |omega i x - omega i y|) else 1
  have hf : ∀ i, 1 ≤ f i := by
    intro i
    dsimp [f]
    split
    · exact Real.one_le_exp (by positivity)
    · exact le_rfl
  by_cases hmult : Multipliable f
  · apply le_hasProd_of_le_prod hmult.hasProd
    intro u
    induction u using Finset.induction_on with
    | empty => simp
    | @insert a w haw ih =>
        rw [Finset.prod_insert haw]
        exact one_le_mul_of_one_le_of_one_le (hf a) ih
  · rw [tprod_eq_one_of_not_multipliable hmult]

private theorem aux_obl_ramp_site_inputs_translated_cube_subset
    {d : ℕ} {m n : ℕ} (hnm : n ≤ m) {z : Vec d} (hz : z ∈ cube d (m : ℤ)) :
    translatedCube d (n : ℤ) z ⊆ cube d ((m + 1 + (m - n) : ℕ) : ℤ) := by
  rintro x ⟨y, hy, rfl⟩
  rw [cube, mem_openCubeSet_originCube_iff] at hz hy ⊢
  intro i
  have hzi := hz i
  have hyi := hy i
  simp only [zpow_natCast] at hzi hyi
  change (-(1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1 + (m - n)) < z i + y i) ∧
    (z i + y i < (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1 + (m - n)))
  have hpow_nm : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ m :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hnm
  have hpow_large : (3 : ℝ) ^ (m + 1) ≤
      (3 : ℝ) ^ (m + 1 + (m - n)) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
  have hmpos : 0 < (3 : ℝ) ^ m := by positivity
  have htarget : (3 : ℝ) ^ m <
      (1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1 + (m - n)) := by
    have hsucc : (3 : ℝ) ^ (m + 1) = 3 * (3 : ℝ) ^ m := by
      rw [pow_succ]
      ring
    rw [hsucc] at hpow_large
    nlinarith
  constructor <;> nlinarith

private theorem aux_obl_ramp_site_inputs_shell_point
    {d : ℕ} {m n : ℕ} (hnm : n ≤ m) {s : ℝ}
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {z : Vec d}
    (hz : z ∈ cube d (m : ℤ))
    (hfield : ∀ j : ℕ,
      supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) 0) (fun x =>
        (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + j ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1) ≤
        12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8))
    (hBdd : BddAbove {a : ℝ | ∃ x ∈
      translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
            Real.exp |omega i x|) +
          ∏' i : ℕ, if m + (m - n) ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1|}) :
    ∀ x ∈ translatedCube d (n : ℤ) z,
      Real.exp |shellBlock m n omega x| ≤
        12 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8) := by
  intro x hx
  have hxlarge : x ∈ cube d ((m + 1 + (m - n) : ℕ) : ℤ) :=
    aux_obl_ramp_site_inputs_translated_cube_subset hnm hz hx
  have hxlarge' : x ∈
      translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0 :=
    ⟨x, hxlarge, by simp⟩
  let finitePart : ℝ :=
    ∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)), Real.exp |omega i x|
  let tailPart : ℝ :=
    ∏' i : ℕ, if m + (m - n) ≤ i then
      Real.exp (4 * |omega i x - omega i 0|) else 1
  have hfinitePos : 0 < finitePart := by
    dsimp [finitePart]
    positivity
  have htailOne : 1 ≤ tailPart := by
    exact aux_obl_ramp_site_inputs_tail_one m (m - n) omega x 0
  have hcontrolPos : 0 < finitePart + tailPart := by linarith
  have hpoint : finitePart + tailPart ≤
      supNormOn (translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0)
        (fun y =>
          (∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
              Real.exp |omega i y|) +
            ∏' i : ℕ, if m + (m - n) ≤ i then
              Real.exp (4 * |omega i y - omega i 0|) else 1) := by
    unfold supNormOn
    have hle := le_csSup hBdd
      (show |finitePart + tailPart| ∈ {a : ℝ | ∃ y ∈
          translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
            a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
                Real.exp |omega i y|) +
              ∏' i : ℕ, if m + (m - n) ≤ i then
                Real.exp (4 * |omega i y - omega i 0|) else 1|} by
        refine ⟨x, hxlarge', ?_⟩
        rfl)
    rwa [abs_of_pos hcontrolPos] at hle
  have hevent := hfield (m - n)
  have hfinite : Real.exp |shellBlock m n omega x| ≤ finitePart := by
    exact aux_obl_ramp_site_inputs_shell_finite_product hnm omega x
  exact hfinite.trans ((le_add_of_nonneg_right (zero_le_one.trans htailOne)).trans
    (hpoint.trans hevent))

private theorem aux_obl_ramp_site_inputs_shell_sup
    {d : ℕ} {m n : ℕ} (hnm : n ≤ m) {s : ℝ}
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {z : Vec d}
    (hz : z ∈ cube d (m : ℤ))
    (hfield : ∀ j : ℕ,
      supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) 0) (fun x =>
        (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + j ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1) ≤
        12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8))
    (hBdd : BddAbove {a : ℝ | ∃ x ∈
      translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
            Real.exp |omega i x|) +
          ∏' i : ℕ, if m + (m - n) ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1|}) :
    Real.exp (supNormOn (translatedCube d (n : ℤ) z)
      (shellBlock m n omega)) ≤
      12 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8) := by
  let B : ℝ := 12 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8)
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hpoint := aux_obl_ramp_site_inputs_shell_point hnm omega hz hfield hBdd
  have habs : ∀ x ∈ translatedCube d (n : ℤ) z,
      |shellBlock m n omega x| ≤ Real.log B := by
    intro x hx
    rw [← Real.log_exp |shellBlock m n omega x|]
    exact Real.log_le_log (Real.exp_pos _) (hpoint x hx)
  have hsup : supNormOn (translatedCube d (n : ℤ) z)
      (shellBlock m n omega) ≤ Real.log B := by
    unfold supNormOn
    apply csSup_le
    · exact ⟨|shellBlock m n omega z|, z,
        ⟨0, aux_obl_ramp_site_inputs_zero_mem_cube d n, by simp⟩, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact habs x hx
  calc
    Real.exp (supNormOn (translatedCube d (n : ℤ) z)
        (shellBlock m n omega)) ≤ Real.exp (Real.log B) :=
      Real.exp_le_exp.mpr hsup
    _ = B := Real.exp_log hBpos
    _ = 12 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8) := rfl

private theorem aux_obl_ramp_site_inputs_full_shell_point
    {d : ℕ} (m : ℕ) {s : ℝ}
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hfield : ∀ j : ℕ,
      supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) 0) (fun x =>
        (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + j ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1) ≤
        12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8))
    (hBdd : BddAbove {a : ℝ | ∃ x ∈
      translatedCube d ((m + 1 + m : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - m) (m + m),
            Real.exp |omega i x|) +
          ∏' i : ℕ, if m + m ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1|}) :
    ∀ x ∈ cube d (m : ℤ),
      Real.exp |fullShellBlock m omega x| ≤
        12 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) := by
  intro x hx
  have hxlarge : x ∈ cube d ((m + 1 + m : ℕ) : ℤ) := by
    refine openCubeSet_originCube_subset_of_scale_le ?_ hx
    exact_mod_cast (by omega : m ≤ m + 1 + m)
  have hxlarge' : x ∈
      translatedCube d ((m + 1 + m : ℕ) : ℤ) 0 :=
    ⟨x, hxlarge, by simp⟩
  let finitePart : ℝ :=
    ∏ i ∈ Finset.Icc (m - m) (m + m), Real.exp |omega i x|
  let tailPart : ℝ :=
    ∏' i : ℕ, if m + m ≤ i then
      Real.exp (4 * |omega i x - omega i 0|) else 1
  have hfinitePos : 0 < finitePart := by
    dsimp [finitePart]
    positivity
  have htailOne : 1 ≤ tailPart := by
    exact aux_obl_ramp_site_inputs_tail_one m m omega x 0
  have hcontrolPos : 0 < finitePart + tailPart := by linarith
  have hpoint : finitePart + tailPart ≤
      supNormOn (translatedCube d ((m + 1 + m : ℕ) : ℤ) 0)
        (fun y =>
          (∏ i ∈ Finset.Icc (m - m) (m + m), Real.exp |omega i y|) +
            ∏' i : ℕ, if m + m ≤ i then
              Real.exp (4 * |omega i y - omega i 0|) else 1) := by
    unfold supNormOn
    have hle := le_csSup hBdd
      (show |finitePart + tailPart| ∈ {a : ℝ | ∃ y ∈
          translatedCube d ((m + 1 + m : ℕ) : ℤ) 0,
            a = |(∏ i ∈ Finset.Icc (m - m) (m + m), Real.exp |omega i y|) +
              ∏' i : ℕ, if m + m ≤ i then
                Real.exp (4 * |omega i y - omega i 0|) else 1|} by
        refine ⟨x, hxlarge', ?_⟩
        rfl)
    rwa [abs_of_pos hcontrolPos] at hle
  have hevent := hfield m
  have hfinite : Real.exp |fullShellBlock m omega x| ≤ finitePart := by
    unfold fullShellBlock
    have hsum : |∑ i ∈ Finset.range (m + 1), omega i x| ≤
        ∑ i ∈ Finset.range (m + 1), |omega i x| :=
      Finset.abs_sum_le_sum_abs _ _
    have hsubset : Finset.range (m + 1) ⊆
        Finset.Icc (m - m) (m + m) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Finset.mem_Icc]
      omega
    have hsum2 : ∑ i ∈ Finset.range (m + 1), |omega i x| ≤
        ∑ i ∈ Finset.Icc (m - m) (m + m), |omega i x| :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun i _ _ => abs_nonneg _)
    have hfin : finitePart = Real.exp
        (∑ i ∈ Finset.Icc (m - m) (m + m), |omega i x|) := by
      dsimp [finitePart]
      rw [Real.exp_sum]
    rw [hfin]
    exact Real.exp_le_exp.mpr (hsum.trans hsum2)
  exact hfinite.trans ((le_add_of_nonneg_right (zero_le_one.trans htailOne)).trans
    (hpoint.trans hevent))

private theorem aux_obl_ramp_site_inputs_full_shell_sup
    {d : ℕ} (m : ℕ) {s : ℝ}
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hfield : ∀ j : ℕ,
      supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) 0) (fun x =>
        (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + j ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1) ≤
        12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8))
    (hBdd : BddAbove {a : ℝ | ∃ x ∈
      translatedCube d ((m + 1 + m : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - m) (m + m),
            Real.exp |omega i x|) +
          ∏' i : ℕ, if m + m ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1|}) :
    Real.exp (supNormOn (cube d (m : ℤ)) (fullShellBlock m omega)) ≤
      12 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) := by
  let B : ℝ := 12 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hpoint := aux_obl_ramp_site_inputs_full_shell_point m omega hfield hBdd
  have habs : ∀ x ∈ cube d (m : ℤ),
      |fullShellBlock m omega x| ≤ Real.log B := by
    intro x hx
    rw [← Real.log_exp |fullShellBlock m omega x|]
    exact Real.log_le_log (Real.exp_pos _) (hpoint x hx)
  have hsup : supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) ≤
      Real.log B := by
    unfold supNormOn
    apply csSup_le
    · exact ⟨|fullShellBlock m omega 0|, 0,
        aux_obl_ramp_site_inputs_zero_mem_cube d m, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact habs x hx
  calc
    Real.exp (supNormOn (cube d (m : ℤ)) (fullShellBlock m omega)) ≤
        Real.exp (Real.log B) := Real.exp_le_exp.mpr hsup
    _ = B := Real.exp_log hBpos
    _ = 12 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) := rfl

private theorem aux_obl_ramp_site_inputs_ratio_bdd
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L m n : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (z : Vec d) :
    BddAbove ((fun x : Vec d =>
      |combinedCoefficientRatio M L m n omega z x - 1|) '' cube d (n : ℤ)) ∧
    BddAbove ((fun x : Vec d =>
      |combinedCoefficientRatioInv M L m n omega z x - 1|) '' cube d (n : ℤ)) := by
  have hshell : Continuous (shellBlock m n (translatePotentialSample z omega)) := by
    unfold shellBlock
    fun_prop
  have hbase : Continuous (fun x : Vec d =>
      shellBlock m n (translatePotentialSample z omega) x +
        normalizerLogError M m n) :=
    hshell.add continuous_const
  have htail : Continuous
      (tailCoefficient M L m (translatePotentialSample z omega)) :=
    continuous_tailCoefficient M L m (translatePotentialSample z omega)
  have hforward : Continuous (fun x : Vec d =>
      combinedCoefficientRatio M L m n omega z x - 1) := by
    unfold combinedCoefficientRatio
    exact ((htail.div_const (tailCoefficientCubeAverage M L m omega)).mul
      (Real.continuous_exp.comp hbase)).sub continuous_const
  have hreverse : Continuous (fun x : Vec d =>
      combinedCoefficientRatioInv M L m n omega z x - 1) := by
    unfold combinedCoefficientRatioInv
    exact ((Real.continuous_exp.comp hbase.neg).mul
      (continuous_const.div htail (fun x =>
        (tailCoefficient_pos_of_ahom_pos M L m
          (translatePotentialSample z omega) (ahom_pos M (min m L)) x).ne'))).sub
      continuous_const
  constructor
  · obtain ⟨C, hC⟩ := aux_obl_ramp_site_inputs_abs_bdd_cube n hforward
    refine ⟨C, ?_⟩
    rintro a ⟨x, hx, rfl⟩
    exact hC ⟨x, hx, rfl⟩
  · obtain ⟨C, hC⟩ := aux_obl_ramp_site_inputs_abs_bdd_cube n hreverse
    refine ⟨C, ?_⟩
    rintro a ⟨x, hx, rfl⟩
    exact hC ⟨x, hx, rfl⟩

private theorem aux_obl_ramp_site_inputs_exp_tau_bound
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s q a : ℝ}
    (hq : 0 ≤ q)
    (hsmall : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ s * Real.log 3 / 16)
    (ha : |a| ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * q) :
    Real.exp |a| ≤ (3 : ℝ) ^ (s * q / 16) := by
  have hqmul := mul_le_mul_of_nonneg_right hsmall hq
  have hbudget : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * q ≤
      Real.log 3 * (s * q / 16) := by
    calc
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * q ≤
          (s * Real.log 3 / 16) * q := hqmul
      _ = Real.log 3 * (s * q / 16) := by ring
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  exact Real.exp_le_exp.mpr (ha.trans (hbudget.trans_eq (by ring)))

private theorem aux_obl_ramp_site_inputs_elementary_exp_bound (b : ℝ) :
    Real.exp b + Real.exp (-b) - 2 ≤ b ^ 2 * Real.exp |b| := by
  have h₁ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.abs_exp_sub_one_sub_id_le_half_sq_mul_exp_abs b
  have h₂ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.abs_exp_sub_one_sub_id_le_half_sq_mul_exp_abs (-b)
  have hp₁ : 0 ≤ Real.exp b - 1 - b := by
    linarith [Real.add_one_le_exp b]
  have hp₂ : 0 ≤ Real.exp (-b) - 1 + b := by
    linarith [Real.add_one_le_exp (-b)]
  rw [abs_of_nonneg hp₁] at h₁
  have hp₂' : 0 ≤ Real.exp (-b) - 1 - (-b) := by
    simpa only [sub_neg_eq_add] using hp₂
  rw [abs_of_nonneg hp₂'] at h₂
  simp only [sub_neg_eq_add, abs_neg, neg_sq] at h₂
  nlinarith

private theorem aux_obl_ramp_site_inputs_shell_translate_sup
    {d : ℕ} (m n : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    supNormOn (cube d (n : ℤ))
        (shellBlock m n (translatePotentialSample z omega)) =
      supNormOn (translatedCube d (n : ℤ) z) (shellBlock m n omega) := by
  rw [show cube d (n : ℤ) = translatedCube d (n : ℤ) 0 by
    unfold translatedCube
    simp]
  calc
    supNormOn (translatedCube d (n : ℤ) 0)
        (shellBlock m n (translatePotentialSample z omega)) =
        supNormOn (translatedCube d (n : ℤ) 0)
          (fun x => shellBlock m n omega (x + z)) := by
      congr 1
    _ = supNormOn (translatedCube d (n : ℤ) z)
        (shellBlock m n omega) := by
      simpa only [add_zero] using
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.supNormOn_translatedCube_comp_add
          z 0 (n : ℤ) (shellBlock m n omega))

private theorem aux_obl_ramp_site_inputs_combined_point
    {d : ℕ} (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hC0big : longRatioGoodEventConstant d ≤ C0)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {L m n : ℕ} (hnm : n ≤ m) (hmL : m ≤ L) {s : ℝ}
    (hsUpper : s ≤ 1 / 2)
    (hsmall : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ s * Real.log 3 / 16)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) {z x : Vec d}
    (hz : z ∈ cube d (m : ℤ)) (hx : x ∈ cube d (n : ℤ))
    (hy : x + z ∈ cube d (m : ℤ))
    (hgood : GoodFieldOne m 0 1 s omega)
    (hfield : ∀ j : ℕ,
      supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) 0) (fun x =>
        (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + j ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1) ≤
        12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8))
    (hBdd : BddAbove {a : ℝ | ∃ y ∈
      translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
            Real.exp |omega i y|) +
          ∏' i : ℕ, if m + (m - n) ≤ i then
            Real.exp (4 * |omega i y - omega i 0|) else 1|}) :
    |combinedCoefficientRatio M L m n omega z x - 1| +
        |combinedCoefficientRatioInv M L m n omega z x - 1| ≤
      24 * (C0 + 2) *
        (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
        min 1 (longRatioGradientTail m omega +
          |shellBlock m n (translatePotentialSample z omega) x| +
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ)) := by
  let S := longRatioGradientTail m omega
  let g := shellBlock m n (translatePotentialSample z omega) x
  let r := normalizerLogError M m n
  let T : ℝ := ((m - n : ℕ) : ℝ)
  let Eg := 12 * (3 : ℝ) ^ ((s * T) / 8)
  let Er := (3 : ℝ) ^ ((s * T) / 16)
  have htail :=
    tailCoefficient_average_ratio_bounds_le_constant_mul_min_of_goodFieldOne
      M hmL zero_le_one le_rfl hsUpper omega hgood hy
  have hforward :
      |tailCoefficient M L m (translatePotentialSample z omega) x /
          tailCoefficientCubeAverage M L m omega - 1| ≤ C0 * min 1 S := by
    rw [tailCoefficient_translatePotentialSample M L m omega z x]
    exact htail.1.trans (mul_le_mul_of_nonneg_right hC0big
      (le_min zero_le_one (longRatioGradientTail_nonneg m omega)))
  have hreverse :
      |tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m (translatePotentialSample z omega) x - 1| ≤
        C0 * min 1 S := by
    rw [tailCoefficient_translatePotentialSample M L m omega z x]
    exact htail.2.trans (mul_le_mul_of_nonneg_right hC0big
      (le_min zero_le_one (longRatioGradientTail_nonneg m omega)))
  have hxtranslated : x + z ∈ translatedCube d (n : ℤ) z := by
    refine ⟨x, hx, ?_⟩
    exact add_comm z x
  have hfieldRaw := aux_obl_ramp_site_inputs_shell_point hnm omega hz
    hfield hBdd (x + z) hxtranslated
  have hEg : Real.exp |g| ≤ Eg := by
    dsimp only [g, Eg, T]
    rw [shellBlock_translatePotentialSample m n omega z x]
    exact hfieldRaw
  have hEr : Real.exp |r| ≤ Er := by
    dsimp only [r, Er, T]
    exact aux_obl_ramp_site_inputs_exp_tau_bound M (by positivity) hsmall
      (abs_normalizerLogError_le_of_le M hnm)
  have hcollapse := combined_ratio_deviation_sum_le_weighted_min
    (A := tailCoefficient M L m (translatePotentialSample z omega) x /
      tailCoefficientCubeAverage M L m omega)
    (Ainv := tailCoefficientCubeAverage M L m omega /
      tailCoefficient M L m (translatePotentialSample z omega) x)
    (g := g) (r := r) (S := S) (G := |g|) (R := |r|)
    (C := C0) (Eg := Eg) (Er := Er)
    hC0 (longRatioGradientTail_nonneg m omega)
    (abs_nonneg g) (abs_nonneg r) hforward hreverse le_rfl le_rfl hEg hEr
  have hpower : Eg * Er =
      12 * (3 : ℝ) ^ ((3 * s * T) / 16) := by
    dsimp only [Eg, Er]
    rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 2
    ring
  have hrho : |r| ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * T := by
    dsimp only [r, T]
    exact abs_normalizerLogError_le_of_le M hnm
  have hmin : min 1 (S + |g| + |r|) ≤
      min 1 (S + |g| + SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * T) := by
    apply min_le_min le_rfl
    linarith only [hrho]
  have hfactor : 0 ≤ 2 * (C0 + 2) * (Eg * Er) := by positivity
  have henlarged := hcollapse.trans
    (mul_le_mul_of_nonneg_left hmin hfactor)
  dsimp only [combinedCoefficientRatio, combinedCoefficientRatioInv] at henlarged ⊢
  rw [hpower] at henlarged
  dsimp only [S, g, r, T] at henlarged ⊢
  convert henlarged using 1 <;> ring_nf

private theorem aux_obl_ramp_site_inputs_subunit_ratio
    {d : ℕ} (C0 : ℝ) (hC0pos : 0 < C0)
    (hC0big : longRatioGoodEventConstant d ≤ C0)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    {s : ℝ} (hsUpper : s ≤ 1 / 2)
    (hsmall : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ s * Real.log 3 / 16)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hgood : GoodFieldOne m 0 1 s eta)
    (hfull : Real.exp (supNormOn (cube d (m : ℤ))
      (fullShellBlock m eta)) ≤ 12 * (3 : ℝ) ^ (s * (m : ℝ) / 8))
    (hsublog : |subunitLogError M m| ≤
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1))
    {x : Vec d} (hx : x ∈ cube d (m : ℤ)) :
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L eta x /
        tailCoefficientCubeAverage M L m eta - 1) ^ 2 +
      (tailCoefficientCubeAverage M L m eta /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L eta x - 1) ^ 2 ≤
      (48 * (C0 + 2) *
        (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
          (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) *
        min 1 (longRatioGradientTail m eta +
          supNormOn (cube d (m : ℤ)) (fullShellBlock m eta) +
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1))) ^ 2 := by
  let A : ℝ := tailCoefficient M L m eta x /
    tailCoefficientCubeAverage M L m eta
  let Ainv : ℝ := tailCoefficientCubeAverage M L m eta /
    tailCoefficient M L m eta x
  let g : ℝ := fullShellBlock m eta x
  let r : ℝ := subunitLogError M m
  let S : ℝ := longRatioGradientTail m eta
  let G : ℝ := supNormOn (cube d (m : ℤ)) (fullShellBlock m eta)
  let R : ℝ := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1)
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact longRatioGradientTail_nonneg m eta
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact le_trans (abs_nonneg (fullShellBlock m eta x))
      (abs_apply_le_supNormOn_cube_of_continuous
        (by unfold fullShellBlock; fun_prop) hx)
  have hR0 : 0 ≤ R := by
    have htau := M.G4.tauSq_pos
    dsimp [R]
    positivity
  obtain ⟨hAbound, hAinvbound⟩ :=
    tailCoefficient_average_ratio_bounds_le_constant_mul_min_of_goodFieldOne
      M hmL zero_le_one le_rfl hsUpper eta hgood hx
  have hA : |A - 1| ≤ C0 * min 1 S := by
    dsimp [A, S]
    exact hAbound.trans (mul_le_mul_of_nonneg_right hC0big
      (le_min zero_le_one (longRatioGradientTail_nonneg m eta)))
  have hAinv : |Ainv - 1| ≤ C0 * min 1 S := by
    dsimp [Ainv, S]
    exact hAinvbound.trans (mul_le_mul_of_nonneg_right hC0big
      (le_min zero_le_one (longRatioGradientTail_nonneg m eta)))
  have hgbound : |g| ≤ G := by
    dsimp [g, G]
    exact abs_apply_le_supNormOn_cube_of_continuous
      (by unfold fullShellBlock; fun_prop) hx
  have hrbound : |r| ≤ R := by
    simpa only [r, R] using hsublog
  have hEg : Real.exp G ≤ 12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) := by
    exact hfull
  have hEr : Real.exp R ≤ (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16) := by
    have hEr' := aux_obl_ramp_site_inputs_exp_tau_bound M
      (q := (m : ℝ) + 1) (a := R)
      (by positivity) hsmall (by
        simpa only [R] using (abs_of_nonneg hR0).le)
    simpa only [abs_of_nonneg hR0] using hEr'
  have hcollapse := combined_ratio_deviation_sum_le_weighted_min
    (A := A) (Ainv := Ainv) (g := g) (r := r) (S := S) (G := G) (R := R)
    (C := C0)
    (Eg := 12 * (3 : ℝ) ^ (s * (m : ℝ) / 8))
    (Er := (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16))
    (hC0pos.le) hS0 hG0 hR0 hA hAinv hgbound hrbound hEg hEr
  have hforward :
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L eta x /
        tailCoefficientCubeAverage M L m eta = A * Real.exp (g + r) := by
    simpa only [A, g, r] using
      (aCutoff_div_tailAverage_eq_ratio_mul_exp M hmL eta x)
  have hreverse :
      tailCoefficientCubeAverage M L m eta /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L eta x =
          Real.exp (-(g + r)) * Ainv := by
    have hAinv_eq : Ainv = A⁻¹ := by
      dsimp [A, Ainv]
      exact (inv_div _ _).symm
    have h1 : tailCoefficientCubeAverage M L m eta /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L eta x =
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L eta x /
          tailCoefficientCubeAverage M L m eta)⁻¹ :=
      (inv_div _ _).symm
    rw [h1, hforward, hAinv_eq, Real.exp_neg, mul_inv]
    ring
  rw [hforward, hreverse]
  have hsum :
      |A * Real.exp (g + r) - 1| +
          |Real.exp (-(g + r)) * Ainv - 1| ≤
        48 * (C0 + 2) *
          (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
            (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) *
          min 1 (S + G + R) := by
    have hmin0 : 0 ≤ min 1 (S + G + R) := by
      exact le_min zero_le_one (by linarith)
    have hcoef :
        2 * (C0 + 2) *
            ((12 * (3 : ℝ) ^ (s * (m : ℝ) / 8)) *
              (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) ≤
          48 * (C0 + 2) *
            (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
              (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) := by
      have hnonneg : 0 ≤ (C0 + 2) *
          ((12 * (3 : ℝ) ^ (s * (m : ℝ) / 8)) *
            (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) := by positivity
      nlinarith
    have h := hcollapse.trans (mul_le_mul_of_nonneg_right hcoef hmin0)
    simpa only [S, G, R] using h
  have hsq :
      (A * Real.exp (g + r) - 1) ^ 2 +
          (Real.exp (-(g + r)) * Ainv - 1) ^ 2 ≤
        (|A * Real.exp (g + r) - 1| +
          |Real.exp (-(g + r)) * Ainv - 1|) ^ 2 := by
    have hsq' :
        |A * Real.exp (g + r) - 1| ^ 2 +
            |Real.exp (-(g + r)) * Ainv - 1| ^ 2 ≤
          (|A * Real.exp (g + r) - 1| +
            |Real.exp (-(g + r)) * Ainv - 1|) ^ 2 := by
      have hu := abs_nonneg (A * Real.exp (g + r) - 1)
      have hv := abs_nonneg (Real.exp (-(g + r)) * Ainv - 1)
      nlinarith [sq_nonneg
        (|A * Real.exp (g + r) - 1| -
          |Real.exp (-(g + r)) * Ainv - 1|),
        mul_nonneg hu hv]
    simpa only [sq_abs] using hsq'
  have hsum0 : 0 ≤
      |A * Real.exp (g + r) - 1| +
        |Real.exp (-(g + r)) * Ainv - 1| := by positivity
  have hbound0 : 0 ≤ 48 * (C0 + 2) *
      (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
        (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) *
      min 1 (S + G + R) := by positivity
  calc
    (A * Real.exp (g + r) - 1) ^ 2 +
        (Real.exp (-(g + r)) * Ainv - 1) ^ 2 ≤
      (|A * Real.exp (g + r) - 1| +
        |Real.exp (-(g + r)) * Ainv - 1|) ^ 2 := hsq
    _ ≤ (48 * (C0 + 2) *
        (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
          (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) *
        min 1 (S + G + R)) ^ 2 :=
      (sq_le_sq₀ hsum0 hbound0).2 hsum
    _ = (48 * (C0 + 2) *
        (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
          (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) *
        min 1 (longRatioGradientTail m eta +
          supNormOn (cube d (m : ℤ)) (fullShellBlock m eta) +
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1))) ^ 2 := by
      rfl
  


theorem obl_ramp_site_inputs
    (d : ℕ) [NeZero d] :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ s * Real.log 3 / 16 →
      ∀ L m : ℕ, m ≤ L →
      ∀ w : Vec d, ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        omega ∈ Paper.product_threshold_good_scale d M 12 (some L) m w 1 s →
        let eta := translatePotentialSample w omega
        longRatioDeviation M L m eta ≤ CB * min 1 (longRatioGradientTail m eta) ∧
        (∀ n : ℕ, n ≤ m → ∀ z : Vec d,
          translatedCube d n z ⊆ cube d m →
          BddAbove ((fun x : Vec d =>
            |combinedCoefficientRatio M L m n eta z x - 1|) '' cube d n) ∧
          BddAbove ((fun x : Vec d =>
            |combinedCoefficientRatioInv M L m n eta z x - 1|) '' cube d n) ∧
          Real.exp (supNormOn (cube d n)
              (shellBlock m n (translatePotentialSample z eta))) ≤
            12 * (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ)) / 8) ∧
          |normalizerLogError M m n| ≤
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)) ∧
          Real.exp |normalizerLogError M m n| ≤
            (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ)) / 16) ∧
          supNormOn (cube d n)
              (fun x => combinedCoefficientRatio M L m n eta z x - 1) +
            supNormOn (cube d n)
              (fun x => combinedCoefficientRatioInv M L m n eta z x - 1) ≤
            CB * (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
              min 1 (longRatioGradientTail m eta +
                supNormOn (cube d n)
                  (shellBlock m n (translatePotentialSample z eta)) +
                SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)))) ∧
        Real.exp (supNormOn (cube d m) (fullShellBlock m eta)) ≤
          12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) ∧
        |subunitLogError M m| ≤
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1) ∧
        (∀ x ∈ cube d m,
          let b := fullShellBlock m eta x + subunitLogError M m
          Real.exp b + Real.exp (-b) - 2 ≤ b ^ 2 * Real.exp |b| ∧
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L eta x /
              tailCoefficientCubeAverage M L m eta - 1) ^ 2 +
              (tailCoefficientCubeAverage M L m eta /
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L eta x - 1) ^ 2 ≤
      (CB * (12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) *
              (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) *
              min 1 (longRatioGradientTail m eta +
                supNormOn (cube d m) (fullShellBlock m eta) +
                SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1))) ^ 2) := by
  let C0 : ℝ := longRatioGoodEventConstant d
  let CB : ℝ := 48 * (C0 + 2)
  have hC0pos : 0 < C0 := by
    dsimp [C0]
    exact longRatioGoodEventConstant_pos d
  have hCBpos : 0 < CB := by
    dsimp [CB]
    nlinarith
  refine ⟨CB, hCBpos, ?_⟩
  intro M s hs hsmall L m hmL w omega homega
  let eta := translatePotentialSample w omega
  have hmem : 0 < (12 : ℝ) ∧ 0 < s ∧ s ≤ 1 ∧ 0 < (1 : ℝ) ∧
      (1 : ℝ) ≤ 1 ∧ GoodFieldOne m w 1 s omega ∧
      (∀ j : ℕ,
        (∀ x ∈ translatedCube d (m + 1 + j) w,
          Multipliable (fun i : ℕ =>
            if m + j ≤ i then Real.exp (4 * |omega i x - omega i w|) else 1)) ∧
        BddAbove ((fun x : Vec d =>
          |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
            ∏' i : ℕ, if m + j ≤ i then
              Real.exp (4 * |omega i x - omega i w|) else 1|) ''
          translatedCube d (m + 1 + j) w) ∧
        supNormOn (translatedCube d (m + 1 + j) w) (fun x =>
          (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
            ∏' i : ℕ, if m + j ≤ i then
              Real.exp (4 * |omega i x - omega i w|) else 1) ≤
          12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8)) ∧
      GoodResponse M (some L) m w 1 s omega := by
    simpa only [product_threshold_good_scale, Set.mem_setOf_eq] using homega
  rcases hmem with ⟨_, _, hs1, _, _, hgood0, hprod0, _⟩
  have hgood : GoodFieldOne m 0 1 s eta := by
    apply (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.goodFieldOne_translatePotentialSample
      m 0 1 s w omega).mpr
    simpa only [add_zero] using hgood0
  have hprod : ∀ j : ℕ,
      supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) 0) (fun x =>
        (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |eta i x|) +
          ∏' i : ℕ, if m + j ≤ i then
            Real.exp (4 * |eta i x - eta i 0|) else 1) ≤
        12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8) := by
    intro j
    have hraw := (hprod0 j).2.2
    calc
      supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) 0) (fun x =>
          (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |eta i x|) +
            ∏' i : ℕ, if m + j ≤ i then
              Real.exp (4 * |eta i x - eta i 0|) else 1) =
          supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) 0) (fun x =>
            (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i (x + w)|) +
              ∏' i : ℕ, if m + j ≤ i then
                Real.exp (4 * |omega i (x + w) - omega i w|) else 1) := by
            congr 1
            funext x
            simp only [eta, translatePotentialSample,
              SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply]
            ring_nf
      _ = supNormOn (translatedCube d ((m + 1 + j : ℕ) : ℤ) w) (fun x =>
            (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
              ∏' i : ℕ, if m + j ≤ i then
                Real.exp (4 * |omega i x - omega i w|) else 1) := by
            simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_zero] using
              (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.supNormOn_translatedCube_comp_add
                w 0 ((m + 1 + j : ℕ) : ℤ) (fun x =>
                  (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
                    ∏' i : ℕ, if m + j ≤ i then
                      Real.exp (4 * |omega i x - omega i w|) else 1))
      _ ≤ 12 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8) := hraw
  have hlong : longRatioDeviation M L m eta ≤ CB *
      min 1 (longRatioGradientTail m eta) := by
    have h := longRatioDeviation_le_constant_mul_min_of_goodFieldOne
      M hmL zero_le_one le_rfl hs.2 eta hgood
    have hmin0 : 0 ≤ min 1 (longRatioGradientTail m eta) :=
      le_min zero_le_one (longRatioGradientTail_nonneg m eta)
    exact h.trans (mul_le_mul_of_nonneg_right (by
      dsimp [CB, C0]
      nlinarith [hC0pos]) hmin0)
  have hfull : Real.exp (supNormOn (cube d (m : ℤ))
      (fullShellBlock m eta)) ≤ 12 * (3 : ℝ) ^ (s * (m : ℝ) / 8) := by
    have hbdd := bddAbove_goodFieldTwo_values_of_goodFieldOne m m
      zero_le_one hs.2 eta hgood
    exact aux_obl_ramp_site_inputs_full_shell_sup m eta hprod hbdd
  have hsublog : |subunitLogError M m| ≤
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1) :=
    abs_subunitLogError_le M m
  refine ⟨hlong, ?_⟩
  refine ⟨?_, hfull, hsublog, ?_⟩
  · intro n hnm z hsubset
    have hz : z ∈ cube d (m : ℤ) := by
      exact hsubset ⟨0, aux_obl_ramp_site_inputs_zero_mem_cube d n, by simp⟩
    have hbdd := bddAbove_goodFieldTwo_values_of_goodFieldOne m (m - n)
      zero_le_one hs.2 eta hgood
    have hratioBdd := aux_obl_ramp_site_inputs_ratio_bdd M L m n eta z
    have hshell : Real.exp (supNormOn (cube d (n : ℤ))
        (shellBlock m n (translatePotentialSample z eta))) ≤
        12 * (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ)) / 8) := by
      rw [aux_obl_ramp_site_inputs_shell_translate_sup]
      have hraw := aux_obl_ramp_site_inputs_shell_sup hnm eta hz hprod hbdd
      simpa only [Nat.cast_sub hnm] using hraw
    have hnormal : |normalizerLogError M m n| ≤
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)) := by
      have h := abs_normalizerLogError_le_of_le M hnm
      simpa only [Nat.cast_sub hnm] using h
    have hexpnormal : Real.exp |normalizerLogError M m n| ≤
        (3 : ℝ) ^ (s * ((m : ℝ) - (n : ℝ)) / 16) := by
      have h := aux_obl_ramp_site_inputs_exp_tau_bound M
        (s := s) (q := ((m - n : ℕ) : ℝ))
        (a := normalizerLogError M m n) (by positivity) hsmall
        (abs_normalizerLogError_le_of_le M hnm)
      simpa only [Nat.cast_sub hnm] using h
    have hpoint : ∀ x ∈ cube d (n : ℤ),
        |combinedCoefficientRatio M L m n eta z x - 1| +
            |combinedCoefficientRatioInv M L m n eta z x - 1| ≤
          24 * (C0 + 2) *
            (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
            min 1 (longRatioGradientTail m eta +
              supNormOn (cube d (n : ℤ))
                (shellBlock m n (translatePotentialSample z eta)) +
              SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ))) := by
      intro x hx
      have hxy : x + z ∈ cube d (m : ℤ) := by
        exact hsubset (⟨x, hx, by rw [add_comm]⟩)
      have hraw := aux_obl_ramp_site_inputs_combined_point C0 hC0pos.le
        (by rfl) M hnm hmL hs.2 hsmall eta hz hx hxy hgood hprod hbdd
      have hshellx : |shellBlock m n (translatePotentialSample z eta) x| ≤
          supNormOn (cube d (n : ℤ))
            (shellBlock m n (translatePotentialSample z eta)) :=
        abs_apply_le_supNormOn_cube_of_continuous (by
          unfold shellBlock
          fun_prop) hx
      have hsum : longRatioGradientTail m eta +
          |shellBlock m n (translatePotentialSample z eta) x| +
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)) ≤
          longRatioGradientTail m eta +
          supNormOn (cube d (n : ℤ))
            (shellBlock m n (translatePotentialSample z eta)) +
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)) := by
        calc
          longRatioGradientTail m eta +
              |shellBlock m n (translatePotentialSample z eta) x| +
              SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)) =
              (longRatioGradientTail m eta +
                |shellBlock m n (translatePotentialSample z eta) x|) +
                SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)) := by ring
          _ ≤ (longRatioGradientTail m eta +
                supNormOn (cube d (n : ℤ))
                  (shellBlock m n (translatePotentialSample z eta))) +
                SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)) :=
            by linarith [hshellx]
          _ = longRatioGradientTail m eta +
              supNormOn (cube d (n : ℤ))
                (shellBlock m n (translatePotentialSample z eta)) +
              SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)) := by ring
      have hmin : min 1
          (longRatioGradientTail m eta +
            |shellBlock m n (translatePotentialSample z eta) x| +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ))) ≤
          min 1
            (longRatioGradientTail m eta +
              supNormOn (cube d (n : ℤ))
                (shellBlock m n (translatePotentialSample z eta)) +
              SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ))) := by
        exact min_le_min_left 1 hsum
      have hraw' :
          |combinedCoefficientRatio M L m n eta z x - 1| +
              |combinedCoefficientRatioInv M L m n eta z x - 1| ≤
            24 * (C0 + 2) *
              (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
              min 1 (longRatioGradientTail m eta +
                |shellBlock m n (translatePotentialSample z eta) x| +
                SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ))) := by
        simpa only [Nat.cast_sub hnm] using hraw
      exact hraw'.trans (mul_le_mul_of_nonneg_left hmin (by positivity))
    have hforward : supNormOn (cube d (n : ℤ)) (fun x =>
        |combinedCoefficientRatio M L m n eta z x - 1|) ≤
        24 * (C0 + 2) *
          (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
          min 1 (longRatioGradientTail m eta +
            supNormOn (cube d (n : ℤ))
              (shellBlock m n (translatePotentialSample z eta)) +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ))) := by
      unfold supNormOn
      apply csSup_le
      · exact ⟨|combinedCoefficientRatio M L m n eta z 0 - 1|, 0,
          aux_obl_ramp_site_inputs_zero_mem_cube d n, by simp⟩
      · rintro _ ⟨x, hx, rfl⟩
        simpa only [abs_abs] using!
          (le_add_of_nonneg_right (abs_nonneg _)).trans (hpoint x hx)
    have hreverse : supNormOn (cube d (n : ℤ)) (fun x =>
        |combinedCoefficientRatioInv M L m n eta z x - 1|) ≤
        24 * (C0 + 2) *
          (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
          min 1 (longRatioGradientTail m eta +
            supNormOn (cube d (n : ℤ))
              (shellBlock m n (translatePotentialSample z eta)) +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ))) := by
      unfold supNormOn
      apply csSup_le
      · exact ⟨|combinedCoefficientRatioInv M L m n eta z 0 - 1|, 0,
          aux_obl_ramp_site_inputs_zero_mem_cube d n, by simp⟩
      · rintro _ ⟨x, hx, rfl⟩
        simpa only [abs_abs] using!
          (le_add_of_nonneg_left (abs_nonneg _)).trans (hpoint x hx)
    have hforward' : supNormOn (cube d (n : ℤ)) (fun x =>
        combinedCoefficientRatio M L m n eta z x - 1) ≤
        24 * (C0 + 2) *
          (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
          min 1 (longRatioGradientTail m eta +
            supNormOn (cube d (n : ℤ))
              (shellBlock m n (translatePotentialSample z eta)) +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ))) := by
      simpa only [supNormOn, abs_abs] using hforward
    have hreverse' : supNormOn (cube d (n : ℤ)) (fun x =>
        combinedCoefficientRatioInv M L m n eta z x - 1) ≤
        24 * (C0 + 2) *
          (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
          min 1 (longRatioGradientTail m eta +
            supNormOn (cube d (n : ℤ))
              (shellBlock m n (translatePotentialSample z eta)) +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ))) := by
      simpa only [supNormOn, abs_abs] using hreverse
    refine ⟨hratioBdd.1, hratioBdd.2, hshell, hnormal, hexpnormal, ?_⟩
    change supNormOn (cube d (n : ℤ)) (fun x =>
        combinedCoefficientRatio M L m n eta z x - 1) +
        supNormOn (cube d (n : ℤ)) (fun x =>
          combinedCoefficientRatioInv M L m n eta z x - 1) ≤
      CB * (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
        min 1 (longRatioGradientTail m eta +
          supNormOn (cube d (n : ℤ))
            (shellBlock m n (translatePotentialSample z eta)) +
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)))
    calc
      supNormOn (cube d (n : ℤ)) (fun x =>
          combinedCoefficientRatio M L m n eta z x - 1) +
          supNormOn (cube d (n : ℤ)) (fun x =>
            combinedCoefficientRatioInv M L m n eta z x - 1) ≤
        (24 * (C0 + 2) *
          (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
          min 1 (longRatioGradientTail m eta +
            supNormOn (cube d (n : ℤ))
              (shellBlock m n (translatePotentialSample z eta)) +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)))) +
        (24 * (C0 + 2) *
          (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
          min 1 (longRatioGradientTail m eta +
            supNormOn (cube d (n : ℤ))
              (shellBlock m n (translatePotentialSample z eta)) +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)))) :=
        add_le_add hforward' hreverse'
      _ = 2 * (24 * (C0 + 2) *
          (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
          min 1 (longRatioGradientTail m eta +
            supNormOn (cube d (n : ℤ))
              (shellBlock m n (translatePotentialSample z eta)) +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ)))) := by ring
      _ = CB * (3 : ℝ) ^ (3 * s * ((m : ℝ) - (n : ℝ)) / 16) *
          min 1 (longRatioGradientTail m eta +
            supNormOn (cube d (n : ℤ))
              (shellBlock m n (translatePotentialSample z eta)) +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) - (n : ℝ))) := by
        dsimp [CB]
        ring
  · intro x hx
    let b := fullShellBlock m eta x + subunitLogError M m
    have helem := aux_obl_ramp_site_inputs_elementary_exp_bound b
    have hratio := aux_obl_ramp_site_inputs_subunit_ratio C0 hC0pos
      (by rfl) M hmL hs.2 hsmall eta hgood hfull hsublog hx
    refine ⟨?_, ?_⟩
    · simpa only [b] using helem
    · simpa only [CB] using hratio

end Paper

