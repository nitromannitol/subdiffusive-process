import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.AnnularRecombination
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.SubunitTail

/-!
# Annular localization above a finite cutoff

This module supplies the raw localization input for the `m > L` branch of
the cutoff good-scale argument.  The nonnegative annular scales split at
`L`: above `L` the two coefficients agree literally, while below `L` the
coefficient change is the centered finite shell ending at `L`.  The subunit
branch uses the same endpoint.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open Homogenization Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

/-! ## Exact finite-shell identities -/

/-- A shell block ending at `L` is the difference of the two shell blocks
ending at the parent scale `m`.  This is the algebraic reason that no new
field slot is needed in the cutoff display. -/
theorem shellBlock_cutoff_eq_parent_sub_parent
    {n L m : ℕ} (hnL : n ≤ L) (hLm : L ≤ m)
    (omega : Sample d) (x : Vec d) :
    shellBlock L n omega x = shellBlock m n omega x - shellBlock m L omega x := by
  unfold shellBlock
  rw [show Finset.Icc (n + 1) L = Finset.Ico (n + 1) (L + 1) by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega,
    show Finset.Icc (n + 1) m = Finset.Ico (n + 1) (m + 1) by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega,
    show Finset.Icc (L + 1) m = Finset.Ico (L + 1) (m + 1) by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega]
  have hsum := Finset.sum_Ico_consecutive (fun i ↦ omega i x)
    (by omega : n + 1 ≤ L + 1) (by omega : L + 1 ≤ m + 1)
  rw [← hsum]
  ring

/-- Once the parent scale has crossed `L`, its normalization is exactly
`ahom L`; hence a local annular probe is literally the cutoff-`L` response. -/
theorem section6LocalProbeMax_eq_cutoffResponseSup_of_cutoff_le_scale
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (omega : Sample d) (R : TriadicCube d) (hR0 : 0 ≤ R.scale) :
    section6LocalProbeMax M L omega 0
        (tailCoefficientCubeAverage M L m omega) R =
      ⨆ e : {e : Vec d // vecNormSq e = 1},
        ENNReal.ofReal
          (section6Response M R.scale.toNat L omega (triadicCubeShift R) e) := by
  rw [tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm]
  unfold section6LocalProbeMax section6Response
  rw [Section6Covariance.translatePotentialSample_zero]
  rw [Int.toNat_of_nonneg hR0]

/-- At a nonnegative annular scale above `L`, the local probe is bounded by
the literal unit-sphere response supremum occurring in the cutoff event. -/
theorem section6LocalProbeMax_le_cutoffResponseSup_of_cutoff_le_localScale
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m n : ℕ}
    (hLm : L ≤ m) (hLn : L ≤ n)
    (omega : Sample d) {R : TriadicCube d} (hRscale : R.scale = (n : ℤ)) :
    section6LocalProbeMax M L omega 0
        (tailCoefficientCubeAverage M L m omega) R ≤
      ENNReal.ofReal (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        q = section6Response M n (min n L) omega (triadicCubeShift R) e}) := by
  rw [section6LocalProbeMax_eq_cutoffResponseSup_of_cutoff_le_scale M hLm omega R
    (by rw [hRscale]; omega)]
  refine iSup_le fun e ↦ ENNReal.ofReal_le_ofReal ?_
  have hmin : min n L = L := min_eq_right hLn
  rw [hmin]
  apply le_csSup (bddAbove_section6Response_unitSphere M n L omega
    (triadicCubeShift R))
  refine ⟨e, e.2, ?_⟩
  simp only [hRscale, Int.toNat_natCast]

/-! ## The finite-cutoff coefficient ratio below `L` -/

/-- Exact forward centered ratio between the normalized cutoff coefficients
at `n` and `L`. -/
theorem cutoff_forward_ratio_eq_exp_shellBlock_add_normalizer
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {n L : ℕ} (hnL : n ≤ L)
    (omega : Sample d) (x : Vec d) :
    ((ahom M n / ahom M L) * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x =
      Real.exp (shellBlock L n omega x + normalizerLogError M L n) := by
  have hcut := aCutoff_div_eq_exp_shellBlock M hnL omega x
  have hhom := ahom_ratio_eq_exp_normalizerLogError M L n
  have hn := SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n omega x
  have hL := SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x
  have han := ahom_pos M n
  have haL := ahom_pos M L
  calc
    ((ahom M n / ahom M L) * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) /
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x =
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x /
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x) *
          (ahom M n / ahom M L) := by field_simp
    _ = Real.exp (shellBlock L n omega x -
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L - n : ℕ) : ℝ)) *
        Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L - n : ℕ) : ℝ) +
          normalizerLogError M L n) := by rw [hcut, hhom]
    _ = Real.exp (shellBlock L n omega x + normalizerLogError M L n) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Reciprocal form of the centered finite-cutoff ratio. -/
theorem cutoff_reverse_ratio_eq_exp_neg_shellBlock_add_normalizer
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {n L : ℕ} (hnL : n ≤ L)
    (omega : Sample d) (x : Vec d) :
    ((ahom M L / ahom M n) * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x) /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x =
      Real.exp (-(shellBlock L n omega x + normalizerLogError M L n)) := by
  have hforward := cutoff_forward_ratio_eq_exp_shellBlock_add_normalizer
    M hnL omega x
  have hn := SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n omega x
  have hL := SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x
  have han := ahom_pos M n
  have haL := ahom_pos M L
  calc
    ((ahom M L / ahom M n) * SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x) /
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x =
        (((ahom M n / ahom M L) *
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) /
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x)⁻¹ := by field_simp
    _ = (Real.exp (shellBlock L n omega x + normalizerLogError M L n))⁻¹ := by
      rw [hforward]
    _ = Real.exp (-(shellBlock L n omega x + normalizerLogError M L n)) := by
      rw [← Real.exp_neg]

/-! ## Reading the finite shell from the parent good event -/

private theorem shellBlock_continuous (m n : ℕ) (omega : Sample d) :
    Continuous (shellBlock m n omega) := by
  unfold shellBlock
  fun_prop

private theorem supNormOn_cube_nonneg (m : ℕ) {f : Vec d → ℝ}
    (hf : Continuous f) : 0 ≤ supNormOn (cube d m) f := by
  have hzero : (0 : Vec d) ∈ cube d m := by
    rw [cube, mem_openCubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
    constructor <;> simp only [Pi.zero_apply] <;> nlinarith
  exact (abs_nonneg (f 0)).trans
    (abs_apply_le_supNormOn_cube_of_continuous hf hzero)

private theorem supNormOn_translatedCube_shellBlock_eq_origin_translate
    (m k : ℕ) (z : Vec d) (omega : Sample d) :
    supNormOn (translatedCube d (k : ℤ) z) (shellBlock m k omega) =
      supNormOn (cube d (k : ℤ))
        (shellBlock m k (translatePotentialSample z omega)) := by
  rw [show cube d (k : ℤ) = translatedCube d (k : ℤ) 0 by
    unfold translatedCube
    simp]
  calc
    supNormOn (translatedCube d (k : ℤ) z) (shellBlock m k omega) =
        supNormOn (translatedCube d (k : ℤ) 0)
          (fun x ↦ shellBlock m k omega (x + z)) := by
      simpa only [add_zero] using
        (Section6Covariance.supNormOn_translatedCube_comp_add z 0
          (k : ℤ) (shellBlock m k omega)).symm
    _ = supNormOn (translatedCube d (k : ℤ) 0)
        (shellBlock m k (translatePotentialSample z omega)) := by
      congr 2

/-- The existing parent event bounds any shell block ending at an intermediate
scale `k ≤ m`; the read region remains the scale-`k` translated cube. -/
theorem exp_supNormOn_intermediateShellBlock_le_of_parent_goodEvent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (K : ℕ)
    {m k : ℕ} (hkm : k ≤ m) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hsUpper : s ≤ 1 / 2) (omega : Sample d) {z : Vec d}
    (hz : z ∈ cube d m)
    (hgood : omega ∈ goodEvent M (some K) m 0 epsilon s) :
    Real.exp (supNormOn (cube d k)
        (shellBlock m k (translatePotentialSample z omega))) ≤
      6 * (3 : ℝ) ^ ((s * ((m - k : ℕ) : ℝ)) / 8) := by
  have hBdd := bddAbove_goodFieldTwo_values_of_goodFieldOne
    m (m - k) hepsilon hsUpper omega hgood.1
  have hraw := exp_supNormOn_shellBlock_le_of_goodFieldTwo
    hkm omega hz hgood.2.1 hBdd
  rw [supNormOn_translatedCube_shellBlock_eq_origin_translate] at hraw
  exact hraw

/-- The cutoff shell is pointwise controlled by the two parent shell blocks
ending at `n` and at `L`. -/
theorem abs_cutoffShellBlock_le_parentShellSup_add
    {n L m : ℕ} (hnL : n ≤ L) (hLm : L ≤ m)
    (omega : Sample d) (z : Vec d) {x : Vec d} (hx : x ∈ cube d n) :
    |shellBlock L n (translatePotentialSample z omega) x| ≤
      supNormOn (cube d n)
          (shellBlock m n (translatePotentialSample z omega)) +
        supNormOn (cube d n)
          (shellBlock m L (translatePotentialSample z omega)) := by
  rw [shellBlock_cutoff_eq_parent_sub_parent hnL hLm]
  refine (abs_sub _ _).trans (add_le_add
    (abs_apply_le_supNormOn_cube_of_continuous
      (shellBlock_continuous m n _) hx) ?_)
  exact abs_apply_le_supNormOn_cube_of_continuous
    (shellBlock_continuous m L _) hx

private theorem supNormOn_cube_mono {n L : ℕ} (hnL : n ≤ L)
    {f : Vec d → ℝ} (hf : Continuous f) :
    supNormOn (cube d n) f ≤ supNormOn (cube d L) f := by
  unfold supNormOn
  apply csSup_le
  · have hzero : (0 : Vec d) ∈ cube d n := by
      rw [cube, mem_openCubeSet_originCube_iff]
      intro i
      have hp : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
      constructor <;> simp only [Pi.zero_apply] <;> nlinarith
    exact ⟨|f 0|, 0, hzero, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxL : x ∈ cube d L :=
      openCubeSet_originCube_subset_of_scale_le (by exact_mod_cast hnL) hx
    exact abs_apply_le_supNormOn_cube_of_continuous hf hxL

private theorem three_rpow_gap_mono {s : ℝ} (hs : 0 ≤ s)
    {a b : ℕ} (hab : a ≤ b) :
    (3 : ℝ) ^ (s * (a : ℝ)) ≤ (3 : ℝ) ^ (s * (b : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hab) hs

/-- Exponential envelope for the cutoff shell, with both parent shell blocks
retained.  The harmless doubled field exponent is still strictly below the
outer annular discount. -/
theorem exp_parentShellSup_add_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {n L m : ℕ}
    (hnL : n ≤ L) (hLm : L ≤ m) {epsilon s : ℝ}
    (hepsilon : 0 ≤ epsilon) (hs0 : 0 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : Sample d) {z : Vec d} (hz : z ∈ cube d m)
    (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s) :
    Real.exp (supNormOn (cube d n)
          (shellBlock m n (translatePotentialSample z omega)) +
        supNormOn (cube d n)
          (shellBlock m L (translatePotentialSample z omega))) ≤
      36 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 4) := by
  have hnM : n ≤ m := hnL.trans hLm
  have hn := exp_supNormOn_intermediateShellBlock_le_of_parent_goodEvent
    M L hnM hepsilon hsUpper omega hz hgood
  have hLlarge := exp_supNormOn_intermediateShellBlock_le_of_parent_goodEvent
    M L hLm hepsilon hsUpper omega hz hgood
  have hL : Real.exp (supNormOn (cube d n)
      (shellBlock m L (translatePotentialSample z omega))) ≤
      6 * (3 : ℝ) ^ ((s * ((m - L : ℕ) : ℝ)) / 8) := by
    exact (Real.exp_le_exp.mpr (supNormOn_cube_mono hnL
      (shellBlock_continuous m L _))).trans hLlarge
  rw [Real.exp_add]
  calc
    _ ≤ (6 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8)) *
        (6 * (3 : ℝ) ^ ((s * ((m - L : ℕ) : ℝ)) / 8)) :=
      mul_le_mul hn hL (Real.exp_pos _).le (by positivity)
    _ ≤ (6 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8)) *
        (6 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hgap : m - L ≤ m - n := by omega
      have hgapReal : ((m - L : ℕ) : ℝ) ≤ ((m - n : ℕ) : ℝ) := by
        exact_mod_cast hgap
      nlinarith
    _ = 36 * ((3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8) *
        (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8)) := by ring
    _ = 36 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 4) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 2
      ring

/-! ## The finite-shell sensitivity error -/

private theorem exp_abs_cutoffShellBlock_le_parent_finiteProduct
    {n L m : ℕ} (hnL : n ≤ L) (hLm : L ≤ m)
    (omega : Sample d) (x : Vec d) :
    Real.exp |shellBlock L n omega x| ≤
      ∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
        Real.exp |omega i x| := by
  unfold shellBlock
  calc
    Real.exp |∑ i ∈ Finset.Icc (n + 1) L, omega i x| ≤
        Real.exp (∑ i ∈ Finset.Icc (n + 1) L, |omega i x|) :=
      Real.exp_le_exp.mpr (Finset.abs_sum_le_sum_abs _ _)
    _ = ∏ i ∈ Finset.Icc (n + 1) L, Real.exp |omega i x| := by
      rw [Real.exp_sum]
    _ ≤ ∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
        Real.exp |omega i x| := by
      let u := Finset.Icc (n + 1) L
      let v := Finset.Icc (m - (m - n)) (m + (m - n))
      have huv : u ⊆ v := by
        intro i hi
        simp only [u, v, Finset.mem_Icc] at hi ⊢
        omega
      have hu0 : 0 ≤ ∏ i ∈ u, Real.exp |omega i x| := by positivity
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
          mul_le_mul_of_nonneg_right hrest hu0
        _ = ∏ i ∈ v, Real.exp |omega i x| := Finset.prod_sdiff huv

/-- Sharp parent-event exponential bound for the shell block ending at `L`.
It uses the single finite product at parent gap `m-n`, exactly as in the
manuscript, rather than multiplying two separate shell envelopes. -/
theorem exp_abs_cutoffShellBlock_le_of_parent_goodEvent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (K : ℕ) {n L m : ℕ}
    (hnL : n ≤ L) (hLm : L ≤ m) {epsilon s : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsUpper : s ≤ 1 / 2)
    (omega : Sample d) {y : Vec d} (hy : y ∈ cube d m)
    (hgood : omega ∈ goodEvent M (some K) m 0 epsilon s) :
    Real.exp |shellBlock L n omega y| ≤
      6 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8) := by
  have hnm : n ≤ m := hnL.trans hLm
  have hBdd := bddAbove_goodFieldTwo_values_of_goodFieldOne
    m (m - n) hepsilon hsUpper omega hgood.1
  have hyLarge : y ∈ translatedCube d
      ((m + 1 + (m - n) : ℕ) : ℤ) 0 := by
    refine ⟨y, openCubeSet_originCube_subset_of_scale_le ?_ hy, by simp⟩
    exact_mod_cast (show m ≤ m + 1 + (m - n) by omega)
  let finitePart : ℝ :=
    ∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)), Real.exp |omega i y|
  let tailPart : ℝ := ∏' i : ℕ, if m + (m - n) ≤ i then
    Real.exp (4 * |omega i y - omega i 0|) else 1
  have hfinite0 : 0 ≤ finitePart := by dsimp only [finitePart]; positivity
  have htailOne : 1 ≤ tailPart := by
    let f : ℕ → ℝ := fun i ↦ if m + (m - n) ≤ i then
      Real.exp (4 * |omega i y - omega i 0|) else 1
    have hf : ∀ i, 1 ≤ f i := by
      intro i
      dsimp only [f]
      split
      · exact Real.one_le_exp (by positivity)
      · exact le_rfl
    by_cases hmult : Multipliable f
    · dsimp only [tailPart]
      apply le_hasProd_of_le_prod hmult.hasProd
      intro u
      induction u using Finset.induction_on with
      | empty => simp
      | @insert a w haw ih =>
          rw [Finset.prod_insert haw]
          exact one_le_mul_of_one_le_of_one_le (hf a) ih
    · dsimp only [tailPart]
      rw [tprod_eq_one_of_not_multipliable hmult]
  have htail0 : 0 ≤ tailPart := zero_le_one.trans htailOne
  have hpoint : finitePart + tailPart ≤
      supNormOn (translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0)
        (fun x ↦
          (∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
              Real.exp |omega i x|) +
            ∏' i : ℕ, if m + (m - n) ≤ i then
              Real.exp (4 * |omega i x - omega i 0|) else 1) := by
    unfold supNormOn
    have hle := le_csSup hBdd
      (show |finitePart + tailPart| ∈ {a : ℝ | ∃ x ∈
          translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
            Real.exp |omega i x|) +
          ∏' i : ℕ, if m + (m - n) ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1|} by
        exact ⟨y, hyLarge, rfl⟩)
    rwa [abs_of_nonneg (add_nonneg hfinite0 htail0)] at hle
  have hfinite : Real.exp |shellBlock L n omega y| ≤ finitePart := by
    exact exp_abs_cutoffShellBlock_le_parent_finiteProduct hnL hLm omega y
  exact hfinite.trans ((le_add_of_nonneg_right htail0).trans
    (hpoint.trans (hgood.2.1 (m - n))))

/-- Below `L`, the two normalized coefficient ratios have the same saturated
deviation bound as in the uncutoff proof.  The cutoff ratio is read directly
from the finite shell block ending at `L`, so the manuscript exponent is
retained without a two-block loss. -/
theorem cutoffFiniteRatio_deviation_sum_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {n L m : ℕ}
    (hnL : n ≤ L) (hLm : L ≤ m) {epsilon s : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsLower : 64 * M.delta ^ 2 ≤ s)
    (hsUpper : s ≤ 1 / 2) (omega : Sample d) {z x : Vec d}
    (hx : x ∈ cube d n) (hy : x + z ∈ cube d m)
    (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s) :
    |Real.exp (shellBlock L n (translatePotentialSample z omega) x +
          normalizerLogError M L n) - 1| +
        |Real.exp (-(shellBlock L n (translatePotentialSample z omega) x +
          normalizerLogError M L n)) - 1| ≤
      24 * (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
        min 1 (supNormOn (cube d n)
              (shellBlock m n (translatePotentialSample z omega)) +
            supNormOn (cube d n)
              (shellBlock m L (translatePotentialSample z omega)) +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L - n : ℕ) : ℝ)) := by
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower
  let g := shellBlock L n (translatePotentialSample z omega) x
  let r := normalizerLogError M L n
  let G := |g|
  let R := |r|
  let Eg := 6 * (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 8)
  let Er := (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 16)
  have hG0 : 0 ≤ G := by dsimp only [G]; exact abs_nonneg _
  have hR0 : 0 ≤ R := by dsimp only [R]; exact abs_nonneg _
  have hg : |g| ≤ G := le_rfl
  have hr : |r| ≤ R := by exact le_rfl
  have hEg : Real.exp G ≤ Eg := by
    dsimp only [G, g, Eg]
    rw [shellBlock_translatePotentialSample L n omega z x]
    exact exp_abs_cutoffShellBlock_le_of_parent_goodEvent M L hnL hLm
      hepsilon hsUpper omega hy hgood
  have hErRaw := exp_abs_normalizerLogError_le_three_rpow M hnL hsLower
  have hEr : Real.exp R ≤ Er := by
    have hgap : L - n ≤ m - n := by omega
    have hgapReal : ((L - n : ℕ) : ℝ) ≤ ((m - n : ℕ) : ℝ) := by
      exact_mod_cast hgap
    have hmono : (3 : ℝ) ^ ((s * ((L - n : ℕ) : ℝ)) / 16) ≤
        (3 : ℝ) ^ ((s * ((m - n : ℕ) : ℝ)) / 16) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith
    dsimp only [R, r, Er]
    exact hErRaw.trans hmono
  have hraw := combined_ratio_deviation_sum_le_weighted_min
    (A := (1 : ℝ)) (Ainv := (1 : ℝ)) (g := g) (r := r)
    (S := (0 : ℝ)) (G := G) (R := R) (C := (0 : ℝ))
    (Eg := Eg) (Er := Er) (by norm_num) (by norm_num) hG0 hR0
    (by norm_num) (by norm_num) hg hr hEg hEr
  have hfactor : 2 * ((0 : ℝ) + 2) * (Eg * Er) =
      24 * (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) := by
    dsimp only [Eg, Er]
    calc
      2 * ((0 : ℝ) + 2) *
          (6 * (3 : ℝ) ^ (s * ((m - n : ℕ) : ℝ) / 8) *
            (3 : ℝ) ^ (s * ((m - n : ℕ) : ℝ) / 16)) =
        24 * ((3 : ℝ) ^ (s * ((m - n : ℕ) : ℝ) / 8) *
          (3 : ℝ) ^ (s * ((m - n : ℕ) : ℝ) / 16)) := by ring
      _ = 24 * (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 2
        ring
  have hrho : R ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
      ((L - n : ℕ) : ℝ) := by
    dsimp only [R, r]
    exact abs_normalizerLogError_le_of_le M hnL
  have hshell : G ≤ supNormOn (cube d n)
        (shellBlock m n (translatePotentialSample z omega)) +
      supNormOn (cube d n)
        (shellBlock m L (translatePotentialSample z omega)) := by
    dsimp only [G, g]
    exact abs_cutoffShellBlock_le_parentShellSup_add hnL hLm omega z hx
  have hmin : min 1 (0 + G + R) ≤ min 1
      (supNormOn (cube d n)
          (shellBlock m n (translatePotentialSample z omega)) +
        supNormOn (cube d n)
          (shellBlock m L (translatePotentialSample z omega)) +
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L - n : ℕ) : ℝ)) := by
    apply min_le_min le_rfl
    linarith
  dsimp only [g, r, G, R] at hraw ⊢
  rw [hfactor] at hraw
  have hscaled := mul_le_mul_of_nonneg_left hmin (show
    0 ≤ 24 * (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) by
      positivity)
  have hfinal := hraw.trans hscaled
  simpa only [one_mul, mul_one, zero_add] using hfinal

/-- The actual two-`L^∞` sensitivity error below the cutoff, on a scale-`n`
descendant of the scale-`m` parent cube. -/
theorem cutoffRatioError_ahom_le_of_parent_goodEvent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {n L m : ℕ}
    (hnL : n ≤ L) (hLm : L ≤ m) {epsilon s : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsLower : 64 * M.delta ^ 2 ≤ s)
    (hsUpper : s ≤ 1 / 2) (omega : Sample d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ))
    (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s) :
    cutoffRatioError M n L
        (translatePotentialSample (triadicCubeShift R) omega)
        (Ch02.cubeDomain (originCube d (n : ℤ))) (ahom M L) ≤
      2 * (24 * (3 : ℝ) ^
          ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
        min 1 (supNormOn (cube d n)
              (shellBlock m n
                (translatePotentialSample (triadicCubeShift R) omega)) +
            supNormOn (cube d n)
              (shellBlock m L
                (translatePotentialSample (triadicCubeShift R) omega)) +
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L - n : ℕ) : ℝ))) ^ 2 := by
  let z := triadicCubeShift R
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  let W := 24 * (3 : ℝ) ^
      ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
    min 1 (supNormOn (cube d n)
          (shellBlock m n (translatePotentialSample z omega)) +
        supNormOn (cube d n)
          (shellBlock m L (translatePotentialSample z omega)) +
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L - n : ℕ) : ℝ))
  have hnm : n ≤ m := hnL.trans hLm
  have hpoint : ∀ x ∈ cube d n,
      |Real.exp (shellBlock L n (translatePotentialSample z omega) x +
            normalizerLogError M L n) - 1| +
          |Real.exp (-(shellBlock L n (translatePotentialSample z omega) x +
            normalizerLogError M L n)) - 1| ≤ W := by
    intro x hx
    have hRscale : R.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    have hxR : z + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simpa only [z, hRscale, add_sub_cancel_left] using hx
    have hy : x + z ∈ cube d m := by
      rw [add_comm]
      exact openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hR) hR hxR
    exact cutoffFiniteRatio_deviation_sum_le M hnL hLm hepsilon hsLower
      hsUpper omega hx hy hgood
  have hzero : (0 : Vec d) ∈ cube d n := by
    rw [cube, mem_openCubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
    constructor <;> simp only [Pi.zero_apply] <;> nlinarith
  have hW0 : 0 ≤ W :=
    (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hpoint 0 hzero)
  have hfwd := scalarRatioLInf_one_le_of_forall_bound (U := U) hW0 (by
    intro x hx
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans
      (hpoint x (by simpa only [U, Ch02.cubeDomain_coe] using hx)))
  have hrev := scalarRatioLInf_one_le_of_forall_bound (U := U) hW0 (by
    intro x hx
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans
      (hpoint x (by simpa only [U, Ch02.cubeDomain_coe] using hx)))
  have hbL := tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale
    M (show L ≤ L from le_rfl) omega
  have hrepacked := cutoffRatioError_tailAverage_eq_combined
    M hnL (show L ≤ L from le_rfl) omega z U
  rw [hbL] at hrepacked
  have hcombined : combinedCoefficientRatio M L L n omega z =
      fun x ↦ Real.exp (shellBlock L n (translatePotentialSample z omega) x +
        normalizerLogError M L n) := by
    funext x
    unfold combinedCoefficientRatio
    rw [Section4Recursion.tailCoefficient_of_ge M (show L ≤ L from le_rfl), hbL,
      div_self (ahom_pos M L).ne', one_mul]
  have hcombinedInv : combinedCoefficientRatioInv M L L n omega z =
      fun x ↦ Real.exp (-(shellBlock L n
        (translatePotentialSample z omega) x + normalizerLogError M L n)) := by
    funext x
    unfold combinedCoefficientRatioInv
    rw [Section4Recursion.tailCoefficient_of_ge M (show L ≤ L from le_rfl), hbL,
      div_self (ahom_pos M L).ne', mul_one]
  rw [hcombined, hcombinedInv] at hrepacked
  rw [hrepacked]
  have hfwd0 := scalarRatioLInf_nonneg U
    (fun x ↦ Real.exp (shellBlock L n (translatePotentialSample z omega) x +
      normalizerLogError M L n)) (fun _ ↦ 1)
  have hrev0 := scalarRatioLInf_nonneg U
    (fun x ↦ Real.exp (-(shellBlock L n (translatePotentialSample z omega) x +
      normalizerLogError M L n))) (fun _ ↦ 1)
  have hfwdSq := mul_self_le_mul_self hfwd0 hfwd
  have hrevSq := mul_self_le_mul_self hrev0 hrev
  dsimp only [W, z, U] at hfwdSq hrevSq ⊢
  nlinarith only [hfwdSq, hrevSq]

/-! ## Weighted positive-scale localization below `L` -/

/-- The cutoff analogue of the manuscript's applied sensitivity estimate at
a nonnegative scale `n < L`.  Both shell blocks remain visible for the final
spatial aggregation. -/
theorem weightedPaperScalarProbe_cutoff_le_response_add_shells
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {n L m j : ℕ}
    (hnL : n ≤ L) (hLm : L ≤ m) {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (hj : j ≤ m) (hnj : n + 2 ≤ j) (omega : Sample d)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ))
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    {e : Vec d} (he : vecNormSq e = 1)
    (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s) :
    (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) *
        paperScalarProbe (originCube d (n : ℤ))
          (aCutoffFamily M L
            (translatePotentialSample (triadicCubeShift R) omega))
          (tailCoefficientCubeAverage M L m omega) e ≤
      2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n n omega (triadicCubeShift R) e +
        12 * (24 : ℝ) ^ 2 *
          (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          (min 1 (supNormOn (cube d n)
                (shellBlock m n
                  (translatePotentialSample (triadicCubeShift R) omega)) +
              supNormOn (cube d n)
                (shellBlock m L
                  (translatePotentialSample (triadicCubeShift R) omega)) +
              SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L - n : ℕ) : ℝ))) ^ 2 := by
  let T : ℝ := ((m - n : ℕ) : ℝ)
  let u : ℝ := s * T
  let A : ℝ := (3 : ℝ) ^ ((3 * s * T) / 16)
  let B : ℝ := min 1 (supNormOn (cube d n)
      (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) +
    supNormOn (cube d n)
      (shellBlock m L (translatePotentialSample (triadicCubeShift R) omega)) +
    SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L - n : ℕ) : ℝ))
  let Jloc : ℝ := section6Response M n n omega (triadicCubeShift R) e
  let E : ℝ := cutoffRatioError M n L
    (translatePotentialSample (triadicCubeShift R) omega)
    (Ch02.cubeDomain (originCube d (n : ℤ))) (ahom M L)
  let P : ℝ := paperScalarProbe (originCube d (n : ℤ))
    (aCutoffFamily M L
      (translatePotentialSample (triadicCubeShift R) omega))
    (ahom M L) e
  let G : ℝ := (3 : ℝ) ^ (u / 8)
  let w : ℝ := (3 : ℝ) ^ (-(3 / 2) * u)
  let v : ℝ := (3 : ℝ) ^ (-u)
  have hnm : n ≤ m := hnL.trans hLm
  have hgap : (m : ℝ) - (n : ℝ) = T := by
    dsimp only [T]
    rw [Nat.cast_sub hnm]
  have hRscale : R.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hR
  have hgrid : OnTriadicGrid n (triadicCubeShift R) :=
    onTriadicGrid_triadicCubeShift_of_scale hRscale
  have hJraw := hgood.2.2 j n hj hnj (triadicCubeShift R)
    (by simpa using hgrid) (by simpa using hann) e he
  have hJ : Jloc ≤ G := by
    have hepsq : epsilon ^ 2 ≤ 1 := by nlinarith [sq_nonneg epsilon]
    have hpow0 : 0 ≤ (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) :=
      Real.rpow_nonneg (by norm_num) _
    have := hJraw.trans (mul_le_mul_of_nonneg_right hepsq hpow0)
    simpa only [Option.getD_some, min_eq_left hnL, one_mul, hgap, Jloc, G, u]
      using this
  have hJ0 : 0 ≤ Jloc := by
    dsimp only [Jloc, section6Response, paperScalarProbe]
    exact Ch02.responseJ_nonneg _ _ _ _
  have hP : P ≤ 2 * Jloc + 3 * E * (Jloc + 1) := by
    exact paperScalarProbe_translatedCutoff_le_section6Response_add_ratioError
      M n L omega (triadicCubeShift R) (ahom_pos M L) e he
  have hE : E ≤ 2 * ((24 : ℝ) * A * B) ^ 2 := by
    simpa only [E, A, B, T] using
      cutoffRatioError_ahom_le_of_parent_goodEvent M hnL hLm hepsilon0
        hsLower hsUpper omega hR hgood
  have hu0 : 0 ≤ u := by
    dsimp only [u, T]
    exact mul_nonneg
      ((mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower)
      (by positivity)
  have hG1 : 1 ≤ G := one_le_responseGrowth hu0
  have hw0 : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
  have hwv : w ≤ v := responseOuterWeight_le_residualWeight hu0
  have hcollapse : w * A ^ 2 * G = v := by
    dsimp only [w, A, G, v, u]
    convert responseErrorWeight_identity (s * T) using 1
    all_goals ring_nf
  have hweighted := weightedTransport_of_bounds hP hE hJ0 hJ hG1 hw0 hwv hcollapse
  have hb := tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm omega
  rw [hb]
  simpa only [P, Jloc, B, w, v, u, T] using hweighted

/-! ## Aggregation into the printed slots -/

private theorem cutoffGoodResponse_discounted_atom_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {m : ℕ}
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    {omega : Sample d} (homega : omega ∈ goodEvent M (some L) m 0 epsilon s)
    {r : ℝ}
    (hr : r ∈ {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
        ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            t = section6Response M n (min n L) omega z e})}) :
    r ≤ epsilon := by
  rcases hr with ⟨j, n, hjm, hnj, z, hzgrid, hzann, rfl⟩
  have hnm : n ≤ m := by omega
  have hgap0 : 0 ≤ (m : ℝ) - (n : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast hnm)
  let A : Set ℝ := {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
    t = section6Response M n (min n L) omega z e}
  have hAbdd : BddAbove A := by
    simpa only [A] using
      bddAbove_section6Response_unitSphere M n (min n L) omega z
  have hAne : A.Nonempty := by
    let i : Fin d := ⟨0, lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension⟩
    refine ⟨section6Response M n (min n L) omega z (Pi.single i 1),
      Pi.single i 1, ?_, rfl⟩
    rw [vecNormSq, vecDot, Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [Pi.single_eq_of_ne hbi]
    · simp
  have hresp : sSup A ≤ epsilon ^ 2 *
      (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := by
    refine csSup_le hAne ?_
    rintro _ ⟨e, he, rfl⟩
    simpa only [A, Option.getD_some] using
      homega.2.2 j n hjm hnj z
        (by simpa only [sub_zero] using hzgrid)
        (by simpa only [sub_zero] using hzann) e he
  have hresp0 : 0 ≤ sSup A := by
    obtain ⟨_, e, he, rfl⟩ := hAne
    have hJ : 0 ≤ section6Response M n (min n L) omega z e := by
      unfold section6Response paperScalarProbe
      exact Ch02.responseJ_nonneg _ _ _ _
    exact hJ.trans (le_csSup hAbdd ⟨e, he, rfl⟩)
  have hsqrt : Real.sqrt (sSup A) ≤ epsilon *
      (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by
    have hright0 : 0 ≤ epsilon *
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by positivity
    rw [Real.sqrt_le_iff]
    refine ⟨hright0, hresp.trans_eq ?_⟩
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  calc
    (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) * Real.sqrt (sSup A) ≤
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          (epsilon * (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) := by
      gcongr
    _ = epsilon * (3 : ℝ) ^
        (-(7 * s / 16) * ((m : ℝ) - (n : ℝ))) := by
      calc
        _ = epsilon * ((3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) := by ring
        _ = epsilon * (3 : ℝ) ^
            (-(s / 2) * ((m : ℝ) - (n : ℝ)) +
              (s * ((m : ℝ) - (n : ℝ))) / 16) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        _ = _ := by
          congr 1
          ring_nf
    _ ≤ epsilon * 1 := by
      gcongr
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hgap0)
    _ = epsilon := mul_one _

private theorem cutoffResponseSlot_bddAbove_of_goodEvent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {m : ℕ}
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    {omega : Sample d} (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s) :
    BddAbove {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
        Real.sqrt (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
          q = section6Response M n (min n L) omega z e})} := by
  refine ⟨epsilon, ?_⟩
  intro r hr
  exact cutoffGoodResponse_discounted_atom_le M L hepsilon0 hs0 hgood hr

private theorem cutoff_response_weight_le_slot_sq
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {m n j : ℕ} (hnm : n ≤ m) {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    (omega : Sample d) (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s)
    (hjm : j ≤ m) (hnj : n + 2 ≤ j) {z e : Vec d}
    (hzgrid : OnTriadicGrid n z) (hzann : z ∈ cube d j \ cube d (j - 1))
    (he : vecNormSq e = 1) :
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        section6Response M n (min n L) omega z e ≤
      cutoffGoodScaleResponseSlot M L s m omega ^ 2 := by
  let A : Set ℝ := {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
    q = section6Response M n (min n L) omega z e}
  have hAbdd : BddAbove A := by
    simpa only [A] using
      bddAbove_section6Response_unitSphere M n (min n L) omega z
  have hJ0 : 0 ≤ section6Response M n (min n L) omega z e := by
    unfold section6Response paperScalarProbe
    exact Ch02.responseJ_nonneg _ _ _ _
  have hA0 : 0 ≤ sSup A := hJ0.trans (le_csSup hAbdd ⟨e, he, rfl⟩)
  let atom := (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
    Real.sqrt (sSup A)
  have hatomMem : atom ∈ {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
        Real.sqrt (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
          q = section6Response M n (min n L) omega z e})} :=
    ⟨j, n, hjm, hnj, z, hzgrid, hzann, by simp only [atom, A]⟩
  have hatomLe : atom ≤ cutoffGoodScaleResponseSlot M L s m omega := by
    unfold cutoffGoodScaleResponseSlot
    exact le_csSup
      (cutoffResponseSlot_bddAbove_of_goodEvent M L hepsilon0 hs0 hgood) hatomMem
  have hatom0 : 0 ≤ atom := by dsimp only [atom]; positivity
  have hgap : (m : ℝ) - (n : ℝ) = ((m - n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hnm]
  calc
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        section6Response M n (min n L) omega z e ≤
      (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) * sSup A := by
        exact mul_le_mul_of_nonneg_left
          (le_csSup hAbdd ⟨e, he, rfl⟩) (Real.rpow_nonneg (by norm_num) _)
    _ = atom ^ 2 := by
      dsimp only [atom]
      rw [mul_pow, Real.sq_sqrt hA0, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 2
      rw [hgap]
      ring
    _ ≤ cutoffGoodScaleResponseSlot M L s m omega ^ 2 :=
      pow_le_pow_left₀ hatom0 hatomLe 2

private theorem localShellBlockSup_le_parent
    {m n k : ℕ} (omega : Sample d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) :
    supNormOn (cube d n)
        (shellBlock m k (translatePotentialSample (triadicCubeShift R) omega)) ≤
      supNormOn (cube d m) (shellBlock m k omega) := by
  unfold supNormOn
  apply csSup_le
  · have hzero : (0 : Vec d) ∈ cube d n := by
      rw [cube, mem_openCubeSet_originCube_iff]
      intro i
      have hp : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
      constructor <;> simp only [Pi.zero_apply] <;> nlinarith
    exact ⟨|shellBlock m k (translatePotentialSample (triadicCubeShift R) omega) 0|,
      0, hzero, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hscale : R.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    have hxR : triadicCubeShift R + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simpa only [hscale, add_sub_cancel_left] using hx
    have hxM : triadicCubeShift R + x ∈ cube d m :=
      openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hR) hR hxR
    have hle := abs_apply_le_supNormOn_cube_of_continuous
      (shellBlock_continuous m k omega) hxM
    simpa only [shellBlock_translatePotentialSample, add_comm] using hle

private theorem shellSlot_bddAbove
    (s : ℝ) (m : ℕ) (omega : Sample d) :
    BddAbove {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d m) (shellBlock m j omega)} := by
  let F : ℕ → ℝ := fun j ↦
    (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
      supNormOn (cube d m) (shellBlock m j omega)
  refine ⟨Finset.sup' (Finset.range (m + 1))
      (Finset.nonempty_range_iff.mpr (by omega)) F, ?_⟩
  rintro _ ⟨j, hj, rfl⟩
  exact Finset.le_sup' F (Finset.mem_range.mpr (by omega))

/-- Either parent shell block produced by the cutoff split is controlled by
the one printed shell slot after the annular discount. -/
private theorem cutoff_shell_weight_le_slot_sq
    {m n k : ℕ} (hnk : n ≤ k) (hkm : k ≤ m) {s : ℝ} (hs0 : 0 ≤ s)
    (omega : Sample d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) :
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        supNormOn (cube d n)
          (shellBlock m k (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 ≤
      goodScaleShellSlot s m omega ^ 2 := by
  have hnm : n ≤ m := hnk.trans hkm
  let G := supNormOn (cube d m) (shellBlock m k omega)
  let atom := (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (k : ℝ))) * G
  have hlocal := localShellBlockSup_le_parent (k := k) omega hR
  have hG0 : 0 ≤ G := supNormOn_cube_nonneg m (shellBlock_continuous m k omega)
  have hatomMem : atom ∈ {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d m) (shellBlock m j omega)} :=
    ⟨k, hkm, by simp only [atom, G]⟩
  have hatomLe : atom ≤ goodScaleShellSlot s m omega := by
    unfold goodScaleShellSlot
    exact le_csSup (shellSlot_bddAbove s m omega) hatomMem
  have hatom0 : 0 ≤ atom := by dsimp only [atom]; positivity
  have hlocal0 : 0 ≤ supNormOn (cube d n)
      (shellBlock m k (translatePotentialSample (triadicCubeShift R) omega)) :=
    supNormOn_cube_nonneg n (shellBlock_continuous m k _)
  have hw : (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) ≤
      ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (k : ℝ)))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hgap : m - k ≤ m - n := by omega
    have hgapReal : ((m - k : ℕ) : ℝ) ≤ ((m - n : ℕ) : ℝ) := by
      exact_mod_cast hgap
    have hcast : (m : ℝ) - (k : ℝ) = ((m - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hkm]
    rw [hcast]
    nlinarith
  calc
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        supNormOn (cube d n)
          (shellBlock m k (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 ≤
      (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) * G ^ 2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlocal0 hlocal 2)
          (Real.rpow_nonneg (by norm_num) _)
    _ ≤ ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (k : ℝ)))) ^ 2 * G ^ 2 := by
      gcongr
    _ = atom ^ 2 := by simp only [atom]; ring
    _ ≤ goodScaleShellSlot s m omega ^ 2 :=
      pow_le_pow_left₀ hatom0 hatomLe 2

private theorem cutoff_drift_weight_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {n L m : ℕ}
    (hnL : n ≤ L) (hLm : L ≤ m) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) :
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L - n : ℕ) : ℝ)) ^ 2 ≤
      2 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
  have hgap : L - n ≤ m - n := by omega
  have hgapReal : ((L - n : ℕ) : ℝ) ≤ ((m - n : ℕ) : ℝ) := by
    exact_mod_cast hgap
  have htau0 : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := M.G4.tauSq_pos.le
  have hsmall : (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L - n : ℕ) : ℝ)) ^ 2 ≤
      (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ)) ^ 2 := by
    apply pow_le_pow_left₀ (mul_nonneg htau0 (by positivity))
    exact mul_le_mul_of_nonneg_left hgapReal htau0
  calc
    _ ≤ (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - n : ℕ) : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 2 * (s⁻¹) ^ 2 * M.delta ^ 4 :=
      three_rpow_neg_mul_tauSq_sq_le M hsLower (by positivity)
    _ = 2 * (s⁻¹ * M.delta ^ 2) ^ 2 := by ring

/-- Common square budget for every nonnegative cutoff annular atom. -/
def cutoffGoodScalePositiveBudget
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s : ℝ) (m : ℕ) (omega : Sample d) : ℝ :=
  2 * cutoffGoodScaleResponseSlot M L s m omega ^ 2 +
    36 * (24 : ℝ) ^ 2 *
      (2 * goodScaleShellSlot s m omega ^ 2 +
        2 * (s⁻¹ * M.delta ^ 2) ^ 2)

theorem cutoffGoodScalePositiveBudget_nonneg
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s : ℝ) (m : ℕ) (omega : Sample d) :
    0 ≤ cutoffGoodScalePositiveBudget M L s m omega := by
  unfold cutoffGoodScalePositiveBudget
  positivity

private theorem weightedLocalProbe_cutoff_below_le_budget
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {n L m j : ℕ}
    (hnL : n ≤ L) (hLm : L ≤ m) {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (hj : j ≤ m) (hnj : n + 2 ≤ j) (omega : Sample d)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ))
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    {e : Vec d} (he : vecNormSq e = 1)
    (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s) :
    (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) *
        paperScalarProbe (originCube d (n : ℤ))
          (aCutoffFamily M L
            (translatePotentialSample (triadicCubeShift R) omega))
          (tailCoefficientCubeAverage M L m omega) e ≤
      cutoffGoodScalePositiveBudget M L s m omega := by
  have hnm : n ≤ m := hnL.trans hLm
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower
  have hraw := weightedPaperScalarProbe_cutoff_le_response_add_shells
    M hnL hLm hepsilon0 hepsilon1 hsLower hsUpper hj hnj omega hR hann he hgood
  have hresp := cutoff_response_weight_le_slot_sq M L hnm hepsilon0 hs0
    omega hgood hj hnj
    (onTriadicGrid_triadicCubeShift_of_scale
      (scale_eq_of_mem_descendantsAtScale hR)) hann he
  have hrespN : (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
      section6Response M n n omega (triadicCubeShift R) e ≤
      cutoffGoodScaleResponseSlot M L s m omega ^ 2 := by
    simpa only [min_eq_left hnL] using hresp
  have hshellN := cutoff_shell_weight_le_slot_sq (show n ≤ n from le_rfl)
    hnm hs0 omega hR
  have hshellL := cutoff_shell_weight_le_slot_sq hnL hLm hs0 omega hR
  have hdrift := cutoff_drift_weight_le M hnL hLm hsLower
  let v : ℝ := (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ)))
  let G1 := supNormOn (cube d n)
    (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega))
  let G2 := supNormOn (cube d n)
    (shellBlock m L (translatePotentialSample (triadicCubeShift R) omega))
  let rho := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L - n : ℕ) : ℝ)
  have hv0 : 0 ≤ v := Real.rpow_nonneg (by norm_num) _
  have hsplit := min_one_add_three_sq_le_three_sum_sq G1 G2 rho
  have hweightedSplit : v * min 1 (G1 + G2 + rho) ^ 2 ≤
      3 * (v * G1 ^ 2 + v * G2 ^ 2 + v * rho ^ 2) := by
    have := mul_le_mul_of_nonneg_left hsplit hv0
    nlinarith
  have hcomponents : v * G1 ^ 2 + v * G2 ^ 2 + v * rho ^ 2 ≤
      2 * goodScaleShellSlot s m omega ^ 2 +
        2 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
    dsimp only [v, G1, G2, rho] at *
    nlinarith
  have herror : 12 * (24 : ℝ) ^ 2 *
      (v * min 1 (G1 + G2 + rho) ^ 2) ≤
      36 * (24 : ℝ) ^ 2 *
        (2 * goodScaleShellSlot s m omega ^ 2 +
          2 * (s⁻¹ * M.delta ^ 2) ^ 2) := by
    calc
      _ ≤ 12 * (24 : ℝ) ^ 2 *
          (3 * (v * G1 ^ 2 + v * G2 ^ 2 + v * rho ^ 2)) := by
        gcongr
      _ = 36 * (24 : ℝ) ^ 2 *
          (v * G1 ^ 2 + v * G2 ^ 2 + v * rho ^ 2) := by ring
      _ ≤ _ := by gcongr
  unfold cutoffGoodScalePositiveBudget
  dsimp only [v, G1, G2, rho] at herror
  calc
    _ ≤ 2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n n omega (triadicCubeShift R) e +
        12 * (24 : ℝ) ^ 2 *
          ((3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
            min 1 (supNormOn (cube d n)
                  (shellBlock m n
                    (translatePotentialSample (triadicCubeShift R) omega)) +
                supNormOn (cube d n)
                  (shellBlock m L
                    (translatePotentialSample (triadicCubeShift R) omega)) +
                SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L - n : ℕ) : ℝ)) ^ 2) := by
      simpa only [mul_assoc] using hraw
    _ ≤ 2 * cutoffGoodScaleResponseSlot M L s m omega ^ 2 +
        36 * (24 : ℝ) ^ 2 *
          (2 * goodScaleShellSlot s m omega ^ 2 +
            2 * (s⁻¹ * M.delta ^ 2) ^ 2) := by
      have hmain := mul_le_mul_of_nonneg_left hrespN
        (show (0 : ℝ) ≤ 2 by norm_num)
      have hmain' : 2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n n omega (triadicCubeShift R) e ≤
          2 * cutoffGoodScaleResponseSlot M L s m omega ^ 2 := by
        calc
          _ = 2 * ((3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
              section6Response M n n omega (triadicCubeShift R) e) := by ring
          _ ≤ _ := hmain
      exact add_le_add hmain' herror

/-- Every nonnegative annular atom on a parent scale above `L` is controlled
by the cutoff positive budget.  The proof splits the local scale at `L`:
below it uses sensitivity, and above it uses literal coefficient equality. -/
theorem positive_annular_atom_le_cutoffBudget
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : Sample d)
    (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s)
    (p : AnnularPairTwo d (m : ℤ)) (hscale0 : 0 ≤ p.1.1.scale) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (p.1.1.scale : ℝ)))) *
        section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega) p.1.1 ≤
      ENNReal.ofReal (cutoffGoodScalePositiveBudget M L s m omega) := by
  obtain ⟨hj, hscale, hann⟩ := p.2
  let n : ℕ := p.1.1.scale.toNat
  let jn : ℕ := p.1.2.toNat
  have hncast : (n : ℤ) = p.1.1.scale := Int.toNat_of_nonneg hscale0
  have hj0 : 0 ≤ p.1.2 := by omega
  have hjcast : (jn : ℤ) = p.1.2 := Int.toNat_of_nonneg hj0
  have hnmZ : (n : ℤ) ≤ (m : ℤ) := by rw [hncast]; omega
  have hjmZ : (jn : ℤ) ≤ (m : ℤ) := by rw [hjcast]; exact hj
  have hnjZ : (n : ℤ) + 2 ≤ (jn : ℤ) := by rw [hncast, hjcast]; omega
  have hnm : n ≤ m := by exact_mod_cast hnmZ
  have hjm : jn ≤ m := by exact_mod_cast hjmZ
  have hnj : n + 2 ≤ jn := by exact_mod_cast hnjZ
  have hR : p.1.1 ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ) := by
    rw [hncast]
    exact annularCube_mem_descendantsAtScale hj hscale hann
  have hweight :
      (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (p.1.1.scale : ℝ))) =
        (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) := by
    congr 1
    have hgap : (m : ℝ) - (n : ℝ) = ((m - n : ℕ) : ℝ) := by
      rw [Nat.cast_sub hnm]
    have hnreal : (n : ℝ) = (p.1.1.scale : ℝ) := by exact_mod_cast hncast
    rw [← hnreal, hgap]
    ring
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower
  unfold section6LocalProbeMax
  rw [ENNReal.mul_iSup]
  refine iSup_le fun e ↦ ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), hweight]
  apply ENNReal.ofReal_le_ofReal
  rcases le_total n L with hnL | hLn
  · simpa only [hncast, Section6Covariance.translatePotentialSample_zero] using
      weightedLocalProbe_cutoff_below_le_budget M hnL hLm hepsilon0 hepsilon1
        hsLower hsUpper hjm hnj omega hR (by simpa only [hjcast] using hann)
          e.2 hgood
  · have hmin : min n L = L := min_eq_right hLn
    have hresp := cutoff_response_weight_le_slot_sq M L hnm hepsilon0 hs0
      omega hgood hjm hnj
      (onTriadicGrid_triadicCubeShift_of_scale
        (scale_eq_of_mem_descendantsAtScale hR))
      (by simpa only [hjcast] using hann) e.2
    rw [hmin] at hresp
    have hu0 : 0 ≤ s * ((m - n : ℕ) : ℝ) :=
      mul_nonneg hs0 (by positivity)
    have houter := responseOuterWeight_le_residualWeight hu0
    have hJ0 : 0 ≤ section6Response M n L omega (triadicCubeShift p.1.1) e := by
      unfold section6Response paperScalarProbe
      exact Ch02.responseJ_nonneg _ _ _ _
    have hb := tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm omega
    have heq : paperScalarProbe (originCube d (n : ℤ))
        (aCutoffFamily M L
          (translatePotentialSample (triadicCubeShift p.1.1) omega))
        (tailCoefficientCubeAverage M L m omega) e =
        section6Response M n L omega (triadicCubeShift p.1.1) e := by
      rw [hb]
      rfl
    rw [Section6Covariance.translatePotentialSample_zero]
    rw [← hncast, heq]
    calc
      (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) *
          section6Response M n L omega (triadicCubeShift p.1.1) e ≤
        (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n L omega (triadicCubeShift p.1.1) e :=
        mul_le_mul_of_nonneg_right houter hJ0
      _ ≤ cutoffGoodScaleResponseSlot M L s m omega ^ 2 := hresp
      _ ≤ cutoffGoodScalePositiveBudget M L s m omega := by
        unfold cutoffGoodScalePositiveBudget
        have hsquare := sq_nonneg (cutoffGoodScaleResponseSlot M L s m omega)
        have hrest : 0 ≤ 36 * (24 : ℝ) ^ 2 *
            (2 * goodScaleShellSlot s m omega ^ 2 +
              2 * (s⁻¹ * M.delta ^ 2) ^ 2) := by positivity
        nlinarith

/-! ## The negative-scale branch ending at `L` -/

/-- The low-frequency block ending at `L` is the parent low block minus the
intervening parent shell. -/
theorem fullShellBlock_cutoff_eq_parent_sub_shellBlock
    {L m : ℕ} (hLm : L ≤ m) (omega : Sample d) (x : Vec d) :
    fullShellBlock L omega x = fullShellBlock m omega x - shellBlock m L omega x := by
  unfold fullShellBlock shellBlock
  rw [show Finset.Icc (L + 1) m = Finset.Ico (L + 1) (m + 1) by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega]
  have hsum := Finset.sum_range_add_sum_Ico (fun i ↦ omega i x)
    (show L + 1 ≤ m + 1 by omega)
  rw [← hsum]
  ring

private theorem fullShellBlock_continuous (m : ℕ) (omega : Sample d) :
    Continuous (fullShellBlock m omega) := by
  unfold fullShellBlock
  fun_prop

private theorem abs_fullShellBlock_cutoff_le_parentSup_add
    {L m : ℕ} (hLm : L ≤ m) (omega : Sample d) {x : Vec d}
    (hx : x ∈ cube d m) :
    |fullShellBlock L omega x| ≤
      supNormOn (cube d m) (fullShellBlock m omega) +
        supNormOn (cube d m) (shellBlock m L omega) := by
  rw [fullShellBlock_cutoff_eq_parent_sub_shellBlock hLm]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · exact abs_apply_le_supNormOn_cube_of_continuous
      (fullShellBlock_continuous m omega) hx
  · exact abs_apply_le_supNormOn_cube_of_continuous
      (shellBlock_continuous m L omega) hx

private theorem exp_parentFull_add_shellSup_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (K : ℕ) {L m : ℕ}
    (hLm : L ≤ m) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hs0 : 0 ≤ s) (hsUpper : s ≤ 1 / 2) (omega : Sample d)
    (hgood : omega ∈ goodEvent M (some K) m 0 epsilon s) :
    Real.exp (supNormOn (cube d m) (fullShellBlock m omega) +
        supNormOn (cube d m) (shellBlock m L omega)) ≤
      36 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) := by
  have hBdd := bddAbove_goodFieldTwo_values_of_goodFieldOne
    m m hepsilon hsUpper omega hgood.1
  have hfull := exp_supNormOn_fullShellBlock_le_of_goodFieldTwo
    m omega hgood.2.1 hBdd
  have hshellPoint : ∀ x ∈ cube d m,
      Real.exp |shellBlock m L omega x| ≤
        6 * (3 : ℝ) ^ ((s * ((m - L : ℕ) : ℝ)) / 8) := by
    intro x hx
    exact exp_abs_cutoffShellBlock_le_of_parent_goodEvent M K hLm le_rfl
      hepsilon hsUpper omega hx hgood
  have hshellSup : Real.exp (supNormOn (cube d m) (shellBlock m L omega)) ≤
      6 * (3 : ℝ) ^ ((s * ((m - L : ℕ) : ℝ)) / 8) := by
    let B := 6 * (3 : ℝ) ^ ((s * ((m - L : ℕ) : ℝ)) / 8)
    have hB0 : 0 < B := by dsimp only [B]; positivity
    have hlog : supNormOn (cube d m) (shellBlock m L omega) ≤ Real.log B := by
      unfold supNormOn
      apply csSup_le
      · have hzero : (0 : Vec d) ∈ cube d m := by
          rw [cube, mem_openCubeSet_originCube_iff]
          intro i
          have hp : 0 < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
          constructor <;> simp only [Pi.zero_apply] <;> nlinarith
        exact ⟨|shellBlock m L omega 0|, 0, hzero, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        rw [← Real.log_exp |shellBlock m L omega x|]
        exact Real.log_le_log (Real.exp_pos _) (hshellPoint x hx)
    calc
      _ ≤ Real.exp (Real.log B) := Real.exp_le_exp.mpr hlog
      _ = B := Real.exp_log hB0
      _ = _ := rfl
  rw [Real.exp_add]
  calc
    _ ≤ (6 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) *
        (6 * (3 : ℝ) ^ ((s * ((m - L : ℕ) : ℝ)) / 8)) :=
      mul_le_mul hfull hshellSup (Real.exp_pos _).le (by positivity)
    _ ≤ (6 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) *
        (6 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hgapReal : ((m - L : ℕ) : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.sub_le m L
      nlinarith
    _ = 36 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) := by
      calc
        _ = 36 * ((3 : ℝ) ^ ((s * (m : ℝ)) / 8) *
            (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) := by ring
        _ = _ := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          congr 2
          ring

private theorem exp_abs_subunitLogError_cutoff_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {s : ℝ} (hsLower : 64 * M.delta ^ 2 ≤ s) :
    Real.exp |subunitLogError M L| ≤
      (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) := by
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ 4 * M.delta ^ 2 := by
    calc
      _ ≤ (Real.log 2 / 2) * M.delta ^ 2 := tauSq_le_delta_sq M
      _ ≤ 4 * M.delta ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg M.delta)
  have hL1 : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
  have hm1 : (L : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hLm 1
  have herr := abs_subunitLogError_le M L
  have hbudget : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L : ℝ) + 1) ≤
      (s * ((m : ℝ) + 1)) / 16 := by
    have h1 := mul_le_mul_of_nonneg_right htau hL1
    have h2 := mul_le_mul_of_nonneg_right hsLower (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)
    nlinarith [mul_le_mul_of_nonneg_left hm1 M.G4.tauSq_pos.le]
  have harg := herr.trans hbudget
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  apply Real.exp_le_exp.mpr
  have hlog3 : 1 ≤ Real.log 3 := by
    have hexp : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    have hlog := Real.log_lt_log (Real.exp_pos 1) hexp
    simpa only [Real.log_exp] using hlog.le
  exact harg.trans (by
    have hnonneg : 0 ≤ (s * ((m : ℝ) + 1)) / 16 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hlog3 hnonneg])

/-- Pointwise ratio energy for the direct negative-scale response, with all
coefficient ratios ending at `L`. -/
theorem cutoffSubunit_ratioEnergy_le_of_parent_goodEvent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : Sample d) (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s)
    {x : Vec d} (hx : x ∈ cube d m) :
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x / ahom M L - 1) ^ 2 +
        (ahom M L / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x - 1) ^ 2 ≤
      (144 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
        (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) *
        min 1 (supNormOn (cube d m) (fullShellBlock m omega) +
          supNormOn (cube d m) (shellBlock m L omega) +
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L : ℝ) + 1))) ^ 2 := by
  let g := fullShellBlock L omega x
  let r := subunitLogError M L
  let G := supNormOn (cube d m) (fullShellBlock m omega) +
    supNormOn (cube d m) (shellBlock m L omega)
  let Rho := |r|
  let Eg := 36 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4)
  let Er := (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16)
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact add_nonneg
      (supNormOn_cube_nonneg m (fullShellBlock_continuous m omega))
      (supNormOn_cube_nonneg m (shellBlock_continuous m L omega))
  have hR0 : 0 ≤ Rho := by dsimp only [Rho]; exact abs_nonneg _
  have hg : |g| ≤ G := by
    dsimp only [g, G]
    exact abs_fullShellBlock_cutoff_le_parentSup_add hLm omega hx
  have hr : |r| ≤ Rho := le_rfl
  have hEg : Real.exp G ≤ Eg := by
    dsimp only [G, Eg]
    exact exp_parentFull_add_shellSup_le M L hLm hepsilon
      ((mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower)
      hsUpper omega hgood
  have hEr : Real.exp Rho ≤ Er := by
    dsimp only [Rho, r, Er]
    exact exp_abs_subunitLogError_cutoff_le M hLm hsLower
  have hdev := combined_ratio_deviation_sum_le_weighted_min
    (A := (1 : ℝ)) (Ainv := (1 : ℝ)) (g := g) (r := r)
    (S := (0 : ℝ)) (G := G) (R := Rho) (C := (0 : ℝ))
    (Eg := Eg) (Er := Er) (by norm_num) (by norm_num) hG0 hR0
    (by norm_num) (by norm_num) hg hr hEg hEr
  have hfactor : 2 * ((0 : ℝ) + 2) * (Eg * Er) =
      144 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
        (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) := by
    dsimp only [Eg, Er]
    ring
  have hrho : Rho ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L : ℝ) + 1) := by
    dsimp only [Rho, r]
    exact abs_subunitLogError_le M L
  have hmin : min 1 (0 + G + Rho) ≤ min 1
      (G + SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L : ℝ) + 1)) := by
    apply min_le_min le_rfl
    linarith
  have hcut : SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x / ahom M L =
      Real.exp (g + r) := by
    have ha := aCutoff_eq_exp_fullShellBlock M L omega x
    have hinv : (ahom M L)⁻¹ = Real.exp (-Real.log (ahom M L)) := by
      calc
        (ahom M L)⁻¹ = (Real.exp (Real.log (ahom M L)))⁻¹ := by
          rw [Real.exp_log (ahom_pos M L)]
        _ = Real.exp (-Real.log (ahom M L)) := (Real.exp_neg _).symm
    rw [div_eq_mul_inv, ha, hinv, ← Real.exp_add]
    dsimp only [g, r, subunitLogError]
    congr 1
    ring
  have hcutInv : ahom M L / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x =
      Real.exp (-(g + r)) := by
    calc
      _ = (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x / ahom M L)⁻¹ := by
        rw [inv_div]
      _ = (Real.exp (g + r))⁻¹ := by rw [hcut]
      _ = _ := by rw [← Real.exp_neg]
  rw [hcut, hcutInv]
  have hsq : (Real.exp (g + r) - 1) ^ 2 +
      (Real.exp (-(g + r)) - 1) ^ 2 ≤
      (|Real.exp (g + r) - 1| + |Real.exp (-(g + r)) - 1|) ^ 2 := by
    rw [← sq_abs (Real.exp (g + r) - 1),
      ← sq_abs (Real.exp (-(g + r)) - 1)]
    nlinarith [abs_nonneg (Real.exp (g + r) - 1),
      abs_nonneg (Real.exp (-(g + r)) - 1)]
  refine hsq.trans ?_
  rw [hfactor] at hdev
  have hscaled := mul_le_mul_of_nonneg_left hmin (show
    0 ≤ 144 * (3 : ℝ) ^ (s * (m : ℝ) / 4) *
      (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16) by positivity)
  have hdev' := hdev.trans hscaled
  exact pow_le_pow_left₀ (by positivity)
    (by simpa only [one_mul, mul_one, zero_add] using hdev') 2

private theorem cutoff_subunit_envelope_weight
    {s : ℝ} (hsUpper : s ≤ 1 / 2) (m : ℕ) :
    (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) *
        (144 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
          (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16)) ^ 2 ≤
      2 * 144 ^ 2 * (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) := by
  have hsFactor : (3 : ℝ) ^ (s / 8) ≤ 2 := by
    have hmono : (3 : ℝ) ^ (s / 8) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [← Real.sqrt_eq_rpow] at hmono
    exact hmono.trans (by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)])
  have hexact : (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) *
      (144 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
        (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16)) ^ 2 =
      144 ^ 2 * (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
        (3 : ℝ) ^ (s / 8) := by
    have hpow1 : ((3 : ℝ) ^ ((s * (m : ℝ)) / 4)) ^ 2 =
        (3 : ℝ) ^ (2 * ((s * (m : ℝ)) / 4)) := by
      rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    have hpow2 : ((3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16)) ^ 2 =
        (3 : ℝ) ^ (2 * ((s * ((m : ℝ) + 1)) / 16)) := by
      rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    rw [mul_pow, mul_pow, hpow1, hpow2]
    calc
      _ = 144 ^ 2 * ((3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) *
          (3 : ℝ) ^ (2 * (s * (m : ℝ) / 4)) *
          (3 : ℝ) ^ (2 * (s * ((m : ℝ) + 1) / 16))) := by ring
      _ = 144 ^ 2 * (3 : ℝ) ^
          (-(3 * s / 2) * (m : ℝ) + 2 * (s * (m : ℝ) / 4) +
            2 * (s * ((m : ℝ) + 1) / 16)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ = _ := by
        have hexp : -(3 * s / 2) * (m : ℝ) + 2 * (s * (m : ℝ) / 4) +
            2 * (s * ((m : ℝ) + 1) / 16) =
            -(7 * s / 8) * (m : ℝ) + s / 8 := by ring
        rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        ring
  rw [hexact]
  have hbase0 : 0 ≤ 144 ^ 2 *
      (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) := by positivity
  nlinarith

private theorem cutoff_subunit_decay_le_fullSlot_sq
    {s : ℝ} (hs0 : 0 ≤ s) (m : ℕ) (omega : Sample d) :
    (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
        supNormOn (cube d m) (fullShellBlock m omega) ^ 2 ≤
      goodScaleFullSlot s m omega ^ 2 := by
  unfold goodScaleFullSlot
  rw [mul_pow]
  have hpow : ((3 : ℝ) ^ (-(s / 8) * (m : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * (-(s / 8) * (m : ℝ))) := by
    rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hpow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]

private theorem cutoff_subunit_decay_le_shellSlot_sq
    {L m : ℕ} (hLm : L ≤ m) {s : ℝ} (hs0 : 0 ≤ s)
    (omega : Sample d) :
    (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
        supNormOn (cube d m) (shellBlock m L omega) ^ 2 ≤
      goodScaleShellSlot s m omega ^ 2 := by
  let G := supNormOn (cube d m) (shellBlock m L omega)
  let atom := (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (L : ℝ))) * G
  have hG0 : 0 ≤ G := supNormOn_cube_nonneg m (shellBlock_continuous m L omega)
  have hatomMem : atom ∈ {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d m) (shellBlock m j omega)} :=
    ⟨L, hLm, by simp only [atom, G]⟩
  have hatomLe : atom ≤ goodScaleShellSlot s m omega := by
    unfold goodScaleShellSlot
    exact le_csSup (shellSlot_bddAbove s m omega) hatomMem
  have hatom0 : 0 ≤ atom := by dsimp only [atom]; positivity
  have hw : (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) ≤
      ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (L : ℝ)))) ^ 2 := by
    rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hLmReal : (L : ℝ) ≤ (m : ℝ) := by exact_mod_cast hLm
    nlinarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
  calc
    _ ≤ ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (L : ℝ)))) ^ 2 * G ^ 2 :=
      mul_le_mul_of_nonneg_right hw (sq_nonneg G)
    _ = atom ^ 2 := by simp only [atom]; ring
    _ ≤ goodScaleShellSlot s m omega ^ 2 :=
      pow_le_pow_left₀ hatom0 hatomLe 2

private theorem cutoff_subunit_decay_drift_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {s : ℝ} (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2) :
    (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
        (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L : ℝ) + 1)) ^ 2 ≤
      16 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
  have hs : 0 < s :=
    (mul_pos (by norm_num) (sq_pos_of_pos M.shellPrefix.delta_pos)).trans_le hsLower
  have hLm1 : (L : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hLm 1
  have hrho : (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L : ℝ) + 1)) ^ 2 ≤
      (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1)) ^ 2 := by
    apply pow_le_pow_left₀
      (mul_nonneg M.G4.tauSq_pos.le (by positivity : (0 : ℝ) ≤ (L : ℝ) + 1))
    exact mul_le_mul_of_nonneg_left hLm1 M.G4.tauSq_pos.le
  have hdecay : (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) ≤
      2 * (3 : ℝ) ^ (-((s / 2) * ((m : ℝ) + 1))) := by
    have hsplit : -(7 * s / 8) * (m : ℝ) ≤
        s / 2 - (s / 2) * ((m : ℝ) + 1) := by
      nlinarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hsplit
    have hrewrite : (3 : ℝ) ^
        (s / 2 - (s / 2) * ((m : ℝ) + 1)) =
        (3 : ℝ) ^ (s / 2) *
          (3 : ℝ) ^ (-((s / 2) * ((m : ℝ) + 1))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
    rw [hrewrite] at hpow
    have hsPow : (3 : ℝ) ^ (s / 2) ≤ 2 := by
      have hmono : (3 : ℝ) ^ (s / 2) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [← Real.sqrt_eq_rpow] at hmono
      exact hmono.trans (by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)])
    have hp0 : 0 ≤ (3 : ℝ) ^ (-((s / 2) * ((m : ℝ) + 1))) := by positivity
    exact hpow.trans (mul_le_mul_of_nonneg_right hsPow hp0)
  have hcore := three_rpow_neg_mul_drift_sq_le
    (s := s / 2) (t := (m : ℝ) + 1)
    (tau := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) (by positivity) (by positivity)
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ^ 2 ≤ M.delta ^ 4 := by
    have hlog : Real.log 2 / 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hle := (tauSq_le_delta_sq M).trans
      (mul_le_of_le_one_left (sq_nonneg M.delta) hlog)
    calc
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ^ 2 ≤ (M.delta ^ 2) ^ 2 :=
        pow_le_pow_left₀ M.G4.tauSq_pos.le hle 2
      _ = M.delta ^ 4 := by ring
  calc
    _ ≤ (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
        (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left hrho (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 2 * (3 : ℝ) ^ (-((s / 2) * ((m : ℝ) + 1))) *
        (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m : ℝ) + 1)) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hdecay (sq_nonneg _)
    _ ≤ 2 * (2 * ((s / 2)⁻¹) ^ 2 *
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ^ 2) := by
      nlinarith [hcore]
    _ ≤ 2 * (2 * ((s / 2)⁻¹) ^ 2 * M.delta ^ 4) := by
      gcongr
    _ = 16 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
      field_simp [hs.ne']
      ring

/-- Square budget for all negative annular scales above a cutoff-saturated
parent. -/
def cutoffGoodScaleSubunitBudget
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : Sample d) : ℝ :=
  6 * 144 ^ 2 * (goodScaleFullSlot s m omega ^ 2 +
    goodScaleShellSlot s m omega ^ 2 +
    16 * (s⁻¹ * M.delta ^ 2) ^ 2)

theorem cutoffGoodScaleSubunitBudget_nonneg
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : Sample d) :
    0 ≤ cutoffGoodScaleSubunitBudget M s m omega := by
  unfold cutoffGoodScaleSubunitBudget
  positivity

/-- Every nonpositive annular atom is controlled by the cutoff subunit
budget; all coefficient ratios end at `L`. -/
theorem weightedLocalProbe_cutoff_subunit_le_budget [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : Sample d) (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s)
    {R : TriadicCube d} {j : ℤ} (hj : j ≤ (m : ℤ))
    (hscale : R.scale ≤ j - 2)
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    (hneg : R.scale ≤ 0) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (R.scale : ℝ)))) *
        section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega) R ≤
      ENNReal.ofReal (cutoffGoodScaleSubunitBudget M s m omega) := by
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hsLower
  set F : ℝ := 144 * (3 : ℝ) ^ ((s * (m : ℝ)) / 4) *
    (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) with hF
  set Gf : ℝ := supNormOn (cube d m) (fullShellBlock m omega) with hGf
  set Gs : ℝ := supNormOn (cube d m) (shellBlock m L omega) with hGs
  set rho : ℝ := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((L : ℝ) + 1) with hrho
  set B : ℝ := min 1 (Gf + Gs + rho) with hB
  set K : ℝ := (F * B) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  set omega' : Sample d := translatePotentialSample (triadicCubeShift R) omega
    with homega'
  have hRdesc : R ∈ descendantsAtScale (originCube d (m : ℤ)) R.scale :=
    annularCube_mem_descendantsAtScale hj hscale hann
  have hpoint : ∀ x ∈ ((Ch02.cubeDomain (originCube d R.scale) :
      Ch02.Domain d) : Set (Vec d)),
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega' x / ahom M L - 1) ^ 2 +
        (ahom M L / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega' x - 1) ^ 2 ≤ K := by
    intro x hx
    have hxcube : x ∈ cube d R.scale := by
      simpa only [Ch02.cubeDomain_coe] using hx
    have hxR : triadicCubeShift R + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simpa only [add_sub_cancel_left] using hxcube
    have hxM : triadicCubeShift R + x ∈ cube d (m : ℤ) :=
      openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hRdesc) hRdesc hxR
    have hxM' : x + triadicCubeShift R ∈ cube d (m : ℤ) := by
      rwa [add_comm] at hxM
    rw [homega', Section6Covariance.aCutoff_translatePotentialSample]
    simpa only [K, F, B, Gf, Gs, rho] using
      cutoffSubunit_ratioEnergy_le_of_parent_goodEvent M hLm hepsilon
        hsLower hsUpper omega hgood hxM'
  have haverage : Ch02.average (Ch02.cubeDomain (originCube d R.scale))
      (fun x ↦
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega' x / ahom M L - 1) ^ 2 +
        (ahom M L / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega' x - 1) ^ 2) ≤ K := by
    set U : Ch02.Domain d := Ch02.cubeDomain (originCube d R.scale) with hU
    have haPos := SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega'
    have hcontinuous : Continuous (fun x ↦
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega' x / ahom M L - 1) ^ 2 +
        (ahom M L / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega' x - 1) ^ 2) :=
      ((((SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega').div_const _).sub
        continuous_const).pow 2).add
        (((continuous_const.div
          (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega')
          (fun x ↦ (haPos x).ne')).sub continuous_const).pow 2)
    exact average_le_of_le_on U
      ((hcontinuous.continuousOn.integrableOn_compact
        U.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set
          subset_closure) hpoint
  have hprobeRaw := section6LocalProbeMax_le_ratioEnergy_average M L m omega R
  have hb := tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm omega
  rw [hb] at hprobeRaw
  have hprobe : section6LocalProbeMax M L omega 0
      (tailCoefficientCubeAverage M L m omega) R ≤ ENNReal.ofReal K := by
    rw [hb]
    exact hprobeRaw.trans (ENNReal.ofReal_le_ofReal haverage)
  have hweight : (3 : ℝ) ^ (-(3 * s / 2) *
      ((m : ℝ) - (R.scale : ℝ))) ≤
      (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hk : ((R.scale : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hneg
    nlinarith
  have hw0 : 0 ≤ (3 : ℝ) ^ (-(3 * s / 2) *
      ((m : ℝ) - (R.scale : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have henv := cutoff_subunit_envelope_weight hsUpper m
  have hsplit := min_one_add_three_sq_le_three_sum_sq Gf Gs rho
  have hdecayFull := cutoff_subunit_decay_le_fullSlot_sq hs0 m omega
  have hdecayShell := cutoff_subunit_decay_le_shellSlot_sq hLm hs0 omega
  have hdecayDrift := cutoff_subunit_decay_drift_le M hLm hsLower hsUpper
  have hfinal : (3 : ℝ) ^ (-(3 * s / 2) *
      ((m : ℝ) - (R.scale : ℝ))) * K ≤
      cutoffGoodScaleSubunitBudget M s m omega := by
    have hB2 : B ^ 2 ≤ 3 * (Gf ^ 2 + Gs ^ 2 + rho ^ 2) := by
      simpa only [B] using hsplit
    have hstep1 : (3 : ℝ) ^ (-(3 * s / 2) *
        ((m : ℝ) - (R.scale : ℝ))) * K ≤
        (2 * 144 ^ 2 * (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ))) * B ^ 2 := by
      have hFB0 : 0 ≤ B ^ 2 := sq_nonneg _
      have hweightF : (3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (R.scale : ℝ))) * F ^ 2 ≤
          (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) * F ^ 2 :=
        mul_le_mul_of_nonneg_right hweight (sq_nonneg F)
      calc
        (3 : ℝ) ^ (-(3 * s / 2) *
            ((m : ℝ) - (R.scale : ℝ))) * K =
            ((3 : ℝ) ^ (-(3 * s / 2) *
              ((m : ℝ) - (R.scale : ℝ))) * F ^ 2) * B ^ 2 := by
          rw [hK]
          ring
        _ ≤ ((3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) * F ^ 2) * B ^ 2 :=
          mul_le_mul_of_nonneg_right hweightF hFB0
        _ = ((3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) *
            (144 * (3 : ℝ) ^ (s * (m : ℝ) / 4) *
              (3 : ℝ) ^ (s * ((m : ℝ) + 1) / 16)) ^ 2) * B ^ 2 := by
          rw [hF]
        _ ≤ (2 * 144 ^ 2 *
            (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ))) * B ^ 2 :=
          mul_le_mul_of_nonneg_right henv hFB0
    refine hstep1.trans ?_
    have hscaleB := mul_le_mul_of_nonneg_left hB2 (show
      0 ≤ 2 * 144 ^ 2 * (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) by
        positivity)
    have hcomponents : (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
        (Gf ^ 2 + Gs ^ 2 + rho ^ 2) ≤
        goodScaleFullSlot s m omega ^ 2 + goodScaleShellSlot s m omega ^ 2 +
          16 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
      rw [mul_add, mul_add]
      simpa only [Gf, Gs, rho] using
        add_le_add (add_le_add hdecayFull hdecayShell) hdecayDrift
    unfold cutoffGoodScaleSubunitBudget
    calc
      _ ≤ (2 * 144 ^ 2 * (3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ))) *
          (3 * (Gf ^ 2 + Gs ^ 2 + rho ^ 2)) := hscaleB
      _ = 6 * 144 ^ 2 * ((3 : ℝ) ^ (-(7 * s / 8) * (m : ℝ)) *
          (Gf ^ 2 + Gs ^ 2 + rho ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcomponents (by positivity)
  calc
    ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (R.scale : ℝ)))) *
        section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega) R ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (R.scale : ℝ)))) * ENNReal.ofReal K := by
        gcongr
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (R.scale : ℝ))) * K) :=
      (ENNReal.ofReal_mul hw0).symm
    _ ≤ ENNReal.ofReal (cutoffGoodScaleSubunitBudget M s m omega) :=
      ENNReal.ofReal_le_ofReal hfinal

/-- Complete refined annular supremum on a cutoff good event above `L`. -/
theorem annularSupTwo_le_cutoffGoodScaleBudget [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : Sample d) (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s) :
    annularSupTwo s (m : ℤ)
        (section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega)) ≤
      ENNReal.ofReal (cutoffGoodScalePositiveBudget M L s m omega +
        cutoffGoodScaleSubunitBudget M s m omega) := by
  refine iSup_le fun p ↦ ?_
  rcases le_or_gt 0 p.1.1.scale with hscale0 | hscaleneg
  · refine (positive_annular_atom_le_cutoffBudget M hLm hepsilon0 hepsilon1
      hsLower hsUpper omega hgood p hscale0).trans (ENNReal.ofReal_le_ofReal ?_)
    have hsub := cutoffGoodScaleSubunitBudget_nonneg M s m omega
    linarith
  · obtain ⟨hj, hsc, hann⟩ := p.2
    refine (weightedLocalProbe_cutoff_subunit_le_budget M hLm hepsilon0
      hsLower hsUpper omega hgood hj hsc hann hscaleneg.le).trans
        (ENNReal.ofReal_le_ofReal ?_)
    have hpos := cutoffGoodScalePositiveBudget_nonneg M L s m omega
    linarith

/-- A universal square constant for the cutoff annular localization. -/
def cutoffAnnularSquareConstant : ℝ :=
  192 * (2 + 41472 + 124416 * 18)

theorem cutoffAnnularSquareConstant_pos : 0 < cutoffAnnularSquareConstant := by
  unfold cutoffAnnularSquareConstant
  norm_num

/-- The requested raw `m > L` annular localization estimate.  Its four slots
are exactly those consumed by `section6HomogenizationError_le_cutoff_min_of_slot_bound`;
the nonnegative gradient slot is included for literal compatibility with that
recombination interface. -/
theorem section6HomogenizationError_le_cutoff_slots_of_cutoff_lt_scale
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L < m)
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : Sample d) (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s) :
    section6HomogenizationError M s L m omega 0 ≤
      Real.sqrt cutoffAnnularSquareConstant *
        (cutoffGoodScaleResponseSlot M L s m omega +
          s⁻¹ * M.delta ^ 2 + goodScaleShellSlot s m omega +
          goodScaleFullSlot s m omega + goodScaleGradientSlot m omega) := by
  have hdim : 2 ≤ d := M.shellPrefix.dimension
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hs : 0 < s :=
    (mul_pos (by norm_num) (sq_pos_of_pos M.shellPrefix.delta_pos)).trans_le hsLower
  have hstep1 := section6HomogenizationError_le_annularSupTwo hs hsUpper hd1
    M L m omega 0
  rw [Section6Covariance.translatePotentialSample_zero] at hstep1
  have hstep2 := annularSupTwo_le_cutoffGoodScaleBudget M hLm.le hepsilon0
    hepsilon1 hsLower hsUpper omega hgood
  let A := cutoffGoodScaleResponseSlot M L s m omega
  let D := s⁻¹ * M.delta ^ 2
  let Bs := goodScaleShellSlot s m omega
  let Bf := goodScaleFullSlot s m omega
  let Bg := goodScaleGradientSlot m omega
  let B := cutoffGoodScalePositiveBudget M L s m omega +
    cutoffGoodScaleSubunitBudget M s m omega
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg (cutoffGoodScalePositiveBudget_nonneg M L s m omega)
      (cutoffGoodScaleSubunitBudget_nonneg M s m omega)
  have hmul : (192 : ℝ≥0∞) * annularSupTwo s (m : ℤ)
      (section6LocalProbeMax M L omega 0
        (tailCoefficientCubeAverage M L m omega)) ≤ ENNReal.ofReal (192 * B) := by
    calc
      _ ≤ (192 : ℝ≥0∞) * ENNReal.ofReal B := by gcongr
      _ = ENNReal.ofReal (192 * B) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 192)]
        congr 1
        simp
  have hchain : ENNReal.ofReal (section6HomogenizationError M s L m omega 0) ≤
      ENNReal.ofReal ((192 * B) ^ (1 / 2 : ℝ)) := by
    refine hstep1.trans ?_
    calc
      _ ≤ (ENNReal.ofReal (192 * B)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hmul (by norm_num)
      _ = ENNReal.ofReal ((192 * B) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
  have hreal : section6HomogenizationError M s L m omega 0 ≤
      Real.sqrt (192 * B) := by
    rw [Real.sqrt_eq_rpow]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
  have hA0 : 0 ≤ A := by
    unfold A cutoffGoodScaleResponseSlot
    refine Real.sSup_nonneg ?_
    rintro a ⟨j, n, -, -, z, -, -, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hBs0 : 0 ≤ Bs := by
    unfold Bs goodScaleShellSlot
    refine Real.sSup_nonneg ?_
    rintro a ⟨j, -, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (supNormOn_cube_nonneg m (shellBlock_continuous m j omega))
  have hBf0 : 0 ≤ Bf := by
    unfold Bf goodScaleFullSlot
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (supNormOn_cube_nonneg m (fullShellBlock_continuous m omega))
  have hBg0 : 0 ≤ Bg := by
    dsimp only [Bg]
    rw [goodScaleGradientSlot_eq_longRatioGradientTail]
    exact longRatioGradientTail_nonneg m omega
  let Sigma := A + D + Bs + Bf + Bg
  have hSigma0 : 0 ≤ Sigma := by dsimp only [Sigma]; positivity
  have hsquares : A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2 ≤ Sigma ^ 2 := by
    dsimp only [Sigma]
    nlinarith [mul_nonneg hA0 hD0, mul_nonneg hA0 hBs0,
      mul_nonneg hA0 hBf0, mul_nonneg hA0 hBg0, mul_nonneg hD0 hBs0,
      mul_nonneg hD0 hBf0, mul_nonneg hD0 hBg0, mul_nonneg hBs0 hBf0,
      mul_nonneg hBs0 hBg0, mul_nonneg hBf0 hBg0]
  have hcoef : 192 * B ≤ cutoffAnnularSquareConstant *
      (A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2) := by
    dsimp only [B, A, D, Bs, Bf, Bg]
    unfold cutoffGoodScalePositiveBudget cutoffGoodScaleSubunitBudget
      cutoffAnnularSquareConstant
    nlinarith [sq_nonneg (cutoffGoodScaleResponseSlot M L s m omega),
      sq_nonneg (s⁻¹ * M.delta ^ 2),
      sq_nonneg (goodScaleShellSlot s m omega),
      sq_nonneg (goodScaleFullSlot s m omega),
      sq_nonneg (goodScaleGradientSlot m omega)]
  calc
    section6HomogenizationError M s L m omega 0 ≤ Real.sqrt (192 * B) := hreal
    _ ≤ Real.sqrt (cutoffAnnularSquareConstant * Sigma ^ 2) :=
      Real.sqrt_le_sqrt (hcoef.trans
        (mul_le_mul_of_nonneg_left hsquares cutoffAnnularSquareConstant_pos.le))
    _ = Real.sqrt cutoffAnnularSquareConstant * Sigma := by
      rw [Real.sqrt_mul cutoffAnnularSquareConstant_pos.le, Real.sqrt_sq hSigma0]
    _ = _ := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
