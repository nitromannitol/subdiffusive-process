module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.AnnularAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables

@[expose] public section

/-!
# The subunit branch of the Section 6 good-scale display

This module discharges the cubes of side at most one in Step 2 of
`p.good.scale.mathcal.E` (`p.good.scale.mathcal.E` and `e.direct.J.bound.subunit`).  For those indices the
manuscript does not localize at all: it applies the direct response bound
`e.direct.J.bound.subunit` and charges the resulting forward-plus-reciprocal
ratio energy of `a_L / (b_{L,m})_{cu_m}` to the last four display slots.

The factorization used here is the manuscript's

```text
R_{L,m}(x) = (b_{L,m}(x) / (b_{L,m})_{cu_m}) * exp (sum_{i=0}^m g_i(x) + rho_m),
rho_m = -((m+1) tau^2 + log ahom_m),
```

so the already established long-ratio event reading, the full-block field growth,
and the deterministic drift collapse can be reused verbatim.

The proof separates the direct response bound, deterministic factorization,
event reading and weight arithmetic.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Elementary helpers -/

private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact Real.exp_one_lt_d9.le.trans (by norm_num)

private theorem exp_le_three_rpow {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.exp x ≤ (3 : ℝ) ^ y := by
  have hy : 0 ≤ y := hx.trans hxy
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  apply Real.exp_le_exp.mpr
  calc
    x ≤ y := hxy
    _ = 1 * y := (one_mul y).symm
    _ ≤ Real.log 3 * y := mul_le_mul_of_nonneg_right one_le_log_three hy

/-- A normalized average is bounded by any pointwise bound on the domain. -/
theorem average_le_of_le_on (U : Ch02.Domain d) {f : Vec d → ℝ} {K : ℝ}
    (hint : IntegrableOn f (U : Set (Vec d)))
    (hle : ∀ x ∈ (U : Set (Vec d)), f x ≤ K) :
    Ch02.average U f ≤ K := by
  have hvol : 0 < (volume (U : Set (Vec d))).toReal :=
    Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U
  have hfin : volume (U : Set (Vec d)) ≠ ⊤ := ne_of_lt U.isDomain.volume_lt_top
  have hconst : IntegrableOn (fun _ : Vec d => K) (U : Set (Vec d)) :=
    integrableOn_const hfin (by finiteness)
  have hmono : ∫ x in (U : Set (Vec d)), f x ≤
      ∫ _x in (U : Set (Vec d)), K :=
    setIntegral_mono_on hint hconst U.measurableSet hle
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at hmono
  show (volume (U : Set (Vec d))).toReal⁻¹ *
    ∫ x in (U : Set (Vec d)), f x ≤ K
  rw [inv_mul_le_iff₀ hvol]
  linarith

/-! ## The full shell block on the good event -/

/-- The full shell block `sum_{i=0}^m g_i` occurring in the frozen display. -/
def fullShellBlock (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), omega i x

private theorem fullShellBlock_continuous (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Continuous (fullShellBlock m omega) := by
  unfold fullShellBlock
  fun_prop

private theorem exp_abs_fullShellBlock_le_finiteProduct (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    Real.exp |fullShellBlock m omega x| ≤
      ∏ i ∈ Finset.Icc (m - m) (m + m), Real.exp |omega i x| := by
  unfold fullShellBlock
  calc
    Real.exp |∑ i ∈ Finset.range (m + 1), omega i x| ≤
        Real.exp (∑ i ∈ Finset.range (m + 1), |omega i x|) :=
      Real.exp_le_exp.mpr (Finset.abs_sum_le_sum_abs _ _)
    _ = ∏ i ∈ Finset.range (m + 1), Real.exp |omega i x| := by
      rw [Real.exp_sum]
    _ ≤ ∏ i ∈ Finset.Icc (m - m) (m + m), Real.exp |omega i x| := by
      let u := Finset.range (m + 1)
      let v := Finset.Icc (m - m) (m + m)
      have huv : u ⊆ v := by
        intro i hi
        simp only [u, v, Finset.mem_Icc, Finset.mem_range] at hi ⊢
        omega
      have hleft : 0 ≤ ∏ i ∈ u, Real.exp |omega i x| := by positivity
      have hrest : 1 ≤ ∏ i ∈ v \ u, Real.exp |omega i x| := by
        induction v \ u using Finset.induction_on with
        | empty => simp
        | @insert a w haw ih =>
            rw [Finset.prod_insert haw]
            exact one_le_mul_of_one_le_of_one_le
              (Real.one_le_exp (abs_nonneg _)) ih
      change (∏ i ∈ u, Real.exp |omega i x|) ≤ ∏ i ∈ v, Real.exp |omega i x|
      calc
        (∏ i ∈ u, Real.exp |omega i x|) =
            1 * ∏ i ∈ u, Real.exp |omega i x| := by rw [one_mul]
        _ ≤ (∏ i ∈ v \ u, Real.exp |omega i x|) *
            ∏ i ∈ u, Real.exp |omega i x| :=
          mul_le_mul_of_nonneg_right hrest hleft
        _ = ∏ i ∈ v, Real.exp |omega i x| := Finset.prod_sdiff huv

private theorem one_le_goodFieldTwo_tail_full
    (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x y : Vec d) :
    1 ≤ ∏' i : ℕ, if m + m ≤ i then
      Real.exp (4 * |omega i x - omega i y|) else 1 := by
  let f : ℕ → ℝ := fun i => if m + m ≤ i then
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

/-- The full-block field growth read from `GoodFieldTwo` at its top index. -/
theorem exp_abs_fullShellBlock_le_of_goodFieldTwo
    (m : ℕ) {s : ℝ} (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldTwo m 0 s omega)
    (hBdd : BddAbove {a : ℝ | ∃ x ∈
      translatedCube d ((m + 1 + m : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - m) (m + m), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + m ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1|}) :
    ∀ x ∈ cube d (m : ℤ),
      Real.exp |fullShellBlock m omega x| ≤
        6 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) := by
  intro x hx
  have hxlarge : x ∈ cube d ((m + 1 + m : ℕ) : ℤ) := by
    refine openCubeSet_originCube_subset_of_scale_le ?_ hx
    exact_mod_cast (by omega : m ≤ m + 1 + m)
  have hxlarge' : x ∈ translatedCube d ((m + 1 + m : ℕ) : ℤ) 0 :=
    ⟨x, hxlarge, by simp⟩
  let finitePart : ℝ :=
    ∏ i ∈ Finset.Icc (m - m) (m + m), Real.exp |omega i x|
  let tailPart : ℝ :=
    ∏' i : ℕ, if m + m ≤ i then
      Real.exp (4 * |omega i x - omega i 0|) else 1
  have hfinitePos : 0 < finitePart := by
    dsimp [finitePart]
    positivity
  have htailOne : 1 ≤ tailPart := one_le_goodFieldTwo_tail_full m omega x 0
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
                Real.exp (4 * |omega i y - omega i 0|) else 1|} from
        ⟨x, hxlarge', rfl⟩)
    rwa [abs_of_pos hcontrolPos] at hle
  have hevent := hgood m
  exact (exp_abs_fullShellBlock_le_finiteProduct m omega x).trans
    ((le_add_of_nonneg_right (zero_le_one.trans htailOne)).trans
      (hpoint.trans hevent))

/-- Supremum-norm form of the full-block field growth estimate. -/
theorem exp_supNormOn_fullShellBlock_le_of_goodFieldTwo
    (m : ℕ) {s : ℝ} (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldTwo m 0 s omega)
    (hBdd : BddAbove {a : ℝ | ∃ x ∈
      translatedCube d ((m + 1 + m : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - m) (m + m), Real.exp |omega i x|) +
          ∏' i : ℕ, if m + m ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1|}) :
    Real.exp (supNormOn (cube d (m : ℤ)) (fullShellBlock m omega)) ≤
      6 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) := by
  let B : ℝ := 6 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hpoint := exp_abs_fullShellBlock_le_of_goodFieldTwo m omega hgood hBdd
  have hzero : (0 : Vec d) ∈ cube d (m : ℤ) := by
    rw [cube, mem_openCubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
    constructor <;> simp only [Pi.zero_apply] <;> nlinarith
  have hsup : supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) ≤
      Real.log B := by
    unfold supNormOn
    apply csSup_le
    · exact ⟨|fullShellBlock m omega 0|, 0, hzero, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← Real.log_exp |fullShellBlock m omega x|]
      exact Real.log_le_log (Real.exp_pos _) (hpoint x hx)
  calc
    Real.exp (supNormOn (cube d (m : ℤ)) (fullShellBlock m omega)) ≤
        Real.exp (Real.log B) := Real.exp_le_exp.mpr hsup
    _ = B := Real.exp_log hBpos

/-! ## The subunit coefficient factorization -/

/-- The subunit branch's deterministic normalizer error
`rho_m = -((m+1) tau^2 + log ahom_m)`. -/
def subunitLogError (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) : ℝ :=
  -(((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P + Real.log (ahom M m))

theorem abs_subunitLogError_le (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) :
    |subunitLogError M m| ≤
      _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1) := by
  have h := abs_ahomShift_le_subunitDrift M m
  unfold subunitLogError
  rw [abs_neg]
  simpa only [subunitDrift, mul_comm] using! h

theorem aCutoff_eq_exp_fullShellBlock
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    _root_.SubdiffusiveProcess.Model.aCutoff M m omega x =
      Real.exp (fullShellBlock m omega x -
        ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
  unfold _root_.SubdiffusiveProcess.Model.aCutoff fullShellBlock
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  ring

/-- **The subunit factorization.**  The globally normalized cutoff splits into
the tail-average long ratio and the exponential of the full shell block plus
the deterministic drift. -/
theorem aCutoff_div_tailAverage_eq_ratio_mul_exp
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
        tailCoefficientCubeAverage M L m omega =
      (tailCoefficient M L m omega x /
          tailCoefficientCubeAverage M L m omega) *
        Real.exp (fullShellBlock m omega x + subunitLogError M m) := by
  have hmin : min m L = m := min_eq_left hmL
  have hahom : 0 < ahom M m := ahom_pos M m
  have hcut : 0 < _root_.SubdiffusiveProcess.Model.aCutoff M m omega x :=
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x
  have hexp : Real.exp (fullShellBlock m omega x + subunitLogError M m) =
      _root_.SubdiffusiveProcess.Model.aCutoff M m omega x / ahom M m := by
    rw [aCutoff_eq_exp_fullShellBlock M m omega x, subunitLogError,
      ← Real.exp_log hahom]
    rw [← Real.exp_sub]
    congr 1
    rw [Real.log_exp]
    ring
  rw [hexp, tailCoefficient, hmin]
  field_simp

/-! ## The pointwise ratio energy on the good event -/

/-- The dimension-only constant of the subunit collapse. -/
def subunitCollapseConstant (d : ℕ) : ℝ :=
  2 * (longRatioGoodEventConstant d + 2)

theorem subunitCollapseConstant_pos (d : ℕ) : 0 < subunitCollapseConstant d := by
  have := longRatioGoodEventConstant_pos d
  unfold subunitCollapseConstant
  linarith

/-- The exponential envelope of the subunit branch. -/
def subunitEnvelope (s : ℝ) (m : ℕ) : ℝ :=
  6 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) * (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16)

theorem subunitEnvelope_pos (s : ℝ) (m : ℕ) : 0 < subunitEnvelope s m := by
  unfold subunitEnvelope
  positivity

/-- The saturated subunit deviation budget. -/
def subunitDeviation (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  min 1 (longRatioGradientTail m omega +
    supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) +
    _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1))

/-- **The subunit ratio energy on the good event.**  This is the manuscript's
`e.direct.J.bound.subunit` integrand, collapsed by the long-ratio, full-block,
and deterministic drift budgets. -/
theorem ratioEnergy_le_of_mem_goodEvent
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : omega ∈ goodEvent M none m 0 1 s)
    {x : Vec d} (hx : x ∈ cube d (m : ℤ)) :
    (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
          tailCoefficientCubeAverage M L m omega - 1) ^ 2 +
        (tailCoefficientCubeAverage M L m omega /
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x - 1) ^ 2 ≤
      (subunitCollapseConstant d * subunitEnvelope s m *
        subunitDeviation M m omega) ^ 2 := by
  have hmin : min m L = m := min_eq_left hmL
  have hb : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  have htail : 0 < tailCoefficient M L m omega x :=
    tailCoefficient_pos_of_ahom_pos M L m omega (by rw [hmin]; exact ahom_pos M m) x
  have hcut : 0 < _root_.SubdiffusiveProcess.Model.aCutoff M L omega x :=
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x
  -- the abstract inputs
  set A : ℝ := tailCoefficient M L m omega x /
    tailCoefficientCubeAverage M L m omega with hA
  set Ainv : ℝ := tailCoefficientCubeAverage M L m omega /
    tailCoefficient M L m omega x with hAinv
  set g : ℝ := fullShellBlock m omega x with hg
  set r : ℝ := subunitLogError M m with hr
  set S : ℝ := longRatioGradientTail m omega with hS
  set G : ℝ := supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) with hG
  set R : ℝ := _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1) with hR
  have hS0 : 0 ≤ S := longRatioGradientTail_nonneg m omega
  have hG0 : 0 ≤ G := by
    refine le_trans (abs_nonneg (fullShellBlock m omega x)) ?_
    exact abs_apply_le_supNormOn_cube_of_continuous
      (fullShellBlock_continuous m omega) hx
  have hR0 : 0 ≤ R := by
    have := M.G4.tauSq_pos
    positivity
  obtain ⟨hAbound, hAinvbound⟩ :=
    tailCoefficient_average_ratio_bounds_le_constant_mul_min_of_goodFieldOne
      M hmL zero_le_one le_rfl hsUpper omega hgood.1 hx
  have hgbound : |g| ≤ G :=
    abs_apply_le_supNormOn_cube_of_continuous
      (fullShellBlock_continuous m omega) hx
  have hrbound : |r| ≤ R := abs_subunitLogError_le M m
  have hEg : Real.exp G ≤ 6 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) :=
    exp_supNormOn_fullShellBlock_le_of_goodFieldTwo m omega hgood.2.1
      (bddAbove_goodFieldTwo_values_of_goodFieldOne m m zero_le_one hsUpper
        omega hgood.1)
  have hEr : Real.exp R ≤ (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16) := by
    refine exp_le_three_rpow hR0 ?_
    have hlogTwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ 4 * M.delta ^ 2 := by
      calc
        _root_.SubdiffusiveProcess.Model.tauSq M.P ≤
            (Real.log 2 / 2) * M.delta ^ 2 := tauSq_le_delta_sq M
        _ ≤ 4 * M.delta ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg M.delta)
    have hm1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    have h1 := mul_le_mul_of_nonneg_right htau hm1
    have h2 := mul_le_mul_of_nonneg_right hsLower hm1
    rw [hR]
    nlinarith
  have hcollapse := combined_ratio_deviation_sum_le_weighted_min
    (A := A) (Ainv := Ainv) (g := g) (r := r) (S := S) (G := G) (R := R)
    (C := longRatioGoodEventConstant d)
    (Eg := 6 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8))
    (Er := (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16))
    (longRatioGoodEventConstant_pos d).le hS0 hG0 hR0
    hAbound hAinvbound hgbound hrbound hEg hEr
  -- transport to the literal cutoff ratio
  have hforward : _root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
      tailCoefficientCubeAverage M L m omega = A * Real.exp (g + r) :=
    aCutoff_div_tailAverage_eq_ratio_mul_exp M hmL omega x
  have hreverse : tailCoefficientCubeAverage M L m omega /
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x =
      Real.exp (-(g + r)) * Ainv := by
    have hAinv_eq : Ainv = A⁻¹ := by rw [hA, hAinv, inv_div]
    have h1 : tailCoefficientCubeAverage M L m omega /
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x =
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
          tailCoefficientCubeAverage M L m omega)⁻¹ := (inv_div _ _).symm
    rw [h1, hforward, hAinv_eq, Real.exp_neg, mul_inv]
    ring
  rw [hforward, hreverse]
  have hW0 : 0 ≤ 2 * (longRatioGoodEventConstant d + 2) *
      ((6 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) *
        (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16)) * min 1 (S + G + R) := by
    have := (longRatioGoodEventConstant_pos d).le
    have hmin0 : 0 ≤ min 1 (S + G + R) := le_min zero_le_one (by linarith)
    positivity
  have hsq : (A * Real.exp (g + r) - 1) ^ 2 +
      (Real.exp (-(g + r)) * Ainv - 1) ^ 2 ≤
      (|A * Real.exp (g + r) - 1| + |Real.exp (-(g + r)) * Ainv - 1|) ^ 2 := by
    have h1 := abs_nonneg (A * Real.exp (g + r) - 1)
    have h2 := abs_nonneg (Real.exp (-(g + r)) * Ainv - 1)
    have e1 : (A * Real.exp (g + r) - 1) ^ 2 =
        |A * Real.exp (g + r) - 1| ^ 2 := (sq_abs _).symm
    have e2 : (Real.exp (-(g + r)) * Ainv - 1) ^ 2 =
        |Real.exp (-(g + r)) * Ainv - 1| ^ 2 := (sq_abs _).symm
    rw [e1, e2]
    nlinarith
  refine hsq.trans ?_
  have hgoal : subunitCollapseConstant d * subunitEnvelope s m *
      subunitDeviation M m omega =
      2 * (longRatioGoodEventConstant d + 2) *
        ((6 * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) *
          (3 : ℝ) ^ ((s * ((m : ℝ) + 1)) / 16)) * min 1 (S + G + R) := by
    unfold subunitCollapseConstant subunitEnvelope subunitDeviation
    rw [hS, hG, hR]
  rw [hgoal]
  exact pow_le_pow_left₀ (by positivity) hcollapse 2

/-! ## The direct response bound at a subunit cube -/

/-- The local probe maximum is bounded by the averaged ratio energy.  This is
the manuscript's `e.direct.J.bound.subunit`, read on the annular carrier. -/
theorem section6LocalProbeMax_le_ratioEnergy_average [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (R : TriadicCube d) :
    section6LocalProbeMax M L omega 0
        (tailCoefficientCubeAverage M L m omega) R ≤
      ENNReal.ofReal (Ch02.average (Ch02.cubeDomain (originCube d R.scale))
        (fun x =>
          (_root_.SubdiffusiveProcess.Model.aCutoff M L
              (translatePotentialSample (triadicCubeShift R) omega) x /
            tailCoefficientCubeAverage M L m omega - 1) ^ 2 +
          (tailCoefficientCubeAverage M L m omega /
            _root_.SubdiffusiveProcess.Model.aCutoff M L
              (translatePotentialSample (triadicCubeShift R) omega) x - 1) ^ 2)) := by
  set U : Ch02.Domain d := Ch02.cubeDomain (originCube d R.scale) with hU
  set omega' : _root_.SubdiffusiveProcess.Model.PotentialSample d :=
    translatePotentialSample (triadicCubeShift R) omega with homega'
  set a : Vec d → ℝ := _root_.SubdiffusiveProcess.Model.aCutoff M L omega' with ha
  have ha_pos : ∀ x, 0 < a x :=
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega'
  have hb : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  have hcontinuous : Continuous (fun x =>
      (a x / tailCoefficientCubeAverage M L m omega - 1) ^ 2 +
        (tailCoefficientCubeAverage M L m omega / a x - 1) ^ 2) :=
    ((((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega').div_const _).sub
      continuous_const).pow 2).add
      (((continuous_const.div
        (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega')
        (fun x => (ha_pos x).ne')).sub continuous_const).pow 2)
  have hint : IntegrableOn (fun x =>
      (a x / tailCoefficientCubeAverage M L m omega - 1) ^ 2 +
        (tailCoefficientCubeAverage M L m omega / a x - 1) ^ 2)
      (U : Set (Vec d)) :=
    (hcontinuous.continuousOn.integrableOn_compact
      U.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
  unfold section6LocalProbeMax
  refine iSup_le fun e => ?_
  rw [Section6Covariance.translatePotentialSample_zero]
  apply ENNReal.ofReal_le_ofReal
  exact responseJ_le_scalar_ratio_energy U (aCutoffCoeffOnData M L omega' U)
    hb ha_pos hint e e.2

/-! ## Weight arithmetic -/

private theorem three_rpow_add (a b : ℝ) :
    (3 : ℝ) ^ a * (3 : ℝ) ^ b = (3 : ℝ) ^ (a + b) :=
  (Real.rpow_add (by norm_num) a b).symm

private theorem three_rpow_sq (a : ℝ) :
    ((3 : ℝ) ^ a) ^ 2 = (3 : ℝ) ^ (2 * a) := by
  rw [pow_two, three_rpow_add]
  ring_nf

private theorem subunit_envelope_weight {s : ℝ} (hs0 : 0 ≤ s)
    (hs2 : s ≤ 1 / 2) (m : ℕ) :
    (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) * subunitEnvelope s m ^ 2 ≤
      108 * (3 : ℝ) ^ (-(s * (m : ℝ))) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have henv : subunitEnvelope s m ^ 2 =
      36 * (3 : ℝ) ^ (2 * ((s * (m : ℝ)) / 8) + 2 * ((s * ((m : ℝ) + 1)) / 16)) := by
    unfold subunitEnvelope
    rw [mul_pow, mul_pow, three_rpow_sq, three_rpow_sq, mul_assoc,
      three_rpow_add]
    norm_num
  rw [henv, ← mul_assoc, mul_comm ((3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ))) 36,
    mul_assoc, three_rpow_add]
  have hexp : -(3 * s / 2) * (m : ℝ) +
      (2 * ((s * (m : ℝ)) / 8) + 2 * ((s * ((m : ℝ) + 1)) / 16)) =
      -(s * (m : ℝ)) + s * (1 - (m : ℝ)) / 8 := by ring
  rw [hexp, ← three_rpow_add]
  have hle : s * (1 - (m : ℝ)) / 8 ≤ 1 := by nlinarith
  have hstep : (3 : ℝ) ^ (s * (1 - (m : ℝ)) / 8) ≤ 3 := by
    calc
      (3 : ℝ) ^ (s * (1 - (m : ℝ)) / 8) ≤ (3 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = 3 := Real.rpow_one 3
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(s * (m : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  nlinarith [hstep, hpos]

/-! ## The subunit slots and budget -/

/-- The full-block slot of the frozen display. -/
def goodScaleFullSlot (s : ℝ) (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) *
    supNormOn (cube d (m : ℤ)) (fullShellBlock m omega)

/-- The subunit budget: the last three slots of the frozen display. -/
def goodScaleSubunitBudget (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  324 * subunitCollapseConstant d ^ 2 *
    (goodScaleGradientSlot m omega ^ 2 +
      goodScaleFullSlot s m omega ^ 2 +
      6 * (s⁻¹ * M.delta ^ 2) ^ 2)

theorem goodScaleSubunitBudget_nonneg (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ goodScaleSubunitBudget M s m omega := by
  unfold goodScaleSubunitBudget
  have := subunitCollapseConstant_pos d
  positivity

/-! ## The subunit annular atom -/

/-- Every annular atom of nonpositive scale is bounded by the subunit budget.
This is the manuscript's `e.good.scale.subunit.tail` estimate. -/
theorem weightedLocalProbe_subunit_le_budget [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : omega ∈ goodEvent M none m 0 1 s)
    {R : TriadicCube d} {j : ℤ} (hj : j ≤ (m : ℤ)) (hscale : R.scale ≤ j - 2)
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    (hneg : R.scale ≤ 0) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ)))) *
        section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega) R ≤
      ENNReal.ofReal (goodScaleSubunitBudget M s m omega) := by
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hsLower
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set K : ℝ := (subunitCollapseConstant d * subunitEnvelope s m *
    subunitDeviation M m omega) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  -- the average of the ratio energy over the local cube
  set omega' : _root_.SubdiffusiveProcess.Model.PotentialSample d :=
    translatePotentialSample (triadicCubeShift R) omega with homega'
  have hRdesc : R ∈ descendantsAtScale (originCube d (m : ℤ)) R.scale :=
    annularCube_mem_descendantsAtScale hj hscale hann
  have hpoint : ∀ x ∈ ((Ch02.cubeDomain (originCube d R.scale) :
      Ch02.Domain d) : Set (Vec d)),
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega' x /
            tailCoefficientCubeAverage M L m omega - 1) ^ 2 +
          (tailCoefficientCubeAverage M L m omega /
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega' x - 1) ^ 2 ≤ K := by
    intro x hx
    have hxcube : x ∈ cube d R.scale := by
      simpa only [Ch02.cubeDomain_coe] using! hx
    have hxR : triadicCubeShift R + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simpa only [add_sub_cancel_left] using! hxcube
    have hxM : triadicCubeShift R + x ∈ cube d (m : ℤ) :=
      openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hRdesc) hRdesc hxR
    have hxM' : x + triadicCubeShift R ∈ cube d (m : ℤ) := by
      rwa [add_comm] at hxM
    rw [homega', Section6Covariance.aCutoff_translatePotentialSample]
    exact ratioEnergy_le_of_mem_goodEvent M hmL hsLower hsUpper omega hgood hxM'
  have haverage : Ch02.average (Ch02.cubeDomain (originCube d R.scale))
      (fun x =>
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega' x /
          tailCoefficientCubeAverage M L m omega - 1) ^ 2 +
        (tailCoefficientCubeAverage M L m omega /
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega' x - 1) ^ 2) ≤ K := by
    set U : Ch02.Domain d := Ch02.cubeDomain (originCube d R.scale) with hU
    have ha_pos : ∀ x, 0 < _root_.SubdiffusiveProcess.Model.aCutoff M L omega' x :=
      _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega'
    have hcontinuous : Continuous (fun x =>
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega' x /
          tailCoefficientCubeAverage M L m omega - 1) ^ 2 +
          (tailCoefficientCubeAverage M L m omega /
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega' x - 1) ^ 2) :=
      ((((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega').div_const _).sub
        continuous_const).pow 2).add
        (((continuous_const.div
          (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega')
          (fun x => (ha_pos x).ne')).sub continuous_const).pow 2)
    exact average_le_of_le_on U
      ((hcontinuous.continuousOn.integrableOn_compact
        U.isDomain.isBoundedDomain.isBounded.isCompact_closure).mono_set
          subset_closure) hpoint
  have hprobe : section6LocalProbeMax M L omega 0
      (tailCoefficientCubeAverage M L m omega) R ≤ ENNReal.ofReal K :=
    (section6LocalProbeMax_le_ratioEnergy_average M L m omega R).trans
      (ENNReal.ofReal_le_ofReal haverage)
  -- the weight arithmetic
  have hweight : (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) ≤
      (3 : ℝ) ^ (-(3 * s / 2) * (m : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hkr : ((R.scale : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hneg
    nlinarith
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hfinal : (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) * K ≤
      goodScaleSubunitBudget M s m omega := by
    set S : ℝ := longRatioGradientTail m omega with hS
    set G : ℝ := supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) with hG
    set Rho : ℝ := _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1) with hRho
    have hC0 : 0 ≤ subunitCollapseConstant d := (subunitCollapseConstant_pos d).le
    have henv := subunit_envelope_weight (s := s) hs0.le hsUpper m
    have hsplit : subunitDeviation M m omega ^ 2 ≤ 3 * (S ^ 2 + G ^ 2 + Rho ^ 2) := by
      rw [subunitDeviation, ← hS, ← hG, ← hRho]
      exact min_one_add_three_sq_le_three_sum_sq S G Rho
    have hdecay0 : (0 : ℝ) < (3 : ℝ) ^ (-(s * (m : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hstep1 : (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) * K ≤
        subunitCollapseConstant d ^ 2 * (108 * (3 : ℝ) ^ (-(s * (m : ℝ)))) *
          subunitDeviation M m omega ^ 2 := by
      have hKexp : K = subunitCollapseConstant d ^ 2 * subunitEnvelope s m ^ 2 *
          subunitDeviation M m omega ^ 2 := by rw [hK]; ring
      rw [hKexp]
      have h1 : (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) *
          (subunitCollapseConstant d ^ 2 * subunitEnvelope s m ^ 2 *
            subunitDeviation M m omega ^ 2) =
          subunitCollapseConstant d ^ 2 *
            ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) *
              subunitEnvelope s m ^ 2) * subunitDeviation M m omega ^ 2 := by ring
      rw [h1]
      have henv0 : (0 : ℝ) ≤ subunitEnvelope s m ^ 2 := sq_nonneg _
      have hchain : (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) *
          subunitEnvelope s m ^ 2 ≤ 108 * (3 : ℝ) ^ (-(s * (m : ℝ))) :=
        le_trans (mul_le_mul_of_nonneg_right hweight henv0) henv
      have hD2 : (0 : ℝ) ≤ subunitDeviation M m omega ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hchain (sq_nonneg _)) hD2
    -- the three slot comparisons
    have hone : (3 : ℝ) ^ (-(s * (m : ℝ))) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : 0 ≤ s * (m : ℝ) := mul_nonneg hs0.le hm0
      linarith
    have hgrad : (3 : ℝ) ^ (-(s * (m : ℝ))) * S ^ 2 ≤
        goodScaleGradientSlot m omega ^ 2 := by
      have hslot : goodScaleGradientSlot m omega = S := by
        rw [hS]
        exact goodScaleGradientSlot_eq_longRatioGradientTail m omega
      rw [hslot]
      calc
        (3 : ℝ) ^ (-(s * (m : ℝ))) * S ^ 2 ≤ 1 * S ^ 2 :=
          mul_le_mul_of_nonneg_right hone (sq_nonneg S)
        _ = S ^ 2 := one_mul _
    have hfull : (3 : ℝ) ^ (-(s * (m : ℝ))) * G ^ 2 ≤
        goodScaleFullSlot s m omega ^ 2 := by
      have hslot : goodScaleFullSlot s m omega ^ 2 =
          (3 : ℝ) ^ (2 * (-(s / 8) * (m : ℝ))) * G ^ 2 := by
        rw [goodScaleFullSlot, mul_pow, three_rpow_sq, ← hG]
      rw [hslot]
      have hexp : -(s * (m : ℝ)) ≤ 2 * (-(s / 8) * (m : ℝ)) := by nlinarith
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp)
        (sq_nonneg G)
    have hdrift : (3 : ℝ) ^ (-(s * (m : ℝ))) * Rho ^ 2 ≤
        6 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
      have hcore := three_rpow_neg_mul_tauSq_sq_le M hsLower
        (t := (m : ℝ) + 1) (by positivity)
      have hshift : (3 : ℝ) ^ (-(s * (m : ℝ))) ≤
          3 * (3 : ℝ) ^ (-(s * ((m : ℝ) + 1))) := by
        have : (3 : ℝ) ^ (-(s * (m : ℝ))) =
            (3 : ℝ) ^ s * (3 : ℝ) ^ (-(s * ((m : ℝ) + 1))) := by
          rw [three_rpow_add]
          congr 1
          ring
        rw [this]
        have hs3 : (3 : ℝ) ^ s ≤ 3 := by
          calc
            (3 : ℝ) ^ s ≤ (3 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 3 := Real.rpow_one 3
        have hp : (0 : ℝ) < (3 : ℝ) ^ (-(s * ((m : ℝ) + 1))) :=
          Real.rpow_pos_of_pos (by norm_num) _
        nlinarith
      have hRho2 : Rho ^ 2 = (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1)) ^ 2 := by
        rw [hRho]
      have hsq0 : (0 : ℝ) ≤ Rho ^ 2 := sq_nonneg _
      calc
        (3 : ℝ) ^ (-(s * (m : ℝ))) * Rho ^ 2 ≤
            3 * (3 : ℝ) ^ (-(s * ((m : ℝ) + 1))) * Rho ^ 2 := by
          exact mul_le_mul_of_nonneg_right hshift hsq0
        _ = 3 * ((3 : ℝ) ^ (-(s * ((m : ℝ) + 1))) *
            (_root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) + 1)) ^ 2) := by
          rw [hRho2]; ring
        _ ≤ 3 * (2 * (s⁻¹) ^ 2 * M.delta ^ 4) := by
          exact mul_le_mul_of_nonneg_left hcore (by norm_num)
        _ = 6 * (s⁻¹ * M.delta ^ 2) ^ 2 := by ring
    refine hstep1.trans ?_
    unfold goodScaleSubunitBudget
    have hexpand : subunitCollapseConstant d ^ 2 *
        (108 * (3 : ℝ) ^ (-(s * (m : ℝ)))) * subunitDeviation M m omega ^ 2 ≤
        subunitCollapseConstant d ^ 2 * (108 * (3 : ℝ) ^ (-(s * (m : ℝ)))) *
          (3 * (S ^ 2 + G ^ 2 + Rho ^ 2)) := by
      refine mul_le_mul_of_nonneg_left hsplit ?_
      have : (0 : ℝ) ≤ 108 * (3 : ℝ) ^ (-(s * (m : ℝ))) := by positivity
      positivity
    refine hexpand.trans ?_
    have hsum : (3 : ℝ) ^ (-(s * (m : ℝ))) * (S ^ 2 + G ^ 2 + Rho ^ 2) ≤
        goodScaleGradientSlot m omega ^ 2 + goodScaleFullSlot s m omega ^ 2 +
          6 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
      have hexp2 : (3 : ℝ) ^ (-(s * (m : ℝ))) * (S ^ 2 + G ^ 2 + Rho ^ 2) =
          (3 : ℝ) ^ (-(s * (m : ℝ))) * S ^ 2 +
          (3 : ℝ) ^ (-(s * (m : ℝ))) * G ^ 2 +
          (3 : ℝ) ^ (-(s * (m : ℝ))) * Rho ^ 2 := by ring
      rw [hexp2]
      exact add_le_add (add_le_add hgrad hfull) hdrift
    have hrearrange : subunitCollapseConstant d ^ 2 *
        (108 * (3 : ℝ) ^ (-(s * (m : ℝ)))) * (3 * (S ^ 2 + G ^ 2 + Rho ^ 2)) =
        324 * subunitCollapseConstant d ^ 2 *
          ((3 : ℝ) ^ (-(s * (m : ℝ))) * (S ^ 2 + G ^ 2 + Rho ^ 2)) := by ring
    rw [hrearrange]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  calc
    ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ)))) *
        section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega) R ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ)))) *
          ENNReal.ofReal K := by
      gcongr
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (R.scale : ℝ))) * K) :=
      (ENNReal.ofReal_mul hw0).symm
    _ ≤ ENNReal.ofReal (goodScaleSubunitBudget M s m omega) :=
      ENNReal.ofReal_le_ofReal hfinal

/-! ## The complete annular supremum on the good event -/



theorem annularSupTwo_le_goodScaleBudget [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : omega ∈ goodEvent M none m 0 1 s) :
    annularSupTwo s (m : ℤ)
        (section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega)) ≤
      ENNReal.ofReal (goodScalePositiveBudget M s m omega +
        goodScaleSubunitBudget M s m omega) := by
  refine iSup_le fun p => ?_
  rcases le_or_gt 0 p.1.1.scale with hscale0 | hscaleneg
  · refine (positive_annular_atom_le_budget M hmL hsLower hsUpper omega hgood
      p hscale0).trans (ENNReal.ofReal_le_ofReal ?_)
    have := goodScaleSubunitBudget_nonneg M s m omega
    linarith
  · obtain ⟨hj, hsc, hann⟩ := p.2
    refine (weightedLocalProbe_subunit_le_budget M hmL hsLower hsUpper omega
      hgood hj hsc hann hscaleneg.le).trans (ENNReal.ofReal_le_ofReal ?_)
    have := goodScalePositiveBudget_nonneg M s m omega
    linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
