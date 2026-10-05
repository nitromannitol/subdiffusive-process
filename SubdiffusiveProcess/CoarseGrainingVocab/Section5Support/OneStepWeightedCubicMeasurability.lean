module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepWeightedEnergyComparison
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section

/-!
# Measurable weighted cubic functionals on the `L²` carrier

The odd term  is
`int |grad v|^2 zeta`.  Point evaluation is unavailable on an `L²` class,
so measurability is not obtained from a jointly measurable representative.
Instead, following Superdiffusion's `CorrectorMeasurableQuartic.lean`, this
module realizes the integral as a countable limit of continuous truncated
functionals on two Hilbert `L²` classes.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-! ## Two scalar truncations -/

private def hilbertVecNormSqTrunc (n : ℕ) (v : HilbertVec d) : ℝ :=
  min ‖v‖ (n : ℝ) ^ 2

private theorem hilbertVecNormSqTrunc_zero (n : ℕ) :
    hilbertVecNormSqTrunc (d := d) n 0 = 0 := by
  simp [hilbertVecNormSqTrunc]

private theorem lipschitzWith_hilbertVecNormSqTrunc (n : ℕ) :
    LipschitzWith (2 * (n : NNReal))
      (hilbertVecNormSqTrunc (d := d) n) := by
  have hclamp : LipschitzWith 1
      (fun v : HilbertVec d ↦ min ‖v‖ (n : ℝ)) :=
    lipschitzWith_one_norm.min_const _
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  let A : ℝ := min ‖x‖ (n : ℝ)
  let B : ℝ := min ‖y‖ (n : ℝ)
  have hA0 : 0 ≤ A := le_min (norm_nonneg _) (Nat.cast_nonneg n)
  have hB0 : 0 ≤ B := le_min (norm_nonneg _) (Nat.cast_nonneg n)
  have hAn : A ≤ (n : ℝ) := min_le_right _ _
  have hBn : B ≤ (n : ℝ) := min_le_right _ _
  have hAB : |A - B| ≤ dist x y := by
    simpa [A, B, Real.dist_eq] using! hclamp.dist_le_mul x y
  have hsum : A + B ≤ 2 * (n : ℝ) := by linarith
  have hsum0 : 0 ≤ A + B := add_nonneg hA0 hB0
  change |A ^ 2 - B ^ 2| ≤ ((2 * (n : NNReal) : NNReal) : ℝ) * dist x y
  rw [show A ^ 2 - B ^ 2 = (A - B) * (A + B) by ring, abs_mul,
    abs_of_nonneg hsum0]
  push_cast
  calc
    |A - B| * (A + B) ≤ dist x y * (2 * (n : ℝ)) :=
      mul_le_mul hAB hsum hsum0 dist_nonneg
    _ = 2 * (n : ℝ) * dist x y := by ring

private def hilbertVecInnerPosTrunc (n : ℕ) (p v : HilbertVec d) : ℝ :=
  max (min (inner ℝ p v) (n : ℝ)) 0

private theorem hilbertVecInnerPosTrunc_zero (n : ℕ) (p : HilbertVec d) :
    hilbertVecInnerPosTrunc n p 0 = 0 := by
  simp [hilbertVecInnerPosTrunc]

private theorem lipschitzWith_hilbertVecInnerPosTrunc
    (n : ℕ) (p : HilbertVec d) :
    LipschitzWith ‖InnerProductSpace.toDual ℝ (HilbertVec d) p‖₊
      (hilbertVecInnerPosTrunc n p) := by
  let L : HilbertVec d →L[ℝ] ℝ :=
    InnerProductSpace.toDual ℝ (HilbertVec d) p
  have hL : LipschitzWith ‖L‖₊ L := L.lipschitzWith
  simpa only [hilbertVecInnerPosTrunc, L, InnerProductSpace.toDual_apply_apply] using!
    (hL.min_const (n : ℝ)).max_const 0

private def normSqTruncLp [IsFiniteMeasure (volumeMeasureOn U)]
    (n : ℕ) (F : HilbertVectorL2 U) : ScalarL2 U :=
  (lipschitzWith_hilbertVecNormSqTrunc (d := d) n).compLp
    (hilbertVecNormSqTrunc_zero n) F

private def innerPosTruncLp [IsFiniteMeasure (volumeMeasureOn U)]
    (n : ℕ) (p : HilbertVec d) (G : HilbertVectorL2 U) : ScalarL2 U :=
  (lipschitzWith_hilbertVecInnerPosTrunc n p).compLp
    (hilbertVecInnerPosTrunc_zero n p) G

private def weightedQuadraticPosTrunc [IsFiniteMeasure (volumeMeasureOn U)]
    (n : ℕ) (p : HilbertVec d)
    (FG : HilbertVectorL2 U × HilbertVectorL2 U) : ℝ :=
  inner ℝ (normSqTruncLp n FG.1) (innerPosTruncLp n p FG.2)

private theorem continuous_weightedQuadraticPosTrunc
    [IsFiniteMeasure (volumeMeasureOn U)] (n : ℕ) (p : HilbertVec d) :
    Continuous (weightedQuadraticPosTrunc (U := U) n p) := by
  apply Continuous.inner
  · exact ((lipschitzWith_hilbertVecNormSqTrunc (d := d) n).continuous_compLp
      (hilbertVecNormSqTrunc_zero n)).comp continuous_fst
  · exact ((lipschitzWith_hilbertVecInnerPosTrunc n p).continuous_compLp
      (hilbertVecInnerPosTrunc_zero n p)).comp continuous_snd

private theorem measurable_weightedQuadraticPosTrunc
    [IsFiniteMeasure (volumeMeasureOn U)] (n : ℕ) (p : HilbertVec d) :
    Measurable (weightedQuadraticPosTrunc (U := U) n p) := by
  let : MeasureTheory.IsSeparable (volumeMeasureOn U) := inferInstance
  let : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (ScalarL2 U) :=
    MeasureTheory.Lp.SecondCountableTopology
  unfold weightedQuadraticPosTrunc normSqTruncLp innerPosTruncLp
  exact (((lipschitzWith_hilbertVecNormSqTrunc (d := d) n).continuous_compLp
      (hilbertVecNormSqTrunc_zero n)).measurable.comp measurable_fst).inner
    (((lipschitzWith_hilbertVecInnerPosTrunc n p).continuous_compLp
      (hilbertVecInnerPosTrunc_zero n p)).measurable.comp measurable_snd)

private theorem weightedQuadraticPosTrunc_eq
    [IsFiniteMeasure (volumeMeasureOn U)]
    (n : ℕ) (p : HilbertVec d)
    (F G : HilbertVectorL2 U) :
    weightedQuadraticPosTrunc (U := U) n p (F, G) =
      ∫ x, hilbertVecNormSqTrunc n (F x) *
        hilbertVecInnerPosTrunc n p (G x) ∂(volumeMeasureOn U) := by
  rw [weightedQuadraticPosTrunc, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards
    [(lipschitzWith_hilbertVecNormSqTrunc (d := d) n).coeFn_compLp
      (hilbertVecNormSqTrunc_zero n) F,
     (lipschitzWith_hilbertVecInnerPosTrunc n p).coeFn_compLp
      (hilbertVecInnerPosTrunc_zero n p) G] with x hF hG
  change inner ℝ
      (((lipschitzWith_hilbertVecNormSqTrunc (d := d) n).compLp
        (hilbertVecNormSqTrunc_zero n) F) x)
      (((lipschitzWith_hilbertVecInnerPosTrunc n p).compLp
        (hilbertVecInnerPosTrunc_zero n p) G) x) = _
  rw [hF, hG]
  simp [mul_comm]

/-! ## Positive and negative extended integrals -/

private theorem hilbertVecNormSqTrunc_nonneg (n : ℕ) (v : HilbertVec d) :
    0 ≤ hilbertVecNormSqTrunc n v := by
  exact sq_nonneg _

private theorem hilbertVecInnerPosTrunc_nonneg
    (n : ℕ) (p v : HilbertVec d) :
    0 ≤ hilbertVecInnerPosTrunc n p v :=
  le_max_right _ _

private theorem monotone_hilbertVecNormSqTrunc (v : HilbertVec d) :
    Monotone fun n : ℕ ↦ hilbertVecNormSqTrunc n v := by
  intro a b hab
  unfold hilbertVecNormSqTrunc
  exact pow_le_pow_left₀ (le_min (norm_nonneg _) (Nat.cast_nonneg a))
    (min_le_min le_rfl (by exact_mod_cast hab)) 2

private theorem monotone_hilbertVecInnerPosTrunc (p v : HilbertVec d) :
    Monotone fun n : ℕ ↦ hilbertVecInnerPosTrunc n p v := by
  intro a b hab
  unfold hilbertVecInnerPosTrunc
  exact max_le_max (min_le_min le_rfl (by exact_mod_cast hab)) le_rfl

private theorem iSup_ofReal_normSqTrunc_mul_innerPosTrunc
    (p v g : HilbertVec d) :
    ⨆ n : ℕ, ENNReal.ofReal
        (hilbertVecNormSqTrunc n v * hilbertVecInnerPosTrunc n p g) =
      ENNReal.ofReal (‖v‖ ^ 2 * max (inner ℝ p g) 0) := by
  let N : ℕ := max ⌈‖v‖⌉₊ ⌈max (inner ℝ p g) 0⌉₊
  have hvN : ‖v‖ ≤ (N : ℝ) :=
    (Nat.le_ceil ‖v‖).trans (by exact_mod_cast le_max_left ⌈‖v‖⌉₊ ⌈max (inner ℝ p g) 0⌉₊)
  have hgN : max (inner ℝ p g) 0 ≤ (N : ℝ) :=
    (Nat.le_ceil (max (inner ℝ p g) 0)).trans
      (by exact_mod_cast le_max_right ⌈‖v‖⌉₊ ⌈max (inner ℝ p g) 0⌉₊)
  refine le_antisymm (iSup_le fun n ↦ ENNReal.ofReal_le_ofReal ?_) ?_
  · apply mul_le_mul
    · exact pow_le_pow_left₀
        (le_min (norm_nonneg _) (Nat.cast_nonneg n)) (min_le_left _ _) 2
    · exact max_le_max (min_le_left _ _) le_rfl
    · exact hilbertVecInnerPosTrunc_nonneg n p g
    · positivity
  · refine le_iSup_of_le N (ENNReal.ofReal_le_ofReal ?_)
    unfold hilbertVecNormSqTrunc hilbertVecInnerPosTrunc
    rw [min_eq_left hvN]
    have hinner : min (inner ℝ p g) (N : ℝ) = inner ℝ p g := by
      apply min_eq_left
      exact le_trans (le_max_left _ 0) hgN
    rw [hinner]

private theorem measurable_weightedQuadraticPosLIntegral
    [IsFiniteMeasure (volumeMeasureOn U)] (p : HilbertVec d) :
    Measurable fun FG : HilbertVectorL2 U × HilbertVectorL2 U ↦
      ∫⁻ x, ENNReal.ofReal
        (‖(FG.1 : Vec d → HilbertVec d) x‖ ^ 2 *
          max (inner ℝ p ((FG.2 : Vec d → HilbertVec d) x)) 0)
        ∂(volumeMeasureOn U) := by
  have hmeas : ∀ n : ℕ, Measurable fun FG :
      HilbertVectorL2 U × HilbertVectorL2 U ↦
        ENNReal.ofReal (weightedQuadraticPosTrunc (U := U) n p FG) :=
    fun n ↦ (measurable_weightedQuadraticPosTrunc
      (U := U) n p).ennreal_ofReal
  have hEq : (fun FG : HilbertVectorL2 U × HilbertVectorL2 U ↦
      ∫⁻ x, ENNReal.ofReal
        (‖(FG.1 : Vec d → HilbertVec d) x‖ ^ 2 *
          max (inner ℝ p ((FG.2 : Vec d → HilbertVec d) x)) 0)
        ∂(volumeMeasureOn U)) =
      fun FG ↦ ⨆ n : ℕ,
        ENNReal.ofReal (weightedQuadraticPosTrunc (U := U) n p FG) := by
    funext FG
    have hcoeF := Lp.aestronglyMeasurable FG.1
    have hcoeG := Lp.aestronglyMeasurable FG.2
    have haem : ∀ n : ℕ, AEMeasurable (fun x ↦ ENNReal.ofReal
        (hilbertVecNormSqTrunc n (FG.1 x) *
          hilbertVecInnerPosTrunc n p (FG.2 x))) (volumeMeasureOn U) := by
      intro n
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        (((lipschitzWith_hilbertVecNormSqTrunc (d := d) n).continuous
          |>.comp_aestronglyMeasurable hcoeF).mul
        ((lipschitzWith_hilbertVecInnerPosTrunc n p).continuous
          |>.comp_aestronglyMeasurable hcoeG)).aemeasurable
    have htrunc : ∀ n : ℕ,
        ENNReal.ofReal (weightedQuadraticPosTrunc (U := U) n p FG) =
          ∫⁻ x, ENNReal.ofReal
            (hilbertVecNormSqTrunc n (FG.1 x) *
              hilbertVecInnerPosTrunc n p (FG.2 x))
            ∂(volumeMeasureOn U) := by
      intro n
      rw [weightedQuadraticPosTrunc_eq]
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun x ↦ mul_nonneg
          (hilbertVecNormSqTrunc_nonneg n _) (hilbertVecInnerPosTrunc_nonneg n p _))]
      · rw [ENNReal.ofReal_toReal]
        have hconst :
            (∫⁻ _x : Vec d, ENNReal.ofReal ((n : ℝ) ^ 3)
              ∂(volumeMeasureOn U)) ≠ ∞ := by
          rw [lintegral_const]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (measure_ne_top (volumeMeasureOn U) Set.univ)
        apply ne_top_of_le_ne_top hconst
        apply lintegral_mono
        intro x
        apply ENNReal.ofReal_le_ofReal
        have h1 : hilbertVecNormSqTrunc n (FG.1 x) ≤ (n : ℝ) ^ 2 := by
            exact pow_le_pow_left₀
              (le_min (norm_nonneg _) (Nat.cast_nonneg n)) (min_le_right _ _) 2
        have h2 : hilbertVecInnerPosTrunc n p (FG.2 x) ≤ (n : ℝ) := by
          exact max_le (min_le_right _ _) (Nat.cast_nonneg n)
        calc
          hilbertVecNormSqTrunc n (FG.1 x) *
              hilbertVecInnerPosTrunc n p (FG.2 x) ≤
              (n : ℝ) ^ 2 * (n : ℝ) :=
            mul_le_mul h1 h2
              (hilbertVecInnerPosTrunc_nonneg n p _) (by positivity)
          _ = (n : ℝ) ^ 3 := by ring
      · exact (((lipschitzWith_hilbertVecNormSqTrunc (d := d) n).continuous
          |>.comp_aestronglyMeasurable hcoeF).mul
        ((lipschitzWith_hilbertVecInnerPosTrunc n p).continuous
          |>.comp_aestronglyMeasurable hcoeG))
    simp_rw [htrunc]
    rw [← lintegral_iSup' haem (Filter.Eventually.of_forall fun x ↦ by
      intro a b hab
      exact ENNReal.ofReal_le_ofReal (mul_le_mul
        (monotone_hilbertVecNormSqTrunc _ hab)
        (monotone_hilbertVecInnerPosTrunc p _ hab)
        (hilbertVecInnerPosTrunc_nonneg a p _)
        (hilbertVecNormSqTrunc_nonneg b _)))]
    exact lintegral_congr fun x ↦
      (iSup_ofReal_normSqTrunc_mul_innerPosTrunc p _ _).symm
  rw [hEq]
  exact Measurable.iSup hmeas

/-! ## The signed Bochner functional -/

/-- Positive extended part of the weighted quadratic integral. -/
def oneStepWeightedCubicPosLIntegral
    (p : HilbertVec d) (F G : HilbertVectorL2 U) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal
    (‖(F : Vec d → HilbertVec d) x‖ ^ 2 *
      max (inner ℝ p ((G : Vec d → HilbertVec d) x)) 0)
    ∂(volumeMeasureOn U)

/-- The positive extended part is Borel in both `L²` classes. -/
theorem measurable_oneStepWeightedCubicPosLIntegral
    [IsFiniteMeasure (volumeMeasureOn U)] (p : HilbertVec d) :
    Measurable fun FG : HilbertVectorL2 U × HilbertVectorL2 U ↦
      oneStepWeightedCubicPosLIntegral p FG.1 FG.2 := by
  simpa only [oneStepWeightedCubicPosLIntegral] using!
    measurable_weightedQuadraticPosLIntegral (U := U) p

/-- Pointwise integrand of the odd weighted quadratic term. -/
def oneStepWeightedCubicIntegrand
    (p : HilbertVec d) (F G : HilbertVectorL2 U) (x : Vec d) : ℝ :=
  ‖(F : Vec d → HilbertVec d) x‖ ^ 2 *
    inner ℝ p ((G : Vec d → HilbertVec d) x)

/-- Spatial integral of the odd weighted quadratic term. -/
def oneStepWeightedCubicIntegral
    (p : HilbertVec d) (F G : HilbertVectorL2 U) : ℝ :=
  ∫ x, oneStepWeightedCubicIntegrand p F G x ∂(volumeMeasureOn U)

private theorem max_mul_of_nonneg_left {a b : ℝ} (ha : 0 ≤ a) :
    max (a * b) 0 = a * max b 0 := by
  by_cases hb : 0 ≤ b
  · rw [max_eq_left (mul_nonneg ha hb), max_eq_left hb]
  · have hb' : b ≤ 0 := le_of_not_ge hb
    rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos ha hb'),
      max_eq_right hb', mul_zero]

/-- Integrable weighted cubic integrals are the difference of the two Borel
extended parts. -/
theorem oneStepWeightedCubicIntegral_eq_pos_sub_neg
    [IsFiniteMeasure (volumeMeasureOn U)]
    (p : HilbertVec d) (F G : HilbertVectorL2 U)
    (hint : Integrable (oneStepWeightedCubicIntegrand p F G)
      (volumeMeasureOn U)) :
    oneStepWeightedCubicIntegral p F G =
      (oneStepWeightedCubicPosLIntegral p F G).toReal -
        (oneStepWeightedCubicPosLIntegral (-p) F G).toReal := by
  unfold oneStepWeightedCubicIntegral
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
  congr 1
  · apply congrArg ENNReal.toReal
    unfold oneStepWeightedCubicPosLIntegral oneStepWeightedCubicIntegrand
    apply lintegral_congr
    intro x
    rw [← max_mul_of_nonneg_left (sq_nonneg _), ENNReal.ofReal_max]
    simp
  · apply congrArg ENNReal.toReal
    unfold oneStepWeightedCubicPosLIntegral oneStepWeightedCubicIntegrand
    simp only [inner_neg_left]
    apply lintegral_congr
    intro x
    rw [← max_mul_of_nonneg_left (sq_nonneg _)]
    rw [show ‖(F : Vec d → HilbertVec d) x‖ ^ 2 *
        -inner ℝ p ((G : Vec d → HilbertVec d) x) =
        -(‖(F : Vec d → HilbertVec d) x‖ ^ 2 *
          inner ℝ p ((G : Vec d → HilbertVec d) x)) by ring]
    rw [ENNReal.ofReal_max]
    simp

/-- Borel totalization of the weighted cubic integral.  On integrable inputs
it agrees with `oneStepWeightedCubicIntegral`; outside that set it retains
the positive/negative extended-part information needed for measurability and
sign reversal. -/
def oneStepWeightedCubicBorel
    (p : HilbertVec d) (F G : HilbertVectorL2 U) : ℝ :=
  (oneStepWeightedCubicPosLIntegral p F G).toReal -
    (oneStepWeightedCubicPosLIntegral (-p) F G).toReal

theorem measurable_oneStepWeightedCubicBorel
    [IsFiniteMeasure (volumeMeasureOn U)] (p : HilbertVec d) :
    Measurable fun FG : HilbertVectorL2 U × HilbertVectorL2 U ↦
      oneStepWeightedCubicBorel p FG.1 FG.2 := by
  exact ((measurable_oneStepWeightedCubicPosLIntegral (U := U) p).ennreal_toReal).sub
    ((measurable_oneStepWeightedCubicPosLIntegral (U := U) (-p)).ennreal_toReal)

theorem oneStepWeightedCubicBorel_eq_integral
    [IsFiniteMeasure (volumeMeasureOn U)]
    (p : HilbertVec d) (F G : HilbertVectorL2 U)
    (hint : Integrable (oneStepWeightedCubicIntegrand p F G)
      (volumeMeasureOn U)) :
    oneStepWeightedCubicBorel p F G = oneStepWeightedCubicIntegral p F G := by
  exact (oneStepWeightedCubicIntegral_eq_pos_sub_neg p F G hint).symm

private theorem oneStepWeightedCubicPosLIntegral_neg_neg
    (p : HilbertVec d) (F G : HilbertVectorL2 U) :
    oneStepWeightedCubicPosLIntegral p (-F) (-G) =
      oneStepWeightedCubicPosLIntegral (-p) F G := by
  unfold oneStepWeightedCubicPosLIntegral
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_neg F, Lp.coeFn_neg G] with x hF hG
  rw [hF, hG]
  simp only [Pi.neg_apply, norm_neg, inner_neg_right, inner_neg_left]

/-- Simultaneous sign reversal leaves the quadratic gradient factor fixed and
reverses the shell factor. -/
theorem oneStepWeightedCubicBorel_neg_neg
    (p : HilbertVec d) (F G : HilbertVectorL2 U) :
    oneStepWeightedCubicBorel p (-F) (-G) =
      -oneStepWeightedCubicBorel p F G := by
  unfold oneStepWeightedCubicBorel
  rw [oneStepWeightedCubicPosLIntegral_neg_neg,
    oneStepWeightedCubicPosLIntegral_neg_neg]
  simp only [neg_neg]
  ring

/-! ## Fresh-shell specializations -/

theorem oneStepLinearShellForcingL2_negate
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    oneStepLinearShellForcingL2 Q p n h (negatePotentialSequence omega) =
      -oneStepLinearShellForcingL2 Q p n h omega := by
  rw [oneStepLinearShellForcingL2, oneStepShellSumContinuousMap_negate,
    oneStepContinuousScalarForcingL2_neg]
  rfl

/-- Borel realization of the primal odd cubic on a fixed cube. -/
def oneStepLinearDirichletCubicBorel
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  oneStepWeightedCubicBorel (HilbertVec.ofVec p)
    (oneStepLinearDirichletGradient Q p n h omega)
    (oneStepLinearShellForcingL2 Q p n h omega)

theorem measurable_oneStepLinearDirichletCubicBorel
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    Measurable (oneStepLinearDirichletCubicBorel Q p n h) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let pair : _root_.SubdiffusiveProcess.Model.PotentialSample d →
      HilbertVectorL2 (openCubeSet Q) × HilbertVectorL2 (openCubeSet Q) :=
    fun omega ↦
      (oneStepLinearDirichletGradient Q p n h omega,
        oneStepLinearShellForcingL2 Q p n h omega)
  have hpair : Measurable pair :=
    (measurable_oneStepLinearDirichletGradient Q p n h).prodMk
      (measurable_oneStepLinearShellForcingL2 Q p n h)
  have hb := (measurable_oneStepWeightedCubicBorel
    (U := openCubeSet Q) (HilbertVec.ofVec p)).comp hpair
  change Measurable fun omega ↦
    oneStepWeightedCubicBorel (HilbertVec.ofVec p)
      (pair omega).1 (pair omega).2 at hb
  exact hb

theorem oneStepLinearDirichletCubicBorel_negate
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    oneStepLinearDirichletCubicBorel Q p n h
        (negatePotentialSequence omega) =
      -oneStepLinearDirichletCubicBorel Q p n h omega := by
  rw [oneStepLinearDirichletCubicBorel,
    oneStepLinearDirichletGradient_negate,
    oneStepLinearShellForcingL2_negate,
    oneStepWeightedCubicBorel_neg_neg]
  rfl

/-- The primal cubic cancels exactly under the model's shell-negation law. -/
theorem integral_oneStepLinearDirichletCubicBorel_eq_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    ∫ omega, oneStepLinearDirichletCubicBorel Q p n h omega
        ∂M.P.toMeasure = 0 := by
  exact integral_eq_zero_of_negatePotentialSequence_odd M
    (oneStepLinearDirichletCubicBorel Q p n h)
    (measurable_oneStepLinearDirichletCubicBorel Q p n h).aestronglyMeasurable
    (oneStepLinearDirichletCubicBorel_negate Q p n h)

/-- Borel realization of the dual odd cubic on a fixed cube. -/
def oneStepLinearNeumannCubicBorel
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  oneStepWeightedCubicBorel (HilbertVec.ofVec p)
    (oneStepLinearNeumannGradient Q p n h omega)
    (oneStepLinearShellForcingL2 Q p n h omega)

theorem measurable_oneStepLinearNeumannCubicBorel
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    Measurable (oneStepLinearNeumannCubicBorel Q p n h) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let pair : _root_.SubdiffusiveProcess.Model.PotentialSample d →
      HilbertVectorL2 (openCubeSet Q) × HilbertVectorL2 (openCubeSet Q) :=
    fun omega ↦
      (oneStepLinearNeumannGradient Q p n h omega,
        oneStepLinearShellForcingL2 Q p n h omega)
  have hpair : Measurable pair :=
    (measurable_oneStepLinearNeumannGradient Q p n h).prodMk
      (measurable_oneStepLinearShellForcingL2 Q p n h)
  have hb := (measurable_oneStepWeightedCubicBorel
    (U := openCubeSet Q) (HilbertVec.ofVec p)).comp hpair
  change Measurable fun omega ↦
    oneStepWeightedCubicBorel (HilbertVec.ofVec p)
      (pair omega).1 (pair omega).2 at hb
  exact hb

theorem oneStepLinearNeumannCubicBorel_negate
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    oneStepLinearNeumannCubicBorel Q p n h
        (negatePotentialSequence omega) =
      -oneStepLinearNeumannCubicBorel Q p n h omega := by
  rw [oneStepLinearNeumannCubicBorel,
    oneStepLinearNeumannGradient_negate,
    oneStepLinearShellForcingL2_negate,
    oneStepWeightedCubicBorel_neg_neg]
  rfl

/-- The dual cubic has the same exact shell-negation cancellation. -/
theorem integral_oneStepLinearNeumannCubicBorel_eq_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    ∫ omega, oneStepLinearNeumannCubicBorel Q p n h omega
        ∂M.P.toMeasure = 0 := by
  exact integral_eq_zero_of_negatePotentialSequence_odd M
    (oneStepLinearNeumannCubicBorel Q p n h)
    (measurable_oneStepLinearNeumannCubicBorel Q p n h).aestronglyMeasurable
    (oneStepLinearNeumannCubicBorel_negate Q p n h)

/-! ## Borel fourth mass on the `L²` carrier -/

private def fourthMassTrunc [IsFiniteMeasure (volumeMeasureOn U)]
    (n : ℕ) (F : HilbertVectorL2 U) : ℝ :=
  inner ℝ (normSqTruncLp n F) (normSqTruncLp n F)

private theorem measurable_fourthMassTrunc
    [IsFiniteMeasure (volumeMeasureOn U)] (n : ℕ) :
    Measurable (fourthMassTrunc (U := U) n) := by
  let : MeasureTheory.IsSeparable (volumeMeasureOn U) := inferInstance
  let : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (ScalarL2 U) :=
    MeasureTheory.Lp.SecondCountableTopology
  exact Continuous.measurable <| by
    apply Continuous.inner
    · exact (lipschitzWith_hilbertVecNormSqTrunc (d := d) n).continuous_compLp
        (hilbertVecNormSqTrunc_zero n)
    · exact (lipschitzWith_hilbertVecNormSqTrunc (d := d) n).continuous_compLp
        (hilbertVecNormSqTrunc_zero n)

private theorem fourthMassTrunc_eq_integral
    [IsFiniteMeasure (volumeMeasureOn U)]
    (n : ℕ) (F : HilbertVectorL2 U) :
    fourthMassTrunc n F =
      ∫ x, (hilbertVecNormSqTrunc n (F x)) ^ 2
        ∂(volumeMeasureOn U) := by
  rw [fourthMassTrunc, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards
    [(lipschitzWith_hilbertVecNormSqTrunc (d := d) n).coeFn_compLp
      (hilbertVecNormSqTrunc_zero n) F] with x hx
  unfold normSqTruncLp
  rw [hx]
  simp [Function.comp_apply, pow_two]



def oneStepFourthMassBorel (F : HilbertVectorL2 U) : ℝ≥0∞ :=
  ∫⁻ x, ‖(F : Vec d → HilbertVec d) x‖ₑ ^ (4 : ℝ)
    ∂(volumeMeasureOn U)

theorem measurable_oneStepFourthMassBorel
    [IsFiniteMeasure (volumeMeasureOn U)] :
    Measurable (oneStepFourthMassBorel (d := d) (U := U)) := by
  have hmeas : ∀ n : ℕ, Measurable fun F : HilbertVectorL2 U ↦
      ENNReal.ofReal (fourthMassTrunc n F) :=
    fun n ↦ (measurable_fourthMassTrunc (d := d) (U := U) n).ennreal_ofReal
  have hEq : oneStepFourthMassBorel (d := d) (U := U) =
      fun F ↦ ⨆ n : ℕ, ENNReal.ofReal (fourthMassTrunc n F) := by
    funext F
    have haem : ∀ n : ℕ, AEMeasurable (fun x ↦
        ENNReal.ofReal ((hilbertVecNormSqTrunc n (F x)) ^ 2))
        (volumeMeasureOn U) := by
      intro n
      have hstrong :=
        ((lipschitzWith_hilbertVecNormSqTrunc (d := d) n).continuous
          |>.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)).pow 2
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        hstrong.aemeasurable
    have hmono : ∀ᵐ x ∂volumeMeasureOn U, Monotone fun n : ℕ ↦
        ENNReal.ofReal ((hilbertVecNormSqTrunc n (F x)) ^ 2) := by
      filter_upwards with x
      intro a b hab
      exact ENNReal.ofReal_le_ofReal <|
        pow_le_pow_left₀ (hilbertVecNormSqTrunc_nonneg a (F x))
          (monotone_hilbertVecNormSqTrunc (F x) hab) 2
    have htrunc : ∀ n : ℕ,
        ENNReal.ofReal (fourthMassTrunc n F) =
          ∫⁻ x, ENNReal.ofReal ((hilbertVecNormSqTrunc n (F x)) ^ 2)
            ∂(volumeMeasureOn U) := by
      intro n
      rw [fourthMassTrunc_eq_integral]
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun x ↦ sq_nonneg _)]
      · rw [ENNReal.ofReal_toReal]
        have hbound : (∫⁻ _x : Vec d, ENNReal.ofReal ((n : ℝ) ^ 4)
            ∂(volumeMeasureOn U)) ≠ ∞ := by
          rw [lintegral_const]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (measure_ne_top (volumeMeasureOn U) Set.univ)
        apply ne_top_of_le_ne_top hbound
        apply lintegral_mono
        intro x
        apply ENNReal.ofReal_le_ofReal
        unfold hilbertVecNormSqTrunc
        have hmin : min ‖(F : Vec d → HilbertVec d) x‖ (n : ℝ) ≤ n :=
          min_le_right _ _
        have hmin0 : 0 ≤ min ‖(F : Vec d → HilbertVec d) x‖ (n : ℝ) :=
          le_min (norm_nonneg _) (Nat.cast_nonneg n)
        calc
          (min ‖(F : Vec d → HilbertVec d) x‖ (n : ℝ) ^ 2) ^ 2 =
              min ‖(F : Vec d → HilbertVec d) x‖ (n : ℝ) ^ 4 := by ring
          _ ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ hmin0 hmin 4
      · exact ((lipschitzWith_hilbertVecNormSqTrunc (d := d) n).continuous
          |>.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)).pow 2
    unfold oneStepFourthMassBorel
    rw [show (fun x ↦ ‖(F : Vec d → HilbertVec d) x‖ₑ ^ (4 : ℝ)) =
        fun x ↦ ⨆ n : ℕ,
          ENNReal.ofReal ((hilbertVecNormSqTrunc n (F x)) ^ 2) by
      funext x
      apply le_antisymm
      · let N := ⌈‖(F : Vec d → HilbertVec d) x‖⌉₊
        refine le_iSup_of_le N ?_
        have hN : ‖(F : Vec d → HilbertVec d) x‖ ≤ (N : ℝ) :=
          Nat.le_ceil _
        unfold hilbertVecNormSqTrunc
        rw [min_eq_left hN]
        rw [← ofReal_norm]
        have hreal : ‖(F : Vec d → HilbertVec d) x‖ ^ 4 ≤
            (‖(F : Vec d → HilbertVec d) x‖ ^ 2) ^ 2 := by
          simpa using (pow_mul ‖(F : Vec d → HilbertVec d) x‖ 2 2).le
        calc
          ENNReal.ofReal ‖(F : Vec d → HilbertVec d) x‖ ^ (4 : ℝ) =
              ENNReal.ofReal ‖(F : Vec d → HilbertVec d) x‖ ^ (4 : ℕ) := by
                norm_num [ENNReal.rpow_natCast]
          _ = ENNReal.ofReal (‖(F : Vec d → HilbertVec d) x‖ ^ 4) :=
            (ENNReal.ofReal_pow (norm_nonneg _) 4).symm
          _ ≤ ENNReal.ofReal ((‖(F : Vec d → HilbertVec d) x‖ ^ 2) ^ 2) :=
            ENNReal.ofReal_le_ofReal hreal
      · refine iSup_le fun n ↦ ?_
        rw [← ofReal_norm]
        unfold hilbertVecNormSqTrunc
        have hmin : min ‖(F : Vec d → HilbertVec d) x‖ (n : ℝ) ≤
            ‖(F : Vec d → HilbertVec d) x‖ := min_le_left _ _
        have hmin0 : 0 ≤ min ‖(F : Vec d → HilbertVec d) x‖ (n : ℝ) :=
          le_min (norm_nonneg _) (Nat.cast_nonneg n)
        have hreal :
          (min ‖(F : Vec d → HilbertVec d) x‖ (n : ℝ) ^ 2) ^ 2 =
              min ‖(F : Vec d → HilbertVec d) x‖ (n : ℝ) ^ 4 := by ring
        have hle : (min ‖(F : Vec d → HilbertVec d) x‖ (n : ℝ) ^ 2) ^ 2 ≤
            ‖(F : Vec d → HilbertVec d) x‖ ^ 4 := hreal.le.trans
          (pow_le_pow_left₀ hmin0 hmin 4)
        calc
          ENNReal.ofReal
              ((min ‖(F : Vec d → HilbertVec d) x‖ (n : ℝ) ^ 2) ^ 2) ≤
              ENNReal.ofReal (‖(F : Vec d → HilbertVec d) x‖ ^ 4) :=
            ENNReal.ofReal_le_ofReal hle
          _ = ENNReal.ofReal ‖(F : Vec d → HilbertVec d) x‖ ^ (4 : ℕ) :=
            ENNReal.ofReal_pow (norm_nonneg _) 4
          _ = ENNReal.ofReal ‖(F : Vec d → HilbertVec d) x‖ ^ (4 : ℝ) := by
            norm_num [ENNReal.rpow_natCast]]
    rw [lintegral_iSup' haem hmono]
    congr 1
    funext n
    exact (htrunc n).symm
  rw [hEq]
  exact Measurable.iSup hmeas

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
