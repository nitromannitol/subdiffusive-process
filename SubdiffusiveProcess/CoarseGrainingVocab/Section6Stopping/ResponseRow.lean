module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ResponseDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.HolderScale

@[expose] public section

/-!
# The fixed-parameter response row in the accumulated error

At the Hölder value `s₀ = 1 / 32`, the response part of the accumulated
error is reduced to a capped square root of the local annular response score.
The cap is important: below the headline moment cutoff the square root turns
the response moment into Gamma-two growth, while above it boundedness supplies
the remaining moments.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Half of the fixed Hölder stopping exponent. -/
def holderResponseScoreS : ℝ := holderStoppingS / 2

theorem holderResponseScoreS_pos : 0 < holderResponseScoreS := by
  norm_num [holderResponseScoreS, holderStoppingS]

theorem holderResponseScoreS_le_one : holderResponseScoreS ≤ 1 := by
  norm_num [holderResponseScoreS, holderStoppingS]

/-- A dimension-independent cap for the fixed-parameter response score.
It is deliberately generous; only positivity and finiteness are used. -/
def holderResponseScoreCap : ℝ := 512

theorem holderResponseScoreCap_pos : 0 < holderResponseScoreCap := by
  norm_num [holderResponseScoreCap]

/-! ## Completing a bounded low-moment estimate -/

/-- A bounded nonnegative observable needs moment estimates only up to one
finite exponent in order to have Gamma-two tails.  Above that exponent the
pointwise cap supplies the moment bound. -/
theorem isBigOWith_gammaTwo_of_bounded_low_moment_growth
    {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {Y : Omega → ℝ} {A B p0 : ℝ}
    (hA : 0 < A) (hYmeas : Measurable Y)
    (hYnonneg : ∀ omega, 0 ≤ Y omega) (hYbound : ∀ omega, Y omega ≤ B)
    (hcap : B ≤ A * Real.sqrt p0)
    (hlow : ∀ {p : ℝ}, 1 ≤ p → p ≤ p0 →
      Integrable (fun omega ↦ Y omega ^ p) P ∧
        ∫ omega, Y omega ^ p ∂P ≤ (A * Real.sqrt p) ^ p) :
    Homogenization.IndependentSums.IsBigOWith P
      (Homogenization.IndependentSums.gammaSigma 2) Y (Real.exp 1 * A) := by
  apply Homogenization.IndependentSums.isBigOWith_gammaSigma_of_moment_growth
    (μ := P) (Y := Y) (M := A) (σ := 2) (by norm_num) hA hYnonneg
  intro p hp
  by_cases hpp0 : p ≤ p0
  · simpa only [Real.sqrt_eq_rpow, one_div] using! hlow hp hpp0
  · have hp0p : p0 ≤ p := le_of_not_ge hpp0
    have hsqrt : Real.sqrt p0 ≤ Real.sqrt p :=
      Real.sqrt_le_sqrt hp0p
    have hbase : ∀ omega, Y omega ≤ A * Real.sqrt p := by
      intro omega
      exact (hYbound omega).trans
        (hcap.trans (mul_le_mul_of_nonneg_left hsqrt hA.le))
    have hpow : ∀ omega, Y omega ^ p ≤ (A * Real.sqrt p) ^ p := by
      intro omega
      exact Real.rpow_le_rpow (hYnonneg omega) (hbase omega)
        (zero_lt_one.trans_le hp).le
    have hmeasPow : Measurable (fun omega ↦ Y omega ^ p) :=
      hYmeas.pow measurable_const
    have hint : Integrable (fun omega ↦ Y omega ^ p) P := by
      apply Integrable.of_bound hmeasPow.aestronglyMeasurable
        ((A * Real.sqrt p) ^ p)
      filter_upwards [] with omega
      rw [Real.norm_eq_abs, abs_of_nonneg
        (Real.rpow_nonneg (hYnonneg omega) p)]
      exact hpow omega
    refine ⟨hint, ?_⟩
    calc
      ∫ omega, Y omega ^ p ∂P ≤
          ∫ _omega : Omega, (A * Real.sqrt p) ^ p ∂P :=
        integral_mono hint (integrable_const _) (hpow)
      _ = (A * Real.sqrt p) ^ p := by simp
      _ = (A * p ^ (2 : ℝ)⁻¹) ^ p := by
        rw [Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]

/-- The local response score at the fixed parameters used by the stopping
argument. -/
noncomputable def holderResponseScore {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) : Sample d → ℝ :=
  fun omega ↦
    (localResponseScore M holderResponseScoreS 1 1 j omega).toReal

/-- Its capped square-root readout. -/
noncomputable def holderResponseRow {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) : Sample d → ℝ :=
  fun omega ↦ Real.sqrt (min (holderResponseScore M j omega) holderResponseScoreCap)

theorem holderResponseRow_nonneg {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (omega : Sample d) :
    0 ≤ holderResponseRow M j omega :=
  Real.sqrt_nonneg _

theorem holderResponseRow_le_sqrt_cap {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (omega : Sample d) :
    holderResponseRow M j omega ≤ Real.sqrt holderResponseScoreCap := by
  unfold holderResponseRow
  exact Real.sqrt_le_sqrt (min_le_right _ _)

theorem measurable_holderResponseScore {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) :
    Measurable (holderResponseScore M j) := by
  unfold holderResponseScore
  exact ENNReal.measurable_toReal.comp
    ((measurable_localResponseScore M holderResponseScoreS 1 1 j).mono
      (aCutoffPotentialLocalSigma_le_borel _) le_rfl)

theorem measurable_holderResponseRow {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) :
    Measurable (holderResponseRow M j) := by
  unfold holderResponseRow
  exact Real.continuous_sqrt.measurable.comp
    ((measurable_holderResponseScore M j).min measurable_const)

/-- The capped annular mass whose square root is the literal response-row
majorant after the finite-quarter-net comparison. -/
noncomputable def holderResponseTruncatedMass {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) : Sample d → ℝ≥0∞ :=
  fun omega ↦ ∑ n ∈ Finset.range (j - 1),
    ENNReal.ofReal
        ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
      min (localResponseScaleAtom M j n omega) 1

theorem measurable_holderResponseTruncatedMass {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) :
    Measurable (holderResponseTruncatedMass M j) := by
  unfold holderResponseTruncatedMass
  apply Finset.measurable_sum
  intro n _hn
  exact measurable_const.mul
    (((measurable_localResponseScaleAtom M j n).mono
      (aCutoffPotentialLocalSigma_le_borel _) le_rfl).min measurable_const)

theorem holderResponseTruncatedMass_ne_top {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (omega : Sample d) :
    holderResponseTruncatedMass M j omega ≠ ∞ := by
  unfold holderResponseTruncatedMass
  rw [ENNReal.sum_ne_top]
  intro n _hn
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_of_lt ((min_le_right _ _).trans_lt ENNReal.one_lt_top))

theorem holderResponseTruncatedMass_le_localScore
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (omega : Sample d) :
    holderResponseTruncatedMass M j omega ≤
      localResponseScore M holderResponseScoreS 1 1 j omega := by
  let S : ℝ≥0∞ := ∑ n ∈ Finset.range (j - 1),
    ENNReal.ofReal
        ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
      localResponseScaleAtom M j n omega
  have hmass : holderResponseTruncatedMass M j omega ≤ S := by
    unfold holderResponseTruncatedMass S
    apply Finset.sum_le_sum
    intro n _hn
    exact mul_le_mul_right (min_le_left _ _) _
  have hcoef : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (2 * holderResponseScoreS⁻¹) := by
    rw [ENNReal.one_le_ofReal]
    norm_num [holderResponseScoreS, holderStoppingS]
  calc
    holderResponseTruncatedMass M j omega ≤ S := hmass
    _ = 1 * S := by rw [one_mul]
    _ ≤ ENNReal.ofReal (2 * holderResponseScoreS⁻¹) * S := by
      gcongr
    _ = localResponseScore M holderResponseScoreS 1 1 j omega := by
      unfold localResponseScore S
      norm_num

theorem holderResponseTruncatedMass_toReal_le_score {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (omega : Sample d) :
    (holderResponseTruncatedMass M j omega).toReal ≤
      holderResponseScore M j omega := by
  unfold holderResponseScore
  exact ENNReal.toReal_mono
    (localResponseScore_ne_top M holderResponseScoreS 1 1 j omega)
    (holderResponseTruncatedMass_le_localScore M j omega)

theorem holderResponse_weight_sum_le_cap (j : ℕ) :
    ∑ n ∈ Finset.range (j - 1),
        (3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ))) ≤
      holderResponseScoreCap := by
  have hsummable := SubdiffusiveProcess.Concentration.summable_wt_half
    holderStoppingS_pos (by norm_num [holderStoppingS]) (j : ℤ)
  have hfinite := hsummable.sum_le_tsum
    (s := (Finset.range (j - 1)).map ⟨Int.ofNat, Int.ofNat_injective⟩)
    (fun q _ ↦ SubdiffusiveProcess.Concentration.wt_nonneg holderResponseScoreS (j : ℤ) q)
  have hsum :
      ∑ n ∈ Finset.range (j - 1),
          (3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ))) ≤
        ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt holderResponseScoreS (j : ℤ) q := by
    rw [Finset.sum_map] at hfinite
    apply (Finset.sum_le_sum fun n hn ↦ ?_).trans hfinite
    have hnj : n ≤ j := by
      have : n < j - 1 := Finset.mem_range.mp hn
      omega
    simp only [Function.Embedding.coeFn_mk, SubdiffusiveProcess.Concentration.wt,
      SubdiffusiveProcess.Concentration.idist_eq]
    have habs : ((j : ℤ) - Int.ofNat n).natAbs = j - n := by
      simpa only [Int.ofNat_eq_natCast] using!
        Int.natAbs_natCast_sub_natCast_of_ge hnj
    rw [habs, Nat.cast_sub hnj]
    apply le_of_eq
    congr 2
    ring
  calc
    _ ≤ ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt holderResponseScoreS (j : ℤ) q := hsum
    _ ≤ 4 / holderStoppingS :=
      SubdiffusiveProcess.Concentration.sum_wt_half_le holderStoppingS_pos
        (by norm_num [holderStoppingS]) (j : ℤ)
    _ ≤ holderResponseScoreCap := by
      norm_num [holderStoppingS, holderResponseScoreCap]

theorem holderResponseTruncatedMass_toReal_le_cap {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (omega : Sample d) :
    (holderResponseTruncatedMass M j omega).toReal ≤ holderResponseScoreCap := by
  have hmass : holderResponseTruncatedMass M j omega ≤
      ENNReal.ofReal holderResponseScoreCap := by
    unfold holderResponseTruncatedMass
    calc
      ∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^
                (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
            min (localResponseScaleAtom M j n omega) 1 ≤
          ∑ n ∈ Finset.range (j - 1),
            ENNReal.ofReal
              ((3 : ℝ) ^
                (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) := by
        apply Finset.sum_le_sum
        intro n _hn
        simpa only [mul_one] using!
          mul_le_mul_right (min_le_right (localResponseScaleAtom M j n omega) 1)
            (ENNReal.ofReal
              ((3 : ℝ) ^
                (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))))
      _ = ENNReal.ofReal
          (∑ n ∈ Finset.range (j - 1),
            (3 : ℝ) ^
              (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro n _hn
        positivity
      _ ≤ ENNReal.ofReal holderResponseScoreCap :=
        ENNReal.ofReal_le_ofReal (holderResponse_weight_sum_le_cap j)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  simpa only [ENNReal.toReal_ofReal holderResponseScoreCap_pos.le] using! hreal

theorem sqrt_holderResponseTruncatedMass_le_row {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (omega : Sample d) :
    Real.sqrt (holderResponseTruncatedMass M j omega).toReal ≤
      holderResponseRow M j omega := by
  unfold holderResponseRow
  apply Real.sqrt_le_sqrt
  exact le_min (holderResponseTruncatedMass_toReal_le_score M j omega)
    (holderResponseTruncatedMass_toReal_le_cap M j omega)

/-- Every weighted annular atom is a summand of its capped response row. -/
theorem holderResponseAtom_le_row {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {j l : ℕ}
    (hlj : l + 2 ≤ j) (omega : Sample d) :
    (3 : ℝ) ^ (-(holderStoppingS / 4) * ((j : ℝ) - (l : ℝ))) *
        Real.sqrt (min (localResponseScaleAtom M j l omega).toReal 1) ≤
      holderResponseRow M j omega := by
  let T : ℝ≥0∞ :=
    ENNReal.ofReal
        ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (l : ℝ)))) *
      min (localResponseScaleAtom M j l omega) 1
  have hlmem : l ∈ Finset.range (j - 1) := by
    rw [Finset.mem_range]
    omega
  have hT : T ≤ holderResponseTruncatedMass M j omega := by
    unfold T holderResponseTruncatedMass
    simpa only using! Finset.single_le_sum
      (f := fun n : ℕ =>
        ENNReal.ofReal ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
          min (localResponseScaleAtom M j n omega) 1)
      (fun _ _ ↦ (show (0 : ℝ≥0∞) ≤ _ from bot_le)) hlmem
  have hreal : T.toReal ≤ (holderResponseTruncatedMass M j omega).toReal :=
    ENNReal.toReal_mono (holderResponseTruncatedMass_ne_top M j omega) hT
  have hsqrt := Real.sqrt_le_sqrt hreal
  have hatomTop : localResponseScaleAtom M j l omega ≠ ∞ :=
    localResponseScaleAtom_ne_top M j l omega
  have hweight : 0 ≤
      (3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (l : ℝ))) := by
    positivity
  have hsqrtWeight : Real.sqrt
        ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (l : ℝ)))) =
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((j : ℝ) - (l : ℝ))) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 3)]
    have hexp :
        (-holderResponseScoreS * ((j : ℝ) - (l : ℝ))) * (1 / 2 : ℝ) =
          -(holderStoppingS / 4) * ((j : ℝ) - (l : ℝ)) := by
      unfold holderResponseScoreS
      ring
    rw [hexp]
  have hTreal : Real.sqrt T.toReal =
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((j : ℝ) - (l : ℝ))) *
        Real.sqrt (min (localResponseScaleAtom M j l omega).toReal 1) := by
    change Real.sqrt
      ((ENNReal.ofReal
          ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (l : ℝ)))) *
        min (localResponseScaleAtom M j l omega) 1).toReal) = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hweight,
      ENNReal.toReal_min hatomTop (by norm_num), ENNReal.toReal_one,
      Real.sqrt_mul hweight, hsqrtWeight]
  rw [← hTreal]
  exact hsqrt.trans (sqrt_holderResponseTruncatedMass_le_row M j omega)

/-! ## Centering a nonnegative Gamma-two row -/

/-- Subtracting a nonnegative constant from a nonnegative one-sided
Gamma-two variable costs only the constant in the scale.  The proof is the
direct tail inclusion and avoids an unnecessary second moment argument. -/
theorem isBigO_gammaTwo_sub_const_of_isBigOWith_nonneg
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {X : Omega → ℝ} {A c : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hX0 : ∀ omega, 0 ≤ X omega)
    (hX : Homogenization.IndependentSums.IsBigOWith mu
      (Homogenization.IndependentSums.gammaSigma 2) X A) :
    Homogenization.IndependentSums.IsBigO mu
      (Homogenization.IndependentSums.gammaSigma 2)
      (fun omega => X omega - c) (A + c) := by
  intro t ht
  refine (measureReal_mono ?_).trans (hX ht)
  intro omega homega
  change (A + c) * t < |X omega - c| at homega
  change A * t < X omega
  by_cases hcx : c ≤ X omega
  · rw [abs_of_nonneg (sub_nonneg.mpr hcx)] at homega
    nlinarith [mul_le_mul_of_nonneg_left ht hc]
  · have hxc : X omega ≤ c := le_of_not_ge hcx
    rw [abs_of_nonpos (sub_nonpos.mpr hxc)] at homega
    have hmul := mul_le_mul_of_nonneg_left ht (add_nonneg hA hc)
    have hscale : A + c ≤ (A + c) * t := by simpa using! hmul
    have hcscale : c ≤ (A + c) * t := (show c ≤ A + c by linarith).trans hscale
    nlinarith [hX0 omega]

/-- A measurable nonnegative Gamma-two row is integrable and its expectation
is bounded by the universal Gamma moment constant. -/
theorem integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {X : Omega → ℝ} {A : ℝ}
    (hA : 0 < A) (hXm : Measurable X) (hX0 : ∀ omega, 0 ≤ X omega)
    (hX : Homogenization.IndependentSums.IsBigOWith mu
      (Homogenization.IndependentSums.gammaSigma 2) X A) :
    Integrable X mu ∧ 0 ≤ ∫ omega, X omega ∂mu ∧
      ∫ omega, X omega ∂mu ≤
        Homogenization.IndependentSums.gammaMomentConst 2 * A := by
  have hintPow :=
    Homogenization.IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
    (μ := mu) (Y := X) (K := A) (σ := 2) (p := 1)
    (by norm_num) hA (by norm_num) hX0 hXm.aemeasurable hX
  have hint : Integrable X mu := by
    simpa only [Real.rpow_one] using! hintPow
  have hmean0 : 0 ≤ ∫ omega, X omega ∂mu :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall hX0)
  have hmoment :=
    Homogenization.IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma
    (μ := mu) (Y := X) (K := A) (σ := 2) (p := 1)
    (by norm_num) hA (by norm_num) hX0 hXm.aemeasurable hX
  refine ⟨hint, hmean0, ?_⟩
  norm_num at hmoment
  simpa only [Real.rpow_one] using! hmoment

/-- Centered fixed response rows retain a uniform Gamma-two scale. -/
theorem isBigO_holderResponseRow_sub_integral
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) {A : ℝ}
    (hA : 0 < A)
    (hrow : Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2)
      (holderResponseRow M j) A) :
    Homogenization.IndependentSums.IsBigO M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2)
      (fun omega => holderResponseRow M j omega -
        ∫ eta, holderResponseRow M j eta ∂M.P.toMeasure)
      ((1 + Homogenization.IndependentSums.gammaMomentConst 2) * A) := by
  obtain ⟨_hint, hmean0, hmean⟩ :=
    integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo hA
      (measurable_holderResponseRow M j)
      (holderResponseRow_nonneg M j) hrow
  have hcenter := isBigO_gammaTwo_sub_const_of_isBigOWith_nonneg
    hA.le hmean0 (holderResponseRow_nonneg M j) hrow
  refine hcenter.mono_scale ?_
  nlinarith

/-! ## Literal annular response carrier -/

/-- Pointwise form of the annular quarter-net comparison on the single
common event furnished by `ae_forall_section6Response_le_two_mul_localNet`. -/
theorem sSup_section6Response_le_two_mul_localResponseScaleAtom_toReal_of_localNet
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (omega : Sample d)
    (hall : ∀ n : ℕ, ∀ R : TriadicCube d,
      R.scale = (n : ℤ) → ∀ e : Vec d, vecNormSq e = 1 →
        ENNReal.ofReal
            (section6Response M n n omega (triadicCubeShift R) e) ≤
          2 * localNormalizedResponseQuarterNetMax M n R omega)
    (j l : ℕ) (hlj : l + 2 ≤ j) (z : Vec d)
    (hzgrid : OnTriadicGrid l z)
    (hzann : z ∈ cube d j \ cube d (j - 1)) :
    sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        t = section6Response M l l omega z e} ≤
      2 * (localResponseScaleAtom M j l omega).toReal := by
  have hzparent : z ∈ cubeSet (originCube d (j : ℤ)) :=
    openCubeSet_subset_cubeSet _ hzann.1
  have hcover := cubeSet_subset_iUnion_descendantsAtScale
    (originCube d (j : ℤ))
    (show (l : ℤ) ≤ (originCube d (j : ℤ)).scale by
      change (l : ℤ) ≤ (j : ℤ)
      exact_mod_cast (show l ≤ j by omega)) hzparent
  obtain ⟨R, hR, hzR⟩ := Set.mem_iUnion₂.1 hcover
  have hscale : R.scale = (l : ℤ) := scale_eq_of_mem_descendantsAtScale hR
  have hshift : triadicCubeShift R = z :=
    triadicCubeShift_eq_of_onTriadicGrid_of_mem_cubeSet hscale hzgrid hzR
  have hannR : triadicCubeShift R ∉ cube d ((j : ℤ) - 1) := by
    rw [hshift]
    exact hzann.2
  have hnetAtom : localNormalizedResponseQuarterNetMax M l R omega ≤
      localResponseScaleAtom M j l omega := by
    unfold localResponseScaleAtom
    rw [dite_eq_left hlj]
    dsimp only [localResponseAnnulusMax]
    calc
      localNormalizedResponseQuarterNetMax M l R omega =
          (if triadicCubeShift R ∉ cube d ((j : ℤ) - 1) then
            localNormalizedResponseQuarterNetMax M l R omega else 0) := by
        rw [ite_eq_left hannR]
      _ ≤ _ := Finset.le_sup' (fun Q =>
        if triadicCubeShift Q ∉ cube d ((j : ℤ) - 1) then
          localNormalizedResponseQuarterNetMax M l Q omega else 0) hR
  let values : Set ℝ := {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
    t = section6Response M l l omega z e}
  have hnonempty : values.Nonempty := by
    let e : ScalarProbeUnitSphere d := Classical.arbitrary _
    exact ⟨section6Response M l l omega z e.1, e.1, e.2, rfl⟩
  have htop : 2 * localResponseScaleAtom M j l omega ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (localResponseScaleAtom_ne_top M j l omega)
  have hupper : ∀ t ∈ values,
      t ≤ 2 * (localResponseScaleAtom M j l omega).toReal := by
    rintro t ⟨e, he, rfl⟩
    have hENN := (hall l R hscale e he).trans
      (mul_le_mul_of_nonneg_left hnetAtom (by norm_num))
    have hreal := (ENNReal.ofReal_le_iff_le_toReal htop).mp hENN
    rw [hshift] at hreal
    simpa only [ENNReal.toReal_ofNat, ENNReal.toReal_mul,
      ENNReal.toReal_ofNat] using! hreal
  exact csSup_le hnonempty hupper

/-- The common quarter-net event controls every literal annular cell
simultaneously; no intersection over spatial points is required. -/
theorem ae_forall_sSup_section6Response_le_two_mul_localResponseScaleAtom_toReal
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ j l : ℕ, l + 2 ≤ j →
      ∀ z : Vec d, OnTriadicGrid l z →
        z ∈ cube d j \ cube d (j - 1) →
          sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
              t = section6Response M l l omega z e} ≤
            2 * (localResponseScaleAtom M j l omega).toReal := by
  filter_upwards [ae_forall_section6Response_le_two_mul_localNet M] with omega hall
  intro j l hlj z hzgrid hzann
  exact sSup_section6Response_le_two_mul_localResponseScaleAtom_toReal_of_localNet
    M omega hall j l hlj z hzgrid hzann



theorem ae_sSup_section6Response_le_two_mul_localResponseScaleAtom_toReal
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j l : ℕ)
    (hlj : l + 2 ≤ j) (z : Vec d) (hzgrid : OnTriadicGrid l z)
    (hzann : z ∈ cube d j \ cube d (j - 1)) :
    ∀ᵐ omega ∂M.P.toMeasure,
      sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
          t = section6Response M l l omega z e} ≤
        2 * (localResponseScaleAtom M j l omega).toReal := by
  filter_upwards
    [ae_forall_sSup_section6Response_le_two_mul_localResponseScaleAtom_toReal M]
      with omega hall
  exact hall j l hlj z hzgrid hzann

/-- A low moment of the uncapped local score gives the corresponding moment
of its capped square root. -/
theorem integral_holderResponseRow_rpow_le_of_score_norm
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ)
    {p R : ℝ} (hp : 2 ≤ p) (hR : 0 ≤ R)
    (hmoment :
      paperENNRealLpNorm M.P.toMeasure (p / 2)
          (localResponseScore M holderResponseScoreS 1 1 j) ≤
        ENNReal.ofReal R) :
    Integrable (fun omega ↦ holderResponseRow M j omega ^ p) M.P.toMeasure ∧
      ∫ omega, holderResponseRow M j omega ^ p ∂M.P.toMeasure ≤
        (Real.sqrt R) ^ p := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p / 2 := by linarith
  have hrowPowMeas : Measurable (fun omega ↦ holderResponseRow M j omega ^ p) :=
    (measurable_holderResponseRow M j).pow measurable_const
  have hcapPow : ∀ omega,
      holderResponseRow M j omega ^ p ≤ (Real.sqrt holderResponseScoreCap) ^ p := by
    intro omega
    exact Real.rpow_le_rpow (holderResponseRow_nonneg M j omega)
      (holderResponseRow_le_sqrt_cap M j omega) hp0.le
  have hint : Integrable
      (fun omega ↦ holderResponseRow M j omega ^ p) M.P.toMeasure := by
    apply Integrable.of_bound hrowPowMeas.aestronglyMeasurable
      ((Real.sqrt holderResponseScoreCap) ^ p)
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Real.rpow_nonneg (holderResponseRow_nonneg M j omega) p)]
    exact hcapPow omega
  refine ⟨hint, ?_⟩
  have hlinScore :
      ∫⁻ omega, (localResponseScore M holderResponseScoreS 1 1 j omega) ^
          (p / 2) ∂M.P.toMeasure ≤
        (ENNReal.ofReal R) ^ (p / 2) := by
    have hpow := ENNReal.rpow_le_rpow hmoment hq0.le
    simpa only [paperENNRealLpNorm, ← ENNReal.rpow_mul,
      inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one] using! hpow
  have hpoint : ∀ omega,
      ENNReal.ofReal (holderResponseRow M j omega ^ p) ≤
        (localResponseScore M holderResponseScoreS 1 1 j omega) ^ (p / 2) := by
    intro omega
    let X := (localResponseScore M holderResponseScoreS 1 1 j omega).toReal
    have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
    have hmin0 : 0 ≤ min X holderResponseScoreCap :=
      le_min hX0 holderResponseScoreCap_pos.le
    have hmin : min X holderResponseScoreCap ≤ X := min_le_left _ _
    have hreal : holderResponseRow M j omega ^ p ≤ X ^ (p / 2) := by
      unfold holderResponseRow holderResponseScore
      change Real.sqrt (min X holderResponseScoreCap) ^ p ≤ X ^ (p / 2)
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hmin0]
      have hexp : (1 / 2 : ℝ) * p = p / 2 := by ring
      rw [hexp]
      exact Real.rpow_le_rpow hmin0 hmin hq0.le
    calc
      ENNReal.ofReal (holderResponseRow M j omega ^ p) ≤
          ENNReal.ofReal (X ^ (p / 2)) := ENNReal.ofReal_le_ofReal hreal
      _ = (localResponseScore M holderResponseScoreS 1 1 j omega) ^
          (p / 2) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hX0 hq0.le,
          ENNReal.ofReal_toReal
            (localResponseScore_ne_top M holderResponseScoreS 1 1 j omega)]
  have hlin :
      ∫⁻ omega, ENNReal.ofReal (holderResponseRow M j omega ^ p)
          ∂M.P.toMeasure ≤
        (ENNReal.ofReal R) ^ (p / 2) :=
    (lintegral_mono hpoint).trans hlinScore
  have hofReal : ENNReal.ofReal
      (∫ omega, holderResponseRow M j omega ^ p ∂M.P.toMeasure) ≤
        ENNReal.ofReal ((Real.sqrt R) ^ p) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun omega ↦
        Real.rpow_nonneg (holderResponseRow_nonneg M j omega) p)]
    calc
      _ ≤ (ENNReal.ofReal R) ^ (p / 2) := hlin
      _ = ENNReal.ofReal ((Real.sqrt R) ^ p) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR,
          ENNReal.ofReal_rpow_of_nonneg hR hq0.le]
        congr 2
        ring
  exact (ENNReal.ofReal_le_ofReal_iff
    (Real.rpow_nonneg (Real.sqrt_nonneg R) p)).mp hofReal

/-- At the fixed Hölder exponent, the proved Section 4 headline gives a
uniform moment bound for the local response score. -/
theorem exists_holderResponseScore_norm_bound {d : ℕ} [NeZero d] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (q : ℝ),
        1 ≤ q →
        q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        2 * (d : ℝ) * holderResponseScoreS⁻¹ ≤ q →
        ∀ j : ℕ,
          paperENNRealLpNorm M.P.toMeasure q
              (localResponseScore M holderResponseScoreS 1 1 j) ≤
            ENNReal.ofReal
              (8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
                Real.log (2 + q) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hmoment⟩ :=
    exists_localResponseScore_moment_bound (d := d)
  refine ⟨c, C, hc, hC, ?_⟩
  intro M q hq hsmall hdim j
  have hraw := hmoment M q hq hsmall holderResponseScoreS 1 1 j
  have hsum := responseScore_geometric_sum_le (j := j)
    holderResponseScoreS_pos holderResponseScoreS_le_one
    (zero_lt_one.trans_le hq) hdim
  have hA0 : 0 ≤ C * q * Real.log (2 + q) * M.delta ^ 2 := by
    have hlog : 0 ≤ Real.log (2 + q) :=
      Real.log_nonneg (by linarith)
    positivity
  have hfactor :
      (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹ *
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2)) =
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
    exact (Finset.sum_mul (s := Finset.range (j - 1))
      (f := fun n ↦
        ENNReal.ofReal
            ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
          ((descendantsAtScale
            (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹)
      (ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2))).symm
  calc
    paperENNRealLpNorm M.P.toMeasure q
        (localResponseScore M holderResponseScoreS 1 1 j) ≤
      ENNReal.ofReal (2 * holderResponseScoreS⁻¹) *
        ∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹ *
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      simpa only [one_pow, inv_one, mul_one] using! hraw
    _ = ENNReal.ofReal (2 * holderResponseScoreS⁻¹) *
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-holderResponseScoreS * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      rw [hfactor]
      ring

    _ ≤ ENNReal.ofReal (2 * holderResponseScoreS⁻¹) *
        ENNReal.ofReal (4 / holderResponseScoreS) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (bot_le)) (bot_le)
    _ = ENNReal.ofReal
        (8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
          Real.log (2 + q) * M.delta ^ 2) := by
      have htInv : 0 ≤ holderResponseScoreS⁻¹ :=
        inv_nonneg.mpr holderResponseScoreS_pos.le
      have hleft : 0 ≤ 2 * holderResponseScoreS⁻¹ := by positivity
      have hright : 0 ≤ 4 / holderResponseScoreS :=
        div_nonneg (by norm_num) holderResponseScoreS_pos.le
      rw [← ENNReal.ofReal_mul hleft,
        ← ENNReal.ofReal_mul (mul_nonneg hleft hright)]
      congr 1
      field_simp [holderResponseScoreS_pos.ne']
      ring

/-! ## The fixed-row Gamma-two estimate -/

/-- A convenient dimension-only floor for the response-score moment. -/
def holderResponseMomentFloor (d : ℕ) : ℝ :=
  2 + 2 * (d : ℝ) * holderResponseScoreS⁻¹

theorem holderResponseMomentFloor_two_le (d : ℕ) :
    2 ≤ holderResponseMomentFloor d := by
  unfold holderResponseMomentFloor
  have hs : 0 ≤ holderResponseScoreS⁻¹ :=
    inv_nonneg.mpr holderResponseScoreS_pos.le
  have : 0 ≤ 2 * (d : ℝ) * holderResponseScoreS⁻¹ := by positivity
  linarith

theorem holderResponseMomentFloor_dimension (d : ℕ) :
    2 * (d : ℝ) * holderResponseScoreS⁻¹ ≤ holderResponseMomentFloor d := by
  unfold holderResponseMomentFloor
  linarith

/-- Lyapunov monotonicity in the integral carrier used by the Gamma-two
moment criterion. -/
theorem integral_nonneg_rpow_le_of_high_moment
    {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {Y : Omega → ℝ} {p q B : ℝ}
    (hYmeas : Measurable Y) (hYnonneg : ∀ omega, 0 ≤ Y omega)
    (hp : 0 < p) (hpq : p ≤ q) (hB : 0 ≤ B)
    (hqInt : Integrable (fun omega ↦ Y omega ^ q) P)
    (hq : ∫ omega, Y omega ^ q ∂P ≤ B ^ q) :
    Integrable (fun omega ↦ Y omega ^ p) P ∧
      ∫ omega, Y omega ^ p ∂P ≤ B ^ p := by
  have hqPos : 0 < q := hp.trans_le hpq
  have hqMem : MemLp Y (ENNReal.ofReal q) P := by
    rw [← integrable_norm_rpow_iff hYmeas.aestronglyMeasurable
      (ENNReal.ofReal_pos.mpr hqPos).ne' ENNReal.ofReal_ne_top]
    simpa only [ENNReal.toReal_ofReal hqPos.le, Real.norm_eq_abs,
      abs_of_nonneg (hYnonneg _)] using! hqInt
  have hpMem : MemLp Y (ENNReal.ofReal p) P :=
    hqMem.mono_exponent (ENNReal.ofReal_le_ofReal hpq)
  have hnorm : eLpNorm Y (ENNReal.ofReal p) P ≤
      eLpNorm Y (ENNReal.ofReal q) P :=
    eLpNorm_le_eLpNorm_of_exponent_le
      (ENNReal.ofReal_le_ofReal hpq)
  have hqRoot :
      (∫ omega, Y omega ^ q ∂P) ^ q⁻¹ ≤ B := by
    calc
      (∫ omega, Y omega ^ q ∂P) ^ q⁻¹ ≤
          (B ^ q) ^ q⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun omega ↦
          Real.rpow_nonneg (hYnonneg omega) q) hq
          (inv_nonneg.mpr hqPos.le)
      _ = B := by
        rw [← Real.rpow_mul hB]
        convert Real.rpow_one B using 2
        field_simp [hqPos.ne']
  have hpRoot :
      (∫ omega, Y omega ^ p ∂P) ^ p⁻¹ ≤ B := by
    rw [hpMem.eLpNorm_eq_integral_rpow_norm
        (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top,
      hqMem.eLpNorm_eq_integral_rpow_norm
        (ENNReal.ofReal_pos.mpr hqPos).ne' ENNReal.ofReal_ne_top] at hnorm
    simp only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hqPos.le,
      Real.norm_eq_abs, abs_of_nonneg (hYnonneg _)] at hnorm
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp
      (hnorm.trans (ENNReal.ofReal_le_ofReal hqRoot))
  have hpInt := hpMem.integrable_norm_rpow
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
  refine ⟨?_, ?_⟩
  · simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs,
      abs_of_nonneg (hYnonneg _)] using! hpInt
  · have hpow := Real.rpow_le_rpow
      (Real.rpow_nonneg (integral_nonneg fun omega ↦
        Real.rpow_nonneg (hYnonneg omega) p) p⁻¹)
      hpRoot hp.le
    simpa only [Real.rpow_inv_rpow
      (integral_nonneg fun omega ↦ Real.rpow_nonneg (hYnonneg omega) p)
      hp.ne'] using! hpow

/-- The dimension-only coefficient that simultaneously pays the direct
headline moments, the fixed-floor Lyapunov downgrade, and the bounded
high-moment completion. -/
noncomputable def holderResponseGammaSqConst (d : ℕ) (C : ℝ) : ℝ :=
  1 + 16 * C * (holderResponseScoreS ^ 2)⁻¹ +
    8 * C * (holderResponseScoreS ^ 2)⁻¹ * holderResponseMomentFloor d *
      Real.log (2 + holderResponseMomentFloor d) * (Real.log 2)⁻¹ +
    C * holderResponseScoreCap / 2

theorem holderResponseGammaSqConst_pos {d : ℕ} {C : ℝ} (hC : 0 < C) :
    0 < holderResponseGammaSqConst d C := by
  have hs : 0 ≤ (holderResponseScoreS ^ 2)⁻¹ := by positivity
  have hq : 0 ≤ holderResponseMomentFloor d :=
    (holderResponseMomentFloor_two_le d).trans' (by norm_num)
  have hlog : 0 ≤ Real.log (2 + holderResponseMomentFloor d) :=
    Real.log_nonneg (by linarith)
  have hlogTwo : 0 ≤ (Real.log 2)⁻¹ :=
    inv_nonneg.mpr (Real.log_pos (by norm_num)).le
  have hcap : 0 ≤ holderResponseScoreCap := holderResponseScoreCap_pos.le
  have hhigh : 0 ≤ 16 * C * (holderResponseScoreS ^ 2)⁻¹ := by positivity
  have hfloor : 0 ≤ 8 * C * (holderResponseScoreS ^ 2)⁻¹ *
      holderResponseMomentFloor d *
      Real.log (2 + holderResponseMomentFloor d) * (Real.log 2)⁻¹ := by
    positivity
  have hcapTerm : 0 ≤ C * holderResponseScoreCap / 2 := by positivity
  unfold holderResponseGammaSqConst
  linarith

/-- The Gamma-two scale of one capped response row. -/
noncomputable def holderResponseGammaScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C : ℝ) : ℝ :=
  Real.sqrt (holderResponseGammaSqConst d C) * M.delta *
    Real.sqrt |Real.log M.delta|

theorem holderResponseGammaScale_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {C : ℝ} (hC : 0 < C) :
    0 < holderResponseGammaScale M C := by
  have hsq : 0 < holderResponseGammaSqConst d C :=
    holderResponseGammaSqConst_pos hC
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  unfold holderResponseGammaScale
  exact mul_pos (mul_pos (Real.sqrt_pos.mpr hsq) M.shellPrefix.delta_pos)
    (Real.sqrt_pos.mpr (abs_pos.mpr hlogNeg.ne))

theorem log_two_le_abs_log_delta {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    Real.log 2 ≤ |Real.log M.delta| := by
  have hlogNonpos : Real.log M.delta ≤ 0 :=
    Real.log_nonpos M.shellPrefix.delta_pos.le
      (M.shellPrefix.delta_le_half.trans (by norm_num))
  have hlogLe : Real.log M.delta ≤ Real.log (1 / 2 : ℝ) :=
    Real.log_le_log M.shellPrefix.delta_pos M.shellPrefix.delta_le_half
  rw [abs_of_nonpos hlogNonpos]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
    (by norm_num : (2 : ℝ) ≠ 0)] at hlogLe
  simp only [Real.log_one, zero_sub] at hlogLe
  linarith

theorem holderResponseGammaScale_sq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {C : ℝ} (hC : 0 < C) :
    holderResponseGammaScale M C ^ 2 =
      holderResponseGammaSqConst d C * M.delta ^ 2 *
        |Real.log M.delta| := by
  have hsq : 0 ≤ holderResponseGammaSqConst d C :=
    (holderResponseGammaSqConst_pos hC).le
  have hlog : 0 ≤ |Real.log M.delta| := abs_nonneg _
  unfold holderResponseGammaScale
  rw [mul_pow, mul_pow, Real.sq_sqrt hsq, Real.sq_sqrt hlog]

theorem holderResponseGammaSqConst_high_le {d : ℕ} {C : ℝ} (hC : 0 < C) :
    16 * C * (holderResponseScoreS ^ 2)⁻¹ ≤
      holderResponseGammaSqConst d C := by
  have hs : 0 ≤ (holderResponseScoreS ^ 2)⁻¹ := by positivity
  have hq : 0 ≤ holderResponseMomentFloor d :=
    (holderResponseMomentFloor_two_le d).trans' (by norm_num)
  have hlog : 0 ≤ Real.log (2 + holderResponseMomentFloor d) :=
    Real.log_nonneg (by linarith)
  have hlogTwo : 0 ≤ (Real.log 2)⁻¹ :=
    inv_nonneg.mpr (Real.log_pos (by norm_num)).le
  have hcap : 0 ≤ holderResponseScoreCap := holderResponseScoreCap_pos.le
  have hhigh : 0 ≤ 16 * C * (holderResponseScoreS ^ 2)⁻¹ := by positivity
  have hfloor : 0 ≤ 8 * C * (holderResponseScoreS ^ 2)⁻¹ *
      holderResponseMomentFloor d *
      Real.log (2 + holderResponseMomentFloor d) * (Real.log 2)⁻¹ := by
    positivity
  have hcapTerm : 0 ≤ C * holderResponseScoreCap / 2 := by positivity
  unfold holderResponseGammaSqConst
  linarith

theorem holderResponseGammaSqConst_floor_le {d : ℕ} {C : ℝ} (hC : 0 < C) :
    8 * C * (holderResponseScoreS ^ 2)⁻¹ * holderResponseMomentFloor d *
        Real.log (2 + holderResponseMomentFloor d) * (Real.log 2)⁻¹ ≤
      holderResponseGammaSqConst d C := by
  have hs : 0 ≤ (holderResponseScoreS ^ 2)⁻¹ := by positivity
  have hq : 0 ≤ holderResponseMomentFloor d :=
    (holderResponseMomentFloor_two_le d).trans' (by norm_num)
  have hlog : 0 ≤ Real.log (2 + holderResponseMomentFloor d) :=
    Real.log_nonneg (by linarith)
  have hlogTwo : 0 ≤ (Real.log 2)⁻¹ :=
    inv_nonneg.mpr (Real.log_pos (by norm_num)).le
  have hcap : 0 ≤ holderResponseScoreCap := holderResponseScoreCap_pos.le
  have hhigh : 0 ≤ 16 * C * (holderResponseScoreS ^ 2)⁻¹ := by positivity
  have hcapTerm : 0 ≤ C * holderResponseScoreCap / 2 := by positivity
  unfold holderResponseGammaSqConst
  linarith

theorem holderResponseGammaSqConst_cap_le {d : ℕ} {C : ℝ} (hC : 0 < C) :
    C * holderResponseScoreCap / 2 ≤ holderResponseGammaSqConst d C := by
  have hs : 0 ≤ (holderResponseScoreS ^ 2)⁻¹ := by positivity
  have hq : 0 ≤ holderResponseMomentFloor d :=
    (holderResponseMomentFloor_two_le d).trans' (by norm_num)
  have hlog : 0 ≤ Real.log (2 + holderResponseMomentFloor d) :=
    Real.log_nonneg (by linarith)
  have hlogTwo : 0 ≤ (Real.log 2)⁻¹ :=
    inv_nonneg.mpr (Real.log_pos (by norm_num)).le
  have hhigh : 0 ≤ 16 * C * (holderResponseScoreS ^ 2)⁻¹ := by positivity
  have hfloor : 0 ≤ 8 * C * (holderResponseScoreS ^ 2)⁻¹ *
      holderResponseMomentFloor d *
      Real.log (2 + holderResponseMomentFloor d) * (Real.log 2)⁻¹ := by
    positivity
  unfold holderResponseGammaSqConst
  linarith

/-- One fixed capped response row has the manuscript's Gamma-two scale once
the fixed dimension-dependent floor lies inside the proved headline range. -/
theorem isBigOWith_gammaTwo_holderResponseRow_of_score_bound
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {C : ℝ} (hC : 0 < C)
    (hCL : 1 ≤ C * |Real.log M.delta|)
    (hfloor : holderResponseMomentFloor d ≤
      C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹)
    (hscore : ∀ (q : ℝ), 1 ≤ q →
      q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
      2 * (d : ℝ) * holderResponseScoreS⁻¹ ≤ q →
      ∀ j : ℕ,
        paperENNRealLpNorm M.P.toMeasure q
            (localResponseScore M holderResponseScoreS 1 1 j) ≤
          ENNReal.ofReal
            (8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
              Real.log (2 + q) * M.delta ^ 2))
    (j : ℕ) :
    Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2)
      (holderResponseRow M j)
      (Real.exp 1 * holderResponseGammaScale M C) := by
  let L : ℝ := |Real.log M.delta|
  let H : ℝ := C⁻¹ * (M.delta ^ 2)⁻¹ * L⁻¹
  let p0 : ℝ := 2 * H
  let A : ℝ := holderResponseGammaScale M C
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hL : 0 < L := by
    dsimp only [L]
    exact abs_pos.mpr (ne_of_lt (Real.log_neg hdelta
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))
  have hH : 0 < H := by dsimp only [H]; positivity
  have hp0 : 0 < p0 := by dsimp only [p0]; positivity
  have hA : 0 < A := holderResponseGammaScale_pos M hC
  have hfloorH : holderResponseMomentFloor d ≤ H := by
    simpa only [H, L] using! hfloor
  have hpFloorP0 : 2 * holderResponseMomentFloor d ≤ p0 := by
    dsimp only [p0]
    linarith
  have hHdelta : H ≤ (M.delta ^ 2)⁻¹ := by
    have hCLinv : (C * L)⁻¹ ≤ 1 :=
      (inv_le_one₀ (mul_pos hC hL)).2 hCL
    dsimp only [H]
    calc
      C⁻¹ * (M.delta ^ 2)⁻¹ * L⁻¹ =
          (C * L)⁻¹ * (M.delta ^ 2)⁻¹ := by field_simp
      _ ≤ 1 * (M.delta ^ 2)⁻¹ := by gcongr
      _ = _ := one_mul _
  have hcapSq : holderResponseScoreCap ≤ A ^ 2 * p0 := by
    have hDcap := holderResponseGammaSqConst_cap_le (d := d) hC
    have hscaleSq := holderResponseGammaScale_sq M hC
    have hcalc : A ^ 2 * p0 =
        2 * holderResponseGammaSqConst d C / C := by
      dsimp only [A, p0, H, L]
      rw [hscaleSq]
      field_simp [hC.ne', hdelta.ne',
        (abs_pos.mpr (ne_of_lt (Real.log_neg hdelta
          (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))).ne']
    rw [hcalc]
    calc
      holderResponseScoreCap = (2 / C) *
          (C * holderResponseScoreCap / 2) := by field_simp [hC.ne']
      _ ≤ (2 / C) * holderResponseGammaSqConst d C :=
        mul_le_mul_of_nonneg_left hDcap (by positivity)
      _ = 2 * holderResponseGammaSqConst d C / C := by ring
  have hcap : Real.sqrt holderResponseScoreCap ≤ A * Real.sqrt p0 := by
    have hleft0 : 0 ≤ Real.sqrt holderResponseScoreCap := Real.sqrt_nonneg _
    have hright0 : 0 ≤ A * Real.sqrt p0 :=
      mul_nonneg hA.le (Real.sqrt_nonneg _)
    rw [← sq_le_sq₀ hleft0 hright0, mul_pow,
      Real.sq_sqrt holderResponseScoreCap_pos.le, Real.sq_sqrt hp0.le]
    exact hcapSq
  apply isBigOWith_gammaTwo_of_bounded_low_moment_growth
    hA (measurable_holderResponseRow M j)
    (holderResponseRow_nonneg M j) (holderResponseRow_le_sqrt_cap M j)
    hcap
  intro p hp hpUpper
  have hpPos : 0 < p := zero_lt_one.trans_le hp
  by_cases hpLarge : 2 * holderResponseMomentFloor d ≤ p
  · let q : ℝ := p / 2
    have hqTwo : 2 ≤ q := by
      dsimp only [q]
      have := holderResponseMomentFloor_two_le d
      linarith
    have hqFloor : holderResponseMomentFloor d ≤ q := by
      dsimp only [q]
      linarith
    have hqH : q ≤ H := by
      dsimp only [q, p0] at hpUpper ⊢
      linarith
    have hqSmall : q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ *
        |Real.log M.delta|⁻¹ := by simpa only [H, L] using! hqH
    have hqDim : 2 * (d : ℝ) * holderResponseScoreS⁻¹ ≤ q :=
      (holderResponseMomentFloor_dimension d).trans hqFloor
    let R : ℝ := 8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
      Real.log (2 + q) * M.delta ^ 2
    have hR : 0 ≤ R := by
      have hlog : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
      dsimp only [R]
      positivity
    have hnorm := hscore q (by linarith) hqSmall hqDim j
    have hmoment := integral_holderResponseRow_rpow_le_of_score_norm
      (p := p) (R := R) M j (by
        linarith [holderResponseMomentFloor_two_le d]) hR (by
        simpa only [R, q] using! hnorm)
    have hqDelta : q ≤ (M.delta ^ 2)⁻¹ := hqH.trans hHdelta
    have hlog := log_two_add_le_four_abs_log hdelta
      M.shellPrefix.delta_le_half (by linarith : 0 ≤ q) hqDelta
    have hRsq : Real.sqrt R ≤ A * Real.sqrt p := by
      have hhigh := holderResponseGammaSqConst_high_le (d := d) hC
      have hscaleSq := holderResponseGammaScale_sq M hC
      have hright0 : 0 ≤ A * Real.sqrt p :=
        mul_nonneg hA.le (Real.sqrt_nonneg _)
      rw [← sq_le_sq₀ (Real.sqrt_nonneg _) hright0,
        Real.sq_sqrt hR, mul_pow, Real.sq_sqrt hpPos.le]
      rw [hscaleSq]
      dsimp only [R, A, L]
      calc
        8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
              Real.log (2 + q) * M.delta ^ 2 ≤
            8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
              (4 * |Real.log M.delta|) * M.delta ^ 2 := by
          gcongr
        _ = (16 * C * (holderResponseScoreS ^ 2)⁻¹) *
              (M.delta ^ 2 * |Real.log M.delta|) * p := by
          dsimp only [q]
          ring
        _ ≤ holderResponseGammaSqConst d C *
              (M.delta ^ 2 * |Real.log M.delta|) * p := by
          gcongr
        _ = holderResponseGammaSqConst d C * M.delta ^ 2 *
              |Real.log M.delta| * p := by ring
    refine ⟨hmoment.1, hmoment.2.trans ?_⟩
    exact Real.rpow_le_rpow (Real.sqrt_nonneg R) hRsq hpPos.le
  · have hpFloor : p ≤ 2 * holderResponseMomentFloor d := le_of_not_ge hpLarge
    let q0 : ℝ := holderResponseMomentFloor d
    let P0 : ℝ := 2 * q0
    let R0 : ℝ := 8 * C * (holderResponseScoreS ^ 2)⁻¹ * q0 *
      Real.log (2 + q0) * M.delta ^ 2
    have hq0Two : 2 ≤ q0 := holderResponseMomentFloor_two_le d
    have hq0Small : q0 ≤ C⁻¹ * (M.delta ^ 2)⁻¹ *
        |Real.log M.delta|⁻¹ := by simpa only [q0] using! hfloor
    have hq0Dim : 2 * (d : ℝ) * holderResponseScoreS⁻¹ ≤ q0 :=
      holderResponseMomentFloor_dimension d
    have hR0 : 0 ≤ R0 := by
      have hlog : 0 ≤ Real.log (2 + q0) := Real.log_nonneg (by
        have := holderResponseMomentFloor_two_le d
        dsimp only [q0]
        linarith)
      dsimp only [R0]
      positivity
    have hnorm0 := hscore q0 (by linarith) hq0Small hq0Dim j
    have hP0half : P0 / 2 = q0 := by
      dsimp only [P0]
      ring
    have hmoment0 := integral_holderResponseRow_rpow_le_of_score_norm
      (p := P0) (R := R0) M j (by
        dsimp only [P0]
        linarith) hR0 (by
          rw [hP0half]
          simpa only [R0] using! hnorm0)
    have hBscale : Real.sqrt R0 ≤ A := by
      have hfloorC := holderResponseGammaSqConst_floor_le (d := d) hC
      have hlogTwo := log_two_le_abs_log_delta M
      have hscaleSq := holderResponseGammaScale_sq M hC
      have hleft0 : 0 ≤ Real.sqrt R0 := Real.sqrt_nonneg _
      rw [← sq_le_sq₀ hleft0 hA.le, Real.sq_sqrt hR0, hscaleSq]
      dsimp only [R0, q0, A]
      have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hcoef0 : 0 ≤ 8 * C * (holderResponseScoreS ^ 2)⁻¹ *
          holderResponseMomentFloor d *
          Real.log (2 + holderResponseMomentFloor d) := by
        have hsInv : 0 ≤ (holderResponseScoreS ^ 2)⁻¹ := by positivity
        have hq0 : 0 ≤ holderResponseMomentFloor d := by linarith
        have hlog0 : 0 ≤ Real.log (2 + holderResponseMomentFloor d) :=
          Real.log_nonneg (by linarith)
        positivity
      have hcoef : 8 * C * (holderResponseScoreS ^ 2)⁻¹ *
            holderResponseMomentFloor d *
            Real.log (2 + holderResponseMomentFloor d) ≤
          holderResponseGammaSqConst d C * Real.log 2 := by
        calc
          _ = (8 * C * (holderResponseScoreS ^ 2)⁻¹ *
                holderResponseMomentFloor d *
                Real.log (2 + holderResponseMomentFloor d) *
                (Real.log 2)⁻¹) * Real.log 2 := by
              field_simp [hlogTwoPos.ne']
          _ ≤ holderResponseGammaSqConst d C * Real.log 2 :=
            mul_le_mul_of_nonneg_right hfloorC hlogTwoPos.le
      calc
        8 * C * (holderResponseScoreS ^ 2)⁻¹ *
              holderResponseMomentFloor d *
              Real.log (2 + holderResponseMomentFloor d) * M.delta ^ 2 ≤
            (holderResponseGammaSqConst d C * Real.log 2) *
              M.delta ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
        _ ≤ (holderResponseGammaSqConst d C * |Real.log M.delta|) *
              M.delta ^ 2 := by
          gcongr
          exact (holderResponseGammaSqConst_pos hC).le
        _ = holderResponseGammaSqConst d C * M.delta ^ 2 *
              |Real.log M.delta| := by ring
    have hP0 : 0 < P0 := by
      dsimp only [P0, q0]
      linarith [holderResponseMomentFloor_two_le d]
    have hdown := integral_nonneg_rpow_le_of_high_moment
      (measurable_holderResponseRow M j) (holderResponseRow_nonneg M j)
      hpPos (q := P0) (by simpa only [P0, q0] using! hpFloor)
      (Real.sqrt_nonneg R0)
      hmoment0.1 hmoment0.2
    have hsqrtp : 1 ≤ Real.sqrt p := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hp
    have hbase : Real.sqrt R0 ≤ A * Real.sqrt p :=
      hBscale.trans (by nlinarith [hA])
    refine ⟨hdown.1, hdown.2.trans ?_⟩
    exact Real.rpow_le_rpow (Real.sqrt_nonneg R0) hbase hpPos.le

/-- Uniform fixed-row Gamma-two estimate, with the proved Section 4 headline
fully consumed.  The sole displayed condition is the dimension-floor cutoff
that the eventual dimension-only smallness choice must guarantee. -/
theorem exists_isBigOWith_gammaTwo_holderResponseRow {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
        holderResponseMomentFloor d ≤
          C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ j : ℕ,
          Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 2)
            (holderResponseRow M j)
            (Real.exp 1 * holderResponseGammaScale M C) := by
  obtain ⟨_c, C0, _hc, hC0, hscore0⟩ :=
    exists_holderResponseScore_norm_bound (d := d)
  let C : ℝ := 1 + C0 + (Real.log 2)⁻¹
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC0C : C0 ≤ C := by
    dsimp only [C]
    have : 0 < (Real.log 2)⁻¹ := inv_pos.mpr hlogTwo
    linarith
  have hlogInvC : (Real.log 2)⁻¹ ≤ C := by
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro M hfloor j
  have hL : 0 < |Real.log M.delta| := by
    exact abs_pos.mpr (ne_of_lt (Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))
  have hCL : 1 ≤ C * |Real.log M.delta| := by
    calc
      1 = (Real.log 2)⁻¹ * Real.log 2 := by
        field_simp [hlogTwo.ne']
      _ ≤ C * Real.log 2 :=
        mul_le_mul_of_nonneg_right hlogInvC hlogTwo.le
      _ ≤ C * |Real.log M.delta| :=
        mul_le_mul_of_nonneg_left (log_two_le_abs_log_delta M) hC.le
  apply isBigOWith_gammaTwo_holderResponseRow_of_score_bound
    M hC hCL hfloor _ j
  intro q hq hsmall hdim k
  have hCinv : C⁻¹ ≤ C0⁻¹ := (inv_le_inv₀ hC hC0).2 hC0C
  have hfactor : 0 ≤ (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
    positivity
  have hsmall0 : q ≤ C0⁻¹ * (M.delta ^ 2)⁻¹ *
      |Real.log M.delta|⁻¹ := by
    exact hsmall.trans (by
      calc
        C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ =
            C⁻¹ * ((M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹) := by ring
        _ ≤ C0⁻¹ * ((M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹) :=
          mul_le_mul_of_nonneg_right hCinv hfactor
        _ = _ := by ring)
  have hraw := hscore0 M q hq hsmall0 hdim k
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hlog : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
  have hrest : 0 ≤ (holderResponseScoreS ^ 2)⁻¹ * q *
      Real.log (2 + q) * M.delta ^ 2 := by positivity
  exact hraw.trans (ENNReal.ofReal_le_ofReal (by
    calc
      8 * C0 * (holderResponseScoreS ^ 2)⁻¹ * q *
          Real.log (2 + q) * M.delta ^ 2 =
          (8 * C0) * ((holderResponseScoreS ^ 2)⁻¹ * q *
            Real.log (2 + q) * M.delta ^ 2) := by ring
      _ ≤ (8 * C) * ((holderResponseScoreS ^ 2)⁻¹ * q *
            Real.log (2 + q) * M.delta ^ 2) := by gcongr
      _ = 8 * C * (holderResponseScoreS ^ 2)⁻¹ * q *
          Real.log (2 + q) * M.delta ^ 2 := by ring))

theorem delta_sq_mul_abs_log_le_delta {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    M.delta ^ 2 * |Real.log M.delta| ≤ M.delta := by
  have hdelta := M.shellPrefix.delta_pos
  have hdeltaOne : M.delta ≤ 1 :=
    M.shellPrefix.delta_le_half.trans (by norm_num)
  have hlogNonpos : Real.log M.delta ≤ 0 :=
    Real.log_nonpos hdelta.le hdeltaOne
  have hinv : 0 < M.delta⁻¹ := inv_pos.mpr hdelta
  have hlogInv := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at hlogInv
  rw [abs_of_nonpos hlogNonpos]
  calc
    M.delta ^ 2 * -Real.log M.delta ≤
        M.delta ^ 2 * (M.delta⁻¹ - 1) :=
      mul_le_mul_of_nonneg_left hlogInv (sq_nonneg _)
    _ ≤ M.delta ^ 2 * M.delta⁻¹ := by
      gcongr
      linarith
    _ = M.delta := by field_simp [hdelta.ne']

/-- The response-row floor is paid by a dimension-only smallness constant. -/
theorem exists_isBigOWith_gammaTwo_holderResponseRow_of_delta_small
    {d : ℕ} [NeZero d] :
    ∃ K C : ℝ, 1 ≤ K ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ K⁻¹ →
        ∀ j : ℕ,
          Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 2)
            (holderResponseRow M j)
            (Real.exp 1 * holderResponseGammaScale M C) := by
  obtain ⟨C, hC, hrow⟩ :=
    exists_isBigOWith_gammaTwo_holderResponseRow (d := d)
  let Q : ℝ := C * holderResponseMomentFloor d
  let K : ℝ := 1 + Q
  have hfloorPos : 0 < holderResponseMomentFloor d :=
    zero_lt_two.trans_le (holderResponseMomentFloor_two_le d)
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hK : 1 ≤ K := by dsimp only [K]; linarith
  refine ⟨K, C, hK, hC, ?_⟩
  intro M hdeltaSmall j
  apply hrow M _ j
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hQK : Q ≤ K := by dsimp only [K]; linarith
  have hQdelta : Q * M.delta ≤ 1 := by
    calc
      Q * M.delta ≤ Q * K⁻¹ :=
        mul_le_mul_of_nonneg_left hdeltaSmall hQ.le
      _ ≤ K * K⁻¹ := mul_le_mul_of_nonneg_right hQK (inv_nonneg.mpr hKpos.le)
      _ = 1 := by field_simp [hKpos.ne']
  have hlogPos : 0 < |Real.log M.delta| := by
    exact abs_pos.mpr (ne_of_lt (Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))
  have hprod : C * holderResponseMomentFloor d *
      (M.delta ^ 2 * |Real.log M.delta|) ≤ 1 := by
    calc
      C * holderResponseMomentFloor d *
          (M.delta ^ 2 * |Real.log M.delta|) ≤
        C * holderResponseMomentFloor d * M.delta :=
          mul_le_mul_of_nonneg_left (delta_sq_mul_abs_log_le_delta M)
            (mul_nonneg hC.le hfloorPos.le)
      _ = Q * M.delta := by rfl
      _ ≤ 1 := hQdelta
  have hdeltaSq : 0 < M.delta ^ 2 := sq_pos_of_pos M.shellPrefix.delta_pos
  have hdenom : 0 < C * (M.delta ^ 2 * |Real.log M.delta|) :=
    mul_pos hC (mul_pos hdeltaSq hlogPos)
  rw [show C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ =
      1 / (C * (M.delta ^ 2 * |Real.log M.delta|)) by
        field_simp [hC.ne', M.shellPrefix.delta_pos.ne', hlogPos.ne']]
  rw [le_div_iff₀ hdenom]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using! hprod

/-- Extend the fixed response row to the same triangular array carrier as the
density response score. -/
noncomputable def holderResponseRowArray {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) : ℤ → ℤ → Sample d → ℝ :=
  fun k j omega ↦
    Real.sqrt (min
      (responseScoreArray M holderResponseScoreS 1 1 k j omega)
      holderResponseScoreCap)

theorem holderResponseRowArray_nonneg {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k j : ℤ) (omega : Sample d) :
    0 ≤ holderResponseRowArray M k j omega :=
  Real.sqrt_nonneg _

theorem measurable_holderResponseRowArray {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k j : ℤ) :
    Measurable (holderResponseRowArray M k j) := by
  unfold holderResponseRowArray
  exact Real.continuous_sqrt.measurable.comp
    ((measurable_responseScoreArray M holderResponseScoreS 1 1 k j).min
      measurable_const)

theorem holderResponseRowArray_diag {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) :
    holderResponseRowArray M (j : ℤ) (j : ℤ) = holderResponseRow M j := by
  funext omega
  unfold holderResponseRowArray holderResponseRow holderResponseScore
  simp only [responseScoreArray, Int.natCast_nonneg, le_rfl, and_self, ite_true,
    Int.toNat_natCast]

/-- Residue-column independence is stable under one fixed Borel transform of
every scalar array entry. -/
theorem columnsIndep_comp_entry
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (X : ℤ → ℤ → Omega → ℝ) (r : ℕ)
    (hX : SubdiffusiveProcess.Concentration.ColumnsIndep P X r)
    (f : ℝ → ℝ) (hf : Measurable f) :
    SubdiffusiveProcess.Concentration.ColumnsIndep P (fun k j omega ↦ f (X k j omega)) r := by
  intro b
  exact (hX b).comp (fun _ g k ↦ f (g k)) fun _ ↦
    Measurable.of_eval fun k ↦ hf.comp (measurable_pi_apply k)

/-- A `ColumnsIndep` certificate contains, in particular, mutual
independence of the diagonal entries in each residue class. -/
theorem columnsIndep_diag_residue
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (X : ℤ → ℤ → Omega → ℝ) (r : ℕ)
    (hX : SubdiffusiveProcess.Concentration.ColumnsIndep P X r) (b : ℤ) :
    ProbabilityTheory.iIndepFun
      (fun q : ℤ => X (q * (r : ℤ) + b) (q * (r : ℤ) + b)) P := by
  exact (hX b).comp
    (fun q f => f (q * (r : ℤ) + b))
    (fun q => measurable_pi_apply (q * (r : ℤ) + b))

/-- The capped square-root response rows retain the established finite-range
annular independence certificate. -/
theorem columnsIndep_holderResponseRowArray {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      (holderResponseRowArray M) (responseScoreRange d) := by
  let f : ℝ → ℝ := fun x ↦ Real.sqrt (min x holderResponseScoreCap)
  have hf : Measurable f := Real.continuous_sqrt.measurable.comp
    (measurable_id.min measurable_const)
  simpa only [holderResponseRowArray, f] using!
    columnsIndep_comp_entry M.P.toMeasure
      (responseScoreArray M holderResponseScoreS 1 1)
      (responseScoreRange d)
      (columnsIndep_responseScoreArray M holderResponseScoreS 1 1) f hf

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
