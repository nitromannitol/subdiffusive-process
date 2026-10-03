module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpTwoBlockMoment
public import SubdiffusiveProcess.Static.CutoffMassMomentBound

@[expose] public section

/-! # Simultaneous comparison of finite cutoffs on a subscale cube

The own-scale shell-block representative controls both coefficient ratios.
Its sharp square-root gap estimate supplies any prescribed small geometric
moment cost after reducing disorder, uniformly in both cutoffs and the centre.
-/

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization (openCubeSet originCube)
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- A finite shell-block comparison factor, including the empty block. -/
def cutoffBlockFactor {d : ℕ} (M : GMCModel d) (L k : ℕ) (z : Vec d)
    (ω : PotentialSample d) : ℝ :=
  if k < L then 1 + finiteBlockRatioRepresentative M L k z ω else 1

theorem measurable_cutoffBlockFactor {d : ℕ} (M : GMCModel d) (L k : ℕ) (z : Vec d) :
    Measurable (cutoffBlockFactor M L k z) := by
  unfold cutoffBlockFactor
  split_ifs
  · exact measurable_const.add ((measurable_finiteBlockRatioRepresentative M L k z).mono
      (potentialShellIndexSigma_le_borel _) le_rfl)
  · exact measurable_const

theorem one_le_cutoffBlockFactor {d : ℕ} (M : GMCModel d) (L k : ℕ) (z : Vec d)
    (ω : PotentialSample d) : 1 ≤ cutoffBlockFactor M L k z ω := by
  unfold cutoffBlockFactor
  split_ifs
  · exact le_add_of_nonneg_right (finiteBlockRatioRepresentative_nonneg M L k z ω)
  · exact le_rfl

/-- Both physical coefficients compare on every point of the smaller cube. -/
theorem cutoffBlockFactor_comparison {d : ℕ} (M : GMCModel d) {L k : ℕ} (hkL : k ≤ L)
    (z : Vec d) (ω : PotentialSample d) {x : Vec d}
    (hx : x - z ∈ openCubeSet (originCube d (k : ℤ))) :
    aCutoff M L ω x ≤ cutoffBlockFactor M L k z ω * aCutoff M k ω x ∧
      aCutoff M k ω x ≤ cutoffBlockFactor M L k z ω * aCutoff M L ω x := by
  rcases hkL.eq_or_lt with h | h
  · subst L
    simp only [cutoffBlockFactor, lt_self_iff_false, ↓reduceIte, one_mul, le_refl, and_self]
  · have hf := abs_cutoffRatioMinusOne_le_finiteBlockRatioRepresentative M h z ω hx
    have hi := abs_inverseCutoffRatioMinusOne_le_finiteBlockRatioRepresentative M h z ω hx
    simp [cutoffRatioMinusOne, inverseCutoffRatioMinusOne, aCutoffAtInt,
      show ¬ (k : ℤ) < 0 from not_lt.mpr (Int.natCast_nonneg k)] at hf hi
    have hf' := (le_abs_self _).trans hf
    have hi' := (le_abs_self _).trans hi
    simp only [cutoffBlockFactor, h, ↓reduceIte]
    constructor
    · exact (div_le_iff₀ (aCutoff_pos M k ω x)).mp (by linarith)
    · exact (div_le_iff₀ (aCutoff_pos M L ω x)).mp (by linarith)

/-- Conversion of the manuscript's nonnegative carrier to a real `Lᵖ` norm. -/
theorem paperLpNorm_ofReal_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {q : ℝ} (hq : 0 < q) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    paperENNRealLpNorm μ q (fun ω => ENNReal.ofReal (f ω)) =
      SubdiffusiveProcess.RawLp.eLpNorm f (ENNReal.ofReal q) μ := by
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by simpa using! hq) ENNReal.ofReal_ne_top f μ,
    ENNReal.toReal_ofReal hq.le, one_div]
  unfold paperENNRealLpNorm
  congr 1
  exact lintegral_congr fun ω => by rw [Real.enorm_eq_ofReal (hf ω)]

/-- Every positive geometric exponent can be obtained independently of the
moment order, by choosing the disorder threshold after that order. -/
theorem exists_cutoffBlockFactor_moment_bound (d : ℕ) (q η : ℝ) (hq : 1 ≤ q) (hη : 0 < η) :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ δ0 → ∀ L k : ℕ, k ≤ L → ∀ z : Vec d,
        eLpNorm (cutoffBlockFactor M L k z) (ENNReal.ofReal q) M.P.toMeasure ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (η * ((L - k : ℕ) : ℝ))) := by
  let a := sharpTwoBlockSmallnessConst d * (8 * η) / (2 * q)
  let δ0 := Real.sqrt a
  let C := 1 + sharpTwoBlockFactorConst d * Real.sqrt (1 / 2)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have ha : 0 < a := by
    dsimp only [a]
    exact div_pos (mul_pos (sharpTwoBlockSmallnessConst_pos d) (by positivity)) (by positivity)
  have hδ0 : 0 < δ0 := Real.sqrt_pos.mpr ha
  have hfactor : 0 ≤ sharpTwoBlockFactorConst d := zero_le_one.trans (le_max_left _ _)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨δ0, C, hδ0, hC, ?_⟩
  intro M hM L k hkL z
  have hsmall : q * M.delta ^ 2 ≤ sharpTwoBlockSmallnessConst d * (8 * η) * (1 / 2) := by
    have hsquare : M.delta ^ 2 ≤ a := by
      have h := pow_le_pow_left₀ M.shellPrefix.delta_pos.le hM 2
      rwa [Real.sq_sqrt ha.le] at h
    have h := mul_le_mul_of_nonneg_left hsquare hq0.le
    have hqa : q * a = sharpTwoBlockSmallnessConst d * (8 * η) * (1 / 2) := by
      dsimp only [a]
      field_simp
    rwa [hqa] at h
  have hconst : eLpNorm (fun _ : PotentialSample d => (1 : ℝ)) (ENNReal.ofReal q)
      M.P.toMeasure = 1 := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hq0).ne' (NeZero.ne M.P.toMeasure)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one, enorm_one]
  rcases hkL.eq_or_lt with h | h
  · subst L
    rw [show cutoffBlockFactor M k k z = fun _ => 1 by
      funext ω; simp only [cutoffBlockFactor, lt_self_iff_false, ↓reduceIte]]
    simp only [Nat.sub_self,
      Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    rw [hconst]
    exact ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))
  · have hrep := finiteBlockRatioRepresentative_lp_le M h z
      (q := q) (xi := q) (delta1 := (1 / 2 : ℝ)) (s := 8 * η)
      hq hq (by linarith) (by norm_num) (by positivity) hsmall
    rw [paperLpNorm_ofReal_eq _ hq0 _ (finiteBlockRatioRepresentative_nonneg M L k z)] at hrep
    have hpower : ((3 : ℝ) ^ (8 * η * ((L - k : ℕ) : ℝ) / 16)) ^ 2 =
        (3 : ℝ) ^ (η * ((L - k : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      push_cast
      ring
    rw [hpower] at hrep
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
      ((measurable_finiteBlockRatioRepresentative M L k z).mono
        (potentialShellIndexSigma_le_borel _) le_rfl).aestronglyMeasurable] at hrep
    rw [show cutoffBlockFactor M L k z = fun ω => 1 + finiteBlockRatioRepresentative M L k z ω by
      funext ω; simp only [cutoffBlockFactor, h, ↓reduceIte]]
    change eLpNorm (fun ω => 1 + finiteBlockRatioRepresentative M L k z ω)
      (ENNReal.ofReal q) M.P.toMeasure ≤ _
    refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hq)).trans ?_
    rw [hconst]
    refine (add_le_add le_rfl hrep).trans ?_
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hge : 1 ≤ (3 : ℝ) ^ (η * ((L - k : ℕ) : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    dsimp only [C]
    nlinarith

end SubdiffusiveProcess.Static
