module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.BlockUpdate
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.CutoffBlockUpdate
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.InductionHypothesis
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.SquareResponseRosenthal
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.SecondBlockSpatialAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.TailCoefficient
public import SubdiffusiveProcess.Frozen.Section3.CrudeJBound
public import SubdiffusiveProcess.Frozen.Section4.EllipticityBound
public import SubdiffusiveProcess.Frozen.Section4.CombineUnderS
public import SubdiffusiveProcess.Frozen.Section4.HomogenizationStep
public import SubdiffusiveProcess.Providers.Section4.HomogenizationStep

@[expose] public section




namespace SubdiffusiveProcess.Providers.Section4

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
open Homogenization.Book
open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Byte-exact conclusion carrier of the still-draft `p.combine.under.S`.
It is recorded here without importing that frozen anchor. -/
def CoarseGrainedCombineConclusion (d : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (xi delta1 : ℝ),
      16 * (d : ℝ) ≤ xi →
      C * xi * M.delta ^ 2 ≤ delta1 → delta1 ≤ c →
      inductionHypothesis M L xi delta1 →
      ∀ m : ℕ, 0 < m → L ≤ m →
        C * Real.rpow 3 (-((m - L : ℕ) : ℝ)) ≤ (1 / 4 : ℝ) →
        ∀ p q : Homogenization.Vec d,
          q = ahom M L • p → Homogenization.vecNormSq q ≤ ahom M L →
          expectedJ M L m p q ≤
            C * delta1 *
                (delta1 + Real.rpow 3 (-((m - L : ℕ) : ℝ))) +
              C * ∑ n ∈ Finset.Icc L m,
                Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
                  expectedJDifference M L n m p q

/-- Byte-exact conclusion carrier of the still-draft
`p.homogenization.step`, again recorded without a draft import. -/
def CoarseGrainedHomogenizationStepConclusion (d : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m0 : ℕ) (xi delta1 : ℝ),
      0 < m0 → 16 * (d : ℝ) ≤ xi →
      C * xi * M.delta ^ 2 ≤ delta1 → delta1 ≤ c →
      inductionHypothesis M m0 xi delta1 →
      ∀ (m L : ℕ), 0 < m → L ≤ m0 →
        (L : ℝ) + C * Real.log (2 + xi) ≤ m →
        paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M L m) ≤
          ENNReal.ofReal ((1 / 4 : ℝ) * delta1)

/-- The proved crude response estimate supplies the literal finite seed
`S(3h, xi, C xi delta^2 h)`.  The strict smallness hypothesis is the one
required by the frozen definition of `inductionHypothesis`, whose radius is
strictly less than one. -/
theorem exists_crude_induction_seed {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (h : ℕ) (xi : ℝ),
        0 < h → 1 ≤ xi →
        C * xi * M.delta ^ 2 * (h : ℝ) < 1 →
        inductionHypothesis M (3 * h) xi
          (C * xi * M.delta ^ 2 * (h : ℝ)) := by
  rcases SubdiffusiveProcess.Frozen.Section3.crude_j_bound (d := d) with
    ⟨C0, hC0, hcrude⟩
  let C : ℝ := 4 * C0 * Real.exp 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro M h xi hh hxi hsmall
  let delta1 : ℝ := C * xi * M.delta ^ 2 * (h : ℝ)
  have hdelta1 : 0 < delta1 := by
    dsimp only [delta1]
    exact mul_pos
      (mul_pos (mul_pos hC (zero_lt_one.trans_le hxi))
        (sq_pos_of_pos M.shellPrefix.delta_pos))
      (by exact_mod_cast hh)
  apply inductionHypothesis_of_scale_bounds M (3 * h) hxi hdelta1 hsmall
  intro n hn
  have hnOne : (n + 1 : ℝ) ≤ 4 * (h : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 4 * h by omega)
  have hbase : 0 ≤ C0 * xi * M.delta ^ 2 := by positivity
  have hexponent : C0 * xi * (n + 1 : ℝ) * M.delta ^ 2 ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hnOne hbase
    have hrewrite :
        C0 * xi * (n + 1 : ℝ) * M.delta ^ 2 ≤
          4 * C0 * xi * M.delta ^ 2 * (h : ℝ) := by
      nlinarith
    have htarget : 4 * C0 * xi * M.delta ^ 2 * (h : ℝ) ≤ 1 := by
      have hexpOne : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have hnonneg : 0 ≤ 4 * C0 * xi * M.delta ^ 2 * (h : ℝ) := by positivity
      have hle :
          4 * C0 * xi * M.delta ^ 2 * (h : ℝ) ≤
            C * xi * M.delta ^ 2 * (h : ℝ) := by
        dsimp only [C]
        nlinarith
      exact hle.trans hsmall.le
    exact hrewrite.trans htarget
  have hreal :
      C0 * xi * (n + 1 : ℝ) * M.delta ^ 2 *
          Real.exp (C0 * xi * (n + 1 : ℝ) * M.delta ^ 2) ≤ delta1 := by
    have hexp := Real.exp_le_exp.mpr hexponent
    have hpref :
        C0 * xi * (n + 1 : ℝ) * M.delta ^ 2 ≤
          4 * C0 * xi * M.delta ^ 2 * (h : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hnOne hbase
      nlinarith
    calc
      C0 * xi * (n + 1 : ℝ) * M.delta ^ 2 *
          Real.exp (C0 * xi * (n + 1 : ℝ) * M.delta ^ 2) ≤
          (4 * C0 * xi * M.delta ^ 2 * (h : ℝ)) * Real.exp 1 :=
        mul_le_mul hpref hexp (Real.exp_pos _).le (by positivity)
      _ = delta1 := by
        dsimp only [delta1, C]
        ring
  exact (hcrude M n xi
      (Ch02.cubeDomain (Homogenization.originCube d (n : ℤ))) hxi
      (by intro x hx; exact hx)).trans (ENNReal.ofReal_le_ofReal hreal)

private theorem coarseInductionHypothesis_mono_terminal {d : ℕ}
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {m0 L : ℕ} {xi delta1 : ℝ}
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0) :
    inductionHypothesis M L xi delta1 := by exact SubdiffusiveProcess.Providers.Section4.inductionHypothesis_mono_terminal (d := d) (M := M) (m0 := m0) (L := L) (xi := xi) (delta1 := delta1) (hS := hS) (hLm0 := hLm0)

private theorem coarseInductionHypothesis_mono_radius {d : ℕ}
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {m0 : ℕ} {xi delta1 delta2 : ℝ}
    (hS : inductionHypothesis M m0 xi delta1) (hdelta : delta1 ≤ delta2)
    (hdelta2 : delta2 < 1) :
    inductionHypothesis M m0 xi delta2 := by
  have hdelta2pos : 0 < delta2 := hS.2.1.trans_le hdelta
  apply inductionHypothesis_of_scale_bounds M m0 hS.1 hdelta2pos hdelta2
  intro n hn
  exact (inductionHypothesis_scale_bound hS hn).trans
    (ENNReal.ofReal_le_ofReal hdelta)

private theorem coarseInductionHypothesisInfinity_mono_radius {d : ℕ}
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {xi delta1 delta2 : ℝ}
    (hS : inductionHypothesisInfinity M xi delta1) (hdelta : delta1 ≤ delta2)
    (hdelta2 : delta2 < 1) :
    inductionHypothesisInfinity M xi delta2 := by
  apply inductionHypothesisInfinity_of_scale_bounds M hS.1
    (hS.2.1.trans_le hdelta) hdelta2
  intro m
  exact (le_iSup (fun r : ℕ => paperENNRealLpNorm M.P.toMeasure xi
    (normalizedDefect M r
      (Ch02.cubeDomain (Homogenization.originCube d (r : ℤ))))) m).trans
      (hS.2.2.2.trans (ENNReal.ofReal_le_ofReal hdelta))

private theorem headline_normalizedDefect_ne_top {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    normalizedDefect M L U omega ≠ ⊤ := by
  have hle := normalizedDefect_le_two_mul_quarterNetMax M L U omega
  have hmax : normalizedResponseQuarterNetMax M L U omega ≠ ⊤ := by
    unfold normalizedResponseQuarterNetMax
    rw [Finset.sup'_apply]
    obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_sup'
      (sphereQuarterNet_points_nonempty (d := d)) (fun e =>
        ENNReal.ofReal
          (J U (aCutoffCoeffOnData M L omega U).toCoeffOn
            ((Real.sqrt (ahom M L))⁻¹ • e)
            (Real.sqrt (ahom M L) • e)))
    rw [heq]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by norm_num) hmax) hle

private theorem normalizedDefect_paperLpNorm_mono_exponent
    {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L m : ℕ) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    paperENNRealLpNorm M.P.toMeasure p (normalizedDefectAt M L m) ≤
      paperENNRealLpNorm M.P.toMeasure q (normalizedDefectAt M L m) := by
  let X := normalizedDefectAt M L m
  have hXtop : ∀ omega, X omega ≠ ∞ := fun omega => by
    dsimp only [X, normalizedDefectAt]
    exact headline_normalizedDefect_ne_top M L
      (Ch02.cubeDomain (Homogenization.originCube d (m : ℤ))) omega
  have hXmeas : Measurable X := by
    dsimp only [X, normalizedDefectAt]
    exact (measurable_normalizedDefect_potentialShellIndexSigma_Iic M L
      (Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl
  rw [paperENNRealLpNorm_eq_eLpNorm_toReal M.P.toMeasure hp hXtop,
    paperENNRealLpNorm_eq_eLpNorm_toReal M.P.toMeasure
      (hp.trans_le hpq) hXtop]
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hXmeas.ennreal_toReal.aestronglyMeasurable,
    SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hXmeas.ennreal_toReal.aestronglyMeasurable]
  exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)

/-- Restrict the infinite predicate to any finite terminal scale. -/
theorem inductionHypothesis_of_infinity {d : ℕ}
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {m0 : ℕ} {xi delta1 : ℝ}
    (hS : inductionHypothesisInfinity M xi delta1) :
    inductionHypothesis M m0 xi delta1 := by
  apply inductionHypothesis_of_scale_bounds M m0 hS.1 hS.2.1 hS.2.2.1
  intro n _hn
  exact (le_iSup (fun r : ℕ =>
    paperENNRealLpNorm M.P.toMeasure xi
      (normalizedDefect M r
        (Ch02.cubeDomain (Homogenization.originCube d (r : ℤ))))) n).trans
    hS.2.2.2

/-- Iterate a source-shaped block implication from the crude seed and pass to
the infinite induction predicate.  The payload theorem supplied to `hstep`
must already include the sliding-scale calculation for every member of the
new block; this lemma performs only the order-theoretic iteration. -/
theorem inductionHypothesisInfinity_of_seed_and_block_step {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (h : ℕ) {xi delta1 : ℝ}
    (hh : 0 < h)
    (hseed : inductionHypothesis M (3 * h) xi delta1)
    (hstep : ∀ m : ℕ, 3 * h ≤ m →
      inductionHypothesis M m xi delta1 →
      inductionHypothesis M (m + h) xi delta1) :
    inductionHypothesisInfinity M xi delta1 := by
  have hblocks : ∀ j : ℕ,
      inductionHypothesis M (3 * h + j * h) xi delta1 := by
    intro j
    induction j with
    | zero =>
        simpa only [Nat.zero_mul, Nat.add_zero] using hseed
    | succ j ih =>
        have hnext := hstep (3 * h + j * h) (by omega) ih
        simpa only [Nat.succ_mul, Nat.add_assoc] using hnext
  apply inductionHypothesisInfinity_of_finite M
  intro m0
  have hm0mul : m0 ≤ m0 * h := Nat.le_mul_of_pos_right m0 hh
  have hm0 : m0 ≤ 3 * h + m0 * h := hm0mul.trans (Nat.le_add_left _ _)
  exact coarseInductionHypothesis_mono_terminal (hblocks m0) hm0

/-- First-induction analytic update on the literal headline carrier.  The
quarter-gain comes from the draft homogenization-step conclusion, while the
proved Gamma-two parent-cube bound is absorbed directly by the printed two
smallness inequalities. -/
theorem headline_firstBlock_cutoff_update {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {r k h : ℕ}
    (hkr : k < r) (hgap : r - k ≤ h) (hh : 0 < h)
    {xi delta1 : ℝ} (hxi : 1 ≤ xi) (hdelta : 0 ≤ delta1)
    (hdelta' : delta1 ≤ 1)
    (hsmall : xi * M.delta ^ 2 * (h : ℝ) ^ 2 ≤
      (cutoffBlockAbsorptionConst d)⁻¹ * delta1)
    (hsmall' : (cutoffBlockAbsorptionConst d)⁻¹ * delta1 ≤
      (cutoffBlockAbsorptionConst d)⁻¹ ^ 2)
    (hold : paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M k r) ≤
      ENNReal.ofReal ((1 / 4 : ℝ) * delta1)) :
    paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M r r) ≤
      ENNReal.ofReal delta1 := by
  have hshell :=
    parentCubeLocalizationRepresentative_squared_moment_le_absorbed
      M hkr hgap hh hxi hdelta hsmall hsmall'
  exact normalizedDefectAt_cutoff_update_close
    M hkr hxi hdelta hdelta' hold hshell

/-- The complete sliding first-block implication.  The single parameter
`K` dominates both the homogenization separation constant and the explicit
parent-shell absorption constant, so the two printed smallness inequalities
discharge every analytic premise of `headline_firstBlock_cutoff_update`. -/
theorem exists_headline_firstBlock {d : ℕ}
    (hhomog : CoarseGrainedHomogenizationStepConclusion d) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m h : ℕ)
        (xi delta1 : ℝ),
        0 < h → 3 * h ≤ m → 16 * (d : ℝ) ≤ xi →
        K * Real.log (2 + xi) ≤ (h : ℝ) →
        xi * M.delta ^ 2 * (h : ℝ) ^ 2 ≤ K⁻¹ * delta1 →
        K⁻¹ * delta1 ≤ K⁻¹ ^ 2 → delta1 ≤ c →
        inductionHypothesis M m xi delta1 →
        inductionHypothesis M (m + h) xi delta1 := by
  rcases hhomog with ⟨c0, C0, hc0, hC0, hhomog⟩
  let K0 := cutoffBlockAbsorptionConst d
  let K : ℝ := max 1 (max C0 K0)
  let c : ℝ := min c0 1
  have hK0one : 1 ≤ K0 := cutoffBlockAbsorptionConst_one_le d
  have hK0 : 0 < K0 := zero_lt_one.trans_le hK0one
  have hKone : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := zero_lt_one.trans_le hKone
  have hKC0 : C0 ≤ K :=
    (le_max_left C0 K0).trans (le_max_right 1 (max C0 K0))
  have hKK0 : K0 ≤ K :=
    (le_max_right C0 K0).trans (le_max_right 1 (max C0 K0))
  have hc : 0 < c := lt_min hc0 zero_lt_one
  refine ⟨c, K, hc, hK, ?_⟩
  intro M m h xi delta1 hh hm hxiDim hlog hsmall hsmall' hdeltaC hS
  have hmpos : 0 < m := by omega
  have hxi : 1 ≤ xi := hS.1
  have hdelta0 : 0 ≤ delta1 := hS.2.1.le
  have hdeltaOne : delta1 ≤ 1 := hdeltaC.trans (min_le_right _ _)
  have hdeltaC0 : delta1 ≤ c0 := hdeltaC.trans (min_le_left _ _)
  have hlog0 : 0 ≤ Real.log (2 + xi) :=
    Real.log_nonneg (by linarith)
  have hhomogLog : C0 * Real.log (2 + xi) ≤ (h : ℝ) :=
    (mul_le_mul_of_nonneg_right hKC0 hlog0).trans hlog
  have hbase0 : 0 ≤ xi * M.delta ^ 2 := by positivity
  have hhOne : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hbaseLe : xi * M.delta ^ 2 ≤
      xi * M.delta ^ 2 * (h : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((h : ℝ) - 1)]
  have hKmulInv : K * K⁻¹ = 1 := by field_simp
  have hhomogSmall : C0 * xi * M.delta ^ 2 ≤ delta1 := by
    have hKbase : K * (xi * M.delta ^ 2) ≤ delta1 := by
      have hscaled := mul_le_mul_of_nonneg_left (hbaseLe.trans hsmall) hK.le
      calc
        K * (xi * M.delta ^ 2) ≤ K * (K⁻¹ * delta1) := hscaled
        _ = delta1 := by rw [← mul_assoc, hKmulInv, one_mul]
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_right hKC0 hbase0).trans hKbase
  have hKinvK0inv : K⁻¹ ≤ K0⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hK0 hKK0
  have hcutoffSmall : xi * M.delta ^ 2 * (h : ℝ) ^ 2 ≤
      K0⁻¹ * delta1 :=
    hsmall.trans (mul_le_mul_of_nonneg_right hKinvK0inv hdelta0)
  have hdeltaK : delta1 ≤ K⁻¹ := by
    have hscaled := mul_le_mul_of_nonneg_left hsmall' hK.le
    have hright : K * K⁻¹ ^ 2 = K⁻¹ := by
      rw [pow_two, ← mul_assoc, hKmulInv, one_mul]
    calc
      delta1 = K * (K⁻¹ * delta1) := by
        rw [← mul_assoc, hKmulInv, one_mul]
      _ ≤ K * K⁻¹ ^ 2 := hscaled
      _ = K⁻¹ := hright
  have hdeltaK0 : delta1 ≤ K0⁻¹ := hdeltaK.trans hKinvK0inv
  have hcutoffSmall' : K0⁻¹ * delta1 ≤ K0⁻¹ ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_left hdeltaK0 (inv_nonneg.mpr hK0.le)
  apply inductionHypothesis_extend hS
  intro r hmr hr
  let k := r - h
  have hkr : k < r := by dsimp only [k]; omega
  have hgap : r - k ≤ h := by dsimp only [k]; omega
  have hkm : k ≤ m := by dsimp only [k]; omega
  have hrpos : 0 < r := hmpos.trans_le (Nat.le_of_lt hmr)
  have hsep : (k : ℝ) + C0 * Real.log (2 + xi) ≤ r := by
    have hkcast : (k : ℝ) + (h : ℝ) = (r : ℝ) := by
      dsimp only [k]
      rw [Nat.cast_sub (by omega : h ≤ r)]
      ring
    nlinarith
  have hold := hhomog M m xi delta1 hmpos hxiDim hhomogSmall hdeltaC0 hS
    r k hrpos hkm hsep
  exact headline_firstBlock_cutoff_update M hkr hgap hh hxi hdelta0
    hdeltaOne hcutoffSmall hcutoffSmall' hold

/-- Source Steps 1--2 with the numerical parameter choice left explicit.
The crude seed is enlarged to the common induction radius, the preceding
sliding implication is iterated, and no analytic premise remains. -/
theorem exists_headline_firstInduction {d : ℕ}
    (hhomog : CoarseGrainedHomogenizationStepConclusion d) :
    ∃ Cseed c K : ℝ, 0 < Cseed ∧ 0 < c ∧ 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (h : ℕ)
        (xi delta1 : ℝ),
        0 < h → 16 * (d : ℝ) ≤ xi → delta1 < 1 →
        Cseed * xi * M.delta ^ 2 * (h : ℝ) ≤ delta1 →
        K * Real.log (2 + xi) ≤ (h : ℝ) →
        xi * M.delta ^ 2 * (h : ℝ) ^ 2 ≤ K⁻¹ * delta1 →
        K⁻¹ * delta1 ≤ K⁻¹ ^ 2 → delta1 ≤ c →
        inductionHypothesisInfinity M xi delta1 := by
  rcases exists_crude_induction_seed (d := d) with
    ⟨Cseed, hCseed, hseed⟩
  rcases exists_headline_firstBlock hhomog with
    ⟨c, K, hc, hK, hblock⟩
  refine ⟨Cseed, c, K, hCseed, hc, hK, ?_⟩
  intro M h xi delta1 hh hxiDim hdeltaOne hseedLe hlog hsmall hsmall'
    hdeltaC
  have hxi : 1 ≤ xi := by
    have hd : (2 : ℕ) ≤ d := M.shellPrefix.dimension
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hseedSmall : Cseed * xi * M.delta ^ 2 * (h : ℝ) < 1 :=
    hseedLe.trans_lt hdeltaOne
  have hseed0 := hseed M h xi hh hxi hseedSmall
  have hseedCommon : inductionHypothesis M (3 * h) xi delta1 :=
    coarseInductionHypothesis_mono_radius hseed0 hseedLe hdeltaOne
  exact inductionHypothesisInfinity_of_seed_and_block_step M h hh hseedCommon
    (fun m hm hS =>
      hblock M m h xi delta1 hh hm hxiDim hlog hsmall hsmall'
        hdeltaC hS)

/-- A fixed high-moment instance of the first induction.  Its radius is a
dimension-only multiple of `delta^2`, exactly the retained-mean input needed
by the second induction. -/
theorem exists_headline_fixedFirstInduction {d : ℕ}
    (hhomog : CoarseGrainedHomogenizationStepConclusion d) :
    ∃ cFirst firstConst : ℝ, 0 < cFirst ∧ 0 < firstConst ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        firstConst * M.delta ^ 2 < cFirst →
        inductionHypothesisInfinity M (16 * (d : ℝ))
          (firstConst * M.delta ^ 2) := by
  rcases exists_headline_firstInduction hhomog with
    ⟨Cseed, c0, K0, hCseed, hc0, hK0, hfirst⟩
  let xiFirst : ℝ := 16 * (d : ℝ)
  obtain ⟨h, hhLarge⟩ := exists_nat_gt
    (max 1 (K0 * Real.log (2 + xiFirst)))
  have hh : 0 < h := by
    have : (1 : ℝ) < (h : ℝ) := (le_max_left _ _).trans_lt hhLarge
    have hh1 : 1 < h := by exact_mod_cast this
    omega
  have hlog : K0 * Real.log (2 + xiFirst) ≤ (h : ℝ) :=
    (le_max_right 1 _).trans hhLarge.le
  let firstConst : ℝ := max 1 (max
    (Cseed * xiFirst * (h : ℝ))
    (K0 * xiFirst * (h : ℝ) ^ 2))
  let cFirst : ℝ := min 1 (min c0 K0⁻¹)
  have hfirstConst : 0 < firstConst := by
    exact zero_lt_one.trans_le (le_max_left _ _)
  have hcFirst : 0 < cFirst := by
    dsimp only [cFirst]
    exact lt_min zero_lt_one (lt_min hc0 (inv_pos.mpr hK0))
  refine ⟨cFirst, firstConst, hcFirst, hfirstConst, ?_⟩
  intro M hsmallFirst
  have hd : (2 : ℕ) ≤ d := M.shellPrefix.dimension
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hxiDim : 16 * (d : ℝ) ≤ xiFirst := by rfl
  have hdeltaFirst : firstConst * M.delta ^ 2 < 1 :=
    hsmallFirst.trans_le (min_le_left _ _)
  have hdeltaC : firstConst * M.delta ^ 2 ≤ c0 :=
    hsmallFirst.le.trans (min_le_right _ _ |>.trans (min_le_left _ _))
  have hdeltaK : firstConst * M.delta ^ 2 ≤ K0⁻¹ :=
    hsmallFirst.le.trans (min_le_right _ _ |>.trans (min_le_right _ _))
  have hseedCoeff : Cseed * xiFirst * (h : ℝ) ≤ firstConst :=
    (le_max_left _ _).trans (le_max_right 1 _)
  have hseedLe : Cseed * xiFirst * M.delta ^ 2 * (h : ℝ) ≤
      firstConst * M.delta ^ 2 := by
    have := mul_le_mul_of_nonneg_right hseedCoeff (sq_nonneg M.delta)
    nlinarith
  have hsmallCoeff : K0 * xiFirst * (h : ℝ) ^ 2 ≤ firstConst :=
    (le_max_right _ _).trans (le_max_right 1 _)
  have hsmall : xiFirst * M.delta ^ 2 * (h : ℝ) ^ 2 ≤
      K0⁻¹ * (firstConst * M.delta ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right hsmallCoeff (sq_nonneg M.delta)
    have hcancel : K0⁻¹ * K0 = 1 := by field_simp
    calc
      xiFirst * M.delta ^ 2 * (h : ℝ) ^ 2 =
          (K0⁻¹ * K0) * (xiFirst * M.delta ^ 2 * (h : ℝ) ^ 2) := by
        rw [hcancel, one_mul]
      _ = K0⁻¹ * (K0 * xiFirst * (h : ℝ) ^ 2 * M.delta ^ 2) := by
        ring
      _ ≤ K0⁻¹ * (firstConst * M.delta ^ 2) := by
        gcongr
  have hsmall' : K0⁻¹ * (firstConst * M.delta ^ 2) ≤ K0⁻¹ ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_left hdeltaK (inv_nonneg.mpr hK0.le)
  exact hfirst M h xiFirst (firstConst * M.delta ^ 2) hh hxiDim
    hdeltaFirst hseedLe (by simpa only [xiFirst] using hlog) hsmall hsmall'
      hdeltaC

/-- The second-induction square-observable estimate on a normalized fixed
direction.  The current `xi` induction supplies the high moment; the completed
moment-two induction supplies the source-strength retained mean
`E[J_n^2] ≤ delta^4`. -/
theorem headline_secondBlock_square_update_quarterNetBudget {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {m0 mFirst L n m h : ℕ} {xi xiFirst delta1 deltaFirst firstConst : ℝ}
    (hS : inductionHypothesis M m0 xi delta1)
    (hSFirst : inductionHypothesis M mFirst xiFirst deltaFirst)
    (hxiFirst : 2 ≤ xiFirst)
    (hfirstRadius : deltaFirst ≤ firstConst * M.delta ^ 2)
    (hmeanSmall : firstConst ^ 2 * (squareResponseAbsorptionConst d)⁻¹ ^ 2 ≤
      squareResponseQuarterNetEta d)
    (hxiDim : 16 * (d : ℝ) ≤ xi) (hxi : 4 ≤ xi)
    (hLm0 : L ≤ m0) (hLmFirst : L ≤ mFirst) (hLn : L ≤ n)
    (hnm : n ≤ m) (hgap : m - n = h) (hh : 0 < h)
    (hlog : squareResponseAbsorptionConst d * Real.log (2 + xi) ≤ (h : ℝ))
    (hsmall : xi * M.delta ^ 2 * (h : ℝ) ≤
      (squareResponseAbsorptionConst d)⁻¹ * delta1)
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1) :
    let p := (Real.sqrt (ahom M L))⁻¹ • e
    let q := Real.sqrt (ahom M L) • e
    (∫ omega,
        |(((Homogenization.descendantsAtScale
            (Homogenization.originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ Homogenization.descendantsAtScale
              (Homogenization.originCube d (m : ℤ)) (n : ℤ),
            cutoffResponseOnCube M L p q R omega ^ 2| ^ (xi / 2)
          ∂M.P.toMeasure) ^ (xi / 2)⁻¹ ≤
      2 * squareResponseQuarterNetEta d * delta1 ^ 2 := by
  dsimp only
  let p : Homogenization.Vec d := (Real.sqrt (ahom M L))⁻¹ • e
  let q : Homogenization.Vec d := Real.sqrt (ahom M L) • e
  have hhigh := initial_fixed_cutoff_response_conclusion
    M m0 xi delta1 hxiDim hS L n hLm0 hLn e he
  have ha : 0 < ahom M L := ahom_pos M L
  have hsqrt : Real.sqrt (ahom M L) ≠ 0 :=
    (Real.sqrt_pos.2 ha).ne'
  have hq : q = ahom M L • p := by
    dsimp only [p, q]
    rw [smul_smul]
    congr 1
    field_simp
    nlinarith [Real.sq_sqrt ha.le]
  have hqNorm : Homogenization.vecNormSq q ≤ ahom M L := by
    dsimp only [q]
    rw [Homogenization.vecNormSq_smul, he, mul_one, Real.sq_sqrt ha.le]
  have hmean :=
    cutoffResponseOnCube_sq_integrable_and_integral_le_of_inductionHypothesis
      M hxiFirst hSFirst hLn hLmFirst p q hq hqNorm
  have hmean' :
      ∫ omega, cutoffResponseOnCube M L p q
          (Homogenization.originCube d (n : ℤ)) omega ^ 2 ∂M.P.toMeasure ≤
        firstConst ^ 2 * M.delta ^ 4 := by
    have hdeltaFirst : 0 ≤ deltaFirst := hSFirst.2.1.le
    have htarget : deltaFirst ^ 2 ≤
        (firstConst * M.delta ^ 2) ^ 2 :=
      pow_le_pow_left₀ hdeltaFirst hfirstRadius 2
    calc
      _ ≤ deltaFirst ^ 2 := hmean.2
      _ ≤ (firstConst * M.delta ^ 2) ^ 2 := htarget
      _ = firstConst ^ 2 * M.delta ^ 4 := by ring
  exact
    cutoffResponseSquareAverage_rpow_root_le_quarterNetBudget_of_meanCoeff
      M L n m h hLn hnm hgap hh p q hxi hlog hsmall
        (sq_nonneg firstConst) hmeanSmall hhigh.1 hhigh.2 hmean'

/-- Fixed-direction square budget with the retained mean supplied directly
at the target radius.  This form lets the headline choose a larger final
dimension-only smallness constant than the intrinsic Rosenthal constant. -/
theorem headline_secondBlock_square_update_quarterNetBudget_of_meanBudget
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {m0 mFirst L n m h : ℕ} {xi xiFirst delta1 deltaFirst firstConst : ℝ}
    (hS : inductionHypothesis M m0 xi delta1)
    (hSFirst : inductionHypothesis M mFirst xiFirst deltaFirst)
    (hxiFirst : 2 ≤ xiFirst)
    (hfirstRadius : deltaFirst ≤ firstConst * M.delta ^ 2)
    (hmeanBudget : firstConst ^ 2 * M.delta ^ 4 ≤
      squareResponseQuarterNetEta d * delta1 ^ 2)
    (hxiDim : 16 * (d : ℝ) ≤ xi) (hxi : 4 ≤ xi)
    (hLm0 : L ≤ m0) (hLmFirst : L ≤ mFirst) (hLn : L ≤ n)
    (hnm : n ≤ m) (hgap : m - n = h)
    (hlog : squareResponseAbsorptionConst d * Real.log (2 + xi) ≤ (h : ℝ))
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1) :
    let p := (Real.sqrt (ahom M L))⁻¹ • e
    let q := Real.sqrt (ahom M L) • e
    (∫ omega,
        |(((Homogenization.descendantsAtScale
            (Homogenization.originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ Homogenization.descendantsAtScale
              (Homogenization.originCube d (m : ℤ)) (n : ℤ),
            cutoffResponseOnCube M L p q R omega ^ 2| ^ (xi / 2)
          ∂M.P.toMeasure) ^ (xi / 2)⁻¹ ≤
      2 * squareResponseQuarterNetEta d * delta1 ^ 2 := by
  dsimp only
  let p : Homogenization.Vec d := (Real.sqrt (ahom M L))⁻¹ • e
  let q : Homogenization.Vec d := Real.sqrt (ahom M L) • e
  have hhigh := initial_fixed_cutoff_response_conclusion
    M m0 xi delta1 hxiDim hS L n hLm0 hLn e he
  have ha : 0 < ahom M L := ahom_pos M L
  have hq : q = ahom M L • p := by
    dsimp only [p, q]
    rw [smul_smul]
    congr 1
    field_simp [(Real.sqrt_pos.2 ha).ne']
    nlinarith [Real.sq_sqrt ha.le]
  have hqNorm : Homogenization.vecNormSq q ≤ ahom M L := by
    dsimp only [q]
    rw [Homogenization.vecNormSq_smul, he, mul_one, Real.sq_sqrt ha.le]
  have hmean :=
    cutoffResponseOnCube_sq_integrable_and_integral_le_of_inductionHypothesis
      M hxiFirst hSFirst hLn hLmFirst p q hq hqNorm
  have hmean' :
      ∫ omega, cutoffResponseOnCube M L p q
          (Homogenization.originCube d (n : ℤ)) omega ^ 2 ∂M.P.toMeasure ≤
        squareResponseQuarterNetEta d * delta1 ^ 2 := by
    have hdeltaFirst : 0 ≤ deltaFirst := hSFirst.2.1.le
    have htarget : deltaFirst ^ 2 ≤
        (firstConst * M.delta ^ 2) ^ 2 :=
      pow_le_pow_left₀ hdeltaFirst hfirstRadius 2
    calc
      _ ≤ deltaFirst ^ 2 := hmean.2
      _ ≤ (firstConst * M.delta ^ 2) ^ 2 := htarget
      _ = firstConst ^ 2 * M.delta ^ 4 := by ring
      _ ≤ _ := hmeanBudget
  exact
    cutoffResponseSquareAverage_rpow_root_le_quarterNetBudget_of_meanBudget
      M L n m h hLn hnm hgap p q hxi hlog hhigh.1 hhigh.2 hmean'

/-- Compatibility form of the fixed-direction estimate, obtained after
forgetting the finite-net reserve. -/
theorem headline_secondBlock_square_update {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {m0 mFirst L n m h : ℕ} {xi xiFirst delta1 deltaFirst firstConst : ℝ}
    (hS : inductionHypothesis M m0 xi delta1)
    (hSFirst : inductionHypothesis M mFirst xiFirst deltaFirst)
    (hxiFirst : 2 ≤ xiFirst)
    (hfirstRadius : deltaFirst ≤ firstConst * M.delta ^ 2)
    (hmeanSmall : firstConst ^ 2 * (squareResponseAbsorptionConst d)⁻¹ ^ 2 ≤
      squareResponseQuarterNetEta d)
    (hxiDim : 16 * (d : ℝ) ≤ xi) (hxi : 4 ≤ xi)
    (hLm0 : L ≤ m0) (hLmFirst : L ≤ mFirst) (hLn : L ≤ n)
    (hnm : n ≤ m) (hgap : m - n = h) (hh : 0 < h)
    (hlog : squareResponseAbsorptionConst d * Real.log (2 + xi) ≤ (h : ℝ))
    (hsmall : xi * M.delta ^ 2 * (h : ℝ) ≤
      (squareResponseAbsorptionConst d)⁻¹ * delta1)
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1) :
    let p := (Real.sqrt (ahom M L))⁻¹ • e
    let q := Real.sqrt (ahom M L) • e
    (∫ omega,
        |(((Homogenization.descendantsAtScale
            (Homogenization.originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ Homogenization.descendantsAtScale
              (Homogenization.originCube d (m : ℤ)) (n : ℤ),
            cutoffResponseOnCube M L p q R omega ^ 2| ^ (xi / 2)
          ∂M.P.toMeasure) ^ (xi / 2)⁻¹ ≤
      (1 / 36 : ℝ) * delta1 ^ 2 := by
  have hraw := headline_secondBlock_square_update_quarterNetBudget M hS hSFirst
    hxiFirst hfirstRadius hmeanSmall hxiDim hxi hLm0 hLmFirst hLn hnm hgap hh
      hlog hsmall e he
  have heta : 2 * squareResponseQuarterNetEta d ≤ (1 / 36 : ℝ) := by
    unfold squareResponseQuarterNetEta
    have hcard : (1 : ℝ) ≤ ((sphereQuarterNet d).points.card : ℝ) := by
      exact_mod_cast (sphereQuarterNet_points_nonempty (d := d)).card_pos
    rw [inv_eq_one_div]
    rw [show 2 * (1 / (288 * ((sphereQuarterNet d).points.card : ℝ))) =
        2 / (288 * ((sphereQuarterNet d).points.card : ℝ)) by ring]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) <
      288 * ((sphereQuarterNet d).points.card : ℝ))).2
    nlinarith
  exact hraw.trans (mul_le_mul_of_nonneg_right heta (sq_nonneg delta1))

/-- Source Step 3 with the retained mean drawn directly from the already
completed first induction.  Restricting `S(∞,xiFirst,deltaFirst)` at `n` and
the second-moment budget perform the printed Lyapunov/Jensen downgrade; the
resulting `firstConst^2 * delta^4` is absorbed by the explicit K condition. -/
theorem headline_secondBlock_square_update_of_firstInduction
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {m0 L n m h : ℕ} {xi xiFirst delta1 deltaFirst firstConst : ℝ}
    (hS : inductionHypothesis M m0 xi delta1)
    (hSFirst : inductionHypothesisInfinity M xiFirst deltaFirst)
    (hxiFirst : 2 ≤ xiFirst)
    (hfirstRadius : deltaFirst ≤ firstConst * M.delta ^ 2)
    (hmeanSmall : firstConst ^ 2 * (squareResponseAbsorptionConst d)⁻¹ ^ 2 ≤
      squareResponseQuarterNetEta d)
    (hxiDim : 16 * (d : ℝ) ≤ xi) (hxi : 4 ≤ xi)
    (hLm0 : L ≤ m0) (hLn : L ≤ n)
    (hnm : n ≤ m) (hgap : m - n = h) (hh : 0 < h)
    (hlog : squareResponseAbsorptionConst d * Real.log (2 + xi) ≤ (h : ℝ))
    (hsmall : xi * M.delta ^ 2 * (h : ℝ) ≤
      (squareResponseAbsorptionConst d)⁻¹ * delta1)
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1) :
    let p := (Real.sqrt (ahom M L))⁻¹ • e
    let q := Real.sqrt (ahom M L) • e
    (∫ omega,
        |(((Homogenization.descendantsAtScale
            (Homogenization.originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ Homogenization.descendantsAtScale
              (Homogenization.originCube d (m : ℤ)) (n : ℤ),
            cutoffResponseOnCube M L p q R omega ^ 2| ^ (xi / 2)
          ∂M.P.toMeasure) ^ (xi / 2)⁻¹ ≤
      (1 / 36 : ℝ) * delta1 ^ 2 := by
  exact headline_secondBlock_square_update M hS
    (inductionHypothesis_of_infinity (m0 := n) hSFirst) hxiFirst
      hfirstRadius hmeanSmall hxiDim hxi hLm0 hLn hLn hnm hgap hh hlog
      hsmall e he

/-- The fixed-direction square estimate aggregated over the finite quarter
net.  The reserved `1/(288 * card(net))` budget pays exactly for the squared
factor-two sphere comparison, leaving the printed `delta1^2/36`. -/
theorem headline_secondBlock_normalizedDefectSquareAverage
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {m0 L n m h : ℕ} {xi xiFirst delta1 deltaFirst firstConst : ℝ}
    (hS : inductionHypothesis M m0 xi delta1)
    (hSFirst : inductionHypothesisInfinity M xiFirst deltaFirst)
    (hxiFirst : 2 ≤ xiFirst)
    (hfirstRadius : deltaFirst ≤ firstConst * M.delta ^ 2)
    (hmeanBudget : firstConst ^ 2 * M.delta ^ 4 ≤
      squareResponseQuarterNetEta d * delta1 ^ 2)
    (hxiDim : 16 * (d : ℝ) ≤ xi) (hxi : 4 ≤ xi)
    (hLm0 : L ≤ m0) (hLn : L ≤ n)
    (hnm : n ≤ m) (hgap : m - n = h)
    (hlog : squareResponseAbsorptionConst d * Real.log (2 + xi) ≤ (h : ℝ)) :
    paperENNRealLpNorm M.P.toMeasure (xi / 2) (fun omega =>
      ENNReal.ofReal
        ((((Homogenization.descendantsAtScale
            (Homogenization.originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹) *
          ∑ R ∈ Homogenization.descendantsAtScale
              (Homogenization.originCube d (m : ℤ)) (n : ℤ),
            (normalizedDefect M L (Ch02.cubeDomain R) omega).toReal ^ 2)) ≤
      ENNReal.ofReal ((1 / 36 : ℝ) * delta1 ^ 2) := by
  classical
  let D := Homogenization.descendantsAtScale
    (Homogenization.originCube d (m : ℤ)) (n : ℤ)
  let S := (sphereQuarterNet d).points
  let F : Homogenization.Vec d →
      SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun e omega =>
    ((D.card : ℝ)⁻¹) * ∑ R ∈ D,
      cutoffResponseOnCube M L ((Real.sqrt (ahom M L))⁻¹ • e)
        (Real.sqrt (ahom M L) • e) R omega ^ 2
  have hrho : 1 ≤ xi / 2 := by linarith
  have hrho0 : 0 < xi / 2 := by linarith
  have hdelta : 0 ≤ delta1 := hS.2.1.le
  have hFmeas : ∀ e ∈ S, Measurable (F e) := by
    intro e he
    dsimp only [F]
    exact measurable_const.mul (Finset.measurable_sum _ fun R _ =>
      (measurable_cutoffResponseOnCube M L
        ((Real.sqrt (ahom M L))⁻¹ • e)
        (Real.sqrt (ahom M L) • e) R).pow_const 2)
  have hFnonneg : ∀ e ∈ S, ∀ omega, 0 ≤ F e omega := by
    intro e he omega
    dsimp only [F]
    positivity
  have hFint : ∀ e ∈ S,
      Integrable (fun omega => |F e omega| ^ (xi / 2)) M.P.toMeasure := by
    intro e he
    have hhigh := initial_fixed_cutoff_response_conclusion
      M m0 xi delta1 hxiDim hS L n hLm0 hLn e ((sphereQuarterNet d).unit e he)
    simpa only [F, D] using
      integrable_abs_cutoffResponseSquareAverage_rpow M L n m
        ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e)
        (by linarith) hhigh.1
  have hFroot : ∀ e ∈ S,
      (∫ omega, |F e omega| ^ (xi / 2) ∂M.P.toMeasure) ^ (xi / 2)⁻¹ ≤
        2 * squareResponseQuarterNetEta d * delta1 ^ 2 := by
    intro e he
    simpa only [F, D] using
      headline_secondBlock_square_update_quarterNetBudget_of_meanBudget M hS
        (inductionHypothesis_of_infinity (m0 := n) hSFirst) hxiFirst
        hfirstRadius hmeanBudget hxiDim hxi hLm0 hLn hLn hnm hgap hlog
        e ((sphereQuarterNet d).unit e he)
  let Y : Homogenization.Vec d →
      SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ≥0∞ := fun e omega =>
    ENNReal.ofReal (F e omega)
  have hYmeas : ∀ e ∈ S, Measurable (Y e) := by
    intro e he
    exact (hFmeas e he).ennreal_ofReal
  have hYnorm : ∀ e ∈ S,
      paperENNRealLpNorm M.P.toMeasure (xi / 2) (Y e) ≤
        ENNReal.ofReal (2 * squareResponseQuarterNetEta d * delta1 ^ 2) := by
    intro e he
    have heq : Y e = fun omega => ENNReal.ofReal |F e omega| := by
      funext omega
      rw [abs_of_nonneg (hFnonneg e he omega)]
    rw [heq, paperENNRealLpNorm_ofReal_abs_eq_integral_abs_rpow_root
      M.P.toMeasure hrho0 (hFmeas e he) (hFint e he)]
    exact ENNReal.ofReal_le_ofReal (hFroot e he)
  have hcell : ∀ R ∈ D, ∀ omega,
      (normalizedDefect M L (Ch02.cubeDomain R) omega).toReal ^ 2 ≤
        4 * ∑ e ∈ S,
          cutoffResponseOnCube M L ((Real.sqrt (ahom M L))⁻¹ • e)
            (Real.sqrt (ahom M L) • e) R omega ^ 2 := by
    intro R hR omega
    let Z : Homogenization.Vec d → ℝ≥0∞ := fun e => ENNReal.ofReal
      (J (Ch02.cubeDomain R)
        (aCutoffCoeffOnData M L omega (Ch02.cubeDomain R)).toCoeffOn
        ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e))
    obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_sup'
      (sphereQuarterNet_points_nonempty (d := d)) Z
    have hmaxEq : normalizedResponseQuarterNetMax M L (Ch02.cubeDomain R) omega =
        Z e := by
      unfold normalizedResponseQuarterNetMax
      rw [Finset.sup'_apply]
      simpa only [Z] using heq
    have hmaxTop : normalizedResponseQuarterNetMax M L
        (Ch02.cubeDomain R) omega ≠ ⊤ := by
      rw [hmaxEq]
      exact ENNReal.ofReal_ne_top
    have htwoTop : (2 * normalizedResponseQuarterNetMax M L
        (Ch02.cubeDomain R) omega) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hmaxTop
    have hreal := ENNReal.toReal_mono htwoTop
      (normalizedDefect_le_two_mul_quarterNetMax M L
        (Ch02.cubeDomain R) omega)
    have hresp0 : 0 ≤ J (Ch02.cubeDomain R)
        (aCutoffCoeffOnData M L omega (Ch02.cubeDomain R)).toCoeffOn
        ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e) :=
      Ch02.responseJ_nonneg _ _ _ _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, hmaxEq,
      ENNReal.toReal_ofReal hresp0] at hreal
    have hcut :
        cutoffResponseOnCube M L ((Real.sqrt (ahom M L))⁻¹ • e)
            (Real.sqrt (ahom M L) • e) R omega =
          J (Ch02.cubeDomain R)
            (aCutoffCoeffOnData M L omega (Ch02.cubeDomain R)).toCoeffOn
            ((Real.sqrt (ahom M L))⁻¹ • e)
            (Real.sqrt (ahom M L) • e) := by
      unfold cutoffResponseOnCube aCutoffFamily
      exact responseJ_toCoeffOn_eq
        ((aCutoffTriadicData M L omega).onCube R)
        (aCutoffCoeffOnData M L omega (Ch02.cubeDomain R)) _ _
    rw [← hcut] at hreal
    have hsq := pow_le_pow_left₀ (ENNReal.toReal_nonneg) hreal 2
    have hone : cutoffResponseOnCube M L
        ((Real.sqrt (ahom M L))⁻¹ • e) (Real.sqrt (ahom M L) • e) R omega ^ 2 ≤
        ∑ v ∈ S, cutoffResponseOnCube M L
          ((Real.sqrt (ahom M L))⁻¹ • v)
          (Real.sqrt (ahom M L) • v) R omega ^ 2 := by
      simpa only [S] using
        (Finset.single_le_sum (fun v _ => sq_nonneg
          (cutoffResponseOnCube M L ((Real.sqrt (ahom M L))⁻¹ • v)
            (Real.sqrt (ahom M L) • v) R omega)) he)
    nlinarith
  have hpoint : ∀ omega,
      ENNReal.ofReal (((D.card : ℝ)⁻¹) * ∑ R ∈ D,
        (normalizedDefect M L (Ch02.cubeDomain R) omega).toReal ^ 2) ≤
        4 * ∑ e ∈ S, Y e omega := by
    intro omega
    have hsum := Finset.sum_le_sum fun R hR => hcell R hR omega
    have hcard0 : 0 ≤ ((D.card : ℝ)⁻¹) := by positivity
    have hreal :
      ((D.card : ℝ)⁻¹) * ∑ R ∈ D,
          (normalizedDefect M L (Ch02.cubeDomain R) omega).toReal ^ 2 ≤
          4 * ∑ e ∈ S, F e omega := by
      calc
        ((D.card : ℝ)⁻¹) * ∑ R ∈ D,
            (normalizedDefect M L (Ch02.cubeDomain R) omega).toReal ^ 2 ≤
            ((D.card : ℝ)⁻¹) * ∑ R ∈ D, 4 * ∑ e ∈ S,
            cutoffResponseOnCube M L ((Real.sqrt (ahom M L))⁻¹ • e)
              (Real.sqrt (ahom M L) • e) R omega ^ 2 :=
          mul_le_mul_of_nonneg_left hsum hcard0
        _ = 4 * ∑ e ∈ S, F e omega := by
          simp only [F]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          ring_nf
    calc
      ENNReal.ofReal (((D.card : ℝ)⁻¹) * ∑ R ∈ D,
          (normalizedDefect M L (Ch02.cubeDomain R) omega).toReal ^ 2) ≤
          ENNReal.ofReal (4 * ∑ e ∈ S, F e omega) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = 4 * ∑ e ∈ S, Y e omega := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
        congr 1
        exact ENNReal.ofReal_sum_of_nonneg fun e he => hFnonneg e he omega
  have hraw := paperENNRealLpNorm_mono_ae M.P.toMeasure hrho0.le
    (Filter.Eventually.of_forall hpoint)
  have hsum := paperENNRealLpNorm_finset_sum_le M.P.toMeasure hrho S Y hYmeas
  have hsumBound : paperENNRealLpNorm M.P.toMeasure (xi / 2)
      (fun omega => ∑ e ∈ S, Y e omega) ≤
        ∑ e ∈ S, ENNReal.ofReal
          (2 * squareResponseQuarterNetEta d * delta1 ^ 2) :=
    hsum.trans (Finset.sum_le_sum fun e he => hYnorm e he)
  have hconst := paperENNRealLpNorm_const_mul_eq M.P.toMeasure hrho0
    (4 : ℝ≥0∞) (fun omega => ∑ e ∈ S, Y e omega)
      (Finset.measurable_sum _ hYmeas)
  refine hraw.trans ?_
  rw [hconst]
  refine (mul_le_mul_of_nonneg_left hsumBound (by positivity)).trans ?_
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
    show (S.card : ℝ≥0∞) = ENNReal.ofReal (S.card : ℝ) by norm_num]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (S.card : ℝ)),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  apply ENNReal.ofReal_le_ofReal
  unfold squareResponseQuarterNetEta S
  have hcard : 0 < (((sphereQuarterNet d).points.card : ℝ)) := by
    exact_mod_cast (sphereQuarterNet_points_nonempty (d := d)).card_pos
  field_simp
  ring_nf
  exact le_rfl

/-- The literal same-scale second-block update.  The square-average prefix is
the full quarter-net endpoint above; the suffix is the linear-in-`h`
cellwise moment, and `normalizedDefect_parent_le_secondBlockSpatialBound`
performs the source spatial aggregation and independence factorization. -/
theorem headline_secondBlock_cutoff_update
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {m0 r k h : ℕ} {xi xiFirst delta1 deltaFirst firstConst : ℝ}
    (hS : inductionHypothesis M m0 xi delta1)
    (hSFirst : inductionHypothesisInfinity M xiFirst deltaFirst)
    (hxiFirst : 2 ≤ xiFirst)
    (hfirstRadius : deltaFirst ≤ firstConst * M.delta ^ 2)
    (hmeanBudget : firstConst ^ 2 * M.delta ^ 4 ≤
      squareResponseQuarterNetEta d * delta1 ^ 2)
    (hxiDim : 16 * (d : ℝ) ≤ xi) (hxi : 4 ≤ xi)
    (hk0 : k ≤ m0) (hkr : k < r)
    (hgap : r - k = h) (hh : 0 < h)
    (hlog : squareResponseAbsorptionConst d * Real.log (2 + xi) ≤ (h : ℝ))
    (hsuffixSmall : (sharpTwoBlockSmallnessConst d)⁻¹ *
      xi * M.delta ^ 2 * (h : ℝ) < 1)
    (hshell : 3 * secondBlockSpatialShellFactor d *
      xi * M.delta ^ 2 * (h : ℝ) ≤ (1 / 4 : ℝ) * delta1)
    (hdeltaOne : delta1 ≤ 1) :
    paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M r r) ≤
      ENNReal.ofReal delta1 := by
  let shell : ℝ := secondBlockSpatialShellFactor d *
    xi * M.delta ^ 2 * (h : ℝ)
  have hprefix := headline_secondBlock_normalizedDefectSquareAverage
    M hS hSFirst hxiFirst hfirstRadius hmeanBudget hxiDim hxi hk0 le_rfl
      hkr.le hgap hlog
  have hsuffix : ∀ R ∈ Homogenization.descendantsAtScale
      (Homogenization.originCube d (r : ℤ)) (k : ℤ),
      paperENNRealLpNorm M.P.toMeasure xi (fun omega => ENNReal.ofReal
        (sharpTwoBlockSuffixRepresentative M r k
          (Homogenization.triadicCubeShift R) omega ^ 2)) ≤
        ENNReal.ofReal shell := by
    intro R hR
    simpa only [shell] using
      sharpTwoBlock_suffix_square_moment_le_linear_shell M hkr hgap hh
        (show 1 ≤ xi by linarith) hsuffixSmall R
  have hspatial := normalizedDefect_parent_le_secondBlockSpatialBound
    M hkr hxi hS.2.1.le (by
      dsimp only [shell]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (secondBlockSpatialShellFactor_pos d).le
          (show 0 ≤ xi by linarith)) (sq_nonneg M.delta)) (by positivity))
      hprefix hsuffix
  have hreal : 3 * shell + (1 / 2 : ℝ) * (1 + shell) * delta1 ≤
      delta1 := by
    have hs0 : 0 ≤ shell := by
      dsimp only [shell]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (secondBlockSpatialShellFactor_pos d).le
          (show 0 ≤ xi by linarith)) (sq_nonneg M.delta)) (by positivity)
    apply secondBlockUpdate_close (Jnext :=
      3 * shell + (1 / 2 : ℝ) * (1 + shell) * delta1)
      (shell := 3 * shell)
      hS.2.1.le hdeltaOne
    · have hprod : 0 ≤ shell * delta1 :=
        mul_nonneg hs0 hS.2.1.le
      nlinarith
    · change 3 * (secondBlockSpatialShellFactor d *
        xi * M.delta ^ 2 * (h : ℝ)) ≤ (1 / 4 : ℝ) * delta1
      simpa only [mul_assoc] using hshell
  exact hspatial.trans (ENNReal.ofReal_le_ofReal hreal)

/-- The complete sliding second-block implication under one common
dimension-only parameter `K`.  Its four domination clauses respectively pay
for the colored square estimate, the sharp-shell smallness, the linear shell
coefficient, and the retained mean from the first induction. -/
theorem headline_secondBlock_implication
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {xiFirst deltaFirst firstConst K : ℝ}
    (hSFirst : inductionHypothesisInfinity M xiFirst
      (deltaFirst * M.delta ^ 2))
    (hxiFirst : 2 ≤ xiFirst)
    (hfirstRadius : deltaFirst ≤ firstConst)
    (hKpos : 0 < K)
    (hKsquare : squareResponseAbsorptionConst d ≤ K)
    (hKsuffix : (sharpTwoBlockSmallnessConst d)⁻¹ ≤ K)
    (hKshell : 12 * secondBlockSpatialShellFactor d ≤ K)
    (hKmean : firstConst ^ 2 * K⁻¹ ^ 2 ≤
      squareResponseQuarterNetEta d) :
    ∀ (m h : ℕ)
      (xi delta1 : ℝ),
      0 < h → 3 * h ≤ m → 16 * (d : ℝ) ≤ xi →
      K * Real.log (2 + xi) ≤ (h : ℝ) →
      xi * M.delta ^ 2 * (h : ℝ) ≤ K⁻¹ * delta1 →
      K⁻¹ * delta1 ≤ K⁻¹ ^ 2 →
      inductionHypothesis M m xi delta1 →
      inductionHypothesis M (m + h) xi delta1 := by
  intro m h xi delta1 hh hm hxiDim hlog hsmall hsmall' hS
  have hxi : 4 ≤ xi := by
    have hd : (2 : ℕ) ≤ d := M.shellPrefix.dimension
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hdelta0 : 0 ≤ delta1 := hS.2.1.le
  have hlogSquare : squareResponseAbsorptionConst d * Real.log (2 + xi) ≤
      (h : ℝ) := by
    have hlog0 : 0 ≤ Real.log (2 + xi) := Real.log_nonneg (by linarith)
    exact (mul_le_mul_of_nonneg_right hKsquare hlog0).trans hlog
  have hTnonneg : 0 ≤ xi * M.delta ^ 2 * (h : ℝ) := by positivity
  have hdeltaSq : M.delta ^ 2 ≤ K⁻¹ * delta1 := by
    have hhR : 1 ≤ (h : ℝ) := by exact_mod_cast hh
    have hprod : 1 ≤ xi * (h : ℝ) := by nlinarith
    calc
      M.delta ^ 2 ≤ (xi * (h : ℝ)) * M.delta ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) hprod
      _ = xi * M.delta ^ 2 * (h : ℝ) := by ring
      _ ≤ _ := hsmall
  have hmeanBudget : firstConst ^ 2 * M.delta ^ 4 ≤
      squareResponseQuarterNetEta d * delta1 ^ 2 := by
    have hsq := pow_le_pow_left₀ (sq_nonneg M.delta) hdeltaSq 2
    have hsq' : M.delta ^ 4 ≤ (K⁻¹ * delta1) ^ 2 := by
      calc
        M.delta ^ 4 = (M.delta ^ 2) ^ 2 := by ring
        _ ≤ _ := hsq
    calc
      firstConst ^ 2 * M.delta ^ 4 ≤
          firstConst ^ 2 * (K⁻¹ * delta1) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsq' (sq_nonneg firstConst)
      _ = (firstConst ^ 2 * K⁻¹ ^ 2) * delta1 ^ 2 := by ring
      _ ≤ squareResponseQuarterNetEta d * delta1 ^ 2 :=
        mul_le_mul_of_nonneg_right hKmean (sq_nonneg delta1)
  have hsuffixSmall : (sharpTwoBlockSmallnessConst d)⁻¹ *
      xi * M.delta ^ 2 * (h : ℝ) < 1 := by
    have hcoef : (sharpTwoBlockSmallnessConst d)⁻¹ * K⁻¹ ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_right hKsuffix (inv_nonneg.mpr hKpos.le)
      have hcancel : K * K⁻¹ = 1 := by field_simp
      nlinarith
    have hbound := mul_le_mul_of_nonneg_left hsmall
      (inv_nonneg.mpr (sharpTwoBlockSmallnessConst_pos d).le)
    have hdeltaOne : delta1 < 1 := hS.2.2.1
    calc
      (sharpTwoBlockSmallnessConst d)⁻¹ *
          xi * M.delta ^ 2 * (h : ℝ) ≤
          ((sharpTwoBlockSmallnessConst d)⁻¹ * K⁻¹) * delta1 := by
        calc
          _ = (sharpTwoBlockSmallnessConst d)⁻¹ *
              (xi * M.delta ^ 2 * (h : ℝ)) := by ring
          _ ≤ (sharpTwoBlockSmallnessConst d)⁻¹ *
              (K⁻¹ * delta1) := hbound
          _ = _ := by ring
      _ ≤ delta1 := by
        have := mul_le_mul_of_nonneg_right hcoef hdelta0
        nlinarith
      _ < 1 := hdeltaOne
  have hshell : 3 * secondBlockSpatialShellFactor d *
      xi * M.delta ^ 2 * (h : ℝ) ≤ (1 / 4 : ℝ) * delta1 := by
    have hscaled := mul_le_mul_of_nonneg_left hsmall
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
        (secondBlockSpatialShellFactor_pos d).le)
    have hcoef : 3 * secondBlockSpatialShellFactor d * K⁻¹ ≤ 1 / 4 := by
      have hmul := mul_le_mul_of_nonneg_right hKshell (inv_nonneg.mpr hKpos.le)
      have hcancel : K * K⁻¹ = 1 := by field_simp
      nlinarith
    calc
      3 * secondBlockSpatialShellFactor d *
          xi * M.delta ^ 2 * (h : ℝ) ≤
          (3 * secondBlockSpatialShellFactor d * K⁻¹) * delta1 := by
        calc
          _ = (3 * secondBlockSpatialShellFactor d) *
              (xi * M.delta ^ 2 * (h : ℝ)) := by ring
          _ ≤ (3 * secondBlockSpatialShellFactor d) *
              (K⁻¹ * delta1) := hscaled
          _ = _ := by ring
      _ ≤ (1 / 4 : ℝ) * delta1 :=
        mul_le_mul_of_nonneg_right hcoef hdelta0
  apply inductionHypothesis_extend hS
  intro r hmr hr
  let k := r - h
  have hkr : k < r := by dsimp only [k]; omega
  have hgap : r - k = h := by dsimp only [k]; omega
  have hkm : k ≤ m := by dsimp only [k]; omega
  exact headline_secondBlock_cutoff_update M hS hSFirst hxiFirst
    (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hfirstRadius (sq_nonneg M.delta))
    hmeanBudget hxiDim hxi hkm hkr hgap hh hlogSquare
      hsuffixSmall hshell hS.2.2.1.le

/-- Global second induction in the high-moment range.  The constants include
the fixed first-induction retained mean and every dimension-only coefficient
of the second block. -/
theorem exists_headline_highMomentSecondInduction {d : ℕ} [NeZero d]
    (hhomog : CoarseGrainedHomogenizationStepConclusion d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (xi : ℝ),
        16 * (d : ℝ) ≤ xi →
        C * xi * Real.log (2 + xi) * M.delta ^ 2 < c →
        inductionHypothesisInfinity M xi
          (C * xi * Real.log (2 + xi) * M.delta ^ 2) := by
  rcases exists_crude_induction_seed (d := d) with
    ⟨Cseed, hCseedPos, hseed⟩
  rcases exists_headline_fixedFirstInduction hhomog with
    ⟨cFirst, firstConst, hcFirst, hfirstConst, hfirst⟩
  let eta := squareResponseQuarterNetEta d
  let K : ℝ := max 1 (max (squareResponseAbsorptionConst d)
    (max (sharpTwoBlockSmallnessConst d)⁻¹
      (max (12 * secondBlockSpatialShellFactor d) (firstConst * eta⁻¹))))
  have heta : 0 < eta := by
    simpa only [eta] using squareResponseQuarterNetEta_pos (d := d)
  have hetaOne : eta ≤ 1 := by
    dsimp only [eta, squareResponseQuarterNetEta]
    have hcard : (1 : ℝ) ≤ ((sphereQuarterNet d).points.card : ℝ) := by
      exact_mod_cast (sphereQuarterNet_points_nonempty (d := d)).card_pos
    apply (inv_le_one₀ (by positivity : (0 : ℝ) <
      288 * ((sphereQuarterNet d).points.card : ℝ))).2
    nlinarith
  have hKone : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := zero_lt_one.trans_le hKone
  have hKsquare : squareResponseAbsorptionConst d ≤ K :=
    (le_max_left _ _).trans (le_max_right 1 _)
  have hKsuffix : (sharpTwoBlockSmallnessConst d)⁻¹ ≤ K :=
    (le_max_left _ _).trans (le_max_right _ _ |>.trans (le_max_right 1 _))
  have hKshell : 12 * secondBlockSpatialShellFactor d ≤ K :=
    (le_max_left _ _).trans
      (le_max_right _ _ |>.trans (le_max_right _ _ |>.trans (le_max_right 1 _)))
  have hKfirstEta : firstConst * eta⁻¹ ≤ K :=
    (le_max_right _ _).trans
      (le_max_right _ _ |>.trans (le_max_right _ _ |>.trans (le_max_right 1 _)))
  have hKmean : firstConst ^ 2 * K⁻¹ ^ 2 ≤ eta := by
    have hfirstEta : firstConst ≤ K * eta := by
      apply (div_le_iff₀ heta).mp
      simpa only [div_eq_mul_inv, mul_comm] using hKfirstEta
    have hfirstLe : firstConst * K⁻¹ ≤ eta := by
      rw [← div_eq_mul_inv]
      exact (div_le_iff₀ hK).2 (by simpa only [mul_comm] using hfirstEta)
    have hsq := pow_le_pow_left₀
      (mul_nonneg hfirstConst.le (inv_nonneg.mpr hK.le)) hfirstLe 2
    calc
      firstConst ^ 2 * K⁻¹ ^ 2 = (firstConst * K⁻¹) ^ 2 := by ring
      _ ≤ eta ^ 2 := hsq
      _ ≤ eta := by nlinarith
  let C : ℝ := max 1 (max firstConst
    (max (Cseed * (K + 1)) (K * (K + 1))))
  let c : ℝ := min 1 (min cFirst K⁻¹)
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hc : 0 < c := by
    dsimp only [c]
    exact lt_min zero_lt_one (lt_min hcFirst (inv_pos.mpr hK))
  refine ⟨c, C, hc, hC, ?_⟩
  intro M xi hxiDim hdeltaSmall
  let logXi : ℝ := Real.log (2 + xi)
  let h : ℕ := Nat.ceil (K * logXi)
  let delta1 : ℝ := C * xi * logXi * M.delta ^ 2
  have hxi : 1 ≤ xi := by
    have hd : (2 : ℕ) ≤ d := M.shellPrefix.dimension
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hlogXi : 1 ≤ logXi := by
    dsimp only [logXi]
    have hthree : (3 : ℝ) ≤ 2 + xi := by linarith
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hthree
    have hlogThree : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_d9.trans (by norm_num)
    linarith
  have hlogXi0 : 0 ≤ logXi := zero_le_one.trans hlogXi
  have hKlog0 : 0 ≤ K * logXi := mul_nonneg hK.le hlogXi0
  have hhLower : K * logXi ≤ (h : ℝ) := by
    dsimp only [h]
    exact Nat.le_ceil _
  have hhUpper : (h : ℝ) ≤ (K + 1) * logXi := by
    have hceil : (h : ℝ) < K * logXi + 1 := by
      dsimp only [h]
      exact Nat.ceil_lt_add_one hKlog0
    nlinarith
  have hh : 0 < h := by
    have : (0 : ℝ) < (h : ℝ) :=
      (mul_pos hK (zero_lt_one.trans_le hlogXi)).trans_le hhLower
    exact_mod_cast this
  have hCfirst : firstConst ≤ C :=
    (le_max_left _ _).trans (le_max_right 1 _)
  have hCseedBound : Cseed * (K + 1) ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _ |>.trans (le_max_right 1 _))
  have hCK : K * (K + 1) ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _ |>.trans (le_max_right 1 _))
  have hdelta0 : 0 < delta1 := by
    dsimp only [delta1]
    exact mul_pos (mul_pos (mul_pos hC (zero_lt_one.trans_le hxi))
      (zero_lt_one.trans_le hlogXi)) (sq_pos_of_pos M.shellPrefix.delta_pos)
  have hdeltaOne : delta1 < 1 := by
    dsimp only [delta1, c] at hdeltaSmall ⊢
    exact hdeltaSmall.trans_le (min_le_left _ _)
  have hdeltaK : delta1 ≤ K⁻¹ := by
    dsimp only [delta1, c] at hdeltaSmall ⊢
    exact hdeltaSmall.le.trans (min_le_right _ _ |>.trans (min_le_right _ _))
  have hfirstSmall : firstConst * M.delta ^ 2 < cFirst := by
    have hle : firstConst * M.delta ^ 2 ≤ delta1 := by
      dsimp only [delta1]
      have hxiLog : 1 ≤ xi * logXi := by nlinarith
      have hcoef : firstConst ≤ C * (xi * logXi) :=
        hCfirst.trans (le_mul_of_one_le_right hC.le hxiLog)
      nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg M.delta)]
    exact hle.trans_lt (hdeltaSmall.trans_le (min_le_right _ _ |>.trans
      (min_le_left _ _)))
  have hSFirst := hfirst M hfirstSmall
  have hseedLe : Cseed * xi * M.delta ^ 2 * (h : ℝ) ≤ delta1 := by
    dsimp only [delta1]
    have hhScaled := mul_le_mul_of_nonneg_left hhUpper hCseedPos.le
    have hboundScaled := mul_le_mul_of_nonneg_right hCseedBound hlogXi0
    have hcoef : Cseed * (h : ℝ) ≤ C * logXi := by
      calc
        Cseed * (h : ℝ) ≤ Cseed * ((K + 1) * logXi) := hhScaled
        _ = (Cseed * (K + 1)) * logXi := by ring
        _ ≤ C * logXi := hboundScaled
    have hmul := mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (show 0 ≤ xi by linarith) (sq_nonneg M.delta))
    nlinarith
  have hseedSmall : Cseed * xi * M.delta ^ 2 * (h : ℝ) < 1 :=
    hseedLe.trans_lt hdeltaOne
  have hseed0 := hseed M h xi hh hxi hseedSmall
  have hseedCommon : inductionHypothesis M (3 * h) xi delta1 :=
    coarseInductionHypothesis_mono_radius hseed0 hseedLe hdeltaOne
  have hsmall : xi * M.delta ^ 2 * (h : ℝ) ≤ K⁻¹ * delta1 := by
    have hcoef := mul_le_mul_of_nonneg_left hhUpper
      (mul_nonneg (show 0 ≤ xi by linarith) (sq_nonneg M.delta))
    have hCKscaled := mul_le_mul_of_nonneg_right hCK
      (mul_nonneg (mul_nonneg (show 0 ≤ xi by linarith) hlogXi0)
        (sq_nonneg M.delta))
    have hcancel : K⁻¹ * K = 1 := by field_simp
    dsimp only [delta1]
    calc
      xi * M.delta ^ 2 * (h : ℝ) ≤
          xi * M.delta ^ 2 * ((K + 1) * logXi) := by gcongr
      _ ≤ K⁻¹ * (C * xi * logXi * M.delta ^ 2) := by
        have hscaled := mul_le_mul_of_nonneg_left hCKscaled
          (inv_nonneg.mpr hK.le)
        calc
          xi * M.delta ^ 2 * ((K + 1) * logXi) =
              K⁻¹ * (K * (K + 1) * (xi * logXi * M.delta ^ 2)) := by
            field_simp [hK.ne']
          _ ≤ K⁻¹ * (C * (xi * logXi * M.delta ^ 2)) := hscaled
          _ = _ := by ring
  have hsmall' : K⁻¹ * delta1 ≤ K⁻¹ ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_left hdeltaK (inv_nonneg.mpr hK.le)
  exact inductionHypothesisInfinity_of_seed_and_block_step M h hh hseedCommon
    (fun m hm hS => headline_secondBlock_implication
      (xiFirst := 16 * (d : ℝ)) (deltaFirst := firstConst)
      (firstConst := firstConst) (K := K)
      M hSFirst (by
        have hd : (2 : ℕ) ≤ d := M.shellPrefix.dimension
        exact_mod_cast (show (2 : ℕ) ≤ 16 * d by omega)) le_rfl
      hK hKsquare hKsuffix hKshell hKmean m h xi delta1 hh hm hxiDim
        hhLower hsmall hsmall' hS)

/-- The high-moment induction plus Lyapunov monotonicity supplies the full
`xi ≥ 1` response range, with one enlarged dimension-only coefficient. -/
theorem exists_headline_allMomentSecondInduction {d : ℕ} [NeZero d]
    (hhomog : CoarseGrainedHomogenizationStepConclusion d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (xi : ℝ),
        1 ≤ xi →
        C * xi * Real.log (2 + xi) * M.delta ^ 2 < c →
        inductionHypothesisInfinity M xi
          (C * xi * Real.log (2 + xi) * M.delta ^ 2) := by
  rcases exists_headline_highMomentSecondInduction hhomog with
    ⟨c0, C0, hc0, hC0, hhigh⟩
  let xi0 : ℝ := 16 * (d : ℝ)
  let B : ℝ := max 1 (xi0 * Real.log (2 + xi0))
  let C : ℝ := C0 * B
  let c : ℝ := min c0 1
  have hxi0 : 1 ≤ xi0 := by
    have hd : (1 : ℕ) ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    dsimp only [xi0]
    exact_mod_cast (show (1 : ℕ) ≤ 16 * d by omega)
  have hlogXi0 : 1 ≤ Real.log (2 + xi0) := by
    have hthree : (3 : ℝ) ≤ 2 + xi0 := by linarith
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hthree
    have hlogThree : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_d9.trans (by norm_num)
    linarith
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hC : 0 < C := mul_pos hC0 hB
  have hc : 0 < c := lt_min hc0 zero_lt_one
  refine ⟨c, C, hc, hC, ?_⟩
  intro M xi hxi hsmall
  let delta1 : ℝ := C * xi * Real.log (2 + xi) * M.delta ^ 2
  have hlogXi : 1 ≤ Real.log (2 + xi) := by
    have hthree : (3 : ℝ) ≤ 2 + xi := by linarith
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hthree
    have hlogThree : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_one_lt_d9.trans (by norm_num)
    linarith
  have hdeltaPos : 0 < delta1 := by
    dsimp only [delta1]
    exact mul_pos
      (mul_pos (mul_pos hC (zero_lt_one.trans_le hxi))
        (zero_lt_one.trans_le hlogXi))
      (sq_pos_of_pos M.shellPrefix.delta_pos)
  have hdeltaOne : delta1 < 1 :=
    hsmall.trans_le (min_le_right _ _)
  by_cases hxiHigh : xi0 ≤ xi
  · have hC0C : C0 ≤ C := by
      dsimp only [C]
      exact le_mul_of_one_le_right hC0.le (le_max_left _ _)
    have hsmall0 : C0 * xi * Real.log (2 + xi) * M.delta ^ 2 < c0 := by
      have hle : C0 * xi * Real.log (2 + xi) * M.delta ^ 2 ≤
          C * xi * Real.log (2 + xi) * M.delta ^ 2 := by
        calc
          _ = C0 * (xi * Real.log (2 + xi) * M.delta ^ 2) := by ring
          _ ≤ C * (xi * Real.log (2 + xi) * M.delta ^ 2) :=
            mul_le_mul_of_nonneg_right hC0C
              (mul_nonneg (mul_nonneg (zero_le_one.trans hxi)
                (zero_le_one.trans hlogXi)) (sq_nonneg M.delta))
          _ = _ := by ring
      exact hle.trans_lt (hsmall.trans_le (min_le_left _ _))
    have hS0 := hhigh M xi hxiHigh hsmall0
    exact coarseInductionHypothesisInfinity_mono_radius hS0 (by
      calc
        C0 * xi * Real.log (2 + xi) * M.delta ^ 2 =
            C0 * (xi * Real.log (2 + xi) * M.delta ^ 2) := by ring
        _ ≤ C * (xi * Real.log (2 + xi) * M.delta ^ 2) :=
          mul_le_mul_of_nonneg_right hC0C
            (mul_nonneg (mul_nonneg (zero_le_one.trans hxi)
              (zero_le_one.trans hlogXi)) (sq_nonneg M.delta))
        _ = _ := by ring)
      hdeltaOne
  · have hxiLe : xi ≤ xi0 := le_of_not_ge hxiHigh
    have hbaseCoeff : C0 * xi0 * Real.log (2 + xi0) ≤
        C * xi * Real.log (2 + xi) := by
      have hbaseB : xi0 * Real.log (2 + xi0) ≤ B := le_max_right _ _
      have hxiLog : 1 ≤ xi * Real.log (2 + xi) := by nlinarith
      dsimp only [C]
      calc
        C0 * xi0 * Real.log (2 + xi0) =
            C0 * (xi0 * Real.log (2 + xi0)) := by ring
        _ ≤ C0 * B := mul_le_mul_of_nonneg_left hbaseB hC0.le
        _ ≤ C0 * B * (xi * Real.log (2 + xi)) :=
          le_mul_of_one_le_right (mul_nonneg hC0.le hB.le) hxiLog
        _ = _ := by ring
    have hbaseSmall : C0 * xi0 * Real.log (2 + xi0) * M.delta ^ 2 < c0 := by
      have hle := mul_le_mul_of_nonneg_right hbaseCoeff (sq_nonneg M.delta)
      exact hle.trans_lt (hsmall.trans_le (min_le_left _ _))
    have hS0 := hhigh M xi0 le_rfl hbaseSmall
    apply inductionHypothesisInfinity_of_scale_bounds M hxi hdeltaPos hdeltaOne
    intro m
    have hnorm0 := (le_iSup (fun r : ℕ =>
      paperENNRealLpNorm M.P.toMeasure xi0
        (normalizedDefectAt M r r)) m).trans hS0.2.2.2
    have hmono := normalizedDefect_paperLpNorm_mono_exponent M m m
      (zero_lt_one.trans_le hxi) hxiLe
    exact hmono.trans (hnorm0.trans (ENNReal.ofReal_le_ofReal (by
      dsimp only [delta1]
      exact mul_le_mul_of_nonneg_right hbaseCoeff (sq_nonneg M.delta))))

private theorem log_two_add_xi_le_six_abs_log_delta
    {C xi delta : ℝ} (hC : 1 ≤ C) (hxi : 1 ≤ xi)
    (hdelta : 0 < delta) (hhalf : delta ≤ (1 : ℝ) / 2)
    (hupper : xi ≤ C⁻¹ * (delta ^ 2)⁻¹ * |Real.log delta|⁻¹) :
    Real.log (2 + xi) ≤ 6 * |Real.log delta| := by
  let L := |Real.log delta|
  have hdeltaOne : delta ≤ 1 := hhalf.trans (by norm_num)
  have hlogNonpos : Real.log delta ≤ 0 := Real.log_nonpos hdelta.le hdeltaOne
  have hL : (1 / 2 : ℝ) ≤ L := by
    dsimp only [L]
    rw [abs_of_nonpos hlogNonpos]
    have hmono : Real.log delta ≤ Real.log ((1 : ℝ) / 2) :=
      Real.log_le_log hdelta hhalf
    have hhalfLog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
      simp
    rw [hhalfLog] at hmono
    have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hCinv : C⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_one.trans_le hC)).2 hC
  have hLinv : L⁻¹ ≤ 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hL
      (inv_nonneg.mpr hLpos.le)
    have hcancel : L * L⁻¹ = 1 := by field_simp
    nlinarith
  have hdeltaInv0 : 0 ≤ (delta ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg delta)
  have hxiUpper : xi ≤ 2 * (delta ^ 2)⁻¹ := by
    calc
      xi ≤ C⁻¹ * (delta ^ 2)⁻¹ * L⁻¹ := by simpa only [L] using hupper
      _ ≤ 1 * (delta ^ 2)⁻¹ * 2 := by
        calc
          C⁻¹ * (delta ^ 2)⁻¹ * L⁻¹ ≤
              1 * (delta ^ 2)⁻¹ * L⁻¹ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCinv hdeltaInv0)
              (inv_nonneg.mpr hLpos.le)
          _ ≤ 1 * (delta ^ 2)⁻¹ * 2 :=
            mul_le_mul_of_nonneg_left hLinv (by positivity)
      _ = 2 * (delta ^ 2)⁻¹ := by ring
  have hdeltaInv : 4 ≤ (delta ^ 2)⁻¹ := by
    have hinv : (2 : ℝ) ≤ delta⁻¹ := by
      have htwoDelta : 2 * delta ≤ 1 := by nlinarith
      have hscaled := mul_le_mul_of_nonneg_right htwoDelta
        (inv_nonneg.mpr hdelta.le)
      have hcancel : delta * delta⁻¹ = 1 := by field_simp
      nlinarith
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hinv 2
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ delta⁻¹ ^ 2 := hsq
      _ = (delta ^ 2)⁻¹ := by rw [inv_pow]
  have harg : 2 + xi ≤ 3 * (delta ^ 2)⁻¹ := by nlinarith
  have hlog := Real.log_le_log (by linarith) harg
  have hlogRight : Real.log (3 * (delta ^ 2)⁻¹) =
      Real.log 3 + 2 * L := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (inv_ne_zero (pow_ne_zero 2 hdelta.ne')),
      Real.log_inv, Real.log_pow]
    dsimp only [L]
    rw [abs_of_nonpos hlogNonpos]
    ring
  rw [hlogRight] at hlog
  have hlogThree : Real.log 3 ≤ 2 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)).trans_eq (by norm_num)
  nlinarith

private theorem headline_radius_le_six_mul_inv
    {C R xi delta : ℝ} (hC : 0 < C) (hR : 0 ≤ R) (hxi : 0 ≤ xi)
    (hdelta : 0 < delta) (hLpos : 0 < |Real.log delta|)
    (hupper : xi ≤ C⁻¹ * (delta ^ 2)⁻¹ * |Real.log delta|⁻¹)
    (hlog : Real.log (2 + xi) ≤ 6 * |Real.log delta|) :
    R * xi * Real.log (2 + xi) * delta ^ 2 ≤ 6 * R * C⁻¹ := by
  have hscaled := mul_le_mul_of_nonneg_right hupper
    (mul_nonneg (sq_nonneg delta) (abs_nonneg (Real.log delta)))
  have hxiL : xi * (delta ^ 2 * |Real.log delta|) ≤ C⁻¹ := by
    calc
      xi * (delta ^ 2 * |Real.log delta|) ≤
          (C⁻¹ * (delta ^ 2)⁻¹ * |Real.log delta|⁻¹) *
            (delta ^ 2 * |Real.log delta|) := hscaled
      _ = C⁻¹ := by
        field_simp [hdelta.ne', hLpos.ne']
  have hlogScaled := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg hxi (sq_nonneg delta))
  have hbase : xi * Real.log (2 + xi) * delta ^ 2 ≤ 6 * C⁻¹ := by
    calc
      xi * Real.log (2 + xi) * delta ^ 2 =
          (xi * delta ^ 2) * Real.log (2 + xi) := by ring
      _ ≤ (xi * delta ^ 2) * (6 * |Real.log delta|) := hlogScaled
      _ = 6 * (xi * (delta ^ 2 * |Real.log delta|)) := by ring
      _ ≤ 6 * C⁻¹ := mul_le_mul_of_nonneg_left hxiL (by norm_num)
  calc
    R * xi * Real.log (2 + xi) * delta ^ 2 =
        R * (xi * Real.log (2 + xi) * delta ^ 2) := by ring
    _ ≤ R * (6 * C⁻¹) := mul_le_mul_of_nonneg_left hbase hR
    _ = 6 * R * C⁻¹ := by ring

/-- Conditional provider for the frozen `p.coarse.grained.bound` export.
The only premises are the byte-exact conclusions of the two still-draft
Section 4 anchors. -/
theorem coarse_grained_bound {d : ℕ}
    (hcombine : CoarseGrainedCombineConclusion d)
    (hhomog : CoarseGrainedHomogenizationStepConclusion d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (xi : ℝ),
        1 ≤ xi →
        xi ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ m : ℕ,
          paperENNRealLpNorm M.P.toMeasure xi
              (normalizedDefect M m
                (Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))) ≤
            ENNReal.ofReal (C * xi * Real.log (2 + xi) * M.delta ^ 2) ∧
          ∀ s : ℝ, 0 < s → s ≤ 1 →
            4 * (d : ℝ) * s⁻¹ ≤ xi →
            C * xi * Real.log (2 + xi) * M.delta ^ 2 ≤ c * s →
            c ≤ s * Real.log (2 + xi) →
            paperENNRealLpNorm M.P.toMeasure xi
                (homogenizationErrorRandom M m m s) ≤
              ENNReal.ofReal
                (C * s⁻¹ * Real.sqrt
                  (xi * Real.log (2 + xi) * M.delta ^ 2)) := by
  let _combineWitness : CoarseGrainedCombineConclusion d := hcombine
  by_cases hd : d = 0
  · subst d
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro M
    have hdim := M.shellPrefix.dimension
    omega
  · letI : NeZero d := ⟨hd⟩
    rcases exists_headline_allMomentSecondInduction hhomog with
      ⟨cR, CR, hcR, hCR, hresponse⟩
    rcases SubdiffusiveProcess.Frozen.Section4.ellipticity_bound (d := d) with
      ⟨cE, CE, hcE, hcE1, hCE, helliptic⟩
    let small : ℝ := min cR 1
    let c : ℝ := small / 2
    let R : ℝ := max 1 (max CR (2 * (cE * small)⁻¹))
    let C : ℝ := 1 + R + CE * Real.sqrt R + 12 * R * small⁻¹
    have hSmallDef : small = min cR 1 := rfl
    have hCDef : C = 1 + R + CE * Real.sqrt R + 12 * R * small⁻¹ := rfl
    have hRDef : R = max 1 (max CR (2 * (cE * small)⁻¹)) := rfl
    have hCDefLower : c = small / 2 := rfl
    have hsmall : 0 < small := lt_min hcR zero_lt_one
    have hc : 0 < c := div_pos hsmall (by norm_num)
    have hR1 : 1 ≤ R := le_max_left _ _
    have hR0 : 0 ≤ R := zero_le_one.trans hR1
    have hCRR : CR ≤ R := (le_max_left CR _).trans (le_max_right _ _)
    have hRlarge : 2 * (cE * small)⁻¹ ≤ R :=
      (le_max_right CR _).trans (le_max_right _ _)
    have hC1 : 1 ≤ C := by
      rw [hCDef]
      have hsqrt : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
      have hinv : 0 ≤ small⁻¹ := inv_nonneg.mpr hsmall.le
      nlinarith [mul_nonneg (zero_le_one.trans hCE) hsqrt,
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hR0) hinv]
    have hC : 0 < C := zero_lt_one.trans_le hC1
    have hRC : R ≤ C := by
      rw [hCDef]
      have hsqrt : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
      have hinv : 0 ≤ small⁻¹ := inv_nonneg.mpr hsmall.le
      nlinarith [mul_nonneg (zero_le_one.trans hCE) hsqrt,
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hR0) hinv]
    have hCEC : CE * Real.sqrt R ≤ C := by
      rw [hCDef]
      have hsqrt : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
      have hinv : 0 ≤ small⁻¹ := inv_nonneg.mpr hsmall.le
      nlinarith [mul_nonneg (zero_le_one.trans hCE) hsqrt,
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hR0) hinv]
    have hCabsorb : 12 * R * small⁻¹ ≤ C := by
      rw [hCDef]
      have hsqrt : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
      nlinarith [mul_nonneg (zero_le_one.trans hCE) hsqrt]
    have hEc : 1 ≤ cE * R * c := by
      have hfactor : 0 ≤ cE * c := mul_nonneg hcE.le hc.le
      have hscaled := mul_le_mul_of_nonneg_left hRlarge hfactor
      calc
        (1 : ℝ) = cE * (2 * (cE * small)⁻¹) * c := by
          dsimp only [c]
          field_simp [hcE.ne', hsmall.ne']
        _ = (cE * c) * (2 * (cE * small)⁻¹) := by ring
        _ ≤ (cE * c) * R := hscaled
        _ = cE * R * c := by ring
    clear_value small c R C
    refine ⟨c, C, hc, hC, ?_⟩
    intro M xi hxi hupper m
    have hlog : 1 ≤ Real.log (2 + xi) := by
      have hthree : (3 : ℝ) ≤ 2 + xi := by linarith
      have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hthree
      have hlogThree : 1 < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
        exact Real.exp_one_lt_d9.trans (by norm_num)
      linarith
    have hlogDelta := log_two_add_xi_le_six_abs_log_delta hC1 hxi
      M.shellPrefix.delta_pos M.shellPrefix.delta_le_half hupper
    have hLpos : 0 < |Real.log M.delta| := by
      apply abs_pos.mpr
      exact ne_of_lt (Real.log_neg M.shellPrefix.delta_pos
        (M.shellPrefix.delta_le_half.trans_lt (by norm_num)))
    let base : ℝ := xi * Real.log (2 + xi) * M.delta ^ 2
    let delta1 : ℝ := R * base
    have hbase : 0 < base := by
      dsimp only [base]
      exact mul_pos (mul_pos (zero_lt_one.trans_le hxi)
        (zero_lt_one.trans_le hlog))
        (sq_pos_of_pos M.shellPrefix.delta_pos)
    have hdelta1 : 0 < delta1 := mul_pos (zero_lt_one.trans_le hR1) hbase
    have hdeltaUpper : delta1 ≤ small / 2 := by
      have hradius := headline_radius_le_six_mul_inv hC hR0
        (zero_le_one.trans hxi) M.shellPrefix.delta_pos hLpos hupper hlogDelta
      have hsmallInv : 0 ≤ small⁻¹ := inv_nonneg.mpr hsmall.le
      have hscaled := mul_le_mul_of_nonneg_right hCabsorb
        (mul_nonneg (by positivity : 0 ≤ C⁻¹) (by positivity : 0 ≤ small))
      have hinvC : C * C⁻¹ = 1 := by field_simp [hC.ne']
      have hinvSmall : small⁻¹ * small = 1 := by field_simp [hsmall.ne']
      have hsix : 6 * R * C⁻¹ ≤ small / 2 := by
        nlinarith
      dsimp only [delta1, base]
      calc
        R * (xi * Real.log (2 + xi) * M.delta ^ 2) =
            R * xi * Real.log (2 + xi) * M.delta ^ 2 := by ring
        _ ≤ 6 * R * C⁻¹ := hradius
        _ ≤ small / 2 := hsix
    have hdeltaOne : delta1 < 1 :=
      hdeltaUpper.trans_lt (by rw [hSmallDef]; linarith [min_le_right cR 1])
    have hCRsmall : CR * base < cR := by
      have hle : CR * base ≤ delta1 := by
        dsimp only [delta1]
        exact mul_le_mul_of_nonneg_right hCRR hbase.le
      exact hle.trans_lt (hdeltaUpper.trans_lt (by
        rw [hSmallDef]
        have hmin := min_le_left cR 1
        linarith))
    have hS0 := hresponse M xi hxi (by
      simpa only [base, mul_assoc] using hCRsmall)
    have hS : inductionHypothesisInfinity M xi delta1 :=
      coarseInductionHypothesisInfinity_mono_radius hS0 (by
        have hle := mul_le_mul_of_nonneg_right hCRR hbase.le
        simpa only [delta1, base, mul_assoc] using hle) hdeltaOne
    constructor
    · have hm := (le_iSup (fun r : ℕ =>
          paperENNRealLpNorm M.P.toMeasure xi (normalizedDefectAt M r r)) m).trans
          hS.2.2.2
      exact hm.trans (ENNReal.ofReal_le_ofReal (by
        have hle := mul_le_mul_of_nonneg_right hRC hbase.le
        simpa only [delta1, base, mul_assoc] using hle))
    · intro s hs hs1 hdim hsmallScale hcScale
      have hsInv : 1 ≤ s⁻¹ := by
        have hscaled := mul_le_mul_of_nonneg_right hs1 (inv_nonneg.mpr hs.le)
        have hcancel : s * s⁻¹ = 1 := by field_simp [hs.ne']
        simpa only [hcancel, one_mul] using hscaled
      have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast M.shellPrefix.dimension
      have hprod : (2 : ℝ) * 1 ≤ (d : ℝ) * s⁻¹ :=
        mul_le_mul hdreal hsInv (by norm_num) (by positivity)
      have hxi6 : 6 ≤ xi := by
        have : (6 : ℝ) ≤ 4 * (d : ℝ) * s⁻¹ := by nlinarith only [hprod]
        exact this.trans hdim
      have hdeltaSq : M.delta ^ 2 ≤ delta1 := by
        dsimp only [delta1, base]
        have hRxi : 1 ≤ R * xi := by
          simpa only [one_mul] using
            mul_le_mul hR1 hxi (by norm_num : (0 : ℝ) ≤ 1) hR0
        have hcoeff : 1 ≤ R * xi * Real.log (2 + xi) := by
          simpa only [one_mul] using
            mul_le_mul hRxi hlog (by norm_num : (0 : ℝ) ≤ 1)
              (mul_nonneg hR0 (zero_le_one.trans hxi))
        have hmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg M.delta)
        simpa only [one_mul, mul_assoc] using hmul
      have hEllSmall : xi ≤ cE * s * (M.delta ^ 2)⁻¹ * delta1 := by
        have hcoef : 1 ≤ cE * R * (s * Real.log (2 + xi)) :=
          hEc.trans (mul_le_mul_of_nonneg_left hcScale
            (mul_nonneg hcE.le hR0))
        calc
          xi ≤ (cE * R * (s * Real.log (2 + xi))) * xi :=
            le_mul_of_one_le_left (zero_le_one.trans hxi) hcoef
          _ = cE * s * (M.delta ^ 2)⁻¹ * delta1 := by
            dsimp only [delta1, base]
            field_simp [M.shellPrefix.delta_pos.ne']
      have hfinite := inductionHypothesis_of_infinity (m0 := m) hS
      have herr := (helliptic M m xi delta1 hxi6 hdeltaSq hdeltaOne hfinite
        s hs hs1 hdim hEllSmall).2 m le_rfl
      apply herr.trans
      apply ENNReal.ofReal_le_ofReal
      have hsInv0 : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
      have hsqrtR : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
      have hsqrtBase : 0 ≤ Real.sqrt base := Real.sqrt_nonneg base
      have hcoef := mul_le_mul_of_nonneg_right hCEC
        (mul_nonneg hsInv0 hsqrtBase)
      calc
        CE * s⁻¹ * Real.sqrt delta1 =
            (CE * Real.sqrt R) * (s⁻¹ * Real.sqrt base) := by
          dsimp only [delta1]
          rw [Real.sqrt_mul hR0]
          ring
        _ ≤ C * (s⁻¹ * Real.sqrt base) := hcoef
        _ = C * s⁻¹ * Real.sqrt
            (xi * Real.log (2 + xi) * M.delta ^ 2) := by
          dsimp only [base]
          ring

end

end SubdiffusiveProcess.Providers.Section4
