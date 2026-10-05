module

public import SubdiffusiveProcess.Static.AnchoredTailComparison
public import SubdiffusiveProcess.Static.CutoffMassMomentBound
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables

@[expose] public section

/-! # Uniform moments of a tail factor on a fixed enlarged window -/

open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The enlarged-window tail factor at a translated physical centre. -/
def localTailFactor {d : ℕ} (J m : ℕ) (z : Vec d) (ω : PotentialSample d) : ℝ :=
  1 + cutoffChangeSuffixRepresentative m ((m : ℤ) + (J : ℤ))
    (translatePotentialSample z ω)

theorem measurable_localTailFactor {d : ℕ} (J m : ℕ) (z : Vec d) :
    Measurable (localTailFactor J m z) := by
  have h := (measurable_cutoffChangeSuffixRepresentative (d := d) m
    ((m : ℤ) + (J : ℤ))).mono (potentialShellIndexSigma_le_borel _) le_rfl
  exact measurable_const.add (h.comp (measurable_translatePotentialSample z))

theorem one_le_localTailFactor {d : ℕ} (J m : ℕ) (z : Vec d) (ω : PotentialSample d) :
    1 ≤ localTailFactor J m z ω :=
  le_add_of_nonneg_right (cutoffChangeSuffixRepresentative_nonneg _ _ _)

private theorem eLpNorm_nonneg_eq_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {q : ℝ} (hq : 0 < q) {W : Ω → ℝ}
    (hW : ∀ ω, 0 ≤ W ω) (hint : Integrable (fun ω => W ω ^ q) μ) :
    SubdiffusiveProcess.RawLp.eLpNorm W (ENNReal.ofReal q) μ = ENNReal.ofReal ((∫ ω, W ω ^ q ∂μ) ^ q⁻¹) := by
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (ENNReal.ofReal_pos.mpr hq).ne'
    ENNReal.ofReal_ne_top W μ, ENNReal.toReal_ofReal hq.le, one_div]
  have hpoint : ∀ ω, ‖W ω‖ₑ ^ q = ENNReal.ofReal (W ω ^ q) := by
    intro ω
    rw [Real.enorm_eq_ofReal (hW ω), ENNReal.ofReal_rpow_of_nonneg (hW ω) hq.le]
  simp_rw [hpoint]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hW ω) q)]
  exact ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun ω => Real.rpow_nonneg (hW ω) q)
    (inv_nonneg.mpr hq.le)

/-- The norm of the unshifted enlarged-window representative is uniform
in the parent scale, at every fixed moment order. -/
theorem enlarged_tail_norm_le {d : ℕ} (M : GMCModel d) (hM : M.delta ≤ 1)
    (J m : ℕ) {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (cutoffChangeSuffixRepresentative (d := d) m ((m : ℤ) + (J : ℤ)))
      (ENNReal.ofReal q) M.P.toMeasure ≤
      ENNReal.ofReal (2 * Homogenization.Book.Ch04.gammaMomentConst 2 *
        Real.sqrt (2 * q) * (shellSensitivityConst d * (3 : ℝ) ^ J) *
        Real.exp (q * (shellSensitivityConst d * (3 : ℝ) ^ J) ^ 2)) := by
  have hraw := cutoffChangeSuffixRepresentative_moment M m ((m : ℤ) + (J : ℤ)) q hq
  dsimp only at hraw
  rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
    ((measurable_cutoffChangeSuffixRepresentative (d := d) m ((m : ℤ) + (J : ℤ))).mono
      (potentialShellIndexSigma_le_borel _) le_rfl).aestronglyMeasurable]
  rw [eLpNorm_nonneg_eq_moment M.P.toMeasure (zero_lt_one.trans_le hq)
    (fun ω => cutoffChangeSuffixRepresentative_nonneg _ _ ω) hraw.1]
  apply ENNReal.ofReal_le_ofReal
  refine hraw.2.trans ?_
  have hgamma : 0 < Homogenization.Book.Ch04.gammaMomentConst 2 := by
    simpa using! Homogenization.IndependentSums.gammaMomentConst_pos
      (by norm_num : (0 : ℝ) < 2)
  have hs : 0 < shellSensitivityConst d := shellSensitivityConst_pos d
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  have hbase : shellSensitivityConst d * M.delta * (3 : ℝ) ^
      (((m : ℤ) + (J : ℤ)) - (m : ℤ)) ≤ shellSensitivityConst d * (3 : ℝ) ^ J := by
    simp only [add_sub_cancel_left, zpow_natCast]
    calc
      _ ≤ shellSensitivityConst d * 1 * (3 : ℝ) ^ J := by gcongr
      _ = _ := by ring
  have hbase0 : 0 ≤ shellSensitivityConst d * M.delta * (3 : ℝ) ^
      (((m : ℤ) + (J : ℤ)) - (m : ℤ)) := by positivity
  gcongr

/-- Moments of the translated physical tail factor are uniform in scale
and real centre. The disorder restriction is the fixed bound `δ ≤ 1`. -/
theorem exists_localTailFactor_moment_bound (d J : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : GMCModel d), M.delta ≤ 1 → ∀ m : ℕ, ∀ z : Vec d,
      (∫⁻ ω, ENNReal.ofReal (localTailFactor J m z ω ^ q) ∂M.P.toMeasure) ≤
        ENNReal.ofReal C := by
  let B := 2 * Homogenization.Book.Ch04.gammaMomentConst 2 * Real.sqrt (2 * q) *
    (shellSensitivityConst d * (3 : ℝ) ^ J) *
      Real.exp (q * (shellSensitivityConst d * (3 : ℝ) ^ J) ^ 2)
  have hgamma : 0 < Homogenization.Book.Ch04.gammaMomentConst 2 := by
    simpa using! Homogenization.IndependentSums.gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2)
  have hs : 0 < shellSensitivityConst d := shellSensitivityConst_pos d
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨(1 + B) ^ q, by positivity, ?_⟩
  intro M hM m z
  let W := cutoffChangeSuffixRepresentative (d := d) m ((m : ℤ) + (J : ℤ))
  have hW : Measurable W := (measurable_cutoffChangeSuffixRepresentative _ _).mono
    (potentialShellIndexSigma_le_borel _) le_rfl
  have hnorm : eLpNorm (W ∘ translatePotentialSample z) (ENNReal.ofReal q) M.P.toMeasure ≤
      ENNReal.ofReal B := by
    rw [eLpNorm_comp_measurePreserving hW.aestronglyMeasurable
      (measurePreserving_translatePotentialSample M z)]
    exact enlarged_tail_norm_le M hM J m hq
  have hconst : eLpNorm (fun _ : PotentialSample d => (1 : ℝ)) (ENNReal.ofReal q)
      M.P.toMeasure = 1 := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hq)).ne'
      (NeZero.ne M.P.toMeasure)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one, enorm_one]
  have hF : eLpNorm (localTailFactor J m z) (ENNReal.ofReal q) M.P.toMeasure ≤
      ENNReal.ofReal (1 + B) := by
    refine (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hq)).trans ?_
    rw [hconst]
    refine (add_le_add le_rfl hnorm).trans_eq ?_
    rw [ENNReal.ofReal_add zero_le_one hB, ENNReal.ofReal_one]
  rw [SubdiffusiveProcess.Static.lintegral_rpow_eq_eLpNorm_rpow_of_aestronglyMeasurable M.P.toMeasure
    (localTailFactor J m z) (fun ω => zero_le_one.trans (one_le_localTailFactor J m z ω))
    (zero_lt_one.trans_le hq)
    (measurable_localTailFactor J m z).aestronglyMeasurable]
  exact (ENNReal.rpow_le_rpow hF (zero_le_one.trans hq)).trans_eq
    (ENNReal.ofReal_rpow_of_nonneg (by positivity) (zero_le_one.trans hq))

/-- Almost surely the same tail factor compares every finite cutoff above
the physical scale, and the infinite cutoff, throughout the enlarged window. -/
theorem ae_localDensity_tail_comparison {d : ℕ} (M : GMCModel d) (J m : ℕ) (z : Vec d) :
    ∀ᵐ ω ∂localAnchoredLaw M, ∀ L : WithTop ℕ, (m : WithTop ℕ) ≤ L → ∀ x : Vec d,
      (3 : ℝ) ^ m • x ∈ Homogenization.openCubeSet
        (Homogenization.originCube d ((m : ℤ) + (J : ℤ))) →
      (localTailFactor J m z ω.1)⁻¹ * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) ≤
        SubdiffusiveProcess.Static.localDensity M L m z ω x ∧
      SubdiffusiveProcess.Static.localDensity M L m z ω x ≤
        localTailFactor J m z ω.1 * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) := by
  have ht := (measurePreserving_translatePotentialSample M z).quasiMeasurePreserving.ae
    (ae_tail_pair_ratios_on_cube M m ((m : ℤ) + (J : ℤ)))
  filter_upwards [(measurePreserving_anchoredVal M).quasiMeasurePreserving.ae ht]
    with ω hω
  intro L hmL x hx
  have hF : 0 < localTailFactor J m z ω.1 :=
    zero_lt_one.trans_le (one_le_localTailFactor J m z ω.1)
  have hzero : (0 : Vec d) ∈ Homogenization.openCubeSet
      (Homogenization.originCube d ((m : ℤ) + (J : ℤ))) := by
    rw [Homogenization.mem_openCubeSet_originCube_iff]
    intro i
    simp only [Pi.zero_apply]
    constructor
    · have hp := zpow_pos (by norm_num : (0 : ℝ) < 3) ((m : ℤ) + (J : ℤ))
      linarith
    · positivity
  have hfinite : ∀ L : ℕ, m ≤ L →
      (localTailFactor J m z ω.1)⁻¹ * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) ≤
        SubdiffusiveProcess.Static.localDensity M (L : WithTop ℕ) m z ω x ∧
      SubdiffusiveProcess.Static.localDensity M (L : WithTop ℕ) m z ω x ≤
        localTailFactor J m z ω.1 * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) := by
    intro L hL
    apply finite_localDensity_comparison M hL z ω x hF
    · have h := hω L hL ((3 : ℝ) ^ m • x) 0 hx hzero
      simp only [aCutoff_translatePotentialSample, zero_add] at h
      rw [add_comm ((3 : ℝ) ^ m • x) z] at h
      have := le_abs_self ((aCutoff M L ω.1 (z + (3 : ℝ) ^ m • x) /
        aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x)) /
          (aCutoff M L ω.1 z / aCutoff M m ω.1 z) - 1)
      change _ ≤ 1 + _
      linarith
    · have h := hω L hL 0 ((3 : ℝ) ^ m • x) hzero hx
      simp only [aCutoff_translatePotentialSample, zero_add] at h
      rw [add_comm ((3 : ℝ) ^ m • x) z] at h
      have := le_abs_self ((aCutoff M L ω.1 z / aCutoff M m ω.1 z) /
        (aCutoff M L ω.1 (z + (3 : ℝ) ^ m • x) /
          aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x)) - 1)
      change _ ≤ 1 + _
      linarith
  cases L using WithTop.recTopCoe
  · exact full_localDensity_comparison M m z ω x _ hfinite
  · exact hfinite _ (WithTop.coe_le_coe.mp hmL)

/-- A closed moment-and-comparison supplier for all finite and infinite
infrared tails. No law completion or chosen infrared field is required. -/
theorem exists_uniform_local_tail_comparison (d J : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : GMCModel d), M.delta ≤ 1 → ∀ m : ℕ, ∀ z : Vec d,
      ∃ F : AnchoredC11Sample d → ℝ, Measurable F ∧ (∀ ω, 1 ≤ F ω) ∧
        (∫⁻ ω, ENNReal.ofReal (F ω ^ q) ∂localAnchoredLaw M) ≤ ENNReal.ofReal C ∧
        ∀ᵐ ω ∂localAnchoredLaw M, ∀ L : WithTop ℕ, (m : WithTop ℕ) ≤ L → ∀ x : Vec d,
          (3 : ℝ) ^ m • x ∈ Homogenization.openCubeSet
            (Homogenization.originCube d ((m : ℤ) + (J : ℤ))) →
          (F ω)⁻¹ * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) ≤
            SubdiffusiveProcess.Static.localDensity M L m z ω x ∧
          SubdiffusiveProcess.Static.localDensity M L m z ω x ≤
            F ω * aCutoff M m ω.1 (z + (3 : ℝ) ^ m • x) := by
  obtain ⟨C, hC, hmoment⟩ := exists_localTailFactor_moment_bound d J q hq
  refine ⟨C, hC, ?_⟩
  intro M hM m z
  refine ⟨fun ω => localTailFactor J m z ω.1,
    (measurable_localTailFactor J m z).comp measurable_subtype_coe,
    fun ω => one_le_localTailFactor J m z ω.1, ?_, ae_localDensity_tail_comparison M J m z⟩
  rw [anchored_moment_eq M _ (measurable_localTailFactor J m z) q]
  exact hmoment M hM m z

end SubdiffusiveProcess.Static
