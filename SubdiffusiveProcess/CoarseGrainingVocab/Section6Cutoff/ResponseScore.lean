import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseSupremum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ResponseScore




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open Filter MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- A translated scale-`n` response at an arbitrary cutoff is the same
response evaluated on the corresponding scale-`n` triadic cube. -/
theorem section6Response_shift_eq_cutoffResponseOnCube {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n cutoff : ℕ)
    (R : TriadicCube d) (hR : R.scale = (n : ℤ)) (e : Vec d)
    (omega : Sample d) :
    section6Response M n cutoff omega (triadicCubeShift R) e =
      cutoffResponseOnCube M cutoff
        ((Real.sqrt (ahom M cutoff))⁻¹ • e)
        (Real.sqrt (ahom M cutoff) • e) R omega := by
  change paperScalarProbe (originCube d (n : ℤ))
      (aCutoffFamily M cutoff (translatePotentialSample (triadicCubeShift R) omega))
        (ahom M cutoff) e =
    paperScalarProbe R (aCutoffFamily M cutoff omega) (ahom M cutoff) e
  rw [paperScalarProbe_aCutoffFamily_eq_origin
    M cutoff omega R (ahom M cutoff) e, hR]

/-- The local quarter-net representative at cutoff `n ∧ L` dominates every
literal unit-direction cutoff response atom almost surely. -/
theorem ofReal_section6Response_cutoff_shift_ae_le_two_mul_localNet
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ)
    (R : TriadicCube d) (hR : R.scale = (n : ℤ))
    (e : Vec d) (he : vecNormSq e = 1) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ENNReal.ofReal
          (section6Response M n (min n L) omega (triadicCubeShift R) e) ≤
        2 * localNormalizedResponseQuarterNetMax M (min n L) R omega := by
  filter_upwards
    [normalizedResponseQuarterNetMax_ae_eq_local M (min n L) R]
      with omega homega
  calc
    ENNReal.ofReal
        (section6Response M n (min n L) omega (triadicCubeShift R) e) ≤
        normalizedDefect M (min n L) (Ch02.cubeDomain R) omega :=
      by
        rw [section6Response_shift_eq_cutoffResponseOnCube
          M n (min n L) R hR e omega]
        unfold cutoffResponseOnCube SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect
          paperScalarProbeMaxOn
        exact le_iSup_of_le ⟨e, he⟩ (le_refl _)
    _ ≤ 2 * normalizedResponseQuarterNetMax M (min n L)
          (Ch02.cubeDomain R) omega :=
      normalizedDefect_le_two_mul_quarterNetMax
        M (min n L) (Ch02.cubeDomain R) omega
    _ = 2 * localNormalizedResponseQuarterNetMax M (min n L) R omega := by
      rw [homega]

/-- The finite annular maximum with every response cutoff truncated at
`min n L`. -/
noncomputable def cutoffLocalResponseAnnulusMax {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j n : ℕ) (hnj : n ≤ j) :
    Sample d → ℝ≥0∞ := by
  classical
  let D := descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)
  exact fun omega =>
    D.sup' (descendantsAtScale_nonempty (originCube d (j : ℤ))
        (by change (n : ℤ) ≤ (j : ℤ); exact_mod_cast hnj))
      fun R =>
      if triadicCubeShift R ∉ cube d ((j : ℤ) - 1) then
        localNormalizedResponseQuarterNetMax M (min n L) R omega
      else 0

theorem measurable_cutoffLocalResponseAnnulusMax {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j n : ℕ) (hnj : n + 2 ≤ j) :
    Measurable[aCutoffPotentialLocalSigma (j - 2) (responseAnnulusReadRegion d j)]
      (cutoffLocalResponseAnnulusMax M L j n (by omega)) := by
  classical
  letI : MeasurableSpace (Sample d) :=
    aCutoffPotentialLocalSigma (j - 2) (responseAnnulusReadRegion d j)
  let D := descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)
  have hD : D.Nonempty := descendantsAtScale_nonempty (originCube d (j : ℤ))
    (by change (n : ℤ) ≤ (j : ℤ); exact_mod_cast (show n ≤ j by omega))
  have hmeas :
      Measurable[aCutoffPotentialLocalSigma (j - 2) (responseAnnulusReadRegion d j)]
        (D.sup' hD fun R omega =>
          if triadicCubeShift R ∉ cube d ((j : ℤ) - 1) then
            localNormalizedResponseQuarterNetMax M (min n L) R omega
          else 0) := by
    apply Finset.measurable_sup' (α := ℝ≥0∞) (δ := Sample d) hD
    intro R hR
    by_cases hann : triadicCubeShift R ∉ cube d ((j : ℤ) - 1)
    · simpa only [if_pos hann] using
        measurable_localNormalizedResponseQuarterNetMax_of_mono M
          (show min n L ≤ j - 2 by omega) R
          (V := responseAnnulusReadRegion d j) (by
            intro x hx
            unfold responseAnnulusReadRegion
            apply Set.mem_iUnion.2
            refine ⟨⟨n, hnj⟩, ?_⟩
            apply Set.mem_iUnion.2
            exact ⟨⟨R, hR, hann⟩, hx⟩)
    · simpa only [if_neg hann] using
        (measurable_const :
          Measurable[aCutoffPotentialLocalSigma (j - 2)
            (responseAnnulusReadRegion d j)] (fun _ : Sample d => (0 : ℝ≥0∞)))
  convert hmeas using 1
  funext omega
  dsimp only [cutoffLocalResponseAnnulusMax, D]
  rw [Finset.sup'_apply]

/-- Scale-`n` cutoff response atom, extended by zero outside `n + 2 ≤ j`. -/
noncomputable def cutoffLocalResponseScaleAtom {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j n : ℕ) : Sample d → ℝ≥0∞ :=
  if hnj : n + 2 ≤ j then
    cutoffLocalResponseAnnulusMax M L j n (by omega)
  else fun _ => 0

theorem measurable_cutoffLocalResponseScaleAtom {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j n : ℕ) :
    Measurable[aCutoffPotentialLocalSigma (j - 2) (responseAnnulusReadRegion d j)]
      (cutoffLocalResponseScaleAtom M L j n) := by
  classical
  unfold cutoffLocalResponseScaleAtom
  split_ifs with h
  · exact measurable_cutoffLocalResponseAnnulusMax M L j n h
  · exact measurable_const

/-- Local discounted response score for the cutoff good event. -/
noncomputable def cutoffLocalResponseScore {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s epsilon K : ℝ) (j : ℕ) : Sample d → ℝ≥0∞ :=
  fun omega =>
    ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
      ∑ n ∈ Finset.range (j - 1),
        ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
          cutoffLocalResponseScaleAtom M L j n omega

theorem measurable_cutoffLocalResponseScore {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s epsilon K : ℝ) (j : ℕ) :
    Measurable[aCutoffPotentialLocalSigma (j - 2) (responseAnnulusReadRegion d j)]
      (cutoffLocalResponseScore M L s epsilon K j) := by
  unfold cutoffLocalResponseScore
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro n _hn
  exact measurable_const.mul (measurable_cutoffLocalResponseScaleAtom M L j n)

/-- Two-sided Appendix-B array built from the local cutoff response score. -/
noncomputable def cutoffResponseScoreArray {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s epsilon K : ℝ) : ℤ → ℤ → Sample d → ℝ :=
  fun k j omega =>
    if 0 ≤ k ∧ 0 ≤ j ∧ j ≤ k then
      (cutoffLocalResponseScore M L s epsilon K j.toNat omega).toReal
    else 0

theorem measurable_cutoffResponseScoreArray {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s epsilon K : ℝ) (m j : ℤ) :
    Measurable (cutoffResponseScoreArray M L s epsilon K m j) := by
  unfold cutoffResponseScoreArray
  split_ifs
  · exact ENNReal.measurable_toReal.comp
      ((measurable_cutoffLocalResponseScore M L s epsilon K j.toNat).mono
        (aCutoffPotentialLocalSigma_le_borel _) le_rfl)
  · exact measurable_const

/-! ## Moment control from the proved Section 4 headline -/

/-- The full normalized-defect maximum on the descendant family, with every
defect evaluated at the manuscript cutoff `min n L`. -/
noncomputable def cutoffResponseDefectMaximum {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j n : ℕ) (hnj : n ≤ j) :
    Sample d → ℝ≥0∞ :=
  let D := descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)
  D.sup' (descendantsAtScale_nonempty (originCube d (j : ℤ))
      (by change (n : ℤ) ≤ (j : ℤ); exact_mod_cast hnj))
    fun R => normalizedDefect M (min n L) (Ch02.cubeDomain R)

theorem cutoffLocalResponseAnnulusMax_ae_le_cutoffResponseDefectMaximum
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j n : ℕ) (hnj : n ≤ j) :
    cutoffLocalResponseAnnulusMax M L j n hnj ≤ᵐ[M.P.toMeasure]
      cutoffResponseDefectMaximum M L j n hnj := by
  classical
  let D := descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)
  have hall : ∀ᵐ omega ∂M.P.toMeasure, ∀ R ∈ D,
      localNormalizedResponseQuarterNetMax M (min n L) R omega ≤
        normalizedDefect M (min n L) (Ch02.cubeDomain R) omega :=
    (Finset.eventually_all D).2 fun R _hR =>
      localNormalizedResponseQuarterNetMax_ae_le_normalizedDefect
        M (min n L) R
  filter_upwards [hall] with omega homega
  dsimp only [cutoffLocalResponseAnnulusMax, cutoffResponseDefectMaximum, D]
  rw [Finset.sup'_apply]
  apply Finset.sup'_le
  intro R hR
  by_cases hann : triadicCubeShift R ∉ cube d ((j : ℤ) - 1)
  · rw [if_pos hann]
    exact (homega R hR).trans (Finset.le_sup' (fun Q =>
      normalizedDefect M (min n L) (Ch02.cubeDomain Q) omega) hR)
  · rw [if_neg hann]
    exact bot_le

theorem cutoffResponseDefectMaximum_moment_le {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j n : ℕ) (hnj : n ≤ j)
    {xi : ℝ} (hxi : 0 < xi) (A : ℝ≥0∞)
    (hcenter :
      paperENNRealLpNorm M.P.toMeasure xi
          (normalizedDefect M (min n L)
            (Ch02.cubeDomain (originCube d (n : ℤ)))) ≤ A) :
    paperENNRealLpNorm M.P.toMeasure xi
        (cutoffResponseDefectMaximum M L j n hnj) ≤
      ((descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ xi⁻¹ * A := by
  classical
  let D := descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)
  have hD : D.Nonempty := descendantsAtScale_nonempty (originCube d (j : ℤ))
    (by change (n : ℤ) ≤ (j : ℤ); exact_mod_cast hnj)
  let X : TriadicCube d → Sample d → ℝ≥0∞ :=
    fun R => normalizedDefect M (min n L) (Ch02.cubeDomain R)
  have hXmeas : ∀ R ∈ D, Measurable (X R) := by
    intro R _hR
    exact (measurable_normalizedDefect_potentialShellIndexSigma_Iic
      M (min n L) (Ch02.cubeDomain R)).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Iic (min n L))) le_rfl
  have hXmoment : ∀ R ∈ D,
      paperENNRealLpNorm M.P.toMeasure xi (X R) ≤ A := by
    intro R hR
    rw [paperENNRealLpNorm_normalizedDefect_cube_eq_origin
      M (min n L) xi R, scale_eq_of_mem_descendantsAtScale hR]
    exact hcenter
  simpa only [cutoffResponseDefectMaximum, D, X] using
    paperENNRealLpNorm_finset_sup'_le_card_rpow_mul
      M.P.toMeasure hxi D hD X hXmeas A hXmoment

theorem cutoffLocalResponseAnnulusMax_moment_le {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L j n : ℕ) (hnj : n ≤ j)
    {xi : ℝ} (hxi : 0 < xi) (A : ℝ≥0∞)
    (hcenter :
      paperENNRealLpNorm M.P.toMeasure xi
          (normalizedDefect M (min n L)
            (Ch02.cubeDomain (originCube d (n : ℤ)))) ≤ A) :
    paperENNRealLpNorm M.P.toMeasure xi
        (cutoffLocalResponseAnnulusMax M L j n hnj) ≤
      ((descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ xi⁻¹ * A :=
  (paperENNRealLpNorm_mono_ae M.P.toMeasure hxi.le
    (cutoffLocalResponseAnnulusMax_ae_le_cutoffResponseDefectMaximum
      M L j n hnj)).trans
      (cutoffResponseDefectMaximum_moment_le M L j n hnj hxi A hcenter)

/-- Uniform cutoff response-score moment, assuming the matching centered
defect estimate at every response scale. -/
theorem cutoffLocalResponseScore_moment_le_of_center {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s epsilon K : ℝ) (j : ℕ) {xi : ℝ} (hxi : 1 ≤ xi) (A : ℝ≥0∞)
    (hcenter : ∀ n : ℕ,
      paperENNRealLpNorm M.P.toMeasure xi
          (normalizedDefect M (min n L)
            (Ch02.cubeDomain (originCube d (n : ℤ)))) ≤ A) :
    paperENNRealLpNorm M.P.toMeasure xi
        (cutoffLocalResponseScore M L s epsilon K j) ≤
      ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
        ∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ xi⁻¹ * A := by
  let X : ℕ → Sample d → ℝ≥0∞ := fun n omega =>
    ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
      cutoffLocalResponseScaleAtom M L j n omega
  have hXmeas : ∀ n ∈ Finset.range (j - 1), Measurable (X n) := by
    intro n _hn
    exact measurable_const.mul
      ((measurable_cutoffLocalResponseScaleAtom M L j n).mono
        (aCutoffPotentialLocalSigma_le_borel _) le_rfl)
  have hXmoment : ∀ n ∈ Finset.range (j - 1),
      paperENNRealLpNorm M.P.toMeasure xi (X n) ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
          ((descendantsAtScale
            (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ xi⁻¹ * A := by
    intro n hn
    have hnj : n + 2 ≤ j := by
      have : n < j - 1 := Finset.mem_range.mp hn
      omega
    rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure
      (zero_lt_one.trans_le hxi) _
      (cutoffLocalResponseScaleAtom M L j n)
      ((measurable_cutoffLocalResponseScaleAtom M L j n).mono
        (aCutoffPotentialLocalSigma_le_borel _) le_rfl)]
    unfold cutoffLocalResponseScaleAtom
    rw [dif_pos hnj]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (cutoffLocalResponseAnnulusMax_moment_le M L j n (by omega)
        (zero_lt_one.trans_le hxi) A (hcenter n)) (zero_le _)
  have hsum := paperENNRealLpNorm_finset_sum_le M.P.toMeasure hxi
    (Finset.range (j - 1)) X hXmeas
  have hsumMeas : Measurable (fun omega =>
      ∑ n ∈ Finset.range (j - 1), X n omega) :=
    Finset.measurable_sum _ fun n hn => hXmeas n hn
  rw [show cutoffLocalResponseScore M L s epsilon K j =
      fun omega => ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
        ∑ n ∈ Finset.range (j - 1), X n omega by rfl,
    paperENNRealLpNorm_const_mul_eq M.P.toMeasure
      (zero_lt_one.trans_le hxi) _ _ hsumMeas]
  exact mul_le_mul_of_nonneg_left
    (hsum.trans (Finset.sum_le_sum fun n hn => hXmoment n hn)) (zero_le _)

/-- The proved coarse-grained headline supplies the centered hypothesis in
`cutoffLocalResponseScore_moment_le_of_center`, uniformly in `L`. -/
theorem exists_cutoffLocalResponseScore_moment_bound {d : ℕ} [NeZero d] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (xi : ℝ),
        1 ≤ xi →
        xi ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ (L : ℕ) (s epsilon K : ℝ) (j : ℕ),
          paperENNRealLpNorm M.P.toMeasure xi
              (cutoffLocalResponseScore M L s epsilon K j) ≤
            ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
              ∑ n ∈ Finset.range (j - 1),
                ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
                  ((descendantsAtScale
                    (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ xi⁻¹ *
                  ENNReal.ofReal
                    (C * xi * Real.log (2 + xi) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hheadline⟩ :=
    exists_cutoffNormalizedResponse_moment_bound d
  refine ⟨c, C, hc, hC, ?_⟩
  intro M xi hxi hsmall L s epsilon K j
  exact cutoffLocalResponseScore_moment_le_of_center
    M L s epsilon K j hxi
      (ENNReal.ofReal (C * xi * Real.log (2 + xi) * M.delta ^ 2))
      (hheadline M xi hxi hsmall L)

/-- Per-column Markov extraction for the cutoff response score. -/
theorem measure_cutoffLocalResponseScore_ge_le_of_moment
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s epsilon K : ℝ) (j : ℕ)
    {xi t : ℝ} (hxi : 0 < xi) (ht : 0 < t) (B : ℝ≥0∞) (hB : B ≠ ∞)
    (hmoment :
      paperENNRealLpNorm M.P.toMeasure xi
        (cutoffLocalResponseScore M L s epsilon K j) ≤ B) :
    M.P.toMeasure
        {omega | ENNReal.ofReal t ≤
          cutoffLocalResponseScore M L s epsilon K j omega} ≤
      (B / ENNReal.ofReal t) ^ xi := by
  have hmeas : Measurable (cutoffLocalResponseScore M L s epsilon K j) :=
    (measurable_cutoffLocalResponseScore M L s epsilon K j).mono
      (aCutoffPotentialLocalSigma_le_borel _) le_rfl
  have hBreal : ENNReal.ofReal B.toReal = B := ENNReal.ofReal_toReal hB
  have hraw :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.measure_le_ratio_rpow_of_paperENNRealLpNorm
      hxi ht hmeas (A := B.toReal) (by simpa only [hBreal] using hmoment)
      (B := {omega | ENNReal.ofReal t ≤
        cutoffLocalResponseScore M L s epsilon K j omega})
      (fun _ h => h)
  simpa only [hBreal] using hraw

/-- The cutoff array has exactly the same finite-range column certificate as
the uncutoff response array; truncating the coefficient can only shorten the
shell read. -/
theorem columnsIndep_cutoffResponseScoreArray_of_separated
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s epsilon K : ℝ)
    (r : ℕ)
    (hsep : ∀ b : ℤ,
      Pairwise fun i j : {q : ℤ // 0 ≤ q * (r : ℤ) + b} =>
        ∀ ⦃x y : Vec d⦄,
          x ∈ responseAnnulusReadRegion d (i.1 * (r : ℤ) + b).toNat →
          y ∈ responseAnnulusReadRegion d (j.1 * (r : ℤ) + b).toNat →
          Real.sqrt (d : ℝ) *
              (3 : ℝ) ^ min ((i.1 * (r : ℤ) + b).toNat - 2)
                ((j.1 * (r : ℤ) + b).toNat - 2) ≤
            Ch02.vecNorm (x - y)) :
    SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      (cutoffResponseScoreArray M L s epsilon K) r := by
  intro b
  let A : Set ℤ := {j | 0 ≤ j * (r : ℤ) + b}
  let F : ℤ → Sample d → (ℤ → ℝ) := fun j omega k =>
    cutoffResponseScoreArray M L s epsilon K k (j * (r : ℤ) + b) omega
  apply iIndepFun_of_iIndepFun_subtype_of_constant A F
  · let Lidx : A → ℕ := fun j => (j.1 * (r : ℤ) + b).toNat - 2
    let U : A → Set (Vec d) := fun j =>
      responseAnnulusReadRegion d (j.1 * (r : ℤ) + b).toNat
    have hsigma :
        iIndep (fun j : A => aCutoffPotentialLocalSigma (Lidx j) (U j))
          M.P.toMeasure :=
      iIndep_aCutoffPotentialLocalSigma_of_varyingLevel M Lidx
        (fun j => (isOpen_responseAnnulusReadRegion d _).measurableSet)
        (hsep b)
    rw [iIndepFun_iff_iIndep]
    exact iIndep_of_le hsigma fun j => by
      have hF :
          @Measurable (Sample d) (ℤ → ℝ)
            (aCutoffPotentialLocalSigma (Lidx j) (U j)) _ (F j) := by
        letI : MeasurableSpace (Sample d) :=
          aCutoffPotentialLocalSigma (Lidx j) (U j)
        apply measurable_pi_lambda
        intro k
        have hj : 0 ≤ j.1 * (r : ℤ) + b := j.2
        by_cases hkj : 0 ≤ k ∧ j.1 * (r : ℤ) + b ≤ k
        · have hfull : 0 ≤ k ∧ 0 ≤ j.1 * (r : ℤ) + b ∧
              j.1 * (r : ℤ) + b ≤ k := ⟨hkj.1, hj, hkj.2⟩
          simp only [F, cutoffResponseScoreArray, if_pos hfull]
          exact ENNReal.measurable_toReal.comp
            (measurable_cutoffLocalResponseScore M L s epsilon K
              (j.1 * (r : ℤ) + b).toNat)
        · have hnot : ¬(0 ≤ k ∧ 0 ≤ j.1 * (r : ℤ) + b ∧
              j.1 * (r : ℤ) + b ≤ k) := by omega
          simp only [F, cutoffResponseScoreArray, if_neg hnot]
          exact measurable_const
      exact hF.comap_le
  · intro j hj
    have hneg : j * (r : ℤ) + b < 0 := by simpa [A] using hj
    refine ⟨fun _ => 0, ?_⟩
    intro omega
    funext k
    simp [F, cutoffResponseScoreArray,
      show ¬0 ≤ j * (r : ℤ) + b by omega]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
