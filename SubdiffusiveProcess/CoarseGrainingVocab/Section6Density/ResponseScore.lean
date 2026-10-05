module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ResponseRosenthal
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.SphereQuarterNet
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.BadEventEstimates
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6AnnularCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.LayerIndependence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ShellColumns
public import SubdiffusiveProcess.Section4.CoarseGrainedBound

@[expose] public section

/-!
# The annular response score for density of good scales

This file builds the response-only array from the proof of
`l.discounted.J.local`.  The first layer chooses the already-proved
restriction-local representatives of fixed cutoff responses and packages the
finite quarter-net maximum without losing its local sigma-field.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open Filter MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Increasing the cutoff level only enlarges the finite shell-local source
sigma-field. -/
theorem aCutoffPotentialLocalSigma_mono_level {d : ℕ} {L K : ℕ}
    (hLK : L ≤ K) (U : Set (Vec d)) :
    aCutoffPotentialLocalSigma L U ≤ aCutoffPotentialLocalSigma K U := by
  unfold aCutoffPotentialLocalSigma
  refine iSup_le fun k => ?_
  let k' : Fin (K + 1) := ⟨k, lt_of_lt_of_le k.isLt (Nat.succ_le_succ hLK)⟩
  exact le_iSup_of_le k' (by rfl)

/-- Enlarging the spatial read region enlarges the finite cutoff source
sigma-field. -/
theorem aCutoffPotentialLocalSigma_mono_set {d L : ℕ}
    {U V : Set (Vec d)} (hUV : U ⊆ V) :
    aCutoffPotentialLocalSigma L U ≤ aCutoffPotentialLocalSigma L V := by
  unfold aCutoffPotentialLocalSigma
  refine iSup_mono fun k => ?_
  exact MeasurableSpace.comap_mono (potentialFieldLocalSigma_mono hUV)

theorem aCutoffPotentialLocalSigma_le_borel {d L : ℕ} (U : Set (Vec d)) :
    aCutoffPotentialLocalSigma L U ≤
      (inferInstance : MeasurableSpace (Sample d)) := by
  unfold aCutoffPotentialLocalSigma
  refine iSup_le fun k => ?_
  exact (MeasurableSpace.comap_mono (potentialFieldLocalSigma_le_borel U)).trans
    (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k).comap_le

/-- A fixed local representative of one cutoff response on a triadic cube. -/
noncomputable def cutoffResponseLocalRepresentative {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) : Sample d → ℝ :=
  Classical.choose (exists_cutoffResponseOnCube_thickenedLocal_ae_eq M L p q R)

theorem measurable_cutoffResponseLocalRepresentative {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) :
    @Measurable (Sample d) ℝ
      ((LocalSigmaR
        (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
          (aCutoffRegCoeffField M L)) _
      (cutoffResponseLocalRepresentative M L p q R) :=
  (Classical.choose_spec
    (exists_cutoffResponseOnCube_thickenedLocal_ae_eq M L p q R)).1

theorem cutoffResponseOnCube_ae_eq_localRepresentative {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (p q : Vec d)
    (R : TriadicCube d) :
    cutoffResponseOnCube M L p q R =ᵐ[M.P.toMeasure]
      cutoffResponseLocalRepresentative M L p q R :=
  (Classical.choose_spec
    (exists_cutoffResponseOnCube_thickenedLocal_ae_eq M L p q R)).2

/-- The fixed local representative of the normalized response maximum on the
finite quarter-net. -/
noncomputable def localNormalizedResponseQuarterNetMax {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (R : TriadicCube d) : Sample d → ℝ≥0∞ :=
  (sphereQuarterNet d).points.sup' sphereQuarterNet_points_nonempty fun e omega =>
    ENNReal.ofReal (cutoffResponseLocalRepresentative M n
      ((Real.sqrt (ahom M n))⁻¹ • e) (Real.sqrt (ahom M n) • e) R omega)

theorem measurable_localNormalizedResponseQuarterNetMax {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (R : TriadicCube d) :
    @Measurable (Sample d) ℝ≥0∞
      ((LocalSigmaR
        (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
          (aCutoffRegCoeffField M n)) _
      (localNormalizedResponseQuarterNetMax M n R) := by
  let : MeasurableSpace (Sample d) :=
    (LocalSigmaR
      (Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R))).comap
        (aCutoffRegCoeffField M n)
  unfold localNormalizedResponseQuarterNetMax
  apply Finset.measurable_sup' (α := ℝ≥0∞) (δ := Sample d)
  intro e _he
  exact ENNReal.continuous_ofReal.measurable.comp
    (measurable_cutoffResponseLocalRepresentative M n
      ((Real.sqrt (ahom M n))⁻¹ • e) (Real.sqrt (ahom M n) • e) R)

/-- A fixed-cube representative can be read from any larger spatial region
and any later cutoff source sigma-field. -/
theorem measurable_localNormalizedResponseQuarterNetMax_of_mono
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n K : ℕ} (hnK : n ≤ K)
    (R : TriadicCube d) {V : Set (Vec d)}
    (hRV : Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R) ⊆ V) :
    Measurable[aCutoffPotentialLocalSigma K V]
      (localNormalizedResponseQuarterNetMax M n R) := by
  apply (measurable_localNormalizedResponseQuarterNetMax M n R).mono _ le_rfl
  exact (measurable_aCutoffRegCoeffField_local M n Metric.isOpen_thickening).comap_le.trans
    ((aCutoffPotentialLocalSigma_mono_level hnK _).trans
      (aCutoffPotentialLocalSigma_mono_set hRV))

/-- The local quarter-net maximum agrees almost surely with the literal one. -/
theorem normalizedResponseQuarterNetMax_ae_eq_local {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (R : TriadicCube d) :
    normalizedResponseQuarterNetMax M n (Ch02.cubeDomain R) =ᵐ[M.P.toMeasure]
      localNormalizedResponseQuarterNetMax M n R := by
  have hall : ∀ᵐ omega ∂M.P.toMeasure,
      ∀ e ∈ (sphereQuarterNet d).points,
        cutoffResponseOnCube M n
            ((Real.sqrt (ahom M n))⁻¹ • e) (Real.sqrt (ahom M n) • e) R omega =
          cutoffResponseLocalRepresentative M n
            ((Real.sqrt (ahom M n))⁻¹ • e) (Real.sqrt (ahom M n) • e) R omega :=
    (Finset.eventually_all (sphereQuarterNet d).points).2 fun e _he =>
      cutoffResponseOnCube_ae_eq_localRepresentative M n
        ((Real.sqrt (ahom M n))⁻¹ • e) (Real.sqrt (ahom M n) • e) R
  filter_upwards [hall] with omega homega
  unfold normalizedResponseQuarterNetMax localNormalizedResponseQuarterNetMax
  rw [Finset.sup'_apply, Finset.sup'_apply]
  apply Finset.sup'_congr sphereQuarterNet_points_nonempty rfl
  intro e he
  rw [← homega e he]
  rfl

/-- A translated centered response atom is the same response evaluated on the
corresponding triadic cube. -/
theorem section6Response_shift_eq_cutoffResponseOnCube {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (R : TriadicCube d) (hR : R.scale = (n : ℤ)) (e : Vec d)
    (omega : Sample d) :
    section6Response M n n omega (triadicCubeShift R) e =
      cutoffResponseOnCube M n
        ((Real.sqrt (ahom M n))⁻¹ • e) (Real.sqrt (ahom M n) • e) R omega := by
  change paperScalarProbe (originCube d (n : ℤ))
      (aCutoffFamily M n (translatePotentialSample (triadicCubeShift R) omega))
        (ahom M n) e =
    paperScalarProbe R (aCutoffFamily M n omega) (ahom M n) e
  rw [paperScalarProbe_aCutoffFamily_eq_origin M n omega R (ahom M n) e, hR]

/-- The quarter-net maximum is a restriction of the full unit-sphere
normalized defect. -/
theorem normalizedResponseQuarterNetMax_le_normalizedDefect {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) :
    normalizedResponseQuarterNetMax M n U omega ≤ normalizedDefect M n U omega := by
  unfold normalizedResponseQuarterNetMax normalizedDefect paperScalarProbeMaxOn
  rw [Finset.sup'_apply]
  apply Finset.sup'_le
  intro e he
  exact le_iSup_of_le ⟨e, (sphereQuarterNet d).unit e he⟩ (le_refl _)

/-- Every unit-direction response atom in the response score is dominated by
the normalized defect on its triadic cube. -/
theorem ofReal_section6Response_shift_le_normalizedDefect {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (R : TriadicCube d) (hR : R.scale = (n : ℤ))
    (e : Vec d) (he : vecNormSq e = 1) (omega : Sample d) :
    ENNReal.ofReal (section6Response M n n omega (triadicCubeShift R) e) ≤
      normalizedDefect M n (Ch02.cubeDomain R) omega := by
  rw [section6Response_shift_eq_cutoffResponseOnCube M n R hR e omega]
  unfold cutoffResponseOnCube normalizedDefect paperScalarProbeMaxOn
  exact le_iSup_of_le ⟨e, he⟩ (le_refl _)

/-- The measurable local representative inherits the headline
carrier bound almost surely. -/
theorem localNormalizedResponseQuarterNetMax_ae_le_normalizedDefect
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (R : TriadicCube d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      localNormalizedResponseQuarterNetMax M n R omega ≤
        normalizedDefect M n (Ch02.cubeDomain R) omega := by
  filter_upwards [normalizedResponseQuarterNetMax_ae_eq_local M n R] with omega homega
  rw [← homega]
  exact normalizedResponseQuarterNetMax_le_normalizedDefect M n
    (Ch02.cubeDomain R) omega

/-- The local quarter-net representative, with factor two, dominates every
literal unit-direction translated response atom almost surely. -/
theorem ofReal_section6Response_shift_ae_le_two_mul_localNet
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (R : TriadicCube d) (hR : R.scale = (n : ℤ))
    (e : Vec d) (he : vecNormSq e = 1) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ENNReal.ofReal (section6Response M n n omega (triadicCubeShift R) e) ≤
        2 * localNormalizedResponseQuarterNetMax M n R omega := by
  filter_upwards [normalizedResponseQuarterNetMax_ae_eq_local M n R] with omega homega
  calc
    ENNReal.ofReal (section6Response M n n omega (triadicCubeShift R) e) ≤
        normalizedDefect M n (Ch02.cubeDomain R) omega :=
      ofReal_section6Response_shift_le_normalizedDefect M n R hR e he omega
    _ ≤ 2 * normalizedResponseQuarterNetMax M n (Ch02.cubeDomain R) omega :=
      normalizedDefect_le_two_mul_quarterNetMax M n (Ch02.cubeDomain R) omega
    _ = 2 * localNormalizedResponseQuarterNetMax M n R omega := by rw [homega]

/-! ## The finite annular maximum -/

/-- The actual spatial region read by response column j: positively
thickened scale-n cells with n ≤ j - 2 whose centres lie outside
the inner cube.  Descendancy supplies the other annulus inclusion. -/
def responseAnnulusReadRegion (d j : ℕ) : Set (Vec d) :=
  ⋃ n : {n : ℕ // n + 2 ≤ j},
    ⋃ R : {R : TriadicCube d //
        R ∈ descendantsAtScale (originCube d (j : ℤ)) (n.1 : ℤ) ∧
          triadicCubeShift R ∉ cube d ((j : ℤ) - 1)},
      Metric.thickening (responseRestrictionBridgeRadius d) (cubeSet R.1)

theorem isOpen_responseAnnulusReadRegion (d j : ℕ) :
    IsOpen (responseAnnulusReadRegion d j) := by
  unfold responseAnnulusReadRegion
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_thickening

/-- The local finite maximum over all scale-n descendants of the scale-j
centered cube, with the cells inside the scale-(j-1) cube set to zero. -/
noncomputable def localResponseAnnulusMax {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j n : ℕ) (hnj : n ≤ j) :
    Sample d → ℝ≥0∞ := by
  classical
  let D := descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)
  exact fun omega =>
    D.sup' (descendantsAtScale_nonempty (originCube d (j : ℤ))
        (by change (n : ℤ) ≤ (j : ℤ); exact_mod_cast hnj))
      fun R =>
      if triadicCubeShift R ∉ cube d ((j : ℤ) - 1) then
        localNormalizedResponseQuarterNetMax M n R omega
      else 0

theorem measurable_localResponseAnnulusMax {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j n : ℕ) (hnj : n + 2 ≤ j) :
    Measurable[aCutoffPotentialLocalSigma (j - 2) (responseAnnulusReadRegion d j)]
      (localResponseAnnulusMax M j n (by omega)) := by
  classical
  let : MeasurableSpace (Sample d) :=
    aCutoffPotentialLocalSigma (j - 2) (responseAnnulusReadRegion d j)
  let D := descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)
  have hD : D.Nonempty := descendantsAtScale_nonempty (originCube d (j : ℤ))
    (by change (n : ℤ) ≤ (j : ℤ); exact_mod_cast (show n ≤ j by omega))
  have hmeas :
      Measurable[aCutoffPotentialLocalSigma (j - 2) (responseAnnulusReadRegion d j)]
        (D.sup' hD fun R omega =>
          if triadicCubeShift R ∉ cube d ((j : ℤ) - 1) then
            localNormalizedResponseQuarterNetMax M n R omega
          else 0) := by
    apply Finset.measurable_sup' (α := ℝ≥0∞) (δ := Sample d) hD
    intro R hR
    by_cases hann : triadicCubeShift R ∉ cube d ((j : ℤ) - 1)
    · simpa only [ite_eq_left hann] using
        measurable_localNormalizedResponseQuarterNetMax_of_mono M (by omega) R
          (V := responseAnnulusReadRegion d j) (by
            intro x hx
            unfold responseAnnulusReadRegion
            apply Set.mem_iUnion.2
            refine ⟨⟨n, hnj⟩, ?_⟩
            apply Set.mem_iUnion.2
            exact ⟨⟨R, hR, hann⟩, hx⟩)
    · simpa only [ite_eq_right hann] using
        (measurable_const :
          Measurable[aCutoffPotentialLocalSigma (j - 2) (responseAnnulusReadRegion d j)]
            (fun _ : Sample d => (0 : ℝ≥0∞)))
  convert hmeas using 1
  funext omega
  dsimp only [localResponseAnnulusMax, D]
  rw [Finset.sup'_apply]

/-- The scale-n summand of column j, extended by zero outside the manuscript
range n ≤ j - 2. -/
noncomputable def localResponseScaleAtom {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j n : ℕ) : Sample d → ℝ≥0∞ :=
  if hnj : n + 2 ≤ j then localResponseAnnulusMax M j n (by omega) else fun _ => 0

theorem measurable_localResponseScaleAtom {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j n : ℕ) :
    Measurable[aCutoffPotentialLocalSigma (j - 2) (responseAnnulusReadRegion d j)]
      (localResponseScaleAtom M j n) := by
  classical
  unfold localResponseScaleAtom
  split_ifs with h
  · exact measurable_localResponseAnnulusMax M j n h
  · exact measurable_const

/-- A local truncated response score column.  The leading factor two is the
quarter-net majorant of the literal unit-sphere maximum and is absorbed into
the manuscript's dimensional constant. -/
noncomputable def localResponseScore {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s epsilon K : ℝ) (j : ℕ) :
    Sample d → ℝ≥0∞ :=
  fun omega =>
    ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
      ∑ n ∈ Finset.range (j - 1),
        ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
          localResponseScaleAtom M j n omega

theorem measurable_localResponseScore {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s epsilon K : ℝ) (j : ℕ) :
    Measurable[aCutoffPotentialLocalSigma (j - 2) (responseAnnulusReadRegion d j)]
      (localResponseScore M s epsilon K j) := by
  let : MeasurableSpace (Sample d) :=
    aCutoffPotentialLocalSigma (j - 2) (responseAnnulusReadRegion d j)
  unfold localResponseScore
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro n _hn
  exact measurable_const.mul (measurable_localResponseScaleAtom M j n)

/-- The two-sided Appendix-B array: nonnegative columns carry the response
score and negative columns are deterministically zero. -/
noncomputable def responseScoreArray {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s epsilon K : ℝ) :
    ℤ → ℤ → Sample d → ℝ :=
  fun k j omega =>
    if 0 ≤ k ∧ 0 ≤ j ∧ j ≤ k then
      (localResponseScore M s epsilon K j.toNat omega).toReal
    else 0

/-! ## Moment and Markov control from the Section 4 headline -/

/-- The full normalized-defect maximum on the same finite descendant family.
It is a convenient stationary majorant for the local annular maximum. -/
noncomputable def responseDefectMaximum {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j n : ℕ) (hnj : n ≤ j) :
    Sample d → ℝ≥0∞ :=
  let D := descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)
  D.sup' (descendantsAtScale_nonempty (originCube d (j : ℤ))
      (by change (n : ℤ) ≤ (j : ℤ); exact_mod_cast hnj))
    fun R => normalizedDefect M n (Ch02.cubeDomain R)

theorem localResponseAnnulusMax_ae_le_responseDefectMaximum
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j n : ℕ) (hnj : n ≤ j) :
    localResponseAnnulusMax M j n hnj ≤ᵐ[M.P.toMeasure]
      responseDefectMaximum M j n hnj := by
  classical
  let D := descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)
  have hall : ∀ᵐ omega ∂M.P.toMeasure, ∀ R ∈ D,
      localNormalizedResponseQuarterNetMax M n R omega ≤
        normalizedDefect M n (Ch02.cubeDomain R) omega :=
    (Finset.eventually_all D).2 fun R _hR =>
      localNormalizedResponseQuarterNetMax_ae_le_normalizedDefect M n R
  filter_upwards [hall] with omega homega
  dsimp only [localResponseAnnulusMax, responseDefectMaximum, D]
  rw [Finset.sup'_apply]
  apply Finset.sup'_le
  intro R hR
  by_cases hann : triadicCubeShift R ∉ cube d ((j : ℤ) - 1)
  · rw [ite_eq_left hann]
    exact (homega R hR).trans (Finset.le_sup' (fun Q =>
      normalizedDefect M n (Ch02.cubeDomain Q) omega) hR)
  · rw [ite_eq_right hann]
    exact bot_le

theorem responseDefectMaximum_moment_le {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j n : ℕ) (hnj : n ≤ j)
    {xi : ℝ} (hxi : 0 < xi) (A : ℝ≥0∞)
    (hcenter :
      paperENNRealLpNorm M.P.toMeasure xi
          (normalizedDefect M n (Ch02.cubeDomain (originCube d (n : ℤ)))) ≤ A) :
    paperENNRealLpNorm M.P.toMeasure xi (responseDefectMaximum M j n hnj) ≤
      ((descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ xi⁻¹ * A := by
  classical
  let D := descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)
  have hD : D.Nonempty := descendantsAtScale_nonempty (originCube d (j : ℤ))
    (by change (n : ℤ) ≤ (j : ℤ); exact_mod_cast hnj)
  let X : TriadicCube d → Sample d → ℝ≥0∞ :=
    fun R => normalizedDefect M n (Ch02.cubeDomain R)
  have hXmeas : ∀ R ∈ D, Measurable (X R) := by
    intro R _hR
    exact (measurable_normalizedDefect_potentialShellIndexSigma_Iic
      M n (Ch02.cubeDomain R)).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Iic n)) le_rfl
  have hXmoment : ∀ R ∈ D,
      paperENNRealLpNorm M.P.toMeasure xi (X R) ≤ A := by
    intro R hR
    rw [paperENNRealLpNorm_normalizedDefect_cube_eq_origin M n xi R,
      scale_eq_of_mem_descendantsAtScale hR]
    exact hcenter
  simpa only [responseDefectMaximum, D, X] using
    paperENNRealLpNorm_finset_sup'_le_card_rpow_mul
      M.P.toMeasure hxi D hD X hXmeas A hXmoment

theorem localResponseAnnulusMax_moment_le {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j n : ℕ) (hnj : n ≤ j)
    {xi : ℝ} (hxi : 0 < xi) (A : ℝ≥0∞)
    (hcenter :
      paperENNRealLpNorm M.P.toMeasure xi
          (normalizedDefect M n (Ch02.cubeDomain (originCube d (n : ℤ)))) ≤ A) :
    paperENNRealLpNorm M.P.toMeasure xi (localResponseAnnulusMax M j n hnj) ≤
      ((descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ xi⁻¹ * A :=
  (paperENNRealLpNorm_mono_ae M.P.toMeasure hxi.le
    (localResponseAnnulusMax_ae_le_responseDefectMaximum M j n hnj)).trans
      (responseDefectMaximum_moment_le M j n hnj hxi A hcenter)

/-- The response-annulus moment estimate obtained directly from the proved
Section 4 headline. -/
theorem exists_localResponseAnnulusMax_moment_bound {d : ℕ} [NeZero d] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (xi : ℝ),
        1 ≤ xi →
        xi ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ j n : ℕ, ∀ hnj : n ≤ j,
          paperENNRealLpNorm M.P.toMeasure xi
              (localResponseAnnulusMax M j n hnj) ≤
            ((descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ xi⁻¹ *
              ENNReal.ofReal (C * xi * Real.log (2 + xi) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hheadline⟩ :=
    _root_.SubdiffusiveProcess.Section4.coarse_grained_bound (d := d)
  refine ⟨c, C, hc, hC, ?_⟩
  intro M xi hxi hsmall j n hnj
  exact localResponseAnnulusMax_moment_le M j n hnj
    (zero_lt_one.trans_le hxi)
    (ENNReal.ofReal (C * xi * Real.log (2 + xi) * M.delta ^ 2))
    (hheadline M xi hxi hsmall n).1

theorem localResponseScore_moment_le_of_center {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s epsilon K : ℝ) (j : ℕ)
    {xi : ℝ} (hxi : 1 ≤ xi) (A : ℝ≥0∞)
    (hcenter : ∀ n : ℕ,
      paperENNRealLpNorm M.P.toMeasure xi
          (normalizedDefect M n (Ch02.cubeDomain (originCube d (n : ℤ)))) ≤ A) :
    paperENNRealLpNorm M.P.toMeasure xi (localResponseScore M s epsilon K j) ≤
      ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
        ∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ xi⁻¹ * A := by
  let X : ℕ → Sample d → ℝ≥0∞ := fun n omega =>
    ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
      localResponseScaleAtom M j n omega
  have hXmeas : ∀ n ∈ Finset.range (j - 1), Measurable (X n) := by
    intro n _hn
    exact measurable_const.mul
      ((measurable_localResponseScaleAtom M j n).mono
        (aCutoffPotentialLocalSigma_le_borel _) le_rfl)
  have hXmoment : ∀ n ∈ Finset.range (j - 1),
      paperENNRealLpNorm M.P.toMeasure xi (X n) ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
          ((descendantsAtScale (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ xi⁻¹ * A := by
    intro n hn
    have hnj : n + 2 ≤ j := by
      have : n < j - 1 := Finset.mem_range.mp hn
      omega
    rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure
      (zero_lt_one.trans_le hxi) _
      (localResponseScaleAtom M j n)
      ((measurable_localResponseScaleAtom M j n).mono
        (aCutoffPotentialLocalSigma_le_borel _) le_rfl)]
    unfold localResponseScaleAtom
    rw [dite_eq_left hnj]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (localResponseAnnulusMax_moment_le M j n (by omega)
        (zero_lt_one.trans_le hxi) A (hcenter n)) zero_le
  have hsum := paperENNRealLpNorm_finset_sum_le M.P.toMeasure hxi
    (Finset.range (j - 1)) X hXmeas
  have hsumMeas : Measurable (fun omega =>
      ∑ n ∈ Finset.range (j - 1), X n omega) :=
    Finset.measurable_sum _ fun n hn => hXmeas n hn
  rw [show localResponseScore M s epsilon K j =
      fun omega => ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
        ∑ n ∈ Finset.range (j - 1), X n omega by rfl,
    paperENNRealLpNorm_const_mul_eq M.P.toMeasure
      (zero_lt_one.trans_le hxi) _ _ hsumMeas]
  exact mul_le_mul_of_nonneg_left
    (hsum.trans (Finset.sum_le_sum fun n hn => hXmoment n hn)) zero_le

theorem exists_localResponseScore_moment_bound {d : ℕ} [NeZero d] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (xi : ℝ),
        1 ≤ xi →
        xi ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ (s epsilon K : ℝ) (j : ℕ),
          paperENNRealLpNorm M.P.toMeasure xi (localResponseScore M s epsilon K j) ≤
            ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
              ∑ n ∈ Finset.range (j - 1),
                ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
                  ((descendantsAtScale
                    (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ xi⁻¹ *
                  ENNReal.ofReal (C * xi * Real.log (2 + xi) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hheadline⟩ :=
    _root_.SubdiffusiveProcess.Section4.coarse_grained_bound (d := d)
  refine ⟨c, C, hc, hC, ?_⟩
  intro M xi hxi hsmall s epsilon K j
  exact localResponseScore_moment_le_of_center M s epsilon K j hxi
    (ENNReal.ofReal (C * xi * Real.log (2 + xi) * M.delta ^ 2))
    (fun n => (hheadline M xi hxi hsmall n).1)

/-- Per-column Markov extraction in the same ENNReal moment convention used
by the headline. -/
theorem measure_localResponseScore_ge_le_of_moment
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s epsilon K : ℝ) (j : ℕ)
    {xi t : ℝ} (hxi : 0 < xi) (ht : 0 < t) (B : ℝ≥0∞) (hB : B ≠ ∞)
    (hmoment :
      paperENNRealLpNorm M.P.toMeasure xi (localResponseScore M s epsilon K j) ≤ B) :
    M.P.toMeasure {omega | ENNReal.ofReal t ≤ localResponseScore M s epsilon K j omega} ≤
      (B / ENNReal.ofReal t) ^ xi := by
  have hmeas : Measurable (localResponseScore M s epsilon K j) :=
    (measurable_localResponseScore M s epsilon K j).mono
      (aCutoffPotentialLocalSigma_le_borel _) le_rfl
  have hBreal : ENNReal.ofReal B.toReal = B := ENNReal.ofReal_toReal hB
  have hraw :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.measure_le_ratio_rpow_of_paperENNRealLpNorm
    hxi ht hmeas (A := B.toReal) (by simpa only [hBreal] using hmoment)
    (B := {omega | ENNReal.ofReal t ≤ localResponseScore M s epsilon K j omega})
    (fun _ h => h)
  simpa only [hBreal] using hraw

/-! ## Varying-cutoff column independence -/

/-- Pairwise range separation upgrades to mutual independence for the local
reads of one fixed GMC shell. -/
theorem iIndep_potentialShellLocalSigma_of_pairwise_separated
    {d : ℕ} {ι : Type*}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ)
    {U : ι → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j => ∀ ⦃x y : Vec d⦄, x ∈ U i → y ∈ U j →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ k ≤ Ch02.vecNorm (x - y)) :
    iIndep (fun i =>
      (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (U i)).comap
        (fun omega : Sample d => omega k)) M.P.toMeasure := by
  classical
  rw [iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hUnion : MeasurableSet (⋃ j ∈ s, U j) :=
        Finset.measurableSet_biUnion _ fun j _ => hU j
      have hsepUnion : ∀ ⦃x y : Vec d⦄, x ∈ U i → y ∈ ⋃ j ∈ s, U j →
          Real.sqrt (d : ℝ) * (3 : ℝ) ^ k ≤ Ch02.vecNorm (x - y) := by
        intro x y hx hy
        obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.1 hy
        have hij : i ≠ j := by
          intro heq
          apply hi
          simpa [heq] using hj
        exact hsep hij hx hyj
      have hmeas :
          MeasurableSet[
            (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (⋃ j ∈ s, U j)).comap
              (fun omega : Sample d => omega k)] (⋂ j ∈ s, f j) := by
        refine @Finset.measurableSet_biInter _ _
          ((_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (⋃ j ∈ s, U j)).comap
            (fun omega : Sample d => omega k)) _ _ (fun j hj => ?_)
        exact MeasurableSpace.comap_mono
          (potentialFieldLocalSigma_mono
            (fun x hx => Set.mem_iUnion₂.2 ⟨j, hj, hx⟩)) _
          (hf j (Finset.mem_insert_of_mem hj))
      have hindep := indep_potentialShellLocal_of_cutoff_separation M k
        (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))
        (U i) (⋃ j ∈ s, U j) (hU i) hUnion hsepUnion
      have hprod := (Indep_iff _ _ M.P.toMeasure).1 hindep
        (f i) (⋂ j ∈ s, f j) (hf i (Finset.mem_insert_self i s)) hmeas
      rw [Finset.set_biInter_insert, hprod, Finset.prod_insert hi,
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

def activeCutoffShellRegion {d : ℕ} {ι : Type*}
    (Lidx : ι → ℕ) (U : ι → Set (Vec d)) (i : ι) (k : ℕ) : Set (Vec d) :=
  if k ≤ Lidx i then U i else ∅

@[instance_reducible]
def activeCutoffShellSigma {d : ℕ} {ι : Type*}
    (Lidx : ι → ℕ) (U : ι → Set (Vec d)) (i : ι) (k : ℕ) :
    MeasurableSpace (Sample d) :=
  (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma
    (activeCutoffShellRegion Lidx U i k)).comap
      (fun omega : Sample d => omega k)

theorem activeCutoffShellSigma_le {d : ℕ} {ι : Type*}
    (Lidx : ι → ℕ) (U : ι → Set (Vec d)) (i : ι) (k : ℕ) :
    activeCutoffShellSigma Lidx U i k ≤
      MeasurableSpace.comap (fun omega : Sample d => omega k) inferInstance :=
  MeasurableSpace.comap_mono
    (potentialFieldLocalSigma_le_borel (activeCutoffShellRegion Lidx U i k))

theorem aCutoffPotentialLocalSigma_le_iSup_active {d : ℕ} {ι : Type*}
    (Lidx : ι → ℕ) (U : ι → Set (Vec d)) (i : ι) :
    aCutoffPotentialLocalSigma (Lidx i) (U i) ≤
      ⨆ k : ℕ, activeCutoffShellSigma Lidx U i k := by
  unfold aCutoffPotentialLocalSigma
  refine iSup_le fun k => ?_
  have hk : (k : ℕ) ≤ Lidx i := Nat.le_of_lt_succ k.isLt
  have heq : activeCutoffShellSigma Lidx U i k =
      (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (U i)).comap
        (fun omega : Sample d => omega k) := by
    unfold activeCutoffShellSigma activeCutoffShellRegion
    rw [ite_eq_left hk]
  rw [← heq]
  exact le_iSup (fun l : ℕ => activeCutoffShellSigma Lidx U i l) k

theorem iIndep_activeCutoffShellSigma_row {d : ℕ} {ι : Type*}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Lidx : ι → ℕ)
    {U : ι → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j => ∀ ⦃x y : Vec d⦄, x ∈ U i → y ∈ U j →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ min (Lidx i) (Lidx j) ≤
        Ch02.vecNorm (x - y))
    (k : ℕ) :
    iIndep (fun i => activeCutoffShellSigma Lidx U i k) M.P.toMeasure := by
  have hUactive : ∀ i, MeasurableSet (activeCutoffShellRegion Lidx U i k) := by
    intro i
    unfold activeCutoffShellRegion
    split_ifs
    · exact hU i
    · exact MeasurableSet.empty
  apply iIndep_potentialShellLocalSigma_of_pairwise_separated M k hUactive
  intro i j hij x y hx hy
  by_cases hi : k ≤ Lidx i
  · by_cases hj : k ≤ Lidx j
    · have hpow : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ min (Lidx i) (Lidx j) :=
        pow_le_pow_right₀ (by norm_num) (le_min hi hj)
      have hthreshold :
          Real.sqrt (d : ℝ) * (3 : ℝ) ^ k ≤
            Real.sqrt (d : ℝ) * (3 : ℝ) ^ min (Lidx i) (Lidx j) :=
        mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)
      apply hthreshold.trans
      apply hsep hij
      · simpa [activeCutoffShellRegion, hi] using hx
      · simpa [activeCutoffShellRegion, hj] using hy
    · simp [activeCutoffShellRegion, hj] at hy
  · simp [activeCutoffShellRegion, hi] at hx

/-- Honest mutual independence for spatially local finite cutoffs whose
truncation levels vary with the column. -/
theorem iIndep_aCutoffPotentialLocalSigma_of_varyingLevel
    {d : ℕ} {ι : Type*}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Lidx : ι → ℕ)
    {U : ι → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j => ∀ ⦃x y : Vec d⦄, x ∈ U i → y ∈ U j →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ min (Lidx i) (Lidx j) ≤
        Ch02.vecNorm (x - y)) :
    iIndep (fun i => aCutoffPotentialLocalSigma (Lidx i) (U i))
      M.P.toMeasure := by
  have hjoin :
      iIndep (fun i => ⨆ k : ℕ, activeCutoffShellSigma Lidx U i k)
        M.P.toMeasure :=
    iIndep_iSup_of_iIndep_rows
      (kappa := fun k : ℕ =>
        MeasurableSpace.comap (fun omega : Sample d => omega k) inferInstance)
      M.shellPrefix.independent.iIndep
      (fun k => (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k).comap_le)
      (fun i k => activeCutoffShellSigma_le Lidx U i k)
      (fun k => iIndep_activeCutoffShellSigma_row M Lidx hU hsep k)
  exact iIndep_of_le hjoin fun i =>
    aCutoffPotentialLocalSigma_le_iSup_active Lidx U i

/-- Exact Appendix-B column certificate, reduced only to the deterministic
separation of the annular read regions along each residue class. -/
theorem columnsIndep_responseScoreArray_of_separated
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s epsilon K : ℝ)
    (r : ℕ)
    (hsep : ∀ b : ℤ,
      Pairwise fun i j :
          {q : ℤ // 0 ≤ q * (r : ℤ) + b} =>
        ∀ ⦃x y : Vec d⦄,
          x ∈ responseAnnulusReadRegion d (i.1 * (r : ℤ) + b).toNat →
          y ∈ responseAnnulusReadRegion d (j.1 * (r : ℤ) + b).toNat →
          Real.sqrt (d : ℝ) *
              (3 : ℝ) ^ min ((i.1 * (r : ℤ) + b).toNat - 2)
                ((j.1 * (r : ℤ) + b).toNat - 2) ≤
            Ch02.vecNorm (x - y)) :
    SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      (responseScoreArray M s epsilon K) r := by
  intro b
  let A : Set ℤ := {j | 0 ≤ j * (r : ℤ) + b}
  let F : ℤ → Sample d → (ℤ → ℝ) := fun j omega k =>
    responseScoreArray M s epsilon K k (j * (r : ℤ) + b) omega
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
        let : MeasurableSpace (Sample d) :=
          aCutoffPotentialLocalSigma (Lidx j) (U j)
        apply Measurable.of_eval
        intro k
        have hj : 0 ≤ j.1 * (r : ℤ) + b := j.2
        by_cases hkj : 0 ≤ k ∧ j.1 * (r : ℤ) + b ≤ k
        · have hfull : 0 ≤ k ∧ 0 ≤ j.1 * (r : ℤ) + b ∧
              j.1 * (r : ℤ) + b ≤ k := ⟨hkj.1, hj, hkj.2⟩
          simp only [F, responseScoreArray, ite_eq_left hfull]
          exact ENNReal.measurable_toReal.comp
            (measurable_localResponseScore M s epsilon K
              (j.1 * (r : ℤ) + b).toNat)
        · have hnot : ¬(0 ≤ k ∧ 0 ≤ j.1 * (r : ℤ) + b ∧
              j.1 * (r : ℤ) + b ≤ k) := by omega
          simp only [F, responseScoreArray, ite_eq_right hnot]
          exact measurable_const
      exact hF.comap_le
  · intro j hj
    have hneg : j * (r : ℤ) + b < 0 := by simpa [A] using hj
    refine ⟨fun _ => 0, ?_⟩
    intro omega
    funext k
    simp [F, responseScoreArray, show ¬0 ≤ j * (r : ℤ) + b by omega]

end


end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
