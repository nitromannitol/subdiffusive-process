import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.MaximalDerivative
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable

/-!
# A restricted-coefficient measurable gradient envelope

The Gaussian derivative envelope is not measurable in the sigma-field generated
by the cutoff coefficient on the ambient cube.  This file replaces it at the
consumer boundary by a countable dense-pair Lipschitz modulus of `log aCutoff`.
It is measurable in the restricted coefficient sigma-field, while the shell
derivative envelope dominates it pathwise and hence supplies its Gaussian tail.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open Homogenization IndependentSums
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := PotentialSample d

/-- One countable two-point test of the logarithmic Lipschitz modulus. -/
def coveringLogSlopeTest {d : ℕ} (M : GMCModel d) (L : ℕ) (m : ℤ)
    (z : Vec d) (q : (Fin d → ℤ) × ℕ × ℕ) (omega : Sample d) : ℝ :=
  let p := q.1
  let x := Section6Anchored.densePt d q.2.1
  let y := Section6Anchored.densePt d q.2.2
  if p ∈ shellCoverShifts d m ∧
      x ∈ boundedMultiplierCoverCell d m z p ∧
      y ∈ boundedMultiplierCoverCell d m z p ∧ x ≠ y then
    |Real.log (aCutoff M L omega x) - Real.log (aCutoff M L omega y)| /
      ‖x - y‖
  else 0

/-- The canonical restricted-sigma logarithmic Lipschitz envelope on all unit
cells of the finite cover. -/
def coveringLogLipschitzModulus {d : ℕ} (M : GMCModel d) (L : ℕ) (m : ℤ)
    (z : Vec d) (omega : Sample d) : ℝ :=
  ⨆ q : (Fin d → ℤ) × ℕ × ℕ, coveringLogSlopeTest M L m z q omega

private theorem translatedCube_convex {d : ℕ} (m : ℤ) (z : Vec d) :
    Convex ℝ (translatedCube d m z) := by
  unfold translatedCube cube
  exact (convex_openCubeSet (originCube d m)).translate z

private theorem log_pair_slope_le_derivativeEnvelope {d : ℕ}
    (M : GMCModel d) (L : ℕ) (c : Vec d) (omega : Sample d)
    {x y : Vec d} (hx : x ∈ translatedCube d 0 c)
    (hy : y ∈ translatedCube d 0 c) (hxy : x ≠ y) :
    |Real.log (aCutoff M L omega x) - Real.log (aCutoff M L omega y)| /
        ‖x - y‖ ≤ fixedCutoffLogDerivativeEnvelope L c omega := by
  have hmean := (translatedCube_convex 0 c).norm_image_sub_le_of_norm_fderiv_le
    (f := fun w : Vec d ↦ Real.log (aCutoff M L omega w))
    (fun w _hw ↦ (hasFDerivAt_log_aCutoff M L omega w).differentiableAt)
    (fun w hw ↦ by
      rw [(hasFDerivAt_log_aCutoff M L omega w).fderiv]
      exact norm_fixedCutoffLogFDeriv_le_envelope L c omega hw)
    hx hy
  rw [Real.norm_eq_abs] at hmean
  have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  rw [div_le_iff₀ hnorm]
  simpa only [abs_sub_comm, norm_sub_rev] using hmean

theorem coveringLogSlopeTest_nonneg {d : ℕ} (M : GMCModel d) (L : ℕ)
    (m : ℤ) (z : Vec d) (q : (Fin d → ℤ) × ℕ × ℕ)
    (omega : Sample d) : 0 ≤ coveringLogSlopeTest M L m z q omega := by
  dsimp [coveringLogSlopeTest]
  split_ifs
  · positivity
  · exact le_rfl

private theorem coveringLogSlopeTest_le_coverSum {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    (q : (Fin d → ℤ) × ℕ × ℕ) (omega : Sample d) :
    coveringLogSlopeTest M L m z q omega ≤
      ∑ p ∈ shellCoverShifts d m,
        fixedCutoffLogDerivativeEnvelope L
          (z + physicalShellCoverCenter 0 p) omega := by
  dsimp [coveringLogSlopeTest]
  split_ifs with h
  · rcases h with ⟨hp, hx, hy, hxy⟩
    have hslope := log_pair_slope_le_derivativeEnvelope M L
      (z + physicalShellCoverCenter 0 q.1) omega hx.2 hy.2 hxy
    have hnonneg (p : Fin d → ℤ) : 0 ≤
        fixedCutoffLogDerivativeEnvelope L
          (z + physicalShellCoverCenter 0 p) omega := by
      unfold fixedCutoffLogDerivativeEnvelope
      exact Finset.sum_nonneg fun k _hk ↦
        translatedSmallShellEnvelope_nonneg k (0 : ℤ)
          (z + physicalShellCoverCenter 0 p) omega
    exact hslope.trans (Finset.single_le_sum
      (fun p _hp' ↦ hnonneg p)
      hp)
  · exact Finset.sum_nonneg fun p _hp ↦ by
      unfold fixedCutoffLogDerivativeEnvelope
      exact Finset.sum_nonneg fun k _hk ↦
        translatedSmallShellEnvelope_nonneg k (0 : ℤ)
          (z + physicalShellCoverCenter 0 p) omega

private theorem bddAbove_coveringLogSlopeTest {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) (omega : Sample d) :
    BddAbove (Set.range fun q : (Fin d → ℤ) × ℕ × ℕ ↦
      coveringLogSlopeTest M L m z q omega) := by
  refine ⟨∑ p ∈ shellCoverShifts d m,
      fixedCutoffLogDerivativeEnvelope L
        (z + physicalShellCoverCenter 0 p) omega, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact coveringLogSlopeTest_le_coverSum M L m z q omega

theorem coveringLogSlopeTest_le_modulus {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    (q : (Fin d → ℤ) × ℕ × ℕ) (omega : Sample d) :
    coveringLogSlopeTest M L m z q omega ≤
      coveringLogLipschitzModulus M L m z omega := by
  exact le_ciSup (bddAbove_coveringLogSlopeTest M L m z omega) q

theorem coveringLogLipschitzModulus_nonneg {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) (omega : Sample d) :
    0 ≤ coveringLogLipschitzModulus M L m z omega := by
  let q : (Fin d → ℤ) × ℕ × ℕ := (0, 0, 0)
  exact (coveringLogSlopeTest_nonneg M L m z q omega).trans
    (coveringLogSlopeTest_le_modulus M L m z q omega)

theorem measurable_coveringLogLipschitzModulus_restricted {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) :
    @Measurable (Sample d) ℝ
      (restrictedCoefficientSigma (aCutoff M L) (translatedCube d m z))
      inferInstance (coveringLogLipschitzModulus M L m z) := by
  unfold coveringLogLipschitzModulus
  refine Measurable.iSup fun q ↦ ?_
  let x := Section6Anchored.densePt d q.2.1
  let y := Section6Anchored.densePt d q.2.2
  by_cases h : q.1 ∈ shellCoverShifts d m ∧
      x ∈ boundedMultiplierCoverCell d m z q.1 ∧
      y ∈ boundedMultiplierCoverCell d m z q.1 ∧ x ≠ y
  · rcases h with ⟨_hp, hx, hy, _hxy⟩
    have heq : coveringLogSlopeTest M L m z q = fun omega ↦
        |Real.log (aCutoff M L omega x) - Real.log (aCutoff M L omega y)| /
          ‖x - y‖ := by
      funext omega
      simp [coveringLogSlopeTest, x, y, _hp, hx, hy, _hxy]
    rw [heq]
    have hxm : @Measurable (Sample d) ℝ
        (restrictedCoefficientSigma (aCutoff M L) (translatedCube d m z))
        inferInstance (fun omega ↦ aCutoff M L omega x) :=
      measurable_eval_restrictedCoefficientSigma hx.1
    have hym : @Measurable (Sample d) ℝ
        (restrictedCoefficientSigma (aCutoff M L) (translatedCube d m z))
        inferInstance (fun omega ↦ aCutoff M L omega y) :=
      measurable_eval_restrictedCoefficientSigma hy.1
    have hsub : @Measurable (Sample d) ℝ
        (restrictedCoefficientSigma (aCutoff M L) (translatedCube d m z))
        inferInstance (fun omega ↦ Real.log (aCutoff M L omega x) -
          Real.log (aCutoff M L omega y)) := hxm.log.sub hym.log
    have habs : @Measurable (Sample d) ℝ
        (restrictedCoefficientSigma (aCutoff M L) (translatedCube d m z))
        inferInstance (fun omega ↦ |Real.log (aCutoff M L omega x) -
          Real.log (aCutoff M L omega y)|) :=
      continuous_abs.measurable.comp hsub
    exact habs.div_const _
  · have heq : coveringLogSlopeTest M L m z q = fun _ ↦ (0 : ℝ) := by
      funext omega
      simp only [coveringLogSlopeTest]
      rw [if_neg]
      simpa only [x, y] using h
    rw [heq]
    exact measurable_const

private theorem translatedCube_isOpen {d : ℕ} (m : ℤ) (z : Vec d) :
    IsOpen (translatedCube d m z) := by
  have hset : translatedCube d m z =
      (fun x : Vec d ↦ x - z) ⁻¹' openCubeSet (originCube d m) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      change u ∈ openCubeSet (originCube d m) at hu
      simpa using hu
    · intro hx
      refine ⟨x - z, ?_, ?_⟩
      · simpa [cube] using hx
      · ext i
        simp
  rw [hset]
  exact (isOpen_openCubeSet (originCube d m)).preimage
    (continuous_id.sub continuous_const)

private theorem abs_sub_le_mul_norm_of_densePt {d : ℕ} {B : Set (Vec d)}
    (hB : IsOpen B) {f : Vec d → ℝ} (hf : Continuous f) {G : ℝ}
    (hG : ∀ i j : ℕ, Section6Anchored.densePt d i ∈ B →
      Section6Anchored.densePt d j ∈ B →
      |f (Section6Anchored.densePt d i) -
        f (Section6Anchored.densePt d j)| ≤
        G * ‖Section6Anchored.densePt d i - Section6Anchored.densePt d j‖) :
    ∀ x ∈ B, ∀ y ∈ B, |f x - f y| ≤ G * ‖x - y‖ := by
  have hclosed : IsClosed {q : Vec d × Vec d |
      |f q.1 - f q.2| ≤ G * ‖q.1 - q.2‖} := by
    exact isClosed_le
      (continuous_abs.comp
        ((hf.comp continuous_fst).sub (hf.comp continuous_snd)))
      (continuous_const.mul ((continuous_fst.sub continuous_snd).norm))
  have hsub : B ×ˢ B ∩
      (Set.range (Section6Anchored.densePt d) ×ˢ
        Set.range (Section6Anchored.densePt d)) ⊆
      {q : Vec d × Vec d | |f q.1 - f q.2| ≤ G * ‖q.1 - q.2‖} := by
    rintro ⟨u, v⟩ ⟨⟨hu, hv⟩, ⟨i, rfl⟩, ⟨j, rfl⟩⟩
    exact hG i j hu hv
  have hdense : Dense
      (Set.range (Section6Anchored.densePt d) ×ˢ
        Set.range (Section6Anchored.densePt d)) :=
    Section6Anchored.dense_range_densePt.prod
      Section6Anchored.dense_range_densePt
  intro x hx y hy
  have hxy : (x, y) ∈ B ×ˢ B := ⟨hx, hy⟩
  exact hclosed.closure_subset_iff.mpr hsub
    (hdense.open_subset_closure_inter (hB.prod hB) hxy)

/-- The countable modulus controls every pair in every clipped unit cell.
This is the consumer-facing replacement for an `L∞` gradient norm. -/
theorem abs_log_aCutoff_sub_le_coveringLogLipschitzModulus_mul_norm
    {d : ℕ} (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    (omega : Sample d) (p : Fin d → ℤ) (hp : p ∈ shellCoverShifts d m)
    {x y : Vec d} (hx : x ∈ boundedMultiplierCoverCell d m z p)
    (hy : y ∈ boundedMultiplierCoverCell d m z p) :
    |Real.log (aCutoff M L omega x) - Real.log (aCutoff M L omega y)| ≤
      coveringLogLipschitzModulus M L m z omega * ‖x - y‖ := by
  refine abs_sub_le_mul_norm_of_densePt
    ((translatedCube_isOpen m z).inter
      (translatedCube_isOpen 0 (z + physicalShellCoverCenter 0 p)))
    ((continuous_aCutoff M L omega).log fun u ↦
      (aCutoff_pos M L omega u).ne') ?_ x hx y hy
  intro i j hi hj
  by_cases hij : Section6Anchored.densePt d i =
      Section6Anchored.densePt d j
  · rw [hij]
    simp
  · have htest := coveringLogSlopeTest_le_modulus M L m z
      (p, i, j) omega
    dsimp [coveringLogSlopeTest] at htest
    rw [if_pos ⟨hp, hi, hj, hij⟩] at htest
    have hnorm : 0 < ‖Section6Anchored.densePt d i -
        Section6Anchored.densePt d j‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hij)
    rw [div_le_iff₀ hnorm] at htest
    exact htest

private theorem fixedCutoffLogDerivativeEnvelope_nonneg {d : ℕ}
    (L : ℕ) (z : Vec d) (omega : Sample d) :
    0 ≤ fixedCutoffLogDerivativeEnvelope L z omega := by
  unfold fixedCutoffLogDerivativeEnvelope
  exact Finset.sum_nonneg fun k _hk ↦
    translatedSmallShellEnvelope_nonneg k (0 : ℤ) z omega

private theorem coveringLogLipschitzModulus_le_of_envelopes_le {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    (omega : Sample d) {t : ℝ}
    (ht : ∀ p ∈ shellCoverShifts d m,
      fixedCutoffOscillationEnvelope L
        (z + physicalShellCoverCenter 0 p) omega ≤ t) :
    coveringLogLipschitzModulus M L m z omega ≤ t / 2 := by
  unfold coveringLogLipschitzModulus
  apply ciSup_le
  intro q
  dsimp [coveringLogSlopeTest]
  split_ifs with h
  · rcases h with ⟨hp, hx, hy, hxy⟩
    have hslope := log_pair_slope_le_derivativeEnvelope M L
      (z + physicalShellCoverCenter 0 q.1) omega hx.2 hy.2 hxy
    have henv := ht q.1 hp
    rw [fixedCutoffOscillationEnvelope_eq_two_mul_logDerivativeEnvelope] at henv
    exact hslope.trans (by linarith)
  · have hnonneg := fixedCutoffLogDerivativeEnvelope_nonneg L
        (z + physicalShellCoverCenter 0 (Classical.choose
          (shellCoverShifts_nonempty d m))) omega
    have henv := ht (Classical.choose (shellCoverShifts_nonempty d m))
      (Classical.choose_spec (shellCoverShifts_nonempty d m))
    rw [fixedCutoffOscillationEnvelope_eq_two_mul_logDerivativeEnvelope] at henv
    linarith

/-- Unshifted `Gamma_2` tail for the maximum over the unit cells.  The only
entropy cost is the finite union over those cells. -/
theorem measureReal_coveringLogLipschitzModulus_tail_le {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    {s : ℝ} (hs : 1 ≤ s) :
    M.P.toMeasure.real
        {omega | fixedCutoffOscillationConst * M.delta * s / 2 <
          coveringLogLipschitzModulus M L m z omega} ≤
      ((shellCoverShifts d m).card : ℝ) * Real.exp (-(s ^ (2 : ℝ))) := by
  let S := shellCoverShifts d m
  let A := fixedCutoffOscillationConst * M.delta
  let E : (Fin d → ℤ) → Set (Sample d) := fun p ↦
    upperTailEvent (fixedCutoffOscillationEnvelope L
      (z + physicalShellCoverCenter 0 p)) (A * s)
  have hsubset : {omega | A * s / 2 <
      coveringLogLipschitzModulus M L m z omega} ⊆
      ⋃ p ∈ S, E p := by
    intro omega hbad
    by_contra hnot
    have hall : ∀ p ∈ S,
        fixedCutoffOscillationEnvelope L
          (z + physicalShellCoverCenter 0 p) omega ≤ A * s := by
      intro p hp
      by_contra hpbad
      apply hnot
      refine Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, ?_⟩⟩
      change A * s < fixedCutoffOscillationEnvelope L
        (z + physicalShellCoverCenter 0 p) omega
      exact lt_of_not_ge hpbad
    exact (not_lt_of_ge
      (coveringLogLipschitzModulus_le_of_envelopes_le M L m z omega hall)) hbad
  calc
    M.P.toMeasure.real
        {omega | fixedCutoffOscillationConst * M.delta * s / 2 <
          coveringLogLipschitzModulus M L m z omega} ≤
        M.P.toMeasure.real (⋃ p ∈ S, E p) := by
      exact measureReal_mono (by simpa [A] using hsubset)
        (measure_ne_top M.P.toMeasure _)
    _ ≤ (S.card : ℝ) * Real.exp (-(s ^ (2 : ℝ))) := by
      exact Section6Anchored.measureReal_biUnion_upperTailEvent_le S hs
        (fun p _hp ↦ by
          simpa [A] using
            isBigOWith_gammaTwo_fixedCutoffOscillationEnvelope M L
              (z + physicalShellCoverCenter 0 p))
    _ = ((shellCoverShifts d m).card : ℝ) *
        Real.exp (-(s ^ (2 : ℝ))) := rfl

/-- The restricted-sigma gradient event at the same unshifted threshold as the
coefficient-ratio event. -/
def coveringRestrictedGradientGood {d : ℕ} (M : GMCModel d) (L : ℕ)
    (m : ℤ) (z : Vec d) : Set (Sample d) :=
  {omega | coveringLogLipschitzModulus M L m z omega ≤
    boundedMultiplierCoverOscillationThreshold M m / 2}

theorem measurableSet_coveringRestrictedGradientGood {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) :
    MeasurableSet[restrictedCoefficientSigma (aCutoff M L)
      (translatedCube d m z)]
      (coveringRestrictedGradientGood M L m z) := by
  exact measurableSet_le
    (measurable_coveringLogLipschitzModulus_restricted M L m z)
    measurable_const

theorem mem_coveringRestrictedGradientGood_of_envelopeGood {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) {omega : Sample d}
    (hgood : omega ∈ coveringFixedCutoffEnvelopeGood M L m z) :
    omega ∈ coveringRestrictedGradientGood M L m z := by
  exact coveringLogLipschitzModulus_le_of_envelopes_le M L m z omega
    (mem_coveringFixedCutoffEnvelopeGood_iff.1 hgood)

/-- The printed exceptional probability, now for an event measurable in the
restricted coefficient sigma-field. -/
theorem measure_compl_coveringRestrictedGradientGood_le {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) :
    M.P.toMeasure (coveringRestrictedGradientGood M L m z)ᶜ ≤
      ENNReal.ofReal
        (Real.exp (-1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) := by
  refine (measure_mono ?_).trans
    (measure_compl_coveringFixedCutoffEnvelopeGood_le M L m z)
  intro omega hbad henv
  exact hbad (mem_coveringRestrictedGradientGood_of_envelopeGood
    M L m z henv)

/-- Restricted-sigma bad-event packaging together with the random Lipschitz
modulus used to choose the local radius. -/
theorem exists_restrictedBad_coveringLogLipschitzModulus {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) :
    ∃ bad : Set (Sample d),
      @MeasurableSet (Sample d)
        (restrictedCoefficientSigma (aCutoff M L) (translatedCube d m z)) bad ∧
      M.P.toMeasure bad ≤ ENNReal.ofReal
        (Real.exp (-1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
      ∀ omega ∉ bad,
        coveringLogLipschitzModulus M L m z omega ≤
          boundedMultiplierCoverOscillationThreshold M m / 2 := by
  refine ⟨(coveringRestrictedGradientGood M L m z)ᶜ,
    (measurableSet_coveringRestrictedGradientGood M L m z).compl,
    measure_compl_coveringRestrictedGradientGood_le M L m z, ?_⟩
  intro omega homega
  simpa [coveringRestrictedGradientGood] using homega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
