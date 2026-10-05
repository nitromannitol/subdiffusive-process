module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanControlComparator
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanControlReduction

@[expose] public section

/-!
# The physical boundary mean through flat comparators

This is the noncircular scalar decomposition used in the Superdiffusion
excess-decay argument.  The physical mean is split through two flat harmonic
replacements; face oddness controls their difference, and the latter's
oscillation is returned to the two comparison errors plus the physical and
datum oscillations.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-- Loop-free physical mean control on one clamped boundary cell. -/
theorem exists_physicalBoundaryMean_le_flatComparatorPrices
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m k : ℤ) (q : Vec d) (i : Fin d) (sg : ℝ)
        (u h : H1Function (openCubeSet (originCube d m))),
        k < m → (sg = 1 ∨ sg = -1) →
        wellPlacedHalfGap m k < sg * q i →
        MemH10 (openCubeSet (originCube d m))
          (fun y => u.toFun y - h.toFun y) →
        let c := wellPlacedCentre q m k
        let P := translatedCube d k c
        ∃ ubar hbar : H1Function (truncatedWindow c m k),
          IsUnitWeaklyHarmonicOn (truncatedWindow c m k) ubar ∧
          IsUnitWeaklyHarmonicOn (truncatedWindow c m k) hbar ∧
          MemH10 (truncatedWindow c m k)
            (fun y => ubar.toFun y - u.toFun y) ∧
          MemH10 (truncatedWindow c m k)
            (fun y => hbar.toFun y - h.toFun y) ∧
          normalizedL2On P (fun y => u.toFun y - ubar.toFun y) ≤
            flatComparatorPriceConst d * (3 : ℝ) ^ k *
              ∑ j : Fin d, normalizedL2On P (fun y => u.grad y j) ∧
          normalizedL2On P (fun y => h.toFun y - hbar.toFun y) ≤
            flatComparatorPriceConst d * (3 : ℝ) ^ k *
              ∑ j : Fin d, normalizedL2On P (fun y => h.grad y j) ∧
          |volumeAverage P (fun y => u.toFun y - h.toFun y)| ≤
            (1 + 2 * C) *
                (normalizedL2On P (fun y => u.toFun y - ubar.toFun y) +
                  normalizedL2On P (fun y => h.toFun y - hbar.toFun y)) +
              C * (normalizedL2On P
                    (fun y => u.toFun y - volumeAverage P u.toFun) +
                  normalizedL2On P
                    (fun y => h.toFun y - volumeAverage P h.toFun)) := by
  classical
  obtain ⟨C, hC0, hpair⟩ :=
    exists_flatComparatorDifference_mean_le_oscillation d
  refine ⟨C, hC0, ?_⟩
  intro m k q i sg u h hkm hsg hover hdat
  let c : Vec d := wellPlacedCentre q m k
  let P : Set (Vec d) := translatedCube d k c
  let W : Set (Vec d) := truncatedWindow c m k
  have hWP : W = P := by
    simpa only [W, P, c] using!
      truncatedWindow_wellPlacedCentre_eq_translatedCube hkm.le q
  obtain ⟨ubar, hbar, hubarHarm, hhbarHarm, hubarTrace, hhbarTrace,
      hubarPrice, hhbarPrice, hdiffMean⟩ :=
    hpair m k q i sg u h hkm hsg hover hdat
  have hPsub : P ⊆ openCubeSet (originCube d m) := by
    dsimp only [P, c]
    exact translatedCube_wellPlacedCentre_subset_cube q hkm.le
  have huP : MemLp u.toFun 2 (volume.restrict P) :=
    u.memL2.mono_measure (Measure.restrict_mono hPsub le_rfl)
  have hhP : MemLp h.toFun 2 (volume.restrict P) :=
    h.memL2.mono_measure (Measure.restrict_mono hPsub le_rfl)
  have hubarP : MemLp ubar.toFun 2 (volume.restrict P) := by
    rw [← hWP]
    exact ubar.memL2
  have hhbarP : MemLp hbar.toFun 2 (volume.restrict P) := by
    rw [← hWP]
    exact hbar.memL2
  have hPmeas : MeasurableSet P := by
    dsimp only [P]
    exact measurableSet_translatedCube d k c
  have hPtop : volume P ≠ ⊤ := by
    rw [← hWP]
    exact ne_of_lt (volume_truncatedWindow_lt_top c m k)
  have hPpos : 0 < (volume P).toReal := by
    apply ENNReal.toReal_pos
    · rw [← hWP]
      exact (SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.volume_truncatedWindow_pos
        k (wellPlacedCentre_mem_cube q hkm.le)).ne'
    · exact hPtop
  let : IsFiniteMeasure (volume.restrict P) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hPtop⟩
  have huv := huP.sub hubarP
  have hhbh := hhbarP.sub hhP
  have hvh := hubarP.sub hhbarP
  have hsplit := abs_volumeAverage_sub_le_comparatorSplit
    hPmeas hPpos (huv.integrable (by norm_num))
      (hhbh.integrable (by norm_num)) (hvh.integrable (by norm_num))
      huv.integrable_sq hhbh.integrable_sq
  have hosc := oscillation_comparatorDifference_le
    hPmeas hPpos hPtop
    (huP.integrable (by norm_num)) (hhP.integrable (by norm_num))
    (hubarP.integrable (by norm_num)) (hhbarP.integrable (by norm_num))
    huv.integrable_sq (hhP.sub hhbarP).integrable_sq
    (hubarP.sub huP)
    (hhbarP.sub hhP)
    (huP.sub (memLp_const _))
    (hhP.sub (memLp_const _))
    (hubarP.sub (memLp_const _))
    ((hhbarP.sub (memLp_const _)).neg)
  have hnegNorm : normalizedL2On P (fun y => hbar.toFun y - h.toFun y) =
      normalizedL2On P (fun y => h.toFun y - hbar.toFun y) := by
    have heq : (fun y => hbar.toFun y - h.toFun y) =
        fun y => -(h.toFun y - hbar.toFun y) := by
      funext y
      ring
    rw [heq, normalizedL2On_neg]
  rw [hnegNorm] at hsplit
  have hdiff := hdiffMean
  change |volumeAverage P (fun y => ubar.toFun y - hbar.toFun y)| ≤
    C * normalizedL2On P
      (fun y => (ubar.toFun y - hbar.toFun y) -
        volumeAverage P (fun z => ubar.toFun z - hbar.toFun z)) at hdiff
  have hCmul := mul_le_mul_of_nonneg_left hosc hC0
  refine ⟨ubar, hbar, hubarHarm, hhbarHarm, hubarTrace, hhbarTrace,
    hubarPrice, hhbarPrice, ?_⟩
  try dsimp only [c, P] at ⊢
  calc
    |volumeAverage P (fun y => u.toFun y - h.toFun y)| ≤
        (normalizedL2On P (fun y => u.toFun y - ubar.toFun y) +
          normalizedL2On P (fun y => h.toFun y - hbar.toFun y)) +
        |volumeAverage P (fun y => ubar.toFun y - hbar.toFun y)| := hsplit
    _ ≤ (normalizedL2On P (fun y => u.toFun y - ubar.toFun y) +
          normalizedL2On P (fun y => h.toFun y - hbar.toFun y)) +
        C * normalizedL2On P
          (fun y => (ubar.toFun y - hbar.toFun y) -
            volumeAverage P (fun z => ubar.toFun z - hbar.toFun z)) :=
      add_le_add (le_refl _) hdiff
    _ ≤ (normalizedL2On P (fun y => u.toFun y - ubar.toFun y) +
          normalizedL2On P (fun y => h.toFun y - hbar.toFun y)) +
        C * (2 * normalizedL2On P (fun y => u.toFun y - ubar.toFun y) +
          2 * normalizedL2On P (fun y => h.toFun y - hbar.toFun y) +
          normalizedL2On P (fun y => u.toFun y - volumeAverage P u.toFun) +
          normalizedL2On P (fun y => h.toFun y - volumeAverage P h.toFun)) :=
      add_le_add (le_refl _) hCmul
    _ = (1 + 2 * C) *
          (normalizedL2On P (fun y => u.toFun y - ubar.toFun y) +
            normalizedL2On P (fun y => h.toFun y - hbar.toFun y)) +
        C * (normalizedL2On P
              (fun y => u.toFun y - volumeAverage P u.toFun) +
            normalizedL2On P
              (fun y => h.toFun y - volumeAverage P h.toFun)) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
