import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ProjectedCoverAssembly
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Composition




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Finite-cover absorption in the literal order used by the manuscript:
first average the cellwise remainders and only then move their common
fraction of the parent average to the left. -/
theorem descendantsAverage_le_of_remainder_average_absorb
    (Q : TriadicCube d) (F remainder : TriadicCube d → ℝ)
    {B theta : ℝ} (hthetaOne : theta < 1)
    (hcell : ∀ R ∈ descendantsAtDepth Q 2, F R ≤ B + remainder R)
    (hremainder : descendantsAverage Q 2 remainder ≤
      theta * descendantsAverage Q 2 F) :
    descendantsAverage Q 2 F ≤ (1 - theta)⁻¹ * B := by
  have havg := descendantsAverage_le_descendantsAverage Q 2 hcell
  rw [descendantsAverage_add_local, descendantsAverage_const_eq] at havg
  have hgap : 0 < 1 - theta := sub_pos.mpr hthetaOne
  have hlin : (1 - theta) * descendantsAverage Q 2 F ≤ B := by
    linarith only [havg, hremainder]
  calc
    descendantsAverage Q 2 F =
        (1 - theta)⁻¹ * ((1 - theta) * descendantsAverage Q 2 F) := by
      field_simp [hgap.ne']
    _ ≤ (1 - theta)⁻¹ * B :=
      mul_le_mul_of_nonneg_left hlin (inv_nonneg.mpr hgap.le)

/-- Half-absorbable specialization of
`descendantsAverage_le_of_remainder_average_absorb`. -/
theorem descendantsAverage_le_two_mul_of_remainder_average_half_absorb
    (Q : TriadicCube d) (F remainder : TriadicCube d → ℝ) {B : ℝ}
    (hcell : ∀ R ∈ descendantsAtDepth Q 2, F R ≤ B + remainder R)
    (hremainder : descendantsAverage Q 2 remainder ≤
      (1 / 2 : ℝ) * descendantsAverage Q 2 F) :
    descendantsAverage Q 2 F ≤ 2 * B := by
  have h := descendantsAverage_le_of_remainder_average_absorb Q F remainder
    (theta := (1 / 2 : ℝ)) (by norm_num) hcell hremainder
  norm_num at h ⊢
  exact h

/-- Physical projected-cover form of the average-level half absorption.  The
boundary remainder is indexed by the actual cell centre; only its *finite
average* is required to be half of the parent energy. -/
theorem normalizedCutoffEnergy_projectedCover_le_two_mul_of_remainderAverage
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m n : ℕ} {x y : Vec d}
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (hD : translatedCube d ((n : ℤ) - 2) y ⊆
      truncatedCube d (m : ℤ) ((n : ℤ) - 1) x)
    (remainder : Vec d → ℝ) {B : ℝ}
    (hremainderNonneg : ∀ q, 0 ≤ remainder q)
    (hinterior : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ B)
    (hboundary : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ B + remainder q)
    (hremainder : descendantsAverage (originCube d ((n : ℤ) - 2)) 2
        (fun R ↦ remainder (y + triadicCubeShift R)) ≤
      (1 / 2 : ℝ) * normalizedSetAverage
        (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
            vecNormSq (u.grad p))) :
    normalizedSetAverage (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
      2 * B := by
  let k : ℤ := (n : ℤ) - 2
  let energy : Vec d → ℝ := fun p ↦
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)
  let F : TriadicCube d → ℝ := fun R ↦
    normalizedSetAverage (translateSet y (openCubeSet R)) energy
  let rem : TriadicCube d → ℝ := fun R ↦
    remainder (y + triadicCubeShift R)
  have hparent : translatedCube d k y ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro p hp
    exact (hD (by simpa only [k] using hp)).2
  have hdecomp : normalizedSetAverage (translatedCube d k y) energy =
      descendantsAverage (originCube d k) 2 F := by
    simpa only [energy, F] using
      cutoffEnergy_translatedCube_eq_depthTwoDescendantsAverage
        M L omega u hparent
  have hcell : ∀ R ∈ descendantsAtDepth (originCube d k) 2,
      F R ≤ B + rem R := by
    intro R hR
    let q : Vec d := y + triadicCubeShift R
    have htranslate : translateSet y (openCubeSet (originCube d k)) =
        translatedCube d k y := by
      rw [translatedCube, cube,
        Section6SchauderDatum.image_add_eq_translateSet]
    have hq : q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x := by
      apply translated_descendantCentre_mem_of_parent_subset hR
      rw [htranslate]
      simpa only [k] using hD
    have hset : translateSet y (openCubeSet R) =
        truncatedCube d (m : ℤ) ((n : ℤ) - 4) q := by
      have heq := translate_descendant_openCubeSet_eq_truncatedCube hR
        (by
          rw [htranslate]
          simpa only [cube] using hparent)
      simpa only [k, sub_sub, sub_self, sub_zero] using heq
    by_cases hpatch : openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ)
    · have h := hinterior q hq hpatch
      rw [← hset] at h
      exact h.trans (le_add_of_nonneg_right (by
        dsimp only [rem]
        exact hremainderNonneg _))
    · have h := hboundary q hq hpatch
      rw [← hset] at h
      simpa only [F, rem, energy, q] using h
  rw [hdecomp]
  apply descendantsAverage_le_two_mul_of_remainder_average_half_absorb
    (originCube d k) F rem hcell
  have hr := hremainder
  change descendantsAverage (originCube d k) 2 rem ≤
    (1 / 2 : ℝ) * normalizedSetAverage (translatedCube d k y) energy at hr
  rw [hdecomp] at hr
  exact hr

/-- Assemble the projected `9^d` cover and only then absorb the common
residual energy.  The theorem is deliberately stated with a free coefficient
`theta`; the harmonic-approximation application uses a fixed value strictly
below one after the localized Young estimate.
-/
theorem normalizedCutoffEnergy_projectedCover_le_of_self_absorb
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m n : ℕ} {x y : Vec d}
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (hD : translatedCube d ((n : ℤ) - 2) y ⊆
      truncatedCube d (m : ℤ) ((n : ℤ) - 1) x)
    {B theta : ℝ} (htheta : 0 ≤ theta)
    (hthetaOne : theta < 1)
    (hinterior : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ B)
    (hboundary : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤
        B + theta * normalizedSetAverage
          (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p))) :
    normalizedSetAverage (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
      (1 - theta)⁻¹ * B := by
  let E : ℝ := normalizedSetAverage
    (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p))
  have henergyNonneg : ∀ p,
      0 ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p) :=
    fun p ↦ mul_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega p).le
      (vecNormSq_nonneg _)
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact volumeAverage_nonneg_of_nonneg_on
      (Section6Schauder.measurableSet_translatedCube d ((n : ℤ) - 2) y)
      (fun p _ ↦ henergyNonneg p)
  have hcover := normalizedCutoffEnergy_projectedCover_le_max
    M L omega u hD B (B + theta * E) hinterior
      (by simpa only [E] using hboundary)
  have hthetaE : 0 ≤ theta * E := mul_nonneg htheta hE
  have hBle : B ≤ B + theta * E := le_add_of_nonneg_right hthetaE
  rw [max_eq_right hBle] at hcover
  have hgap : 0 < 1 - theta := sub_pos.mpr hthetaOne
  have hlin : (1 - theta) * E ≤ B := by
    dsimp only [E] at hcover ⊢
    linarith
  calc
    E = (1 - theta)⁻¹ * ((1 - theta) * E) := by
      field_simp [hgap.ne']
    _ ≤ (1 - theta)⁻¹ * B :=
      mul_le_mul_of_nonneg_left hlin (inv_nonneg.mpr hgap.le)

/-- The concrete half-absorbable form used by the harmonic-approximation
boundary row. -/
theorem normalizedCutoffEnergy_projectedCover_le_two_mul_of_half_absorb
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m n : ℕ} {x y : Vec d}
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (hD : translatedCube d ((n : ℤ) - 2) y ⊆
      truncatedCube d (m : ℤ) ((n : ℤ) - 1) x)
    {B : ℝ}
    (hinterior : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ B)
    (hboundary : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤
        B + (1 / 2 : ℝ) * normalizedSetAverage
          (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p))) :
    normalizedSetAverage (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
      2 * B := by
  have h := normalizedCutoffEnergy_projectedCover_le_of_self_absorb
    M L omega u hD (theta := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      hinterior hboundary
  norm_num at h ⊢
  exact h

/-- Constant-collecting form of the cover-first half absorption.  It matches
the final local PDE assembly: the interior and boundary rows may have
different dimension-only constants, but share one nonnegative sum of the four
manuscript budgets. -/
theorem normalizedCutoffEnergy_projectedCover_le_two_max_mul_of_half_absorb
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m n : ℕ} {x y : Vec d}
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (hD : translatedCube d ((n : ℤ) - 2) y ⊆
      truncatedCube d (m : ℤ) ((n : ℤ) - 1) x)
    {Cinterior Cboundary budgets : ℝ}
    (hbudgets : 0 ≤ budgets)
    (hinterior : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ Cinterior * budgets)
    (hboundary : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤
        Cboundary * budgets + (1 / 2 : ℝ) * normalizedSetAverage
          (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p))) :
    normalizedSetAverage (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
      2 * max Cinterior Cboundary * budgets := by
  let C := max Cinterior Cboundary
  let B := C * budgets
  have hinterior' : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ B := by
    intro q hq hpatch
    exact (hinterior q hq hpatch).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hbudgets)
  have hboundary' : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤
        B + (1 / 2 : ℝ) * normalizedSetAverage
          (translatedCube d ((n : ℤ) - 2) y) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) := by
    intro q hq hpatch
    exact (hboundary q hq hpatch).trans (add_le_add
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hbudgets) le_rfl)
  have h := normalizedCutoffEnergy_projectedCover_le_two_mul_of_half_absorb
    M L omega u hD hinterior' hboundary'
  simpa only [B, C, mul_assoc] using h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
