module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryWindowPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanControlGeometry

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03

noncomputable section

variable {d : ℕ}

/-- Every projected boundary cell selected by the manuscript's negated
interior gate has a genuine flush face.  Thus there is no edge/corner class
for which the zero-trace face degenerates: one signed coordinate always
reaches the ambient frontier exactly. -/
theorem exists_projectedBoundaryCell_flushFace
    {m k : ℤ} {q : Vec d} (hkm : k ≤ m)
    (hnot : ¬ translatedCube d (k - 1) q ⊆ cube d m) :
    ∃ (i : Fin d) (sigma : ℝ), (sigma = 1 ∨ sigma = -1) ∧
      sigma * Section6ExcessDecay.wellPlacedCentre q m k i +
          (1 / 2 : ℝ) * (3 : ℝ) ^ k =
        (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  obtain ⟨i, sigma, hsigma, hover⟩ :=
    exists_signedOverhang_of_not_translatedCube_subset hnot
  have hbase : 0 < (3 : ℝ) ^ (k - 1) := zpow_pos (by norm_num) _
  have hscale : (3 : ℝ) ^ k = 3 * (3 : ℝ) ^ (k - 1) := by
    rw [show k = (k - 1) + 1 by ring,
      zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  have hclamp : Section6ExcessDecay.wellPlacedHalfGap m k < sigma * q i := by
    rw [Section6ExcessDecay.wellPlacedHalfGap, hscale]
    linarith only [hover, hbase]
  exact ⟨i, sigma, hsigma,
    MeanControlGeometry.wellPlacedCentre_faceLevel hkm hsigma hclamp⟩

/-- The next zero-trace window used to control the projected residual mean
stays inside the manuscript parent window.  This is the direct two-radius
estimate: both displacements have scale `n - 1`, while the target has scale
`n`. -/
theorem boundaryResidualWindow_subset_nextWindow
    {m n : ℤ} {x q : Vec d}
    (hq : q ∈ truncatedCube d m (n - 1) x) :
    translatedCube d (n - 1) q ∩ cube d m ⊆
      truncatedCube d m n x := by
  intro p hp
  refine ⟨?_, hp.2⟩
  have hpq : p - q ∈ cube d (n - 1) :=
    Section6ExcessDecay.mem_translatedCube_iff.mp hp.1
  have hqx : q - x ∈ cube d (n - 1) :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hq
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    mem_openCubeSet_originCube_iff]
  rw [cube, mem_openCubeSet_originCube_iff] at hpq hqx
  intro i
  have hpow : (3 : ℝ) ^ n = 3 * (3 : ℝ) ^ (n - 1) := by
    rw [show n = (n - 1) + 1 by ring,
      zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  have hpos : 0 < (3 : ℝ) ^ (n - 1) := zpow_pos (by norm_num) _
  have hid : p i - x i = (p i - q i) + (q i - x i) := by ring
  simp only [Pi.sub_apply] at hpq hqx ⊢
  rw [hid, hpow]
  constructor <;>
    linarith only [(hpq i).1, (hpq i).2, (hqx i).1, (hqx i).2, hpos]

/-- A truncated scale-`j` boundary window is exactly the physical translate
of the Caccioppoli core in its well-placed scale-`j+2` parent cube. -/
theorem truncatedCube_eq_translate_projectedCaccioppoliCore
    {m j : ℤ} (q : Vec d) (hjm : j + 2 ≤ m) :
    truncatedCube d m j q =
      translateSet (Section6ExcessDecay.wellPlacedCentre q m (j + 2))
        (caccioppoliCoreSet (originCube d (j + 2))
          (q - Section6ExcessDecay.wellPlacedCentre q m (j + 2))) := by
  ext p
  let c := Section6ExcessDecay.wellPlacedCentre q m (j + 2)
  constructor
  · intro hp
    rw [mem_translateSet_iff_sub_mem]
    constructor
    · have hparent :=
        Section6ExcessDecay.truncatedCube_subset_translatedCube_wellPlacedCentre
          q hjm (by omega : j ≤ j + 2) hp
      exact Section6ExcessDecay.mem_translatedCube_iff.mp hparent
    · rw [show (originCube d (j + 2)).scale - 2 = j by
            change (j + 2) - 2 = j
            ring,
          openCubeAtScale_eq_translateSet, mem_translateSet_iff_sub_mem]
      have hpq := Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hp
      simpa [cube, openCubeAtScale_zero_eq_openCubeSet_originCube] using hpq
  · intro hp
    rw [mem_translateSet_iff_sub_mem] at hp
    refine ⟨?_, ?_⟩
    · rw [Section6ExcessDecay.mem_translatedCube_iff]
      have hpatch := hp.2
      rw [show (originCube d (j + 2)).scale - 2 = j by
            change (j + 2) - 2 = j
            ring,
          openCubeAtScale_eq_translateSet, mem_translateSet_iff_sub_mem] at hpatch
      have heq : p - c - (q - c) = p - q := by abel
      rw [heq] at hpatch
      simpa [cube, openCubeAtScale_zero_eq_openCubeSet_originCube] using hpatch
    · have hparent : p ∈ translatedCube d (j + 2) c :=
        Section6ExcessDecay.mem_translatedCube_iff.mpr hp.1
      exact Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube
        q hjm hparent

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
