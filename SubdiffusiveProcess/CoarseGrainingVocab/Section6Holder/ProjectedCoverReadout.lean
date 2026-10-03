module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.EnergyReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ProjectedCoverAssembly

@[expose] public section

/-!
# Hölder Step 6: projected cover readout

This module transports the fixed depth-two projected cover from its full
well-placed cube back to the smaller truncated window used by the Hölder
energy row.  The only loss is the explicit fixed four-scale volume factor
`81 ^ d`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch01 Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ}

/-- The scale-`n-4` truncated window is read from the well-placed full cube
of scale `n-2`, with the exact fixed volume loss `81 ^ d`. -/
theorem normalizedCutoffEnergy_truncatedCube_predFour_le_projected
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m n : ℕ} {x : Vec d} (hx : x ∈ cube d (m : ℤ))
    (hnm : (n : ℤ) - 2 ≤ (m : ℤ))
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) {B : ℝ}
    (hprojected : normalizedSetAverage
        (translatedCube d ((n : ℤ) - 2)
          (Section6ExcessDecay.wellPlacedCentre x (m : ℤ) ((n : ℤ) - 2)))
        (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (u.grad p)) ≤ B) :
    normalizedSetAverage (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
        (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (u.grad p)) ≤
      (81 : ℝ) ^ d * B := by
  let S := truncatedCube d (m : ℤ) ((n : ℤ) - 4) x
  let y := Section6ExcessDecay.wellPlacedCentre x (m : ℤ) ((n : ℤ) - 2)
  let T := translatedCube d ((n : ℤ) - 2) y
  have hscale : (n : ℤ) - 2 ≤ (m : ℤ) := hnm
  have hST : S ⊆ T := by
    exact Section6ExcessDecay.truncatedCube_subset_translatedCube_wellPlacedCentre
      x hscale (by omega)
  have hSpos : 0 < volume S := by
    exact ((ENNReal.toReal_pos_iff).mp
      (Section6ExcessDecay.volume_toReal_truncatedCube_pos x hx (by omega))).1
  have hTtop : volume T < ⊤ := by
    dsimp only [T]
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq]
    exact volume_openCubeSet_lt_top _
  have hTmeas : MeasurableSet T := by
    exact (Section6ExcessDecay.isOpenBoundedConvexDomain_translatedCube
      d ((n : ℤ) - 2) y).isOpen.measurableSet
  have hTsub : T ⊆ openCubeSet (originCube d (m : ℤ)) := by
    exact Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube x hscale
  have hint : IntegrableOn (fun p ↦
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p * vecNormSq (u.grad p)) T :=
    (integrableOn_aCutoff_energy M L omega (originCube d (m : ℤ)) u).mono_set hTsub
  have hvolume : (volume T).toReal ≤
      (81 : ℝ) ^ d * (volume S).toReal := by
    have hS :=
      (Section6ExcessDecay.volume_toReal_truncatedCube_bounds
        (m := (m : ℤ)) (j := (n : ℤ) - 4) x hx (by omega)).1
    have hS' : ((3 : ℝ) ^ ((n : ℤ) - 6)) ^ d ≤ (volume S).toReal := by
      change ((3 : ℝ) ^ ((n : ℤ) - 6)) ^ d ≤
        (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)).toReal
      rw [show (n : ℤ) - 6 = ((n : ℤ) - 4) - 2 by ring]
      exact hS
    have hT : (volume T).toReal = ((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d := by
      dsimp only [T]
      rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet,
        volume_translateSet_eq, volume_openCubeSet_toReal, cubeVolume_eq_pow_scale]
      rfl
    have hfactor : ((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d =
        (81 : ℝ) ^ d * ((3 : ℝ) ^ ((n : ℤ) - 6)) ^ d := by
      rw [← mul_pow]
      congr 1
      rw [show (n : ℤ) - 2 = ((n : ℤ) - 6) + 4 by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
      ring
    rw [hT, hfactor]
    exact mul_le_mul_of_nonneg_left hS' (by positivity)
  have hsubset := normalizedSetAverage_le_mul_of_subset hST hSpos hTtop hTmeas
    (fun p _ ↦ mul_nonneg
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega p).le
      (vecNormSq_nonneg (u.grad p))) hint hvolume
  exact hsubset.trans (mul_le_mul_of_nonneg_left hprojected (by positivity))

/-- Complete deterministic conversion through the projected mixed cover:
cellwise interior and boundary prices control the smaller truncated window. -/
theorem normalizedCutoffEnergy_truncatedCube_predFour_le_max_of_cellBounds
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m n : ℕ} {x : Vec d} (hx : x ∈ cube d (m : ℤ))
    (hnm : (n : ℤ) - 2 ≤ (m : ℤ))
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (Binterior Bboundary : ℝ)
    (hinterior : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ Binterior)
    (hboundary : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ Bboundary) :
    normalizedSetAverage (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
        (fun p ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
          vecNormSq (u.grad p)) ≤
      (81 : ℝ) ^ d * max Binterior Bboundary := by
  let y := Section6ExcessDecay.wellPlacedCentre x (m : ℤ) ((n : ℤ) - 2)
  have hscale : (n : ℤ) - 2 ≤ (m : ℤ) := hnm
  have hD : translatedCube d ((n : ℤ) - 2) y ⊆
      truncatedCube d (m : ℤ) ((n : ℤ) - 1) x :=
    Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_truncatedCube_pred
      hx hscale
  have hcover := normalizedCutoffEnergy_projectedCover_le_max M L omega u hD
    Binterior Bboundary hinterior hboundary
  exact normalizedCutoffEnergy_truncatedCube_predFour_le_projected
    M L omega hx hnm u hcover

/-- Vector-`L²` form of the projected-cover readout.  This is the exact
carrier used by the second row of `HolderRegularityConclusions`; subsequent
parameter arithmetic only has to price the two scalar cell budgets. -/
theorem vectorNormalizedL2On_truncatedCube_predFour_le_sqrt_max_of_cellBounds
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m n : ℕ} {x : Vec d} (hx : x ∈ cube d (m : ℤ))
    (hnm : (n : ℤ) - 2 ≤ (m : ℤ))
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (Binterior Bboundary : ℝ)
    (hinterior : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ Binterior)
    (hboundary : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x →
      ¬ openCubeAtScale q ((n : ℤ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ Bboundary) :
    vectorNormalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
        (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
          u.grad p) ≤
      Real.sqrt ((81 : ℝ) ^ d * max Binterior Bboundary) := by
  apply vectorNormalizedL2On_sqrt_smul_le_of_volumeAverage_le
    (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) u.grad
    (fun p ↦ (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega p).le)
  exact normalizedCutoffEnergy_truncatedCube_predFour_le_max_of_cellBounds
    M L omega hx hnm u Binterior Bboundary hinterior hboundary

/-- Scale-shifted form whose conclusion is literally the truncated-window
carrier of the frozen Hölder energy row. -/
theorem vectorNormalizedL2On_truncatedCube_le_sqrt_max_of_shiftedCellBounds
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m n : ℕ} {x : Vec d} (hx : x ∈ cube d (m : ℤ))
    (hnm : n + 2 ≤ m)
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (Binterior Bboundary : ℝ)
    (hinterior : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n + 4 : ℕ) - 1) x →
      openCubeAtScale q ((n + 4 : ℕ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n + 4 : ℕ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ Binterior)
    (hboundary : ∀ q,
      q ∈ truncatedCube d (m : ℤ) ((n + 4 : ℕ) - 1) x →
      ¬ openCubeAtScale q ((n + 4 : ℕ) - 3) ⊆ cube d (m : ℤ) →
      normalizedSetAverage
          (truncatedCube d (m : ℤ) ((n + 4 : ℕ) - 4) q) (fun p ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
              vecNormSq (u.grad p)) ≤ Bboundary) :
    vectorNormalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
        (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
          u.grad p) ≤
      Real.sqrt ((81 : ℝ) ^ d * max Binterior Bboundary) := by
  have hraw :=
    vectorNormalizedL2On_truncatedCube_predFour_le_sqrt_max_of_cellBounds
      M L omega hx (n := n + 4) (by omega) u
        Binterior Bboundary hinterior hboundary
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hraw
  simpa only [add_sub_cancel_right] using hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
