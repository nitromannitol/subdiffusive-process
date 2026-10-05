module

public import SubdiffusiveProcess.EllipticRegularity.ResponseJBridge
public import SubdiffusiveProcess.EllipticRegularity.DescendantCells
public import SubdiffusiveProcess.EllipticRegularity.Numeric
public import SubdiffusiveProcess.Sobolev.TriadicDefectSup
public import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationError

@[expose] public section




open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.EllipticRegularity

/-- Reindexing a supremum over the subtype of a `Finset.image` by the index type. -/
theorem iSup_image_univ_subtype {α : Type*} [CompleteLattice α] {ι β : Type*}
    [Fintype ι] [DecidableEq β] (g : ι → β) (f : β → α) :
    ⨆ R : {R : β // R ∈ Finset.image g Finset.univ}, f R = ⨆ i : ι, f (g i) := by
  refine le_antisymm (iSup_le ?_) (iSup_le ?_)
  · rintro ⟨R, hR⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hR
    exact le_iSup (fun i => f (g i)) i
  · intro i
    exact le_iSup (fun R : {R : β // R ∈ Finset.image g Finset.univ} => f R)
      ⟨g i, Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩⟩

/-- The descendant index set of the origin cube at the paper's scale. -/
theorem descendantsAtScale_originCube (d n k : ℕ) :
    Homogenization.descendantsAtScale (Homogenization.originCube d n) ((n : ℤ) - k) =
      Finset.image (descendantCube (d := d) n k) Finset.univ := by
  have hscale : (Homogenization.originCube d n).scale = (n : ℤ) := rfl
  have hle : (n : ℤ) - k ≤ (Homogenization.originCube d n).scale := by
    rw [hscale]; omega
  rw [Homogenization.descendantsAtScale_eq_descendantsAtDepth _ hle, hscale]
  have : ((n : ℤ) - ((n : ℤ) - (k : ℤ))).toNat = k := by omega
  rw [this, descendantsAtDepth_originCube_eq_image]

variable {d : ℕ}

/-- The upstream one-cube probe at a cell is the project's cell defect.  The root cube is
kept abstract (`z`, `r`, `hr`): instantiating it concretely before this unification is what
blows the elaborator's heartbeat budget. -/
theorem paperScalarProbe_eq_affineDiagonalDefect_of_cell
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hD : ∀ J (j : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) j),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) j)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) j)) u‖)
    (hN : ∀ J (j : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) j),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) j)).1‖ ≤
        K * ‖subspaceGradient
          (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) j)) u‖)
    (aQ : PositiveCoefficient (centeredCube z r hr))
    {a : Homogenization.Vec d → ℝ} {alpha : ℝ} (halpha : 0 < alpha)
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData a)
    (haQ : ((aQ.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => a x / alpha))
    (J : ℕ) (j : OddGridIndex d (triadicHalf J))
    (R : Homogenization.TriadicCube d)
    (hcell : (oddGridCell z r hr (triadicHalf J) j : Set (SpatialCoordinates d)) =
      Homogenization.openCubeSet R)
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe R data.toTriadicCoeffFamily alpha e =
      affineDiagonalDefect
        (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
        (hD J j) (hN J j)
        (positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf J) j) aQ) e := by
  have hae : ((positiveCoefficientRestrict
        (oddGridCell_subset z hr (triadicHalf J) j) aQ).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict
          (oddGridCell z r hr (triadicHalf J) j : Set (SpatialCoordinates d))]
        fun x => a x / alpha := by
    filter_upwards [positiveCoefficientRestrict_coeFn
        (oddGridCell_subset z hr (triadicHalf J) j) aQ,
      ae_restrict_of_ae_restrict_of_subset
        (oddGridCell_subset z hr (triadicHalf J) j) haQ] with x h1 h2
    rw [h1]; exact h2
  have hset : (oddGridCell z r hr (triadicHalf J) j : Set (SpatialCoordinates d)) =
      ((Homogenization.Book.Ch02.cubeDomain R : Homogenization.Book.Ch02.Domain d) :
        Set (Homogenization.Vec d)) := by
    rw [Homogenization.Book.Ch02.cubeDomain_coe]; exact hcell
  exact responseJ_eq_affineDiagonalDefect
    (Homogenization.Book.Ch02.cubeDomain R)
    (oddGridCell z r hr (triadicHalf J) j)
    hset halpha (data.onCube R)
    (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _) (hD J j) (hN J j) _ hae e he

/-- The defect range is the range of the two-parameter family it is written from. -/
theorem triadicDefectRange_eq_range (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hD : ∀ J (j : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) j),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) j)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) j)) u‖)
    (hN : ∀ J (j : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) j),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) j)).1‖ ≤
        K * ‖subspaceGradient
          (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) j)) u‖)
    (aQ : PositiveCoefficient (centeredCube z r hr)) (J : ℕ) :
    triadicDefectRange z hr hD hN aQ J =
      Set.range (fun i : OddGridIndex d (triadicHalf J) ×
          {e : Homogenization.Vec d // Homogenization.vecNormSq e = 1} =>
        affineDiagonalDefect
          (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
          (hD J i.1) (hN J i.1)
          (positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf J) i.1) aQ)
          (i.2 : Homogenization.Vec d)) := by
  ext y
  constructor
  · rintro ⟨j, p, hp, rfl⟩
    refine ⟨⟨j, ⟨p, ?_⟩⟩, rfl⟩
    rw [Homogenization.vecNormSq, Homogenization.vecDot, ← hp]
    exact Finset.sum_congr rfl fun i _ => (sq (p i)).symm
  · rintro ⟨⟨j, ⟨p, hp⟩⟩, rfl⟩
    refine ⟨j, p, ?_, rfl⟩
    rw [Homogenization.vecNormSq, Homogenization.vecDot] at hp
    rw [← hp]
    exact Finset.sum_congr rfl fun i _ => sq (p i)




theorem paperMaxDescendantProbeAtScale_eq_ofReal_triadicDefectSup
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hD : ∀ J (j : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) j),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) j)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) j)) u‖)
    (hN : ∀ J (j : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) j),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) j)).1‖ ≤
        K * ‖subspaceGradient
          (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) j)) u‖)
    (aQ : PositiveCoefficient (centeredCube z r hr)) (hd : 0 < d) (n k : ℕ)
    {a : Homogenization.Vec d → ℝ} {alpha : ℝ} (halpha : 0 < alpha)
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData a)
    (haQ : ((aQ.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => a x / alpha))
    (hcells : ∀ j : OddGridIndex d (triadicHalf k),
      (oddGridCell z r hr (triadicHalf k) j : Set (SpatialCoordinates d)) =
        Homogenization.openCubeSet (descendantCube (d := d) n k j)) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
        (Homogenization.originCube d (n : ℤ)) ((n : ℤ) - (k : ℤ))
        data.toTriadicCoeffFamily alpha =
      ENNReal.ofReal (triadicDefectSup z hr hD hN aQ hd k) := by
  classical
  have hne : Nonempty (OddGridIndex d (triadicHalf k) ×
      {e : Homogenization.Vec d // Homogenization.vecNormSq e = 1}) := by
    refine ⟨fun _ => 0, ⟨fun j => if j = (⟨0, hd⟩ : Fin d) then 1 else 0, ?_⟩⟩
    rw [Homogenization.vecNormSq, Homogenization.vecDot]
    simp
  have hrange := triadicDefectRange_eq_range z hr hD hN aQ k
  have hbdd : BddAbove (Set.range (fun i : OddGridIndex d (triadicHalf k) ×
      {e : Homogenization.Vec d // Homogenization.vecNormSq e = 1} =>
        affineDiagonalDefect
          (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
          (hD k i.1) (hN k i.1)
          (positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf k) i.1) aQ)
          (i.2 : Homogenization.Vec d))) := by
    rw [← hrange]; exact triadicDefectRange_bddAbove z hr hD hN aQ k
  have hstep : ∀ j : OddGridIndex d (triadicHalf k),
      SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax (descendantCube (d := d) n k j)
          data.toTriadicCoeffFamily alpha =
        ⨆ e : {e : Homogenization.Vec d // Homogenization.vecNormSq e = 1},
          ENNReal.ofReal (affineDiagonalDefect
            (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
            (hD k j) (hN k j)
            (positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf k) j) aQ)
            (e : Homogenization.Vec d)) := by
    intro j
    refine iSup_congr fun e => congrArg ENNReal.ofReal ?_
    exact paperScalarProbe_eq_affineDiagonalDefect_of_cell z hr hD hN aQ halpha data haQ
      k j _ (hcells j) (e : Homogenization.Vec d) e.2
  rw [SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale,
    descendantsAtScale_originCube,
    iSup_image_univ_subtype (descendantCube (d := d) n k)
      (fun R => SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
        data.toTriadicCoeffFamily alpha)]
  rw [iSup_congr hstep]
  rw [triadicDefectSup, hrange]
  rw [show sSup (Set.range (fun i : OddGridIndex d (triadicHalf k) ×
      {e : Homogenization.Vec d // Homogenization.vecNormSq e = 1} =>
        affineDiagonalDefect
          (centeredCube_isBounded _ _) (centeredCube_volume_pos _ _)
          (hD k i.1) (hN k i.1)
          (positiveCoefficientRestrict (oddGridCell_subset z hr (triadicHalf k) i.1) aQ)
          (i.2 : Homogenization.Vec d))) = ⨆ i, _ from rfl]
  rw [ofReal_iSup_eq_iSup_ofReal _ hbdd, iSup_prod]

end SubdiffusiveProcess.EllipticRegularity
