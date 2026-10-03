module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedSourceParentReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepRetainedNeumannGluing
public import Homogenization.Geometry.BoundaryLayer

@[expose] public section

/-!
# Geometry of the retained-cell boundary discard

For a fixed source scale and fixed centered-parent radius, every source cell
whose enlarged parent is not retained lies in a boundary strip of the
ambient cube.  The normalized strip thickness is the sum of the source-cell
and enlarged-parent half widths divided by the ambient side length.  It
tends to zero as the ambient scale grows.
-/

open Filter MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Normalized boundary thickness sufficient to retain every source cell
meeting the complementary shrunk core. -/
def oneStepRetainedBoundaryThickness {d : ℕ}
    (K source : ℤ) (N : ℕ) : ℝ :=
  (cubeScaleFactor (originCube d (source + (N : ℤ))) +
      cubeScaleFactor (originCube d source)) /
    (2 * cubeScaleFactor (originCube d K))

theorem oneStepRetainedBoundaryThickness_nonneg {d : ℕ}
    (K source : ℤ) (N : ℕ) :
    0 ≤ oneStepRetainedBoundaryThickness (d := d) K source N := by
  unfold oneStepRetainedBoundaryThickness
  simp only [cubeScaleFactor, originCube]
  positivity

/-- Every point in the complementary shrunk core belongs to a retained
source cell.  Closed source cells are used here because they form the exact
triadic partition; their boundaries are harmless for volume integration. -/
theorem cubeShrunkSet_subset_iUnion_oneStepRetainedSourceCells {d : ℕ}
    {K source : ℤ} {N : ℕ} (hsource : source ≤ K) :
    cubeShrunkSet (originCube d K)
        (oneStepRetainedBoundaryThickness (d := d) K source N) ⊆
      ⋃ R ∈ (oneStepRetainedSourceCells (d := d) K source N :
        Set (TriadicCube d)), cubeSet R := by
  intro x hx
  have hxQ : x ∈ cubeSet (originCube d K) :=
    cubeShrunkSet_subset_cubeSet _
      (oneStepRetainedBoundaryThickness_nonneg K source N) hx
  have hcover := cubeSet_subset_iUnion_descendantsAtScale
    (originCube d K) hsource hxQ
  rcases Set.mem_iUnion.mp hcover with ⟨R, hcoverR⟩
  rcases Set.mem_iUnion.mp hcoverR with ⟨hR, hxR⟩
  have hRscale : R.scale = source := scale_eq_of_mem_descendantsAtScale hR
  have hparent : oneStepCenteredParent (cubeCenter R) (source + (N : ℤ)) ⊆
      openCubeSet (originCube d K) := by
    intro y hy i
    have hxi := hx i
    have hxRi := hxR i
    simp only [originCube, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add,
      oneStepRetainedBoundaryThickness, cubeScaleFactor] at hxi
    simp only [cubeScaleFactor] at hxRi
    rw [hRscale] at hxRi
    rw [oneStepCenteredParent, mem_translateSet_iff_sub_mem] at hy
    have hyi' := hy i
    simp only [originCube, Pi.zero_apply, Int.cast_zero,
      cubeScaleFactor, cubeCenter, zero_sub, zero_add, Pi.sub_apply] at hyi'
    rw [hRscale] at hyi'
    simp only [originCube, Pi.zero_apply, Int.cast_zero,
      cubeScaleFactor, zero_sub, zero_add] at ⊢
    have hK : (0 : ℝ) < (3 : ℝ) ^ K := zpow_pos (by norm_num) _
    have hS : (0 : ℝ) < (3 : ℝ) ^ source := zpow_pos (by norm_num) _
    have hP : (0 : ℝ) < (3 : ℝ) ^ (source + (N : ℤ)) :=
      zpow_pos (by norm_num) _
    have hthickness :
        ((3 : ℝ) ^ (source + (N : ℤ)) + (3 : ℝ) ^ source) /
              (2 * (3 : ℝ) ^ K) * (3 : ℝ) ^ K =
          ((3 : ℝ) ^ (source + (N : ℤ)) + (3 : ℝ) ^ source) / 2 := by
      field_simp
    have hxlow :
        -(1 / 2 : ℝ) * (3 : ℝ) ^ K +
            ((3 : ℝ) ^ (source + (N : ℤ)) + (3 : ℝ) ^ source) / 2 ≤
          x i := by
      nlinarith [hxi.1, hthickness]
    have hxhigh :
        x i < (1 / 2 : ℝ) * (3 : ℝ) ^ K -
            ((3 : ℝ) ^ (source + (N : ℤ)) + (3 : ℝ) ^ source) / 2 := by
      nlinarith [hxi.2, hthickness]
    have hcenterLow :
        -(1 / 2 : ℝ) * (3 : ℝ) ^ K +
            (1 / 2 : ℝ) * (3 : ℝ) ^ (source + (N : ℤ)) <
          (R.index i : ℝ) * (3 : ℝ) ^ source := by
      nlinarith [hxlow, hxRi.2]
    have hcenterHigh :
        (R.index i : ℝ) * (3 : ℝ) ^ source <
          (1 / 2 : ℝ) * (3 : ℝ) ^ K -
            (1 / 2 : ℝ) * (3 : ℝ) ^ (source + (N : ℤ)) := by
      nlinarith [hxhigh, hxRi.1]
    constructor
    · nlinarith [hcenterLow, hyi'.1]
    · nlinarith [hcenterHigh, hyi'.2]
  have hretained : R ∈ oneStepRetainedSourceCells (d := d) K source N :=
    mem_oneStepRetainedSourceCells_iff.mpr ⟨hR, hparent⟩
  exact Set.mem_iUnion.mpr ⟨R,
    Set.mem_iUnion.mpr ⟨by simpa using hretained, hxR⟩⟩

/-- The part of the ambient cube not covered by retained closed cells lies
in the explicit boundary layer. -/
theorem cubeSet_diff_iUnion_oneStepRetainedSourceCells_subset_boundaryLayer
    {d : ℕ} {K source : ℤ} {N : ℕ} (hsource : source ≤ K) :
    cubeSet (originCube d K) \ 
        (⋃ R ∈ (oneStepRetainedSourceCells (d := d) K source N :
          Set (TriadicCube d)), cubeSet R) ⊆
      cubeBoundaryLayer (originCube d K)
        (oneStepRetainedBoundaryThickness (d := d) K source N) := by
  intro x hx
  exact ⟨hx.1, fun hcore ↦ hx.2
    (cubeShrunkSet_subset_iUnion_oneStepRetainedSourceCells hsource hcore)⟩

/-- Up to the null union of triadic cell faces, the complement of the
retained open cells lies in the explicit ambient boundary layer. -/
theorem ae_openCubeSet_diff_retainedOpenSet_subset_boundaryLayer {d : ℕ}
    {K source : ℤ} {N : ℕ} (hsource : source ≤ K) :
    ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ openCubeSet (originCube d K) \
          oneStepRetainedOpenSet
            (oneStepRetainedSourceCells (d := d) K source N) →
        x ∈ cubeBoundaryLayer (originCube d K)
          (oneStepRetainedBoundaryThickness (d := d) K source N) := by
  let s := oneStepRetainedSourceCells (d := d) K source N
  have hunion : oneStepRetainedOpenSet s =ᵐ[MeasureTheory.volume]
      ⋃ R ∈ (s : Set (TriadicCube d)), cubeSet R := by
    exact Filter.EventuallyEq.biUnion s.finite_toSet fun R _hR ↦
      (cubeSet_ae_eq_openCubeSet R).symm
  have hparent : openCubeSet (originCube d K) =ᵐ[MeasureTheory.volume]
      cubeSet (originCube d K) := (cubeSet_ae_eq_openCubeSet _).symm
  have hdiff := hparent.diff hunion
  filter_upwards [hdiff] with x hx
  intro hxOpen
  apply cubeSet_diff_iUnion_oneStepRetainedSourceCells_subset_boundaryLayer
    hsource
  exact hx.mp hxOpen

/-- A nonnegative retained-complement energy is bounded by its integral on
the explicit ambient boundary layer. -/
theorem integral_openCubeSet_diff_retainedOpenSet_le_boundaryLayer {d : ℕ}
    {K source : ℤ} {N : ℕ} (hsource : source ≤ K)
    (f : Vec d → ℝ)
    (hf : IntegrableOn f
      (cubeBoundaryLayer (originCube d K)
        (oneStepRetainedBoundaryThickness (d := d) K source N)))
    (hf0 : 0 ≤ᵐ[MeasureTheory.volume.restrict
      (cubeBoundaryLayer (originCube d K)
        (oneStepRetainedBoundaryThickness (d := d) K source N))] f) :
    ∫ x in openCubeSet (originCube d K) \
        oneStepRetainedOpenSet
          (oneStepRetainedSourceCells (d := d) K source N), f x ∂volume ≤
      ∫ x in cubeBoundaryLayer (originCube d K)
        (oneStepRetainedBoundaryThickness (d := d) K source N), f x ∂volume := by
  exact setIntegral_mono_set hf hf0
    (ae_openCubeSet_diff_retainedOpenSet_subset_boundaryLayer hsource)

/-- Uniform pointwise boundary-energy control converts the discarded
integral into the explicit boundary-layer volume price. -/
theorem integral_openCubeSet_diff_retainedOpenSet_le_const_mul_boundaryVolume
    {d : ℕ} {K source : ℤ} {N : ℕ} (hsource : source ≤ K)
    (f : Vec d → ℝ) (C : ℝ)
    (hf : IntegrableOn f
      (cubeBoundaryLayer (originCube d K)
        (oneStepRetainedBoundaryThickness (d := d) K source N)))
    (hf0 : 0 ≤ᵐ[MeasureTheory.volume.restrict
      (cubeBoundaryLayer (originCube d K)
        (oneStepRetainedBoundaryThickness (d := d) K source N))] f)
    (hfC : f ≤ᵐ[MeasureTheory.volume.restrict
      (cubeBoundaryLayer (originCube d K)
        (oneStepRetainedBoundaryThickness (d := d) K source N))]
      fun _ ↦ C) :
    ∫ x in openCubeSet (originCube d K) \
        oneStepRetainedOpenSet
          (oneStepRetainedSourceCells (d := d) K source N), f x ∂volume ≤
      C * (MeasureTheory.volume
        (cubeBoundaryLayer (originCube d K)
          (oneStepRetainedBoundaryThickness (d := d) K source N))).toReal := by
  let layer := cubeBoundaryLayer (originCube d K)
    (oneStepRetainedBoundaryThickness (d := d) K source N)
  have hlayerFinite : MeasureTheory.volume layer ≠ ⊤ :=
    MeasureTheory.measure_ne_top_of_subset
      (cubeBoundaryLayer_subset_cubeSet _ _)
      (volume_cubeSet_lt_top (originCube d K)).ne
  have hconst : IntegrableOn (fun _ : Vec d ↦ C) layer :=
    integrableOn_const hlayerFinite
  calc
    _ ≤ ∫ x in layer, f x ∂volume :=
      integral_openCubeSet_diff_retainedOpenSet_le_boundaryLayer
        hsource f hf hf0
    _ ≤ ∫ _x in layer, C ∂volume :=
      integral_mono_ae hf hconst hfC
    _ = C * (MeasureTheory.volume layer).toReal := by
      rw [setIntegral_const]
      simp only [Measure.real, smul_eq_mul]
      ring

/-- At fixed source scale and auxiliary radius, the normalized retained-cell
boundary thickness vanishes as the ambient natural scale tends to infinity. -/
theorem tendsto_oneStepRetainedBoundaryThickness_zero {d : ℕ}
    (source : ℤ) (N : ℕ) :
    Tendsto (fun K : ℕ ↦
      oneStepRetainedBoundaryThickness (d := d) (K : ℤ) source N)
      atTop (nhds 0) := by
  let C : ℝ := (cubeScaleFactor (originCube d (source + (N : ℤ))) +
    cubeScaleFactor (originCube d source)) / 2
  have hpow : Tendsto (fun K : ℕ ↦ ((1 / 3 : ℝ) ^ K)) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hmul := hpow.const_mul C
  convert hmul using 1
  · funext K
    simp only [oneStepRetainedBoundaryThickness, cubeScaleFactor, originCube]
    rw [show (3 : ℝ) ^ (K : ℤ) = (3 : ℝ) ^ K by simp]
    rw [show (1 / 3 : ℝ) ^ K = ((3 : ℝ) ^ K)⁻¹ by
      rw [one_div, inv_pow]]
    dsimp [C]
    field_simp
  · simp

/-- Dimensionless volume fraction of the explicit retained-cell boundary
strip whenever its thickness is at most one half. -/
def oneStepRetainedBoundaryFraction {d : ℕ}
    (K source : ℤ) (N : ℕ) : ℝ :=
  1 - (1 - 2 * oneStepRetainedBoundaryThickness (d := d) K source N) ^ d

theorem volume_cubeBoundaryLayer_div_cubeVolume_eq_retainedBoundaryFraction
    {d : ℕ} (K source : ℤ) (N : ℕ)
    (hhalf : oneStepRetainedBoundaryThickness (d := d) K source N ≤ 1 / 2) :
    (MeasureTheory.volume
        (cubeBoundaryLayer (originCube d K)
          (oneStepRetainedBoundaryThickness (d := d) K source N))).toReal /
        cubeVolume (originCube d K) =
      oneStepRetainedBoundaryFraction (d := d) K source N := by
  rw [volume_cubeBoundaryLayer_toReal_of_nonneg_le_half
    (originCube d K)
    (oneStepRetainedBoundaryThickness_nonneg K source N) hhalf]
  unfold oneStepRetainedBoundaryFraction
  have hvol : 0 < cubeVolume (originCube d K) := cubeVolume_pos _
  have hcube : cubeVolume (originCube d K) =
      cubeScaleFactor (originCube d K) ^ d := rfl
  rw [hcube, mul_pow]
  field_simp

/-- Normalized form of the boundary-energy estimate, in the same
`volumeAverage` scaling as the starred variational readout. -/
theorem inv_cubeVolume_mul_integral_diff_retained_le_boundaryFraction
    {d : ℕ} {K source : ℤ} {N : ℕ} (hsource : source ≤ K)
    (hhalf : oneStepRetainedBoundaryThickness (d := d) K source N ≤ 1 / 2)
    (f : Vec d → ℝ) (C : ℝ)
    (hf : IntegrableOn f
      (cubeBoundaryLayer (originCube d K)
        (oneStepRetainedBoundaryThickness (d := d) K source N)))
    (hf0 : 0 ≤ᵐ[volume.restrict
      (cubeBoundaryLayer (originCube d K)
        (oneStepRetainedBoundaryThickness (d := d) K source N))] f)
    (hfC : f ≤ᵐ[volume.restrict
      (cubeBoundaryLayer (originCube d K)
        (oneStepRetainedBoundaryThickness (d := d) K source N))]
      fun _ ↦ C) :
    (cubeVolume (originCube d K))⁻¹ *
        ∫ x in openCubeSet (originCube d K) \
          oneStepRetainedOpenSet
            (oneStepRetainedSourceCells (d := d) K source N), f x ∂volume ≤
      C * oneStepRetainedBoundaryFraction (d := d) K source N := by
  have hbase :=
    integral_openCubeSet_diff_retainedOpenSet_le_const_mul_boundaryVolume
      hsource f C hf hf0 hfC
  have hvol : 0 < cubeVolume (originCube d K) := cubeVolume_pos _
  calc
    _ ≤ (cubeVolume (originCube d K))⁻¹ *
        (C * (volume
          (cubeBoundaryLayer (originCube d K)
            (oneStepRetainedBoundaryThickness (d := d) K source N))).toReal) :=
      mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hvol.le)
    _ = C * ((volume
          (cubeBoundaryLayer (originCube d K)
            (oneStepRetainedBoundaryThickness (d := d) K source N))).toReal /
        cubeVolume (originCube d K)) := by field_simp
    _ = C * oneStepRetainedBoundaryFraction (d := d) K source N := by
      rw [volume_cubeBoundaryLayer_div_cubeVolume_eq_retainedBoundaryFraction
        K source N hhalf]

/-- The normalized volume of the discarded boundary strip tends to zero at
fixed source scale and auxiliary radius. -/
theorem tendsto_oneStepRetainedBoundaryFraction_zero {d : ℕ}
    (source : ℤ) (N : ℕ) :
    Tendsto (fun K : ℕ ↦
      oneStepRetainedBoundaryFraction (d := d) (K : ℤ) source N)
      atTop (nhds 0) := by
  have ht := tendsto_oneStepRetainedBoundaryThickness_zero
    (d := d) source N
  have htwo : Tendsto (fun K : ℕ ↦
      2 * oneStepRetainedBoundaryThickness (d := d) (K : ℤ) source N)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ht
  have honeSub : Tendsto (fun K : ℕ ↦
      1 - 2 * oneStepRetainedBoundaryThickness (d := d) (K : ℤ) source N)
      atTop (nhds 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub htwo
  have hpow := honeSub.pow d
  change Tendsto (fun K : ℕ ↦
    1 - (1 - 2 * oneStepRetainedBoundaryThickness
      (d := d) (K : ℤ) source N) ^ d) atTop (nhds 0)
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa only [one_pow, sub_self] using hone.sub hpow

/-- Any fixed integrable/stationary boundary-energy budget multiplied by
the discarded volume fraction vanishes in the thermodynamic limit. -/
theorem tendsto_const_mul_oneStepRetainedBoundaryFraction_zero {d : ℕ}
    (source : ℤ) (N : ℕ) (C : ℝ) :
    Tendsto (fun K : ℕ ↦ C *
      oneStepRetainedBoundaryFraction (d := d) (K : ℤ) source N)
      atTop (nhds 0) := by
  simpa only [mul_zero] using
    tendsto_const_nhds.mul
      (tendsto_oneStepRetainedBoundaryFraction_zero (d := d) source N)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
