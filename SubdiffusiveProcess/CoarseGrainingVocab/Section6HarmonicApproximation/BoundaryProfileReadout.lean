module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAdaptiveGoodEventPrices
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergyReadout

@[expose] public section

/-!
# Reading a Caccioppoli core from the adaptive radius profile

The adaptive boundary estimate is normalized by its projected parent cube,
whereas the physical-cell readout first passes through CoarseGraining's
normalized Caccioppoli core.  This file records the fixed `18^d` conversion.

PROVENANCE: this is the public GMC form of the private
`normalizedSetAverage_caccioppoliCoreSet_le_eighteen_pow_mul_localEnergyRadiusProfile`
argument in
`Homogenization/Book/Ch03/Theorems/CoarseCaccioppoliScaleZeroCore.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem core_subset_localClosedCube_oneThird
    (Q : TriadicCube d) (center : Vec d) :
    caccioppoliCoreSet Q center ⊆
      coarseCaccioppoliLocalClosedCube Q center (1 / 3 : ℝ) := by
  have hrad : coarseCaccioppoliLocalPatchRadius Q (1 / 3 : ℝ) =
      Real.rpow (3 : ℝ) (((Q.scale - 2 : ℤ) : ℝ)) / 2 := by
    calc
      coarseCaccioppoliLocalPatchRadius Q (1 / 3 : ℝ) =
          (3 : ℝ) ^ (Q.scale - 2) / 2 := by
        unfold coarseCaccioppoliLocalPatchRadius cubeRadius cubeScaleFactor
        rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num
        ring
      _ = Real.rpow (3 : ℝ) (((Q.scale - 2 : ℤ) : ℝ)) / 2 :=
        congrArg (fun r : ℝ ↦ r / 2)
          (Real.rpow_intCast (3 : ℝ) (Q.scale - 2)).symm
  intro y hy i
  have hi := hy.2 i
  change |y i - center i| ≤ coarseCaccioppoliLocalPatchRadius Q (1 / 3 : ℝ)
  rw [hrad]
  simpa [openCubeAtScale] using le_of_lt hi

/-- A normalized Caccioppoli-core energy is controlled by the radius-`1/3`
cross-scale profile with the standard dimension-only volume loss. -/
theorem normalizedSetAverage_caccioppoliCoreSet_le_eighteen_pow_mul_crossScaleProfile
    (Q : TriadicCube d) {center : Vec d} {energy : Vec d → ℝ}
    (hcenter : center ∈ openCubeSet Q)
    (henergyNonneg : ∀ y ∈ cubeSet Q, 0 ≤ energy y)
    (henergyInt : IntegrableOn energy (cubeSet Q) volume) :
    normalizedSetAverage (caccioppoliCoreSet Q center) energy ≤
      (18 : ℝ) ^ d *
        boundaryCrossScaleEnergyProfile Q Q center (1 / 3 : ℝ) energy := by
  let localCube := coarseCaccioppoliLocalClosedCube Q center (1 / 3 : ℝ)
  have hlocalInt : IntegrableOn (localCube.indicator energy) (cubeSet Q) volume :=
    integrableOn_indicator_coarseCaccioppoliLocalClosedCube_of_integrableOn_cubeSet
      Q center (1 / 3 : ℝ) henergyInt
  have hlocalNonneg : 0 ≤ᵐ[volume.restrict (cubeSet Q)] localCube.indicator energy := by
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with y hy
    by_cases hylocal : y ∈ localCube
    · simpa [Set.indicator_of_mem hylocal] using henergyNonneg y hy
    · simp [Set.indicator_of_notMem hylocal]
  have hcoreSub : caccioppoliCoreSet Q center ⊆ cubeSet Q :=
    caccioppoliCoreSet_subset_cubeSet Q center
  have hmono :
      ∫ y in caccioppoliCoreSet Q center, localCube.indicator energy y ∂volume ≤
        ∫ y in cubeSet Q, localCube.indicator energy y ∂volume :=
    setIntegral_mono_set hlocalInt hlocalNonneg
      (Filter.Eventually.of_forall hcoreSub)
  have hcoreEq :
      ∫ y in caccioppoliCoreSet Q center, energy y ∂volume =
        ∫ y in caccioppoliCoreSet Q center, localCube.indicator energy y ∂volume := by
    apply setIntegral_congr_fun (measurableSet_caccioppoliCoreSet Q center)
    intro y hy
    have hyLocal : y ∈ localCube := by
      dsimp only [localCube]
      exact core_subset_localClosedCube_oneThird Q center hy
    simp [Set.indicator_of_mem hyLocal]
  have hratio := caccioppoliCoreSet_volumeRatio_le_eighteen_pow Q hcenter
  have hprofileNonneg : 0 ≤ boundaryCrossScaleEnergyProfile Q Q center
      (1 / 3 : ℝ) energy := by
    unfold boundaryCrossScaleEnergyProfile
    rw [volumeAverage_openCubeSet_eq_cubeAverage]
    exact coarseCaccioppoliLocalEnergyProfile_nonneg Q center (1 / 3 : ℝ)
      henergyNonneg
  have hvolNe : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  unfold normalizedSetAverage
  calc
    (volume (caccioppoliCoreSet Q center)).toReal⁻¹ *
          ∫ y in caccioppoliCoreSet Q center, energy y ∂volume =
        (volume (caccioppoliCoreSet Q center)).toReal⁻¹ *
          ∫ y in caccioppoliCoreSet Q center, localCube.indicator energy y ∂volume := by
      rw [hcoreEq]
    _ ≤ (volume (caccioppoliCoreSet Q center)).toReal⁻¹ *
          ∫ y in cubeSet Q, localCube.indicator energy y ∂volume :=
      mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = ((volume (caccioppoliCoreSet Q center)).toReal⁻¹ * cubeVolume Q) *
          boundaryCrossScaleEnergyProfile Q Q center (1 / 3 : ℝ) energy := by
      unfold boundaryCrossScaleEnergyProfile
      rw [volumeAverage_openCubeSet_eq_cubeAverage]
      unfold cubeAverage
      dsimp only [localCube]
      field_simp
    _ ≤ (18 : ℝ) ^ d *
          boundaryCrossScaleEnergyProfile Q Q center (1 / 3 : ℝ) energy :=
      mul_le_mul_of_nonneg_right hratio hprofileNonneg

/-- Public coefficient-energy specialization of the core/profile comparison.
This form is the direct output of the projected boundary construction. -/
theorem localizedCoeffEnergyValue_core_le_eighteen_pow_mul_crossScaleProfile
    [NeZero d] (Q : TriadicCube d) (A : CoeffFamily d)
    (u : H1Function (openCubeSet Q)) {center : Vec d}
    (hcenter : center ∈ openCubeSet Q) :
    localizedCoeffEnergyValue (caccioppoliCoreSet Q center) (A.coeffOn Q) u ≤
      (18 : ℝ) ^ d *
        boundaryCrossScaleEnergyProfile Q Q center (1 / 3 : ℝ)
          (coefficientEnergyDensity (publicCoeffField Q A) u.grad) := by
  have hcore : caccioppoliCoreSet Q center ⊆ openCubeSet Q := fun _ hy ↦ hy.1
  rw [localizedCoeffEnergyValue_eq_volumeAverage_publicCoeffField_of_subset_openCubeSet
    hcore u]
  apply normalizedSetAverage_caccioppoliCoreSet_le_eighteen_pow_mul_crossScaleProfile
  · exact hcenter
  · exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q A) u.grad
  · exact integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q A)
      (by
        simpa [MemVectorL2, volumeMeasureOn,
          volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using
          u.grad_memVectorL2)

/-- For the scalar GMC cutoff, the pointwise public representative and the
literal scalar energy give the same cross-scale profile. -/
theorem boundaryCrossScaleEnergyProfile_publicCoeff_aCutoff_eq
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) (rho : ℝ)
    (u : H1Function (openCubeSet Q)) :
    boundaryCrossScaleEnergyProfile Q R center rho
        (coefficientEnergyDensity
          (publicCoeffField Q (aCutoffFamily M L omega)) u.grad) =
      boundaryCrossScaleEnergyProfile Q R center rho (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) := by
  unfold boundaryCrossScaleEnergyProfile
  apply volumeAverage_eq_of_ae_eq
  filter_upwards
      [publicCoeffField_ae_eq_openCubeSet Q (aCutoffFamily M L omega)] with x hx
  by_cases hlocal : x ∈ coarseCaccioppoliLocalClosedCube R center rho
  · simp only [Set.indicator_of_mem hlocal, coefficientEnergyDensity, hx]
    simp [aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix,
      vecDot_smul_right, vecNormSq]
  · simp [Set.indicator_of_notMem hlocal]

/-- Read a physical scale-`k-2` cell through the radius-`1/3` profile of its
well-placed projected scale-`k` cube. -/
theorem normalizedCutoffEnergy_truncatedCube_le_profile
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m k : ℤ} {q : Vec d} (hq : q ∈ cube d m) (hkm : k ≤ m)
    (u : H1Function (openCubeSet (originCube d m)))
    (u0 : H1Function (openCubeSet (originCube d k)))
    (hu0 : ∀ x, u0.grad x = u.grad (x +
      Section6ExcessDecay.wellPlacedCentre q m k)) :
    normalizedSetAverage (truncatedCube d m (k - 2) q) (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      ((81 : ℝ) ^ d * (18 : ℝ) ^ d) *
        boundaryCrossScaleEnergyProfile (originCube d k) (originCube d k)
          (q - Section6ExcessDecay.wellPlacedCentre q m k) (1 / 3 : ℝ)
          (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
              (translatePotentialSample
                (Section6ExcessDecay.wellPlacedCentre q m k) omega) x *
            vecNormSq (u0.grad x)) := by
  let c := Section6ExcessDecay.wellPlacedCentre q m k
  let Q := originCube d k
  have hcenter : q - c ∈ openCubeSet Q := by
    have hqtrunc : q ∈ truncatedCube d m (k - 1) q :=
      Section6ExcessDecay.mem_truncatedCube_self (k - 1) hq
    have hqtranslated : q ∈ translatedCube d k c :=
      Section6ExcessDecay.truncatedCube_subset_translatedCube_wellPlacedCentre q
        hkm (by omega) hqtrunc
    exact Section6ExcessDecay.mem_translatedCube_iff.mp hqtranslated
  have hread := normalizedCutoffEnergy_truncatedCube_le_projectedCore
    M L omega hq hkm u u0 hu0
  have hprofile := localizedCoeffEnergyValue_core_le_eighteen_pow_mul_crossScaleProfile
    Q (aCutoffFamily M L (translatePotentialSample c omega)) u0 hcenter
  have hmul := mul_le_mul_of_nonneg_left hprofile (by positivity : (0 : ℝ) ≤ 81 ^ d)
  refine hread.trans ?_
  rw [boundaryCrossScaleEnergyProfile_publicCoeff_aCutoff_eq
    M L (translatePotentialSample c omega) Q Q (q - c) (1 / 3 : ℝ) u0] at hmul
  simpa only [c, Q, mul_assoc] using hmul

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
