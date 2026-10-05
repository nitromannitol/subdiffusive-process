module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeMassAverages
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSobolevDisplay
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables

@[expose] public section

/-!
# Physical cube mass comparisons

The average on a translated physical cube equals the pulled-back reference
cube average. Actual cutoff continuity and positivity supply every volume,
integrability, and mass side condition. Consequently average bounds between
one half and three halves turn a geometric volume fraction into one third of
that fraction in weighted mass. A local factor-two coefficient bound gives
one half of the volume fraction for arbitrary measurable sets.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Set MeasureTheory _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Translation moves the physical average to the reference open cube. -/
theorem goodCube_volumeAverage_physical_cube_eq_open
    {d : ℕ} (m : ℤ) (z : Vec d) (f : Vec d → ℝ) :
    volumeAverage (cubeSet (z, (3 : ℝ) ^ m)) f =
      volumeAverage (openCubeSet (originCube d m)) (fun x => f (x + z)) := by
  rw [← translatedCube_eq_cubeSet m z]
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.volumeAverage_image_add_left z
    (openCubeSet (originCube d m)) f

/-- The physical average equals the pulled-back triadic cube average.
The open and half-open carriers are identified only at the level of averages. -/
theorem goodCube_volumeAverage_physical_cube
    {d : ℕ} (m : ℤ) (z : Vec d) (f : Vec d → ℝ) :
    volumeAverage (cubeSet (z, (3 : ℝ) ^ m)) f =
      cubeAverage (originCube d m) (fun x => f (x + z)) := by
  rw [goodCube_volumeAverage_physical_cube_eq_open]
  show (volume (openCubeSet (originCube d m))).toReal⁻¹ *
      ∫ x in openCubeSet (originCube d m), f (x + z) = _
  rw [Homogenization.volume_openCubeSet_toReal,
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.weightedSobolev_cubeAverage_open]

/-- The actual cutoff has positive finite mass and a positive average on
every positive-side physical cube, with all integration side conditions. -/
theorem goodCube_cutoff_physical_mass_data
    {d : ℕ} (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (Q : Cube d) (hQ : 0 < Q.2) :
    MeasurableSet (cubeSet Q) ∧ volume (cubeSet Q) ≠ 0 ∧ volume (cubeSet Q) ≠ ⊤ ∧
      IntegrableOn (aCutoff M L omega) (cubeSet Q) ∧
      (∀ᵐ x ∂volume.restrict (cubeSet Q), 0 ≤ aCutoff M L omega x) ∧
      0 < volumeAverage (cubeSet Q) (aCutoff M L omega) ∧
      weightedMeasure (aCutoff M L omega) (cubeSet Q) ≠ 0 ∧
      weightedMeasure (aCutoff M L omega) (cubeSet Q) ≠ ⊤ := by
  have hmeas : MeasurableSet (cubeSet Q) := measurableSet_cubeSet Q
  have hv : volume (cubeSet Q) = ENNReal.ofReal (Q.2 ^ d) :=
    volume_cubeSet (le_of_lt hQ)
  have hpos : (0 : ℝ) < Q.2 ^ d := pow_pos hQ d
  have hv0 : volume (cubeSet Q) ≠ 0 := by
    rw [hv]; exact ENNReal.ofReal_ne_zero_iff.mpr hpos
  have hvt : volume (cubeSet Q) ≠ ⊤ := by rw [hv]; exact ENNReal.ofReal_ne_top
  have hint : IntegrableOn (aCutoff M L omega) (cubeSet Q) volume :=
    ((continuous_aCutoff M L omega).continuousOn.integrableOn_compact
      (isBounded_centeredAxisCube Q.1 Q.2).isCompact_closure).mono_set subset_closure
  have hae : ∀ᵐ x ∂volume.restrict (cubeSet Q), 0 ≤ aCutoff M L omega x := by
    filter_upwards with x
    exact (aCutoff_pos M L omega x).le
  have hpair := goodCube_weightedMeasure_aCutoff_ne_zero_ne_top M L omega Q hQ
  have havg : 0 < volumeAverage (cubeSet Q) (aCutoff M L omega) := by
    by_contra hle
    push Not at hle
    rw [goodCube_weightedMeasure_eq_volume_mul_average hmeas hv0 hvt hint hae,
      ENNReal.ofReal_eq_zero.mpr hle, zero_mul] at hpair
    exact hpair.1 rfl
  exact ⟨hmeas, hv0, hvt, hint, hae, havg, hpair.1, hpair.2⟩

/-- Pulled-back cube-average bounds transfer an actual physical volume
ratio to a weighted mass ratio, at arbitrary integer scales and cutoff. -/
theorem goodCube_cutoff_physical_mass_ratio
    {d : ℕ} (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (m r : ℤ) (z y : Vec d) {theta : ℝ} (htheta : 0 ≤ theta)
    (hvol : ENNReal.ofReal theta * volume (cubeSet (y, (3 : ℝ) ^ r)) ≤
      volume (cubeSet (z, (3 : ℝ) ^ m)))
    (hlower : (1 / 2 : ℝ) ≤ cubeAverage (originCube d m)
      (fun x => aCutoff M L omega (x + z)))
    (hupper : cubeAverage (originCube d r)
      (fun x => aCutoff M L omega (x + y)) ≤ 3 / 2) :
    ENNReal.ofReal (theta / 3) * weightedMeasure (aCutoff M L omega)
      (cubeSet (y, (3 : ℝ) ^ r)) ≤
        weightedMeasure (aCutoff M L omega) (cubeSet (z, (3 : ℝ) ^ m)) := by
  have hm : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hr : (0 : ℝ) < (3 : ℝ) ^ r := zpow_pos (by norm_num) r
  have dataZ := goodCube_cutoff_physical_mass_data M L omega ⟨z, (3 : ℝ) ^ m⟩ hm
  have dataY := goodCube_cutoff_physical_mass_data M L omega ⟨y, (3 : ℝ) ^ r⟩ hr
  have avgZ := goodCube_volumeAverage_physical_cube m z (aCutoff M L omega)
  have avgY := goodCube_volumeAverage_physical_cube r y (aCutoff M L omega)
  exact goodCube_mass_ratio_of_average_bounds dataZ.1 dataY.1 dataZ.2.1 dataZ.2.2.1
    dataY.2.1 dataY.2.2.1 dataZ.2.2.2.1 dataY.2.2.2.1 dataZ.2.2.2.2.1 dataY.2.2.2.2.1
    htheta hvol (by rw [avgZ]; exact hlower) (by rw [avgY]; exact hupper)

/-- A local factor-two coefficient bound transfers an actual volume ratio
to a mass ratio, for arbitrary measurable sets. -/
theorem goodCube_mass_ratio_of_local_factor_two
    {d : ℕ} (a : Vec d → ℝ) {S U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUS : U ⊆ S) (hVS : V ⊆ S)
    {k theta : ℝ} (hk : 0 < k) (htheta : 0 ≤ theta)
    (hbound : ∀ x ∈ S, k ≤ a x ∧ a x ≤ 2 * k)
    (hvol : ENNReal.ofReal theta * volume V ≤ volume U) :
    ENNReal.ofReal (theta / 2) * weightedMeasure a V ≤ weightedMeasure a U := by
  have hVup : weightedMeasure a V ≤ ENNReal.ofReal (2 * k) * volume V :=
    weightedMeasure_le_of_le a hV (fun x hx => (hbound x (hVS hx)).2)
  have hUlow : ENNReal.ofReal k * volume U ≤ weightedMeasure a U :=
    le_weightedMeasure_of_le a hU (fun x hx => (hbound x (hUS hx)).1)
  have hnonneg1 : 0 ≤ theta / 2 := by linarith
  have hnonneg3 : 0 ≤ k := by linarith
  calc ENNReal.ofReal (theta / 2) * weightedMeasure a V
      ≤ ENNReal.ofReal (theta / 2) * (ENNReal.ofReal (2 * k) * volume V) :=
        mul_le_mul_right hVup _
    _ = ENNReal.ofReal k * (ENNReal.ofReal theta * volume V) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hnonneg1,
          show theta / 2 * (2 * k) = k * theta by ring,
          ENNReal.ofReal_mul hnonneg3, mul_assoc]
    _ ≤ ENNReal.ofReal k * volume U := mul_le_mul_right hvol _
    _ ≤ weightedMeasure a U := hUlow

/-- The factor-two mass ratio on physical cubes for the actual cutoff
coefficient. No scale or positive-side condition is needed. -/
theorem goodCube_cutoff_physical_mass_ratio_of_local_factor_two
    {d : ℕ} (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (Q R : Cube d) {S : Set (Vec d)} (hQS : cubeSet Q ⊆ S) (hRS : cubeSet R ⊆ S)
    {k theta : ℝ} (hk : 0 < k) (htheta : 0 ≤ theta)
    (hbound : ∀ x ∈ S, k ≤ aCutoff M L omega x ∧ aCutoff M L omega x ≤ 2 * k)
    (hvol : ENNReal.ofReal theta * volume (cubeSet R) ≤ volume (cubeSet Q)) :
    ENNReal.ofReal (theta / 2) * weightedMeasure (aCutoff M L omega) (cubeSet R) ≤
      weightedMeasure (aCutoff M L omega) (cubeSet Q) :=
  goodCube_mass_ratio_of_local_factor_two (aCutoff M L omega)
    (measurableSet_cubeSet Q) (measurableSet_cubeSet R) hQS hRS hk htheta hbound hvol

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
