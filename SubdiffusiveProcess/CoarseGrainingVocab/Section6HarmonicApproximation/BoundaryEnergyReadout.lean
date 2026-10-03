module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellGeometry

@[expose] public section

/-!
# Reading projected coefficient energy in the ambient frame

The boundary Caccioppoli theorem is stated for an origin cube and a translated
sample.  The harmonic-approximation estimate integrates the original cutoff
field on translated physical cells.  This file identifies those two energies.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem symmPart_scalarMatrix_local (a : ℝ) :
    symmPart (scalarMatrix (d := d) a) = scalarMatrix (d := d) a := by
  ext i j
  by_cases h : i = j
  · simp [symmPart, scalarMatrix, h]
  · simp [symmPart, scalarMatrix, h, Ne.symm h]

private theorem vecDot_matVecMul_scalarMatrix_local (a : ℝ) (v : Vec d) :
    vecDot v (matVecMul (scalarMatrix (d := d) a) v) = a * vecNormSq v := by
  simp only [scalarMatrix, vecDot, matVecMul, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, mul_comm,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum, vecNormSq]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact covariance of the scalar cutoff energy under the projected-cell
translation. -/
theorem localizedCoeffEnergyValue_aCutoffFamily_eq_translate
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (c : Vec d) (V : Set (Vec d))
    (u0 : H1Function (openCubeSet Q))
    (gradU : Vec d → Vec d)
    (hu0 : ∀ x, u0.grad x = gradU (x + c)) :
    localizedCoeffEnergyValue V
        ((aCutoffFamily M L (translatePotentialSample c omega)).coeffOn Q) u0 =
      volumeAverage (translateSet c V) (fun x =>
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (gradU x)) := by
  unfold localizedCoeffEnergyValue normalizedSetAverage volumeAverage
  rw [volume_translateSet_eq]
  rw [← setIntegral_comp_addRight_translateSet c V (fun x =>
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (gradU x))]
  apply congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z)
  apply integral_congr_ae
  filter_upwards with x
  rw [hu0]
  simp only [aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
    ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
    Section6Covariance.aCutoff_translatePotentialSample]
  rw [symmPart_scalarMatrix_local, vecDot_matVecMul_scalarMatrix_local]

/-- A normalized average over a subset is controlled by the volume ratio and
the ambient normalized average. -/
theorem normalizedSetAverage_le_mul_of_subset
    {S T : Set (Vec d)} {f : Vec d → ℝ} {K : ℝ}
    (hST : S ⊆ T) (hSpos : 0 < volume S) (hTtop : volume T < ∞)
    (hTmeas : MeasurableSet T) (hf : ∀ y ∈ T, 0 ≤ f y)
    (hint : IntegrableOn f T volume)
    (hK : (volume T).toReal ≤ K * (volume S).toReal) :
    normalizedSetAverage S f ≤ K * normalizedSetAverage T f := by
  have hSle : volume S ≤ volume T := measure_mono hST
  have hSreal : 0 < (volume S).toReal :=
    ENNReal.toReal_pos (ne_of_gt hSpos) (ne_of_lt (lt_of_le_of_lt hSle hTtop))
  have hTreal : 0 < (volume T).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le hSpos hSle)) (ne_of_lt hTtop)
  have hTne : (volume T).toReal ≠ 0 := ne_of_gt hTreal
  have hnonneg : 0 ≤ᵐ[volume.restrict T] f := by
    filter_upwards [ae_restrict_mem hTmeas] with y hy
    exact hf y hy
  have hraw : ∫ y in S, f y ∂volume ≤ ∫ y in T, f y ∂volume :=
    setIntegral_mono_set hint hnonneg (Filter.Eventually.of_forall hST)
  have hIT : 0 ≤ ∫ y in T, f y ∂volume := integral_nonneg_of_ae hnonneg
  have hratio : (volume S).toReal⁻¹ * (volume T).toReal ≤ K := by
    have h := mul_le_mul_of_nonneg_left hK (le_of_lt (inv_pos.2 hSreal))
    have heq : (volume S).toReal⁻¹ * (K * (volume S).toReal) = K := by
      field_simp
    rwa [heq] at h
  have hTavg : 0 ≤ (volume T).toReal⁻¹ * ∫ y in T, f y ∂volume :=
    mul_nonneg (le_of_lt (inv_pos.2 hTreal)) hIT
  unfold normalizedSetAverage volumeAverage
  calc
    (volume S).toReal⁻¹ * ∫ y in S, f y ∂volume ≤
        (volume S).toReal⁻¹ * ∫ y in T, f y ∂volume :=
      mul_le_mul_of_nonneg_left hraw (le_of_lt (inv_pos.2 hSreal))
    _ = ((volume S).toReal⁻¹ * (volume T).toReal) *
          ((volume T).toReal⁻¹ * ∫ y in T, f y ∂volume) := by
      field_simp
    _ ≤ K * ((volume T).toReal⁻¹ * ∫ y in T, f y ∂volume) :=
      mul_le_mul_of_nonneg_right hratio hTavg

/-- The translated Caccioppoli core is open. -/
theorem isOpen_translate_caccioppoliCoreSet
    (c : Vec d) (Q : TriadicCube d) (w : Vec d) :
    IsOpen (translateSet c (caccioppoliCoreSet Q w)) := by
  rw [← image_addRight_eq_translateSet]
  exact (Homeomorph.addRight c).isOpenMap _
    ((isOpen_openCubeSet Q).inter (isOpen_openCubeAtScale w (Q.scale - 2)))

/-- A deliberately coarse but dimension-only volume ratio for the projected
cell: the core is at most `81^d` times the scale-`k-2` truncated cell. -/
theorem volume_translate_core_le_eightyOne_pow_mul_truncatedCube
    {m k : ℤ} {q : Vec d} (hq : q ∈ cube d m) (hkm : k ≤ m) :
    (volume (translateSet (Section6ExcessDecay.wellPlacedCentre q m k)
        (caccioppoliCoreSet (originCube d k)
          (q - Section6ExcessDecay.wellPlacedCentre q m k)))).toReal ≤
      (81 : ℝ) ^ d * (volume (truncatedCube d m (k - 2) q)).toReal := by
  let c := Section6ExcessDecay.wellPlacedCentre q m k
  let core := caccioppoliCoreSet (originCube d k) (q - c)
  have hcoreSub : core ⊆ openCubeSet (originCube d k) := fun _ h => h.1
  have hcoreTop : volume (openCubeSet (originCube d k)) ≠ ∞ :=
    ne_of_lt (isOpenBoundedConvexDomain_openCubeSet (originCube d k)).volume_lt_top
  have hcore : (volume (translateSet c core)).toReal ≤ ((3 : ℝ) ^ k) ^ d := by
    rw [volume_translateSet_eq]
    calc
      (volume core).toReal ≤ (volume (openCubeSet (originCube d k))).toReal :=
        ENNReal.toReal_mono hcoreTop (measure_mono hcoreSub)
      _ = ((3 : ℝ) ^ k) ^ d := by
        rw [volume_openCubeSet_toReal, cubeVolume_eq_pow_scale]
        rfl
  have hwindow : ((3 : ℝ) ^ (k - 4)) ^ d ≤
      (volume (truncatedCube d m (k - 2) q)).toReal := by
    simpa only [show k - 2 - 2 = k - 4 by ring] using
      (Section6ExcessDecay.volume_toReal_truncatedCube_bounds q hq
        (by omega : k - 2 - 1 ≤ m)).1
  have hp : (0 : ℝ) ≤ (81 : ℝ) ^ d := by positivity
  have hscale : ((3 : ℝ) ^ k) ^ d =
      (81 : ℝ) ^ d * ((3 : ℝ) ^ (k - 4)) ^ d := by
    have h3 : (3 : ℝ) ^ k = 81 * (3 : ℝ) ^ (k - 4) := by
      rw [show k = 4 + (k - 4) by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    rw [h3, mul_pow]
  calc
    (volume (translateSet c core)).toReal ≤ ((3 : ℝ) ^ k) ^ d := hcore
    _ = (81 : ℝ) ^ d * ((3 : ℝ) ^ (k - 4)) ^ d := hscale
    _ ≤ (81 : ℝ) ^ d * (volume (truncatedCube d m (k - 2) q)).toReal :=
      mul_le_mul_of_nonneg_left hwindow hp

/-- The physical scalar cutoff-energy density is integrable on every
translated projected core. -/
theorem integrableOn_cutoffEnergy_translate_core
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (c w : Vec d)
    (u0 : H1Function (openCubeSet Q)) (gradU : Vec d → Vec d)
    (hu0 : ∀ x, u0.grad x = gradU (x + c)) :
    IntegrableOn (fun x =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (gradU x))
      (translateSet c (caccioppoliCoreSet Q w)) volume := by
  let A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
  let core := caccioppoliCoreSet Q w
  let f : Vec d → ℝ := fun x =>
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (gradU x)
  have hwhole : IntegrableOn (fun x =>
      vecDot (u0.grad x) (matVecMul ((A.coeffOn Q).toCoeffField x) (u0.grad x)))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 u0.grad_memVectorL2
      (memVectorL2_flux Q A u0)
  have hcore : IntegrableOn (fun x =>
      vecDot (u0.grad x) (matVecMul ((A.coeffOn Q).toCoeffField x) (u0.grad x)))
      core := hwhole.mono_set (fun _ h => h.1)
  have hcomp : IntegrableOn (f ∘ fun x => x + c) core := by
    apply hcore.congr_fun
    · intro x _
      change vecDot (u0.grad x) (matVecMul ((A.coeffOn Q).toCoeffField x)
        (u0.grad x)) = f (x + c)
      dsimp only [f]
      rw [hu0]
      dsimp only [A]
      simp only [aCutoffFamily, aCutoffTriadicData,
        ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
        ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
        Section6Covariance.aCutoff_translatePotentialSample]
      rw [vecDot_matVecMul_scalarMatrix_local]
    · exact measurableSet_caccioppoliCoreSet Q w
  have hiff := (measurePreserving_add_right (volume : Measure (Vec d)) c).integrableOn_image
    (Homeomorph.addRight c).measurableEmbedding (f := f) (s := core)
  rw [image_addRight_eq_translateSet] at hiff
  exact hiff.mpr hcomp

/-- The physical scalar cutoff-energy density is integrable on every subset
of the ambient origin cube. -/
theorem integrableOn_cutoffEnergy_of_subset_originCube
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (m : ℤ) (S : Set (Vec d))
    (u : H1Function (openCubeSet (originCube d m)))
    (hSmeas : MeasurableSet S) (hS : S ⊆ openCubeSet (originCube d m)) :
    IntegrableOn (fun x =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) S := by
  let Q := originCube d m
  let A : CoeffFamily d := aCutoffFamily M L omega
  have hwhole : IntegrableOn (fun x =>
      vecDot (u.grad x) (matVecMul ((A.coeffOn Q).toCoeffField x) (u.grad x)))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2
      (memVectorL2_flux Q A u)
  apply (hwhole.mono_set hS).congr_fun
  · intro x _
    dsimp only [A, Q]
    simp only [aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField]
    rw [vecDot_matVecMul_scalarMatrix_local]
  · exact hSmeas

/-- The physical cutoff energy on one scale-`k-2` truncated cell is read from
the translated projected Caccioppoli core, with a dimension-only loss. -/
theorem normalizedCutoffEnergy_truncatedCube_le_projectedCore
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {m k : ℤ} {q : Vec d} (hq : q ∈ cube d m) (hkm : k ≤ m)
    (u : H1Function (openCubeSet (originCube d m)))
    (u0 : H1Function (openCubeSet (originCube d k)))
    (hu0 : ∀ x, u0.grad x = u.grad (x +
      Section6ExcessDecay.wellPlacedCentre q m k)) :
    normalizedSetAverage (truncatedCube d m (k - 2) q) (fun x =>
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      (81 : ℝ) ^ d * localizedCoeffEnergyValue
        (caccioppoliCoreSet (originCube d k)
          (q - Section6ExcessDecay.wellPlacedCentre q m k))
        ((aCutoffFamily M L
          (translatePotentialSample
            (Section6ExcessDecay.wellPlacedCentre q m k) omega)).coeffOn
              (originCube d k)) u0 := by
  let c := Section6ExcessDecay.wellPlacedCentre q m k
  let core := caccioppoliCoreSet (originCube d k) (q - c)
  let S := truncatedCube d m (k - 2) q
  let T := translateSet c core
  let f : Vec d → ℝ := fun x =>
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)
  have hST : S ⊆ T := by
    simpa only [S, T, core, c] using
      (truncatedCube_subset_translate_caccioppoliCore q hkm le_rfl)
  have hSreal : 0 < (volume S).toReal := by
    simpa only [S] using
      Section6ExcessDecay.volume_toReal_truncatedCube_pos q hq
        (by omega : k - 2 - 1 ≤ m)
  have hSpair := ENNReal.toReal_ne_zero.mp hSreal.ne'
  have hSpos : 0 < volume S := pos_iff_ne_zero.mpr hSpair.1
  have hTtop : volume T < ∞ := by
    change volume (translateSet c core) < ∞
    rw [volume_translateSet_eq]
    exact lt_of_le_of_lt (measure_mono (fun _ h => h.1))
      (isOpenBoundedConvexDomain_openCubeSet (originCube d k)).volume_lt_top
  have hTmeas : MeasurableSet T :=
    (isOpen_translate_caccioppoliCoreSet c (originCube d k) (q - c)).measurableSet
  have hf : ∀ x ∈ T, 0 ≤ f x := by
    intro x _
    exact mul_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
      (vecNormSq_nonneg (u.grad x))
  have hint := integrableOn_cutoffEnergy_translate_core M L omega
    (originCube d k) c (q - c) u0 u.grad hu0
  have havg := normalizedSetAverage_le_mul_of_subset hST hSpos hTtop hTmeas
    hf (by simpa only [f, T, core, c] using hint)
    (by simpa only [S, T, core, c] using
      volume_translate_core_le_eightyOne_pow_mul_truncatedCube hq hkm)
  rw [localizedCoeffEnergyValue_aCutoffFamily_eq_translate M L omega
    (originCube d k) c core u0 u.grad hu0]
  simpa only [S, T, core, c, f] using havg

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
