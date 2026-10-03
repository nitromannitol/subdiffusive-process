module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.Paper.lem_extension_cell_moment
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_responseJ_bridge
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

-- Exact physical carrier, requiring a propositional set equality.
private theorem root_carrier_eq {d : ℕ} :
    (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
      Set (SpatialCoordinates d)) = openCubeSet (originCube d 0) := by
  simpa using SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube
    (d := d) 0 (by norm_num)

-- A matched Ch02 response bounds both normalized affine coordinates.
theorem aux_matched_affine_pointwise {d : ℕ}
    (U : Domain d) (Om : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    (hset : (Om : Set (SpatialCoordinates d)) = (U : Set (Homogenization.Vec d)))
    {a : Homogenization.Vec d → ℝ}
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (hOm : Bornology.IsBounded (Om : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Om) w‖)
    (hN : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Om) w‖)
    (aQ : PositiveCoefficient Om)
    (haQ : ((aQ.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a))
    (J : ℝ)
    (hJ : IsGreatest {v : ℝ | ∃ e : Fin d → ℝ,
      (∑ i : Fin d, e i ^ 2) = 1 ∧ v = responseJ U data.toCoeffOn e e} J)
    (e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    affineDirichletResponse hOm hD aQ e ≤
      2 * volume.real (Om : Set (SpatialCoordinates d)) * (J + 1) ∧
    affineInverseNeumannResponse hN aQ e ≤
      2 * volume.real (Om : Set (SpatialCoordinates d)) * (J + 1) := by
  obtain ⟨hdir, hneu⟩ := lem_as_coarse_shallow_grid_responseJ_bridge
    U Om hset data hOm hvol hD hN aQ haQ e he
  have heSq : (∑ i : Fin d, e i ^ 2) = 1 := by
    rw [← he, vecNormSq, vecDot]
    exact Finset.sum_congr rfl fun i _ => sq (e i)
  have hR : responseJ U data.toCoeffOn e e ≤ J :=
    hJ.2 ⟨e, heSq, rfl⟩
  have hfac : 0 ≤ 2 * volume.real (Om : Set (SpatialCoordinates d)) := by
    positivity
  constructor <;> nlinarith

-- Converts the `family` returned by the physical matched-moment theorem to

theorem aux_matched_affine_pointwise_of_family {d : ℕ}
    (U : Domain d) (Om : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    (hset : (Om : Set (SpatialCoordinates d)) = (U : Set (Homogenization.Vec d)))
    {a : Homogenization.Vec d → ℝ}
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (hOm : Bornology.IsBounded (Om : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Om) w‖)
    (hN : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Om) w‖)
    (aQ : PositiveCoefficient Om)
    (haQ : ((aQ.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a))
    (A : CoeffOn U) (hAE : CoeffOn.AEEq A data.toCoeffOn)
    (J : ℝ)
    (hJ : IsGreatest {v : ℝ | ∃ e : Fin d → ℝ,
      (∑ i : Fin d, e i ^ 2) = 1 ∧ v = responseJ U A e e} J)
    (e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    affineDirichletResponse hOm hD aQ e ≤
      2 * volume.real (Om : Set (SpatialCoordinates d)) * (J + 1) ∧
    affineInverseNeumannResponse hN aQ e ≤
      2 * volume.real (Om : Set (SpatialCoordinates d)) * (J + 1) := by
  have hJ' : IsGreatest {v : ℝ | ∃ u : Fin d → ℝ,
      (∑ i : Fin d, u i ^ 2) = 1 ∧ v = responseJ U data.toCoeffOn u u} J := by
    convert hJ using 1
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, (responseJ_eq_ofAEEq hAE u u).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, responseJ_eq_ofAEEq hAE u u⟩
  exact aux_matched_affine_pointwise U Om hset data hOm hvol hD hN aQ haQ J hJ' e he

theorem aux_matched_family_physical_ae {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (om : BilateralField d)
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData
      (cubeDomain (originCube d 0))
      (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N))
    (A : CoeffOn (cubeDomain (originCube d 0)))
    (hA : ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d 0)),
      A.toCoeffField x = scalarMatrix
        (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x)) :
    CoeffOn.AEEq A data.toCoeffOn := by
  unfold CoeffOn.AEEq
  simpa only [cubeDomain_coe, SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData.toCoeffOn,
    SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField,
    Homogenization.volumeMeasureOn, Filter.EventuallyEq] using! hA

theorem aux_matched_physical_scalar_data {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (om : BilateralField d) :
    Nonempty (SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData
      (cubeDomain (originCube d 0))
      (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N)) :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
    (SubdiffusiveProcess.Lane4.cutoffCoefficient_continuous M _ om N)
    (SubdiffusiveProcess.Lane4.cutoffCoefficient_pos M _ om N)
    (cubeDomain (originCube d 0))

theorem aux_matched_physical_positive_coeff_ae {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (om : BilateralField d) :
    ((SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
      (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)).val :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1
        (by norm_num) : Set (SpatialCoordinates d))]
      cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N := by
  let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let K := closedCube (0 : SpatialCoordinates d) 1 (by norm_num)
  haveI : Fact ((Om : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d) (by norm_num)⟩
  have h0 := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := Om) K
    (SubdiffusiveProcess.Lane4.cutoffCoefficientCM M
      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
      (0 : SpatialCoordinates d) (by norm_num))
    (SubdiffusiveProcess.Lane4.cutoffCoefficientCM_pos M
      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
      (0 : SpatialCoordinates d) (by norm_num)) 1 one_pos
  filter_upwards [h0, ae_restrict_mem Om.isOpen.measurableSet] with x hx hxOm
  simpa [Om, K, SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient,
    SubdiffusiveProcess.Lane4.cutoffCoefficientCM] using hx hxOm

theorem aux_matched_root_poincare {d : ℕ} [NeZero d] :
    (∃ K : ℝ≥0, ∀ w : killedSobolevGraph
        (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)),
      ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))) w‖) ∧
    (∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph
        (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)),
      ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))) w‖) := by
  let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  have hset : (Om : Set (SpatialCoordinates d)) = openCubeSet (originCube d 0) :=
    root_carrier_eq
  have hgeom : Homogenization.IsOpenBoundedConvexDomain
      (Om : Set (SpatialCoordinates d)) := by
    rw [hset]
    exact Homogenization.isOpenBoundedConvexDomain_openCubeSet (originCube d 0)
  exact exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain Om hgeom

theorem aux_matched_root_volume_pos {d : ℕ} :
    0 < volume.real (centeredCube (0 : SpatialCoordinates d) 1
      (by norm_num) : Set (SpatialCoordinates d)) := by
  rw [Measure.real, centeredCube_volume]
  simp

theorem aux_matched_physical_affine_pointwise {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (om : BilateralField d)
    (A : CoeffOn (cubeDomain (originCube d 0)))
    (hA : ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d 0)),
      A.toCoeffField x = scalarMatrix
        (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x))
    (J : ℝ)
    (hJ : IsGreatest {v : ℝ | ∃ e : Fin d → ℝ,
      (∑ i : Fin d, e i ^ 2) = 1 ∧
      v = responseJ (cubeDomain (originCube d 0)) A e e} J)
    (e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
    let hP := aux_matched_root_poincare (d := d)
    let aQ := SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
      (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)
    affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d)
        (by norm_num : (0 : ℝ) < 1)) hP.1 aQ e ≤
        2 * volume.real (Om : Set (SpatialCoordinates d)) * (J + 1) ∧
      affineInverseNeumannResponse hP.2 aQ e ≤
        2 * volume.real (Om : Set (SpatialCoordinates d)) * (J + 1) := by
  let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let U := cubeDomain (originCube d 0)
  let a := cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
  let aQ := SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
    (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
    (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)
  let data := Classical.choice (aux_matched_physical_scalar_data M N om)
  have hset : (Om : Set (SpatialCoordinates d)) = (U : Set (Homogenization.Vec d)) := by
    simpa only [U, cubeDomain_coe] using (root_carrier_eq (d := d))
  have hP := aux_matched_root_poincare (d := d)
  have hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)) :=
    aux_matched_root_volume_pos
  have haQ : (aQ.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a :=
    aux_matched_physical_positive_coeff_ae M N om
  have hAE : CoeffOn.AEEq A data.toCoeffOn :=
    aux_matched_family_physical_ae M N om data A hA
  exact aux_matched_affine_pointwise_of_family U Om hset data
    (centeredCube_isBounded (0 : SpatialCoordinates d) (by norm_num)) hvol
    hP.1 hP.2 aQ haQ A hAE J hJ e he

private theorem basis_vec_norm_sq {d : ℕ} [NeZero d] :
    vecNormSq (fun i : Fin d => if i = 0 then (1 : ℝ) else 0) = 1 := by
  rw [vecNormSq, vecDot]
  simp

theorem aux_matched_physical_J_plus_one_nonneg {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (om : BilateralField d)
    (A : CoeffOn (cubeDomain (originCube d 0)))
    (hA : ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d 0)),
      A.toCoeffField x = scalarMatrix
        (cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x))
    (J : ℝ)
    (hJ : IsGreatest {v : ℝ | ∃ e : Fin d → ℝ,
      (∑ i : Fin d, e i ^ 2) = 1 ∧
      v = responseJ (cubeDomain (originCube d 0)) A e e} J) :
    0 ≤ J + 1 := by
  let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let hP := aux_matched_root_poincare (d := d)
  let aQ := SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
    (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
    (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)
  have hpoint0 := (aux_matched_physical_affine_pointwise M N om A hA J hJ
    (fun i : Fin d => if i = 0 then (1 : ℝ) else 0) basis_vec_norm_sq).1
  have hZ0 : 0 ≤ affineDirichletResponse
      (centeredCube_isBounded (0 : SpatialCoordinates d)
        (by norm_num : (0 : ℝ) < 1)) hP.1 aQ
        (fun i : Fin d => if i = 0 then (1 : ℝ) else 0) :=
    dirichletResponse_nonneg (killedResponseSpace hP.1) aQ
      (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d)
        (by norm_num : (0 : ℝ) < 1)) _ 0)
  have hVpos : 0 < 2 * volume.real (Om : Set (SpatialCoordinates d)) :=
    mul_pos (by norm_num : (0 : ℝ) < 2) aux_matched_root_volume_pos
  nlinarith

-- The moment transfer uses exactly the bound supplied by the matched theorem.
theorem aux_matched_affine_eLpNorm {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (p C V : ℝ)
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (J Z : BilateralField d → ℝ)
    (hJmeas : AEStronglyMeasurable J (chaosSampleLaw M).toMeasure)
    (hJnorm : eLpNorm J (ENNReal.ofReal (2 * p))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C)
    (hJ0 : ∀ om, 0 ≤ J om + 1)
    (hZ0 : ∀ om, 0 ≤ Z om)
    (hZ : ∀ om, Z om ≤ V * (J om + 1)) :
    SubdiffusiveProcess.RawLp.eLpNorm Z (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (V * (C + 1)) := by
  have hp2 : 0 < 2 * p := by linarith
  have hpone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) := by
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 2 * p by linarith))
  have hone : eLpNorm (fun _ : BilateralField d => (1 : ℝ))
      (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure = 1 := by
    rw [eLpNorm_const' _ (ENNReal.ofReal_ne_zero_iff.mpr hp2) ENNReal.ofReal_ne_top]
    simp
  have hsum := eLpNorm_add_le (μ := (chaosSampleLaw M).toMeasure) (f := J) (g := fun _ : BilateralField d => (1 : ℝ)) hpone
  have hX : eLpNorm (fun om => J om + 1) (ENNReal.ofReal (2 * p))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C + 1) := by
    refine hsum.trans ?_
    rw [hone, ENNReal.ofReal_add hC zero_le_one, ENNReal.ofReal_one]
    exact add_le_add hJnorm (le_refl _)
  have hZnorm : SubdiffusiveProcess.RawLp.eLpNorm Z (ENNReal.ofReal (2 * p))
      (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal V * eLpNorm (fun om => J om + 1)
          (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure := by
    apply le_trans (SubdiffusiveProcess.RawLp.eLpNorm_mono_ae (g := fun om => V * (J om + 1)) (Filter.Eventually.of_forall fun om => ?_))
    · apply le_trans (SubdiffusiveProcess.RawLp.eLpNorm_le_guarded _ _ _)
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (aestronglyMeasurable_const.mul (hJmeas.add aestronglyMeasurable_const))
      filter_upwards with om
      simp only [Pi.add_apply, Pi.mul_apply]
      rw [Real.norm_of_nonneg (mul_nonneg hV (hJ0 om)), Real.norm_of_nonneg (hJ0 om)]
    
    rw [Real.norm_of_nonneg (hZ0 om)]
    rw [Real.norm_of_nonneg (mul_nonneg hV (hJ0 om))]
    exact hZ om
  calc
    _ ≤ ENNReal.ofReal V * ENNReal.ofReal (C + 1) :=
      hZnorm.trans (mul_le_mul_right hX _)
    _ = ENNReal.ofReal (V * (C + 1)) := (ENNReal.ofReal_mul hV).symm

theorem aux_matched_physical_affine_moment {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (p C : ℝ) (hp : 1 ≤ p) (hC : 0 ≤ C)
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (J : ℕ → BilateralField d → ℝ)
    (hfamily : ∀ N om,
      ∀ᵐ x ∂volume.restrict (openCubeSet (originCube d 0)),
        ((family N om).coeffOn (originCube d 0)).toCoeffField x =
          scalarMatrix (cutoffCoefficient M
            (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x))
    (hJgreat : ∀ N om, IsGreatest {v : ℝ | ∃ e : Fin d → ℝ,
      (∑ i : Fin d, e i ^ 2) = 1 ∧
      v = responseJ (cubeDomain (originCube d 0))
        ((family N om).coeffOn (originCube d 0)) e e} (J N om))
    (hJmeas : ∀ N, AEStronglyMeasurable (J N) (chaosSampleLaw M).toMeasure)
    (hJnorm : ∀ N, eLpNorm (J N) (ENNReal.ofReal (2 * p))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C)
    (N : ℕ) (e : Homogenization.Vec d) (he : vecNormSq e = 1) :
    let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
    let hP := aux_matched_root_poincare (d := d)
    let aQ := fun om => SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
      (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)
    SubdiffusiveProcess.RawLp.eLpNorm (fun om => affineDirichletResponse
        (centeredCube_isBounded (0 : SpatialCoordinates d)
          (by norm_num : (0 : ℝ) < 1)) hP.1 (aQ om) e)
      (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (2 * volume.real (Om : Set (SpatialCoordinates d)) * (C + 1)) ∧
      SubdiffusiveProcess.RawLp.eLpNorm (fun om => affineInverseNeumannResponse hP.2 (aQ om) e)
      (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (2 * volume.real (Om : Set (SpatialCoordinates d)) * (C + 1)) := by
  let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let hP := aux_matched_root_poincare (d := d)
  let aQ := fun om => SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
    (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
    (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)
  let V : ℝ := 2 * volume.real (Om : Set (SpatialCoordinates d))
  have hV : 0 ≤ V := by
    dsimp [V, Om]
    positivity
  have hpoint : ∀ om, affineDirichletResponse
      (centeredCube_isBounded (0 : SpatialCoordinates d)
        (by norm_num : (0 : ℝ) < 1)) hP.1 (aQ om) e ≤ V * (J N om + 1) ∧
      affineInverseNeumannResponse hP.2 (aQ om) e ≤ V * (J N om + 1) := by
    intro om
    exact aux_matched_physical_affine_pointwise M N om
      ((family N om).coeffOn (originCube d 0)) (hfamily N om)
      (J N om) (hJgreat N om) e he
  have hJ0 : ∀ om, 0 ≤ J N om + 1 := by
    intro om
    exact aux_matched_physical_J_plus_one_nonneg M N om
      ((family N om).coeffOn (originCube d 0)) (hfamily N om)
      (J N om) (hJgreat N om)
  have hD0 : ∀ om, 0 ≤ affineDirichletResponse
      (centeredCube_isBounded (0 : SpatialCoordinates d)
        (by norm_num : (0 : ℝ) < 1)) hP.1 (aQ om) e := by
    intro om
    exact dirichletResponse_nonneg (killedResponseSpace hP.1) (aQ om)
      (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d)
        (by norm_num : (0 : ℝ) < 1)) e 0)
  have hN0 : ∀ om, 0 ≤ affineInverseNeumannResponse hP.2 (aQ om) e := by
    intro om
    exact inverseResponse_nonneg (meanZeroResponseSpace hP.2) (aQ om) _
  constructor
  · exact aux_matched_affine_eLpNorm M p C V hp hC hV (J N) _
      (hJmeas N) (hJnorm N) hJ0 hD0 (fun om => (hpoint om).1)
  · exact aux_matched_affine_eLpNorm M p C V hp hC hV (J N) _
      (hJmeas N) (hJnorm N) hJ0 hN0 (fun om => (hpoint om).2)

def aux_matched_physical_affine_moment_bound {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (p C : ℝ)
    (N : ℕ) (e : Homogenization.Vec d) : Prop :=
  let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let hP := aux_matched_root_poincare (d := d)
  let aQ := fun om => SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
    (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
    (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)
  SubdiffusiveProcess.RawLp.eLpNorm (fun om => affineDirichletResponse
      (centeredCube_isBounded (0 : SpatialCoordinates d)
        (by norm_num : (0 : ℝ) < 1)) hP.1 (aQ om) e)
    (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * volume.real (Om : Set (SpatialCoordinates d)) * (C + 1)) ∧
    SubdiffusiveProcess.RawLp.eLpNorm (fun om => affineInverseNeumannResponse hP.2 (aQ om) e)
    (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * volume.real (Om : Set (SpatialCoordinates d)) * (C + 1))

theorem lem_as_coarse_shallow_grid_matched_affine_moment {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (p : ℝ) (hp : 1 ≤ p) :
    ∃ δ0 C0 : ℝ, 0 < δ0 ∧ 0 < C0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ δ0 →
      ∀ N : ℕ, ∀ e : Homogenization.Vec d, vecNormSq e = 1 →
        aux_matched_physical_affine_moment_bound M p C0 N e := by
  obtain ⟨δ0, C0, hδ0, hC0, hmatched⟩ :=
    aux_lem_extension_cell_moment_matched_response hd I p hp
  refine ⟨δ0, C0, hδ0, hC0, ?_⟩
  intro M hδ N e he
  obtain ⟨family, J, hfamily, hJgreat, hJmeas, hJnorm⟩ := hmatched M hδ
  exact aux_matched_physical_affine_moment M p C0 hp hC0.le family J
    (fun N om => hfamily N om (originCube d 0))
    hJgreat hJmeas hJnorm N e he


end Paper













