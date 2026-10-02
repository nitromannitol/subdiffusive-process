import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.coefficient_physical_identity
import SubdiffusiveProcess.Paper.in_common_scale_coupling
import SubdiffusiveProcess.Paper.physical_scale_dictionary
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.Lane2.CellDirichlet
import Homogenization.CoarseGraining.Translation
import Homogenization.Book.Ch02.Theorems.Dilation
import SubdiffusiveProcess.Assumptions.CoefficientPackaging

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

def aux_neumann_response_defect_transport_translateCoeffOn
    {d : ℕ} (V W : Homogenization.Book.Ch02.Domain d) (z : Homogenization.Vec d)
    (hset : (W : Set (Homogenization.Vec d)) =
      Homogenization.translateSet z (V : Set (Homogenization.Vec d)))
    (a : Homogenization.Book.Ch02.CoeffOn V) :
    Homogenization.Book.Ch02.CoeffOn W := by
  let hmp := Homogenization.measurePreserving_subRight_restrict_translateSet
    (d := d) z (V : Set (Homogenization.Vec d))
  refine {
    toCoeffField := Homogenization.translateCoeffField (-z) a.toCoeffField
    lam := a.lam
    Lam := a.Lam
    lam_pos := a.lam_pos
    lam_le_Lam := a.lam_le_Lam
    aeStronglyMeasurable := ?_
    aeElliptic := ?_ }
  · intro i j
    rw [hset]
    have h := (a.aeStronglyMeasurable i j).comp_measurePreserving hmp
    refine h.congr ?_
    filter_upwards [] with x
    by_cases hx : x - z ∈ (V : Set (Homogenization.Vec d))
    · have hxt : x ∈ Homogenization.translateSet z (V : Set (Homogenization.Vec d)) :=
        Homogenization.mem_translateSet_iff_sub_mem.mpr hx
      have hvec : x - z = (fun i => x i + (-z) i) := rfl
      simp only [Function.comp_apply, Homogenization.restrictCoeffField,
        Homogenization.translateCoeffField]
      rw [hvec]
      have hxl : (fun i => x i + (-z) i) ∈ (V : Set (Homogenization.Vec d)) := by
        rw [← hvec]
        exact hx
      have hxl' : (fun i => x i + -z i) ∈ (V : Set (Homogenization.Vec d)) := by
        convert hxl using 1 <;> rfl
      simp [hxl', hxt]
    · have hxt : x ∉ Homogenization.translateSet z (V : Set (Homogenization.Vec d)) := by
        intro hxt
        exact hx (Homogenization.mem_translateSet_iff_sub_mem.mp hxt)
      simp [Function.comp_apply, Homogenization.restrictCoeffField,
        Homogenization.translateCoeffField, hx, hxt]
  · rw [hset]
    have h' : ∀ᵐ x ∂Measure.map (fun x : Homogenization.Vec d => x - z)
          (volume.restrict (Homogenization.translateSet z (V : Set (Homogenization.Vec d)))),
          Homogenization.IsEllipticMatrix a.lam a.Lam (a.toCoeffField x) := by
        rw [hmp.map_eq]
        exact a.aeElliptic
    have h := MeasureTheory.ae_of_ae_map hmp.aemeasurable h'
    filter_upwards [h] with x hx
    simpa [Homogenization.translateCoeffField] using hx

theorem aux_neumann_response_defect_transport_sigma_translate
    {d : ℕ} (V W : Homogenization.Book.Ch02.Domain d) (z : Homogenization.Vec d)
    (hset : (W : Set (Homogenization.Vec d)) =
      Homogenization.translateSet z (V : Set (Homogenization.Vec d)))
    (a : Homogenization.Book.Ch02.CoeffOn V) :
    Homogenization.Book.Ch02.sigmaStarInvCoarse W
        (aux_neumann_response_defect_transport_translateCoeffOn V W z hset a) =
      Homogenization.Book.Ch02.sigmaStarInvCoarse V a := by
  let b := aux_neumann_response_defect_transport_translateCoeffOn V W z hset a
  rw [Homogenization.Internal.Ch02.book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse]
  rw [hset]
  rw [Homogenization.sigmaStarInvCoarse_translateSet_eq_translateCoeffField]
  rw [show Homogenization.translateCoeffField z b.toCoeffField = a.toCoeffField by
    dsimp [b, aux_neumann_response_defect_transport_translateCoeffOn]
    funext x
    simp [Homogenization.translateCoeffField, sub_eq_add_neg, add_assoc]]
  rw [← Homogenization.Internal.Ch02.book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse]

theorem aux_neumann_response_defect_transport_physical_set (d N : ℕ) :
    (centeredCube (fun _ : Fin d => (3 : ℝ)^N / 2) ((3 : ℝ)^N) (by positivity) :
      Set (Fin d → ℝ)) =
      Homogenization.translateSet (fun _ : Fin d => (3 : ℝ)^N / 2)
        (Homogenization.openCubeSet
          (Homogenization.Book.Ch02.dilateCube (N : ℤ)
            (Homogenization.originCube d 0))) := by
  ext x
  rw [centeredCube_eq_pi, Homogenization.mem_translateSet_iff_sub_mem]
  constructor
  · intro hx i
    have hxi := hx i (by simp)
    constructor
    · simp [Homogenization.Book.Ch02.dilateCube, Homogenization.openCubeSet,
        Homogenization.originCube, Homogenization.cubeScaleFactor, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm, add_mul]
      linarith [hxi.1]
    · simp [Homogenization.Book.Ch02.dilateCube, Homogenization.openCubeSet,
        Homogenization.originCube, Homogenization.cubeScaleFactor, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm, add_mul]
      linarith [hxi.2]
  · intro hx i hi
    have hxi := hx i
    have hxi' : x i ∈ Set.Ioo
        ((fun _ : Fin d => (3 : ℝ)^N / 2) i - (3 : ℝ)^N / 2)
        ((fun _ : Fin d => (3 : ℝ)^N / 2) i + (3 : ℝ)^N / 2) := by
      constructor
      · simp [Homogenization.Book.Ch02.dilateCube, Homogenization.openCubeSet,
          Homogenization.originCube, Homogenization.cubeScaleFactor, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, add_mul] at hxi ⊢
        linarith [hxi.1]
      · simp [Homogenization.Book.Ch02.dilateCube, Homogenization.openCubeSet,
          Homogenization.originCube, Homogenization.cubeScaleFactor, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm, add_mul] at hxi ⊢
        linarith [hxi.2]
    exact hxi'



theorem neumann_response_defect_transport
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Rinput : Paper.in_responses d M)
    (pvec : Fin d → ℝ)
    (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
    (N : ℕ) (om eta : BilateralField d)
    (hrelab : ∀ x : SpatialCoordinates d,
      (∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) =
        ∑ j ∈ Finset.range (N + 1), (eta (j : ℤ)) ((3 : ℝ) ^ N • x)) :
    ∃ (U : Homogenization.Book.Ch02.Domain d)
      (f : Homogenization.Vec d → ℝ)
      (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U f),
      (U : Set (Homogenization.Vec d)) =
          (Rinput.cubeAt N (fun _ => (3 : ℝ) ^ N / 2) : Set (Homogenization.Vec d)) ∧
      data.toCoeffOn.toCoeffField = Rinput.coeffAt N eta ∧
      (let Q := unitNeumannCube d
      let S := meanZeroResponseSpace hP
      let L : S.space →L[ℝ] ℝ :=
        (affineNeumannLoad pvec).comp
          (subspaceGradient (meanZeroSobolevGraph Q))
      let aN0 : ℕ → BilateralField d → PositiveCoefficient Q := fun n omega =>
        cutoffPositiveCoefficient M (fun _ => 0) omega n
          (fun _ => (1 / 2 : ℝ)) one_pos
      (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        (aN0 N om).val x =
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
            f ((3 : ℝ) ^ N • x)) ∧
      inverseResponse S (aN0 N om) L =
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Homogenization.vecDot pvec
            (Homogenization.matVecMul
              (Homogenization.Book.Ch02.sigmaStarInvCoarse U data.toCoeffOn)
              pvec) ∧
      IsGreatest
        {t : ℝ | ∃ e : Homogenization.Vec d,
          Homogenization.vecNormSq e = 1 ∧
          t = Homogenization.Book.Ch02.responseJ U data.toCoeffOn
            ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))⁻¹ • e)
            (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) • e)}
        (Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) eta)) := by
  set U : Homogenization.Book.Ch02.Domain d := Rinput.cubeAt N (fun _ => (3 : ℝ) ^ N / 2) with hUdef
  set f : Homogenization.Vec d → ℝ := Rinput.coeffScalar N eta with hfdef
  have hUset : (U : Set (Homogenization.Vec d)) = (Rinput.cubeAt N (fun _ => (3 : ℝ) ^ N / 2) : Set (Homogenization.Vec d)) := rfl
  have h_cont_f : Continuous f := by
    rw [hfdef]
    have h_eq : Rinput.coeffScalar N eta = fun x : SpatialCoordinates d =>
      Real.exp ((∑ j ∈ Finset.range (N + 1), (eta (j : ℤ)) x) -
        ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
      ext x; exact Rinput.coeffScalar_eq N eta x
    rw [h_eq]
    have h_inner : Continuous (fun x : SpatialCoordinates d =>
      ((∑ j ∈ Finset.range (N + 1), (eta (j : ℤ)) x) -
        ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
      refine Continuous.sub ?_ continuous_const
      refine continuous_finset_sum _ (fun j _ => ?_)
      exact (eta (j : ℤ)).continuous
    exact Real.continuous_exp.comp h_inner
  have h_pos_f : ∀ x, 0 < f x := by
    rw [hfdef]; intro x; exact Rinput.coeffScalar_pos N eta x
  have hU_compact : IsCompact (closure (U : Set (Homogenization.Vec d))) :=
    U.isDomain.isBoundedDomain.isBounded.isCompact_closure
  have hU_nonempty : (closure (U : Set (Homogenization.Vec d))).Nonempty :=
    U.nonempty.closure
  obtain ⟨xmin, hxmin_mem, hmin⟩ := hU_compact.exists_isMinOn hU_nonempty h_cont_f.continuousOn
  obtain ⟨xmax, hxmax_mem, hmax⟩ := hU_compact.exists_isMaxOn hU_nonempty h_cont_f.continuousOn
  set lam : ℝ := f xmin with hlamdef
  set Lam : ℝ := f xmax with hlammaxdef
  have hlam_pos : 0 < lam := by rw [hlamdef]; exact h_pos_f xmin
  have hlam_le_Lam : lam ≤ Lam := by
    rw [hlamdef, hlammaxdef]
    exact hmax hxmin_mem
  let data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U f := {
    lam := lam
    Lam := Lam
    lam_pos := hlam_pos
    lam_le_Lam := hlam_le_Lam
    aeStronglyMeasurable := by
      intro i j
      have h_cont_scalar : Continuous (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField f) := by
        have h_scalarMatrix : Continuous (fun (r : ℝ) => Homogenization.scalarMatrix (d := d) r) := by
          refine continuous_pi (fun i => ?_)
          refine continuous_pi (fun j => ?_)
          dsimp [Homogenization.scalarMatrix]
          by_cases hij : i = j
          · subst hij; simpa using continuous_id (X := ℝ)
          · simpa [hij] using continuous_const (X := ℝ) (Y := ℝ)
        exact h_scalarMatrix.comp h_cont_f
      have h_cont_entry : Continuous (fun x : Homogenization.Vec d =>
          SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField f x i j) :=
        (continuous_apply j).comp ((continuous_apply i).comp h_cont_scalar)
      have h_mem : ∀ᵐ x ∂ Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d)),
          x ∈ (U : Set (Homogenization.Vec d)) :=
        MeasureTheory.ae_restrict_mem U.measurableSet
      refine h_cont_entry.aestronglyMeasurable.congr ?_
      filter_upwards [h_mem] with x hx
      simp [SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField,
        Homogenization.restrictCoeffField_apply_of_mem hx]
    aeBounds := by
      have h_mem : ∀ᵐ x ∂ Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d)),
          x ∈ (U : Set (Homogenization.Vec d)) :=
        MeasureTheory.ae_restrict_mem U.measurableSet
      filter_upwards [h_mem] with x hx
      exact ⟨hlamdef ▸ hmin (subset_closure hx), hlammaxdef ▸ hmax (subset_closure hx)⟩
  }
  have h_coeff_field_eq : data.toCoeffOn.toCoeffField = Rinput.coeffAt N eta := by
    ext x i j
    unfold data
    simp [SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData.toCoeffOn,
      SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField,
      Rinput.coeffAt_eq N eta, hfdef]
  refine ⟨U, f, data, hUset, h_coeff_field_eq, ?_⟩
  intro Q
  intro S
  intro L
  intro aN0
  have haN0_val_ae : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      (aN0 N om).val x = cutoffCoefficient M (fun _ => 0) om N x := by
    -- Use the ae lemma from expPotentialCoefficient applied to the underlying Lp function
    -- The key: (aN0 N om).val = Real.exp (compactPotentialToLp ... x) almost everywhere
    -- and compactPotentialToLp ... x = Real.log (cutoffCoefficientCM ... x) for x in the domain
    -- so Real.exp (...) = cutoffCoefficientCM ... x = cutoffCoefficient ... x
    let K : Compacts (SpatialCoordinates d) := closedCube (fun _ => (1/2 : ℝ)) 1 one_pos
    have hK_fact : ((Q : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) ⊆ (K : Set (SpatialCoordinates d)) := by
      dsimp [Q, K, unitNeumannCube]
      exact centeredCube_subset_closedCube _ one_pos
    letI : Fact (((Q : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) ⊆ (K : Set (SpatialCoordinates d))) :=
      ⟨hK_fact⟩
    have h_ae := expPotentialCoefficient_coeFn
      (g := compactPotentialToLp (Ω := Q) K
        (continuousPositiveLog
          (cutoffCoefficientCM M (fun _ => 0) om N (fun _ => (1/2 : ℝ)) one_pos)
          (cutoffCoefficientCM_pos M (fun _ => 0) om N (fun _ => (1/2 : ℝ)) one_pos) -
          ContinuousMap.const K (Real.log 1)))
    -- h_ae : ∀ᵐ x ∂volume.restrict Q, (expPotentialCoefficient ...).val x = Real.exp (compactPotentialToLp ... x)
    have hx_mem_K : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        x ∈ (K : Set (SpatialCoordinates d)) := by
      filter_upwards [ae_restrict_mem Q.isOpen.measurableSet] with x hx
      exact hK_fact hx
    have h_exp_eq : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        Real.exp (compactPotentialToLp (Ω := Q) K
          (continuousPositiveLog
            (cutoffCoefficientCM M (fun _ => 0) om N (fun _ => (1/2 : ℝ)) one_pos)
            (cutoffCoefficientCM_pos M (fun _ => 0) om N (fun _ => (1/2 : ℝ)) one_pos) -
            ContinuousMap.const K (Real.log 1)) x) =
        cutoffCoefficient M (fun _ => 0) om N x := by
      filter_upwards [compactPotentialLp_coeFn (Ω := Q) K
        (continuousPositiveLog
          (cutoffCoefficientCM M (fun _ => 0) om N (fun _ => (1/2 : ℝ)) one_pos)
          (cutoffCoefficientCM_pos M (fun _ => 0) om N (fun _ => (1/2 : ℝ)) one_pos) -
          ContinuousMap.const K (Real.log 1)),
        hx_mem_K] with x hx_lp hx_mem
      rw [compactPotentialToLp_apply K _]
      rw [hx_lp]
      rw [compactPotentialExtension_apply K _ ⟨x, hx_mem⟩]
      -- Now we have Real.exp (continuousPositiveLog ... x - Real.log 1)
      simp [continuousPositiveLog, Real.log_one, cutoffCoefficientCM]
      -- Real.exp (Real.log (cutoffCoefficientCM ... x) - 0) = cutoffCoefficientCM ... x = cutoffCoefficient ... x
      rw [Real.exp_log]
      exact cutoffCoefficientCM_pos M (fun _ => 0) om N (fun _ => (1/2 : ℝ)) one_pos ⟨x, hx_mem⟩
    filter_upwards [h_ae, h_exp_eq] with x hx1 hx2
    change (cutoffPositiveCoefficient M (fun _ => 0) om N
      (fun _ => (1 / 2 : ℝ)) one_pos).val x = _
    unfold cutoffPositiveCoefficient normalizedContinuousPositiveCoefficient
    exact hx1.trans hx2
  have h_coeff_eq_ae : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      cutoffCoefficient M (fun _ => 0) om N x = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * f ((3 : ℝ) ^ N • x) := by
    filter_upwards with x
    dsimp [f, hfdef]
    rw [Rinput.coeffScalar_eq N eta]
    dsimp [cutoffCoefficient, cutoffPotential]
    have hsum : (∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x) =
        ∑ j ∈ Finset.range (N + 1), (eta (j : ℤ)) ((3 : ℝ) ^ N • x) := hrelab x
    rw [hsum]
    ring
  have h_first : (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      (aN0 N om).val x = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * f ((3 : ℝ) ^ N • x)) := by
    filter_upwards [haN0_val_ae, h_coeff_eq_ae] with x hx1 hx2
    rw [hx1, hx2]
  have h_third : IsGreatest
      {t : ℝ | ∃ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 ∧
        t = Homogenization.Book.Ch02.responseJ U data.toCoeffOn
          ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))⁻¹ • e)
          (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) • e)}
      (Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) eta) := by
    have h_defect := Rinput.defect_isGreatest N (fun _ => (3 : ℝ) ^ N / 2) eta
    -- h_defect : IsGreatest {t | ∃ e, vecNormSq e = 1 ∧ t = ResponseJ (cubeAt N (3^N/2) : Set _) ... (coeffAt N eta)} (defect N (3^N/2) eta)
    -- Rewrite to use U and data.toCoeffOn
    have hU_eq : (Rinput.cubeAt N (fun _ => (3 : ℝ) ^ N / 2) : Set (Homogenization.Vec d)) = (U : Set (Homogenization.Vec d)) := by
      dsimp [U, hUdef]
    have h_coeff_eq' : Rinput.coeffAt N eta = data.toCoeffOn.toCoeffField :=
      Eq.symm h_coeff_field_eq
    -- Use the adapter lemma to relate ResponseJ to Book.Ch02.responseJ
    have h_responseJ_eq (e : Homogenization.Vec d) :
        Homogenization.ResponseJ ((Rinput.cubeAt N (fun _ => (3 : ℝ) ^ N / 2) : Set (Homogenization.Vec d)))
          ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))⁻¹ • e)
          (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) • e) (Rinput.coeffAt N eta) =
        Homogenization.Book.Ch02.responseJ U data.toCoeffOn
          ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))⁻¹ • e)
          (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) • e) := by
      rw [hU_eq]
      -- Now: ResponseJ (U : Set _) ... (coeffAt N eta) = Book.Ch02.responseJ U data.toCoeffOn ...
      -- Use the public/internal response adapter.
      rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ U data.toCoeffOn]
      rw [h_coeff_eq']
    -- Now rewrite h_defect
    have h_defect' := h_defect
    -- The LHS set in h_defect is {t | ∃ e, vecNormSq e = 1 ∧ t = ResponseJ (cubeAt ...) ... (coeffAt N eta)}
    -- We need {t | ∃ e, vecNormSq e = 1 ∧ t = Book.Ch02.responseJ U data.toCoeffOn ...}
    -- These are equal because of hU_eq, h_coeff_eq', and h_responseJ_eq
    have h_set_eq : {t : ℝ | ∃ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 ∧
        t = Homogenization.ResponseJ ((Rinput.cubeAt N (fun _ => (3 : ℝ) ^ N / 2) : Set (Homogenization.Vec d)))
          ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))⁻¹ • e)
          (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) • e) (Rinput.coeffAt N eta)} =
        {t : ℝ | ∃ e : Homogenization.Vec d,
          Homogenization.vecNormSq e = 1 ∧
          t = Homogenization.Book.Ch02.responseJ U data.toCoeffOn
            ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))⁻¹ • e)
            (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) • e)} := by
      ext t
      constructor
      · rintro ⟨e, he_norm, he_eq⟩
        refine ⟨e, he_norm, ?_⟩
        calc
          t = Homogenization.ResponseJ ((Rinput.cubeAt N (fun _ => (3 : ℝ) ^ N / 2) : Set (Homogenization.Vec d)))
              ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))⁻¹ • e)
              (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) • e) (Rinput.coeffAt N eta) := he_eq
          _ = _ := h_responseJ_eq e
      · rintro ⟨e, he_norm, he_eq⟩
        refine ⟨e, he_norm, ?_⟩
        calc
          t = Homogenization.Book.Ch02.responseJ U data.toCoeffOn
              ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))⁻¹ • e)
              (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) • e) := he_eq
          _ = Homogenization.ResponseJ ((Rinput.cubeAt N (fun _ => (3 : ℝ) ^ N / 2) : Set (Homogenization.Vec d)))
              ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N))⁻¹ • e)
              (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) • e) (Rinput.coeffAt N eta) := (h_responseJ_eq e).symm
    rw [← h_set_eq]
    exact h_defect'
  refine ⟨h_first, ?_, h_third⟩
  change affineInverseNeumannResponse hP (aN0 N om) pvec = _
  let r : ℝ := (3 : ℝ) ^ N
  have hr : 0 < r := by
    dsimp [r]
    positivity
  let c0 : Homogenization.Vec d := fun _ => (1 / 2 : ℝ)
  let cN : Homogenization.Vec d := fun _ => r / 2
  let Q0 : Homogenization.TriadicCube d := Homogenization.originCube d 0
  let QN : Homogenization.TriadicCube d :=
    Homogenization.Book.Ch02.dilateCube (N : ℤ) Q0
  have hQdom : Homogenization.IsOpenBoundedConvexDomain
      (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    exact lane2_isOpenBoundedConvexDomain_centeredCube c0 one_pos
  have hQne : (unitNeumannCube d : Set (SpatialCoordinates d)).Nonempty := by
    refine ⟨c0, ?_⟩
    rw [unitNeumannCube, centeredCube_eq_pi]
    intro i hi
    constructor <;> norm_num
  let Dunit : Homogenization.Book.Ch02.Domain d :=
    ⟨(unitNeumannCube d : Set (SpatialCoordinates d)), hQdom, hQne⟩
  let D0 : Homogenization.Book.Ch02.Domain d :=
    Homogenization.Book.Ch02.cubeDomain Q0
  let DN : Homogenization.Book.Ch02.Domain d :=
    Homogenization.Book.Ch02.cubeDomain QN
  have hunit_set : (Dunit : Set (Homogenization.Vec d)) =
      Homogenization.translateSet c0 (D0 : Set (Homogenization.Vec d)) := by
    simpa [Dunit, D0, Q0, c0, unitNeumannCube] using
      (aux_neumann_response_defect_transport_physical_set d 0)
  have hphysical_set : (U : Set (Homogenization.Vec d)) =
      Homogenization.translateSet cN (DN : Set (Homogenization.Vec d)) := by
    have hcube := Rinput.cubeAt_eq N (fun _ => (3 : ℝ)^N / 2) (by positivity)
    rw [hUdef, hcube]
    simpa [D0, DN, QN, cN, r, Q0] using
      (aux_neumann_response_defect_transport_physical_set d N)
  let g : Homogenization.Vec d → ℝ := fun x =>
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * f (r • x)
  let g0 : Homogenization.Vec d → ℝ := fun x =>
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * f (r • (x + c0))
  have hg_cont : Continuous g := by
    dsimp [g]
    refine continuous_const.mul (h_cont_f.comp ?_)
    exact continuous_const.smul continuous_id
  have hg0_cont : Continuous g0 := by
    dsimp [g0]
    refine continuous_const.mul (h_cont_f.comp ?_)
    exact continuous_const.smul (continuous_id.add continuous_const)
  have hg_pos : ∀ x, 0 < g x := by
    intro x
    dsimp [g]
    exact mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))
      (h_pos_f (r • x))
  have hg0_pos : ∀ x, 0 < g0 x := by
    intro x
    dsimp [g0]
    exact mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))
      (h_pos_f (r • (x + c0)))
  obtain ⟨dataUnit⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
      hg_cont hg_pos Dunit
  obtain ⟨data0⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
      hg0_cont hg0_pos D0
  let c0data : Homogenization.Book.Ch02.CoeffOn Dunit :=
    aux_neumann_response_defect_transport_translateCoeffOn D0 Dunit c0 hunit_set
      data0.toCoeffOn
  have hunit_coeff_ae : c0data.AEEq dataUnit.toCoeffOn := by
    filter_upwards [] with x
    ext i j
    dsimp [c0data, aux_neumann_response_defect_transport_translateCoeffOn,
      SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData.toCoeffOn,
      SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField, g, g0, c0]
    have hv : r • ((x + -c0) + c0) = r • x := by
      ext k
      dsimp
      ring
    change Homogenization.scalarMatrix
        ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * f (r • ((x + -c0) + c0))) i j =
      Homogenization.scalarMatrix
        ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * f (r • x)) i j
    rw [hv]
  let bN : Homogenization.Book.Ch02.CoeffOn DN := by
    dsimp [DN, QN]
    exact Homogenization.Book.Ch02.CoeffOn.dilate (N : ℤ) data0.toCoeffOn
  have hdil : Homogenization.Book.Ch02.CoeffOn.IsCubeDilation (N : ℤ)
      data0.toCoeffOn bN := by
    simpa [bN, DN, QN, D0, Q0] using
      (Homogenization.Book.Ch02.CoeffOn.dilate_isCubeDilation
        (N : ℤ) data0.toCoeffOn)
  have hbn : ∀ᵐ y ∂Homogenization.volumeMeasureOn (DN : Set (Homogenization.Vec d)),
      bN.toCoeffField y = Homogenization.scalarMatrix (g0
        (Homogenization.Book.Ch02.undilateVec (N : ℤ) y)) := by
    have h := hdil.coeff_ae_eq
    simpa [DN, QN, bN, D0, Q0,
      SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData.toCoeffOn,
      SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField,
      Homogenization.Book.Ch02.dilateCoeffField] using h
  let cNdata : Homogenization.Book.Ch02.CoeffOn U :=
    aux_neumann_response_defect_transport_translateCoeffOn DN U cN
      hphysical_set bN
  have hphysical_coeff_scaled :
      Homogenization.Book.Ch02.CoeffOn.AEScaled
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ data.toCoeffOn cNdata := by
    let hmpN := Homogenization.measurePreserving_subRight_restrict_translateSet
      (d := d) cN (DN : Set (Homogenization.Vec d))
    have hbn' : ∀ᵐ y ∂Measure.map (fun x : Homogenization.Vec d => x - cN)
          (volume.restrict (Homogenization.translateSet cN (DN : Set (Homogenization.Vec d)))),
        bN.toCoeffField y = Homogenization.scalarMatrix (g0
          (Homogenization.Book.Ch02.undilateVec (N : ℤ) y)) := by
      rw [hmpN.map_eq]
      exact hbn
    have hcomp := MeasureTheory.ae_of_ae_map hmpN.aemeasurable hbn'
    have hcompU : ∀ᵐ x ∂volume.restrict (U : Set (Homogenization.Vec d)),
        bN.toCoeffField (x - cN) = Homogenization.scalarMatrix (g0
          (Homogenization.Book.Ch02.undilateVec (N : ℤ) (x - cN))) := by
      rw [hphysical_set]
      exact hcomp
    filter_upwards [hcompU] with x hx
    change cNdata.toCoeffField x =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ • data.toCoeffOn.toCoeffField x
    dsimp [cNdata, aux_neumann_response_defect_transport_translateCoeffOn,
      data, SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData.toCoeffOn,
      SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField]
    have hfac : Homogenization.Book.Ch02.triadicDilationFactor (N : ℤ) = r := by
      simp [Homogenization.Book.Ch02.triadicDilationFactor, r]
    have hpow : (3 : ℝ) ^ (N : ℤ) = (3 : ℝ) ^ N := by
      simp
    have harg : r •
        (Homogenization.Book.Ch02.undilateVec (N : ℤ) (x - cN) + c0) = x := by
      ext k
      dsimp [Homogenization.Book.Ch02.undilateVec,
        Homogenization.Book.Ch02.triadicDilationFactor, cN, c0, r]
      rw [hpow]
      field_simp [Homogenization.Book.Ch02.triadicDilationFactor_ne_zero]
      ring
    simp only [Homogenization.translateCoeffField]
    change bN.toCoeffField (x - cN) =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ • Homogenization.scalarMatrix (f x)
    rw [hx]
    dsimp [g0]
    rw [harg]
    ext i j
    by_cases hij : i = j <;> simp [Homogenization.scalarMatrix, hij,
      Pi.smul_apply, smul_eq_mul]
  have hentry_scale : ∀ q : Homogenization.Vec d,
      Homogenization.Book.Ch02.responseJ U cNdata 0 q =
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Homogenization.Book.Ch02.responseJ U data.toCoeffOn 0 q := by
    intro q
    have hscale :=
      (Homogenization.Book.Ch02.responseSubadditivityAndScalingTheory U
        data.toCoeffOn).responseJ_homogeneous
        (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))
        hphysical_coeff_scaled 0 q
    have hquad :
        Homogenization.Book.Ch02.responseJ U data.toCoeffOn
            ((Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹))⁻¹ •
              (0 : Homogenization.Vec d))
            ((Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹))⁻¹ • q) =
          (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹))⁻¹ ^ 2 *
            Homogenization.Book.Ch02.responseJ U data.toCoeffOn 0 q :=
      Homogenization.Book.Ch02.responseJ_smul
        (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹))⁻¹
        (0 : Homogenization.Vec d) q
    have hsq : (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹))⁻¹ ^ 2 =
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := by
      rw [inv_pow, Real.sq_sqrt]
      · simp
      · exact (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)).le
    simp only [smul_zero] at hscale hquad
    calc
      Homogenization.Book.Ch02.responseJ U cNdata 0 q =
          Homogenization.Book.Ch02.responseJ U data.toCoeffOn 0
            ((Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹))⁻¹ • q) := hscale
      _ = (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹))⁻¹ ^ 2 *
          Homogenization.Book.Ch02.responseJ U data.toCoeffOn 0 q := hquad
      _ = _ := by rw [hsq]
  have hmat_scale :
      Homogenization.Book.Ch02.sigmaStarInvCoarse U cNdata =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) •
          Homogenization.Book.Ch02.sigmaStarInvCoarse U data.toCoeffOn := by
    ext i j
    by_cases hij : i = j
    · simp [Homogenization.Book.Ch02.sigmaStarInvCoarse,
        Homogenization.Book.Ch02.sigmaStarInvEntry, hij, hentry_scale,
        Pi.smul_apply, smul_eq_mul]
      ring
    · simp [Homogenization.Book.Ch02.sigmaStarInvCoarse,
        Homogenization.Book.Ch02.sigmaStarInvEntry, hij, hentry_scale,
        Pi.smul_apply, smul_eq_mul]
      ring
  have haP : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      (aN0 N om).val x = g x := by
    filter_upwards [h_first] with x hx
    simpa [g, r] using hx
  have hvol_unit : 0 < volume.real (Q : Set (SpatialCoordinates d)) := by
    dsimp [Q, unitNeumannCube, c0]
    exact centeredCube_volume_pos _ one_pos
  have hvol_unit_eq : volume.real (Q : Set (SpatialCoordinates d)) = 1 := by
    rw [show Q = unitNeumannCube d by rfl, unitNeumannCube,
      centeredCube_volume_real]
    simp
  have hbridge :=
    SubdiffusiveProcess.Lane4.symmetricNeumannNu_eq_affineInverseNeumannResponse
      hQdom hQne dataUnit hP (aN0 N om) haP hvol_unit pvec
  have hbridge' := hbridge
  field_simp [ne_of_gt hvol_unit] at hbridge'
  have htheory :=
    Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory
      Dunit dataUnit.toCoeffOn dataUnit.isSymmetric
  have hneu := htheory.neumann_value_by_sigmaStarInv pvec
  have h_unit_response :
      affineInverseNeumannResponse hP (aN0 N om) pvec =
        Homogenization.vecDot pvec
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaStarInvCoarse Dunit
              dataUnit.toCoeffOn) pvec) := by
    calc
      affineInverseNeumannResponse hP (aN0 N om) pvec =
          2 * Homogenization.Book.Ch02.symmetricNeumannNu Dunit
            dataUnit.toCoeffOn pvec := by
        rw [hvol_unit_eq] at hbridge'
        linarith
      _ = Homogenization.vecDot pvec
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaStarInvCoarse Dunit
              dataUnit.toCoeffOn) pvec) := by
        rw [hneu]
        ring
  have hmat_unit :
      Homogenization.Book.Ch02.sigmaStarInvCoarse Dunit dataUnit.toCoeffOn =
        Homogenization.Book.Ch02.sigmaStarInvCoarse D0 data0.toCoeffOn := by
    calc
      Homogenization.Book.Ch02.sigmaStarInvCoarse Dunit dataUnit.toCoeffOn =
          Homogenization.Book.Ch02.sigmaStarInvCoarse Dunit c0data := by
        exact (Homogenization.Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq
          hunit_coeff_ae).symm
      _ = Homogenization.Book.Ch02.sigmaStarInvCoarse D0 data0.toCoeffOn := by
        simpa [c0data] using
          (aux_neumann_response_defect_transport_sigma_translate
            D0 Dunit c0 hunit_set data0.toCoeffOn)
  have hmat_dil :
      Homogenization.Book.Ch02.sigmaStarInvCoarse DN bN =
        Homogenization.Book.Ch02.sigmaStarInvCoarse D0 data0.toCoeffOn := by
    simpa [DN, QN, D0, Q0, bN] using
      (Homogenization.Book.Ch02.sigmaStarInvCoarse_dilate hdil)
  have hmat_phys :
      Homogenization.Book.Ch02.sigmaStarInvCoarse U cNdata =
        Homogenization.Book.Ch02.sigmaStarInvCoarse DN bN := by
    simpa [cNdata] using
      (aux_neumann_response_defect_transport_sigma_translate
        DN U cN hphysical_set bN)
  have hmat_unit_phys :
      Homogenization.Book.Ch02.sigmaStarInvCoarse Dunit dataUnit.toCoeffOn =
        Homogenization.Book.Ch02.sigmaStarInvCoarse U cNdata := by
    calc
      Homogenization.Book.Ch02.sigmaStarInvCoarse Dunit dataUnit.toCoeffOn =
          Homogenization.Book.Ch02.sigmaStarInvCoarse D0 data0.toCoeffOn := hmat_unit
      _ = Homogenization.Book.Ch02.sigmaStarInvCoarse DN bN := hmat_dil.symm
      _ = Homogenization.Book.Ch02.sigmaStarInvCoarse U cNdata := hmat_phys.symm
  have hmatrix :
      Homogenization.Book.Ch02.sigmaStarInvCoarse Dunit dataUnit.toCoeffOn =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) •
          Homogenization.Book.Ch02.sigmaStarInvCoarse U data.toCoeffOn := by
    calc
      Homogenization.Book.Ch02.sigmaStarInvCoarse Dunit dataUnit.toCoeffOn =
          Homogenization.Book.Ch02.sigmaStarInvCoarse U cNdata := hmat_unit_phys
      _ = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) •
          Homogenization.Book.Ch02.sigmaStarInvCoarse U data.toCoeffOn := hmat_scale
  calc
    affineInverseNeumannResponse hP (aN0 N om) pvec =
        Homogenization.vecDot pvec
          (Homogenization.matVecMul
            (Homogenization.Book.Ch02.sigmaStarInvCoarse Dunit
              dataUnit.toCoeffOn) pvec) := h_unit_response
    _ = Homogenization.vecDot pvec
          (Homogenization.matVecMul
            ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) •
              Homogenization.Book.Ch02.sigmaStarInvCoarse U data.toCoeffOn)
            pvec) := by rw [hmatrix]
    _ = SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Homogenization.vecDot pvec
            (Homogenization.matVecMul
              (Homogenization.Book.Ch02.sigmaStarInvCoarse U data.toCoeffOn)
              pvec) := by
      rw [Homogenization.smul_matVecMul, Homogenization.vecDot_smul_right]


end Paper
