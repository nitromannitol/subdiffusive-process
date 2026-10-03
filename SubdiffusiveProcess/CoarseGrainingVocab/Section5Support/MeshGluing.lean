module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteDirichletInfimum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Homogenization.Book Kuhn MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The glued `H_0^1` function -/



theorem exists_h10Function_grad_eq_sum_indicator {ι : Type*} [DecidableEq ι]
    {U : Set (Vec d)} (hU : IsOpen U) (S : Finset ι) {V : ι → Set (Vec d)}
    (hVmeas : ∀ i, MeasurableSet (V i)) (hVU : ∀ i, V i ⊆ U)
    (w : (i : ι) → H10Function (V i)) :
    ∃ W : H10Function U, ∀ x : Vec d,
      W.toH1Function.grad x =
        ∑ i ∈ S, Set.indicator (V i) (fun y => (w i).toH1Function.grad y) x := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, fun x => by simp; rfl⟩
  | insert i S hi ih =>
      obtain ⟨W, hW⟩ := ih
      refine ⟨W + (w i).extendByZeroToOpenSuperset (hVmeas i) hU (hVU i), fun x => ?_⟩
      have hgrad :
          (W + (w i).extendByZeroToOpenSuperset (hVmeas i) hU (hVU i)).toH1Function.grad x
            = W.toH1Function.grad x +
                ((w i).extendByZeroToOpenSuperset (hVmeas i) hU (hVU i)).toH1Function.grad x :=
        congrFun (H1Function.add_grad _ _) x
      rw [hgrad, hW x, Finset.sum_insert hi,
        H10Function.extendByZeroToOpenSuperset_grad, add_comm]
      rfl

/-- On the interior of one cell of an equal-scale mesh the glued gradient is
that cell's gradient: the other indicators vanish there. -/
theorem sum_indicator_grad_eq_of_mem_openCarrier {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} {s : ℤ} (hscale : ∀ T ∈ S, T.supportCube.scale = s)
    {G : KuhnCell d → Vec d → Vec d} {T₀ : KuhnCell d} (hT₀ : T₀ ∈ S)
    {x : Vec d} (hx : x ∈ U ∩ T₀.openCarrier) :
    ∑ T ∈ S, Set.indicator (U ∩ T.openCarrier) (fun y => G T y) x = G T₀ x := by
  classical
  refine (Finset.sum_eq_single T₀ ?_ (fun h => absurd hT₀ h)).trans
    (Set.indicator_of_mem hx _)
  intro T hT hTne
  refine Set.indicator_of_notMem (fun hmem => ?_) _
  have hdisj : Disjoint T.openCarrier T₀.openCarrier :=
    disjoint_openCarrier_of_supportCube_scale_eq
      ((hscale T hT).trans (hscale T₀ hT₀).symm) hTne
  exact Set.disjoint_left.mp hdisj hmem.2 hx.2

/-! ## Boundedness of a continuous field on a bounded set -/

/-- A continuous field is bounded on every bounded set. -/
theorem exists_bound_of_continuous_of_isBounded {B : Vec d → ℝ} (hB : Continuous B)
    {U : Set (Vec d)} (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, ∀ x ∈ U, ‖B x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hUb.isCompact_closure.image_of_continuousOn
    hB.continuousOn).isBounded.subset_closedBall 0
  refine ⟨C, fun x hx => ?_⟩
  have := hC (Set.mem_image_of_mem B (subset_closure hx))
  simpa [Real.norm_eq_abs, Real.dist_eq] using this

/-! ## The deterministic core of Step 3 -/



theorem dirichletInfOn_mul_le_sum_cellSup_dirichletInfOn
    {A B : Vec d → ℝ} {S : Finset (KuhnCell d)} {U : Set (Vec d)} {s : ℤ} {p : Vec d}
    (hUopen : IsOpen U) (hUb : Bornology.IsBounded U)
    (hA : Continuous A) (hA0 : ∀ x, 0 ≤ A x) (hB : Continuous B)
    (hB0 : ∀ x, 0 ≤ B x) (hscale : ∀ T ∈ S, T.supportCube.scale = s)
    (hcover : U ⊆ ⋃ T ∈ (S : Set (KuhnCell d)), T.carrier)
    (c : KuhnCompetitor U S)
    (hmin : ∀ T ∈ S, ∃ w : H10Function (U ∩ T.openCarrier),
      dirichletEnergyOn' A (U ∩ T.openCarrier) (p + c.slope T) w.toH1Function.grad =
        dirichletInfOn A (U ∩ T.openCarrier) (p + c.slope T)) :
    dirichletInfOn (fun x => B x * A x) U p ≤
      ∑ T ∈ S, cellSup B T * dirichletInfOn A (U ∩ T.openCarrier) (p + c.slope T) := by
  classical
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  haveI : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hUb.measure_lt_top⟩
  have hcellmeas : ∀ T : KuhnCell d, MeasurableSet (U ∩ T.openCarrier) := fun T =>
    hUmeas.inter (isOpen_openCarrier T).measurableSet
  -- the per-cell minimizers, as a total family
  have hmin' : ∀ T : KuhnCell d, ∃ w : H10Function (U ∩ T.openCarrier), T ∈ S →
      dirichletEnergyOn' A (U ∩ T.openCarrier) (p + c.slope T) w.toH1Function.grad =
        dirichletInfOn A (U ∩ T.openCarrier) (p + c.slope T) := by
    intro T
    by_cases hT : T ∈ S
    · obtain ⟨w, hwT⟩ := hmin T hT
      exact ⟨w, fun _ => hwT⟩
    · exact ⟨0, fun h => absurd h hT⟩
  choose w hw using hmin'
  -- the glued correction
  obtain ⟨W, hW⟩ :=
    exists_h10Function_grad_eq_sum_indicator (U := U) (V := fun T => U ∩ T.openCarrier)
      hUopen S hcellmeas (fun _ => Set.inter_subset_left) w
  have hWtot : ∀ x : Vec d,
      (c.toH10Function + W).toH1Function.grad x = c.grad x + W.toH1Function.grad x :=
    fun x => congrFun (H1Function.add_grad _ _) x
  -- integrability of the glued energy
  have hnorm : IntegrableOn
      (fun x => vecNormSq (p + (c.toH10Function + W).toH1Function.grad x)) U volume :=
    integrableOn_vecNormSq_add_grad (c.toH10Function + W).toH1Function p
  obtain ⟨C, hC⟩ := exists_bound_of_continuous_of_isBounded (hB.mul hA) hUb
  have hint : IntegrableOn
      (fun x => B x * A x * vecNormSq (p + (c.toH10Function + W).toH1Function.grad x))
      U volume :=
    integrableOn_mul_of_integrableOn_vecNormSq hUmeas (hB.mul hA).measurable hC hnorm
  -- the termwise estimate
  have hterm : ∀ T ∈ S,
      (∫ x in U ∩ T.openCarrier,
        B x * A x * vecNormSq (p + (c.toH10Function + W).toH1Function.grad x)) ≤
      cellSup B T * dirichletInfOn A (U ∩ T.openCarrier) (p + c.slope T) := by
    intro T hT
    haveI : IsFiniteMeasure (volume.restrict (U ∩ T.openCarrier)) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) hUb.measure_lt_top⟩
    have hnormT : IntegrableOn
        (fun x => vecNormSq (p + c.slope T + (w T).toH1Function.grad x))
        (U ∩ T.openCarrier) volume :=
      integrableOn_vecNormSq_add_grad (w T).toH1Function (p + c.slope T)
    obtain ⟨CA, hCA⟩ :=
      exists_bound_of_continuous_of_isBounded hA (hUb.subset Set.inter_subset_left)
    have hintT : IntegrableOn
        (fun x => A x * vecNormSq (p + c.slope T + (w T).toH1Function.grad x))
        (U ∩ T.openCarrier) volume :=
      integrableOn_mul_of_integrableOn_vecNormSq (hcellmeas T) hA.measurable hCA hnormT
    have hae : ∀ᵐ x ∂(volume.restrict (U ∩ T.openCarrier)),
        B x * A x * vecNormSq (p + (c.toH10Function + W).toH1Function.grad x) =
          B x * (A x * vecNormSq (p + c.slope T + (w T).toH1Function.grad x)) := by
      filter_upwards [c.grad_ae_eq_slope hT, ae_restrict_mem (hcellmeas T)] with x hx hxmem
      rw [hWtot x, hx, hW x, sum_indicator_grad_eq_of_mem_openCarrier hscale hT hxmem,
        ← add_assoc, mul_assoc]
    rw [integral_congr_ae hae]
    calc (∫ x in U ∩ T.openCarrier,
            B x * (A x * vecNormSq (p + c.slope T + (w T).toH1Function.grad x)))
        ≤ ∫ x in U ∩ T.openCarrier,
            cellSup B T * (A x * vecNormSq (p + c.slope T + (w T).toH1Function.grad x)) := by
          refine integral_mono_ae ((hint.mono_set Set.inter_subset_left).congr hae)
            (hintT.const_mul _) ?_
          filter_upwards [ae_restrict_mem (hcellmeas T)] with x hxmem
          refine mul_le_mul_of_nonneg_right
            (le_cellSup T hB.continuousOn
              (T.openCarrier_subset_closedCarrier hxmem.2)) ?_
          exact mul_nonneg (hA0 x) (vecNormSq_nonneg _)
      _ = cellSup B T * dirichletEnergyOn' A (U ∩ T.openCarrier) (p + c.slope T)
            (w T).toH1Function.grad := integral_const_mul _ _
      _ = cellSup B T * dirichletInfOn A (U ∩ T.openCarrier) (p + c.slope T) := by
          rw [hw T hT]
  calc dirichletInfOn (fun x => B x * A x) U p
      ≤ dirichletEnergyOn' (fun x => B x * A x) U p
          (c.toH10Function + W).toH1Function.grad :=
        dirichletInfOn_le hUmeas (fun x => mul_nonneg (hB0 x) (hA0 x))
          (c.toH10Function + W)
    _ = ∑ T ∈ S, ∫ x in U ∩ T.openCarrier,
          B x * A x * vecNormSq (p + (c.toH10Function + W).toH1Function.grad x) :=
        setIntegral_eq_sum_openCarrier hUmeas hscale hcover hint
    _ ≤ ∑ T ∈ S, cellSup B T * dirichletInfOn A (U ∩ T.openCarrier) (p + c.slope T) :=
        Finset.sum_le_sum hterm

/-! ## The same inequality between finite-volume matrices -/



theorem vecDot_aMatrix_le_sum_cellSup_vecDot_aMatrix
    {A B : Vec d → ℝ} {S : Finset (KuhnCell d)} {s : ℤ} {p : Vec d}
    {U : Ch02.Domain d} {V : KuhnCell d → Ch02.Domain d}
    (hA : Continuous A) (hA0 : ∀ x, 0 ≤ A x) (hB : Continuous B)
    (hB0 : ∀ x, 0 ≤ B x) (hscale : ∀ T ∈ S, T.supportCube.scale = s)
    (hVeq : ∀ T ∈ S, (V T : Set (Vec d)) = T.openCarrier)
    (hsub : ∀ T ∈ S, T.openCarrier ⊆ (U : Set (Vec d)))
    (hcover : (U : Set (Vec d)) ⊆ ⋃ T ∈ (S : Set (KuhnCell d)), T.carrier)
    (c : KuhnCompetitor (U : Set (Vec d)) S)
    (hBA : ScalarCoeffOnData U (fun x => B x * A x))
    (hAV : ∀ T : KuhnCell d, ScalarCoeffOnData (V T) A) :
    vecDot p (matVecMul (aMatrix U hBA.toCoeffOn) p) ≤
      ∑ T ∈ S,
        (volume (V T : Set (Vec d))).toReal / (volume (U : Set (Vec d))).toReal *
          (cellSup B T *
            vecDot (p + c.slope T)
              (matVecMul (aMatrix (V T) (hAV T).toCoeffOn) (p + c.slope T))) := by
  have hUpos : 0 < (volume (U : Set (Vec d))).toReal := volume_toReal_pos U
  -- the per-cell minimizers, transported to the intersection form
  have hmin : ∀ T ∈ S, ∃ w : H10Function ((U : Set (Vec d)) ∩ T.openCarrier),
      dirichletEnergyOn' A ((U : Set (Vec d)) ∩ T.openCarrier) (p + c.slope T)
          w.toH1Function.grad =
        dirichletInfOn A ((U : Set (Vec d)) ∩ T.openCarrier) (p + c.slope T) := by
    intro T hT
    have hset : (U : Set (Vec d)) ∩ T.openCarrier = (V T : Set (Vec d)) := by
      rw [hVeq T hT, Set.inter_eq_self_of_subset_right (hsub T hT)]
    rw [hset]
    exact exists_h10Function_dirichletEnergyOn'_eq_dirichletInfOn (hAV T) hA0 (p + c.slope T)
  have hmain := dirichletInfOn_mul_le_sum_cellSup_dirichletInfOn (A := A) (B := B)
    (S := S) (U := (U : Set (Vec d))) (s := s) (p := p) U.isOpen
    U.isDomain.isBoundedDomain.isBounded hA hA0 hB hB0 hscale hcover c hmin
  -- rewrite both sides through the matrix identity
  rw [vecDot_aMatrix_eq_dirichletInfOn hBA (fun x => mul_nonneg (hB0 x) (hA0 x)) p]
  have hsum : ∑ T ∈ S, cellSup B T *
        dirichletInfOn A ((U : Set (Vec d)) ∩ T.openCarrier) (p + c.slope T) =
      ∑ T ∈ S, (volume (V T : Set (Vec d))).toReal *
        (cellSup B T * vecDot (p + c.slope T)
          (matVecMul (aMatrix (V T) (hAV T).toCoeffOn) (p + c.slope T))) := by
    refine Finset.sum_congr rfl fun T hT => ?_
    have hset : (U : Set (Vec d)) ∩ T.openCarrier = (V T : Set (Vec d)) := by
      rw [hVeq T hT, Set.inter_eq_self_of_subset_right (hsub T hT)]
    have hVpos : (volume (V T : Set (Vec d))).toReal ≠ 0 := ne_of_gt (volume_toReal_pos (V T))
    rw [hset, vecDot_aMatrix_eq_dirichletInfOn (hAV T) hA0 (p + c.slope T)]
    field_simp
  rw [hsum] at hmain
  have hdiv : ∑ T ∈ S,
      (volume (V T : Set (Vec d))).toReal / (volume (U : Set (Vec d))).toReal *
        (cellSup B T * vecDot (p + c.slope T)
          (matVecMul (aMatrix (V T) (hAV T).toCoeffOn) (p + c.slope T))) =
      (volume (U : Set (Vec d))).toReal⁻¹ *
        ∑ T ∈ S, (volume (V T : Set (Vec d))).toReal *
          (cellSup B T * vecDot (p + c.slope T)
            (matVecMul (aMatrix (V T) (hAV T).toCoeffOn) (p + c.slope T))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [hdiv]
  exact mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hUpos.le)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
