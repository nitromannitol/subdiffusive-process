module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseFubini
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ContinuumSelection
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.PartitionInterchange
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerInduction

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Homogenization.Book Kuhn MeasureTheory ProbabilityTheory Set
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The pointwise conditioning with a sparse-block weight -/

theorem layerCoefficient_range_eq (M : GMCModel d) {R : ℕ} (hR : 0 < R) (N : ℕ)
    (omega : PotentialSample d) (x : Vec d) :
    layerCoefficient M (Finset.range (N * R + 1)) omega x =
      layerCoefficient M (sparseLayerIndices R N) omega x *
        layerCoefficient M (complementLayerIndices R (N * R)) omega x := by
  have hdiv : (N * R) / R = N := Nat.mul_div_cancel _ hR
  have hunion := sparse_union_complement hR (N * R)
  have hd := disjoint_sparse_complement hR (N * R)
  rw [hdiv] at hunion hd
  rw [← hunion, layerCoefficient_union M hd omega x]

theorem disjoint_sparse_complement_set {R : ℕ} (hR : 0 < R) (N : ℕ) :
    Disjoint ((sparseLayerIndices R N : Finset ℕ) : Set ℕ)
      ((complementLayerIndices R (N * R) : Finset ℕ) : Set ℕ) := by
  have hdiv : (N * R) / R = N := Nat.mul_div_cancel _ hR
  have hd := disjoint_sparse_complement hR (N * R)
  rw [hdiv] at hd
  exact Finset.disjoint_coe.mpr hd



theorem integral_mul_layerCoefficient_range_eq (M : GMCModel d) {R : ℕ} (hR : 0 < R)
    (N : ℕ) {G : PotentialSample d → ℝ}
    (hGsigma : Measurable[potentialIndexSigma (d := d)
      ((sparseLayerIndices R N : Finset ℕ) : Set ℕ)] G) (x : Vec d) :
    ∫ omega, G omega * layerCoefficient M (Finset.range (N * R + 1)) omega x
        ∂M.P.toMeasure =
      ∫ omega, G omega * layerCoefficient M (sparseLayerIndices R N) omega x
        ∂M.P.toMeasure := by
  have hF : Measurable[potentialIndexSigma (d := d)
      ((sparseLayerIndices R N : Finset ℕ) : Set ℕ)]
      fun omega : PotentialSample d =>
        G omega * layerCoefficient M (sparseLayerIndices R N) omega x :=
    hGsigma.mul (measurable_layerCoefficient_apply_potentialIndexSigma M _ x)
  have hCsigma : Measurable[potentialIndexSigma (d := d)
      ((complementLayerIndices R (N * R) : Finset ℕ) : Set ℕ)]
      fun omega : PotentialSample d =>
        complementLayerCoefficient M R (N * R) omega x :=
    measurable_layerCoefficient_apply_potentialIndexSigma M _ x
  have hindep := indepFun_of_potentialIndexSigma_disjoint M
    (disjoint_sparse_complement_set hR N) hF hCsigma
  have hFmeas : Measurable fun omega : PotentialSample d =>
      G omega * layerCoefficient M (sparseLayerIndices R N) omega x :=
    hF.mono (potentialIndexSigma_le_borel _) le_rfl
  have h := integral_mul_complementLayerCoefficient_apply M R (N * R) x
    hFmeas.aestronglyMeasurable hindep
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  show G omega * layerCoefficient M (Finset.range (N * R + 1)) omega x =
    G omega * layerCoefficient M (sparseLayerIndices R N) omega x *
      layerCoefficient M (complementLayerIndices R (N * R)) omega x
  rw [layerCoefficient_range_eq M hR N omega x]
  ring

/-! ## A measurable nonnegative representative of the weight -/

theorem exists_measurable_repr {φ : Vec d → ℝ} {U : Set (Vec d)}
    (hφ : IntegrableOn φ U volume) (hφ0 : ∀ x, 0 ≤ φ x) :
    ∃ φ' : Vec d → ℝ, Measurable φ' ∧ (∀ x, 0 ≤ φ' x) ∧
      φ' =ᵐ[volume.restrict U] φ ∧ IntegrableOn φ' U volume := by
  obtain ⟨ψ, hψmeas, hψae⟩ := hφ.aestronglyMeasurable
  refine ⟨fun x => max (ψ x) 0, hψmeas.measurable.max measurable_const,
    fun x => le_max_right _ _, ?_, ?_⟩
  · filter_upwards [hψae] with x hx
    have h0 : 0 ≤ ψ x := hx ▸ hφ0 x
    rw [max_eq_left h0]
    exact hx.symm
  · refine hφ.congr ?_
    filter_upwards [hψae] with x hx
    have h0 : 0 ≤ ψ x := hx ▸ hφ0 x
    rw [hx, max_eq_left h0]

/-! ## The comparison -/

/-- **`e.strict.decay.full.sparse.comparison`.**  On every open bounded convex
domain inside a triadic cube, the expected quadratic form of the full cutoff at
a sparse index is at most that of the sparse coefficient. -/
theorem integral_dirichletInfOn_aCutoff_le {n0 : ℕ} (M : GMCModel (n0 + 1))
    {R : ℕ} (hR : 0 < R) (N : ℕ) {Q : TriadicCube (n0 + 1)}
    {U : Set (Vec (n0 + 1))} (hU : IsOpenBoundedConvexDomain U)
    (hUQ : U ⊆ openCubeSet Q) (p : Vec (n0 + 1)) :
    ∫ omega, dirichletInfOn (layerCoefficient M (Finset.range (N * R + 1)) omega)
        U p ∂M.P.toMeasure ≤
      ∫ omega, dirichletInfOn (layerCoefficient M (sparseLayerIndices R N) omega)
        U p ∂M.P.toMeasure := by
  classical
  have hUmeas : MeasurableSet U := hU.isOpen.measurableSet
  have hUb : Bornology.IsBounded U := hU.isBoundedDomain.isBounded
  haveI : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hU.isBoundedDomain.volume_lt_top⟩
  -- the two coefficient families
  set Sfull : Finset ℕ := Finset.range (N * R + 1) with hSfull
  set Ssp : Finset ℕ := sparseLayerIndices R N with hSsp
  -- integrability of the two continuum minima
  have hinf_int : ∀ T : Finset ℕ, Integrable (fun omega : PotentialSample (n0 + 1) =>
      dirichletInfOn (layerCoefficient M T omega) U p) M.P.toMeasure := by
    intro T
    have hmeas : Measurable fun omega : PotentialSample (n0 + 1) =>
        dirichletInfOn (layerCoefficient M T omega) U p :=
      measurable_dirichletInfOn_of_measurable_apply hU hUQ
        (fun omega => continuous_layerCoefficient M T omega)
        (fun omega x => (layerCoefficient_pos M T omega x).le)
        (fun y => measurable_layerCoefficient_apply M T y) p
    have hdom : Integrable (fun omega : PotentialSample (n0 + 1) =>
        (∫ x in U, layerCoefficient M T omega x) * vecNormSq p) M.P.toMeasure :=
      (integrable_setIntegral_layerCoefficient M T hUmeas hUb).mul_const _
    refine hdom.mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (dirichletInfOn_nonneg hUmeas
      fun x => (layerCoefficient_pos M T omega x).le)]
    have h := dirichletInfOn_le_affine (B := layerCoefficient M T omega) (U := U)
      (p := p) hUmeas fun x => (layerCoefficient_pos M T omega x).le
    rwa [integral_mul_const] at h
  refine le_of_forall_pos_le_add fun eps heps => ?_
  -- the countable family of competitors
  obtain ⟨S, q, w, hbound, hopt⟩ :=
    exists_countable_optimal_kuhnCompetitors hU hUQ p
  -- the selection, measurable for the sparse block
  set Pred : PotentialSample (n0 + 1) → ℕ → Prop := fun omega i =>
    kuhnDiscreteEnergy (layerCoefficient M Ssp omega) (S i) U p (q i) <
      dirichletInfOn (layerCoefficient M Ssp omega) U p + eps with hPred
  have hex : ∀ omega, ∃ i, Pred omega i := fun omega =>
    hopt (layerCoefficient M Ssp omega)
      (continuous_layerCoefficient M Ssp omega)
      (fun x => (layerCoefficient_pos M Ssp omega x).le) eps heps
  have hmeasSet : ∀ i, MeasurableSet[potentialIndexSigma (d := n0 + 1)
      ((Ssp : Finset ℕ) : Set ℕ)] {omega | Pred omega i} := by
    intro i
    refine measurableSet_lt ?_ ?_
    · exact @measurable_kuhnDiscreteEnergy (n0 + 1) (PotentialSample (n0 + 1))
        (potentialIndexSigma ((Ssp : Finset ℕ) : Set ℕ))
        (fun omega => layerCoefficient M Ssp omega) (S i) U p (q i)
        (fun T _ => measurable_cellSup_layerCoefficient_potentialIndexSigma M Ssp T)
    · exact (measurable_dirichletInfOn_layerCoefficient_indexSigma M Ssp hU hUQ
        p).add_const eps
  set n : PotentialSample (n0 + 1) → ℕ := fun omega => Nat.find (hex omega) with hn
  have hnsigma : Measurable[potentialIndexSigma (d := n0 + 1)
      ((Ssp : Finset ℕ) : Set ℕ)] n := measurable_find hex hmeasSet
  have hnmeas : Measurable n := hnsigma.mono (potentialIndexSigma_le_borel _) le_rfl
  have hnspec : ∀ omega, Pred omega (n omega) := fun omega => Nat.find_spec (hex omega)
  -- the fibrewise comparison
  have hfiber : ∀ m : ℕ,
      ∫ omega in {omega | n omega = m},
          dirichletInfOn (layerCoefficient M Sfull omega) U p ∂M.P.toMeasure ≤
        ∫ omega in {omega | n omega = m},
          (dirichletInfOn (layerCoefficient M Ssp omega) U p + eps)
            ∂M.P.toMeasure := by
    intro m
    have hFmeas : MeasurableSet {omega : PotentialSample (n0 + 1) | n omega = m} :=
      measurableSet_index_fiber hnmeas m
    -- the measurable nonnegative weight
    obtain ⟨φ, hφmeas, hφ0, hφae, hφint⟩ := exists_measurable_repr
      (integrableOn_vecNormSq_add_grad (w m).toH1Function p)
      (fun x => vecNormSq_nonneg _)
    have henergy : ∀ (T : Finset ℕ) (omega : PotentialSample (n0 + 1)),
        dirichletEnergyOn' (layerCoefficient M T omega) U p
            (w m).toH1Function.grad =
          ∫ x in U, layerCoefficient M T omega x * φ x := by
      intro T omega
      refine integral_congr_ae ?_
      filter_upwards [hφae] with x hx
      rw [hx]
    -- the fibre weight
    set G : PotentialSample (n0 + 1) → ℝ :=
      Set.indicator {omega | n omega = m} (fun _ => (1 : ℝ)) with hG
    have hG0 : ∀ omega, 0 ≤ G omega := fun omega =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) omega
    have hG1 : ∀ omega, G omega ≤ 1 := by
      intro omega
      by_cases homega : omega ∈ {omega : PotentialSample (n0 + 1) | n omega = m} <;>
        simp [hG, Set.indicator_of_mem, Set.indicator_of_notMem, homega]
    have hGmeas : Measurable G :=
      (measurable_const : Measurable fun _ : PotentialSample (n0 + 1) => (1 : ℝ)).indicator
        hFmeas
    have hGsigma : Measurable[potentialIndexSigma (d := n0 + 1)
        ((Ssp : Finset ℕ) : Set ℕ)] G :=
      (measurable_const : Measurable[potentialIndexSigma (d := n0 + 1)
        ((Ssp : Finset ℕ) : Set ℕ)] fun _ : PotentialSample (n0 + 1) => (1 : ℝ)).indicator
        (hnsigma (measurableSet_singleton m))
    have hsetG : ∀ (f : PotentialSample (n0 + 1) → ℝ),
        ∫ omega in {omega | n omega = m}, f omega ∂M.P.toMeasure =
          ∫ omega, G omega * f omega ∂M.P.toMeasure := by
      intro f
      rw [← integral_indicator hFmeas]
      refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
      by_cases homega : omega ∈ {omega : PotentialSample (n0 + 1) | n omega = m} <;>
        simp [hG, Set.indicator_of_mem, Set.indicator_of_notMem, homega]
    -- the Fubini exchange, on both coefficient families
    have hswap : ∀ T : Finset ℕ,
        ∫ omega, G omega * (∫ x in U, layerCoefficient M T omega x * φ x)
            ∂M.P.toMeasure =
          ∫ x in U, (∫ omega, G omega * layerCoefficient M T omega x
            ∂M.P.toMeasure) * φ x := fun T =>
      (integral_mul_setIntegral_layerCoefficient M T hGmeas hG0 hG1 hφmeas hφ0
        hUmeas hUb hφint).1
    have hcond : ∫ omega, G omega *
          (∫ x in U, layerCoefficient M Sfull omega x * φ x) ∂M.P.toMeasure =
        ∫ omega, G omega *
          (∫ x in U, layerCoefficient M Ssp omega x * φ x) ∂M.P.toMeasure := by
      rw [hswap Sfull, hswap Ssp]
      refine setIntegral_congr_fun hUmeas fun x _ => ?_
      rw [integral_mul_layerCoefficient_range_eq M hR N hGsigma x]
    -- integrability of the two energies
    have henint : ∀ T : Finset ℕ,
        Integrable (fun omega : PotentialSample (n0 + 1) =>
          ∫ x in U, layerCoefficient M T omega x * φ x) M.P.toMeasure := by
      intro T
      exact integrable_setIntegral_layerCoefficient_mul M T hφmeas hφ0 hUmeas hUb hφint
    calc ∫ omega in {omega | n omega = m},
            dirichletInfOn (layerCoefficient M Sfull omega) U p ∂M.P.toMeasure
        ≤ ∫ omega in {omega | n omega = m},
            dirichletEnergyOn' (layerCoefficient M Sfull omega) U p
              (w m).toH1Function.grad ∂M.P.toMeasure := by
          refine setIntegral_mono_on (hinf_int Sfull).integrableOn ?_ hFmeas
            fun omega _ => ?_
          · simp only [henergy Sfull]
            exact (henint Sfull).integrableOn
          · exact dirichletInfOn_le hUmeas
              (fun x => (layerCoefficient_pos M Sfull omega x).le) (w m)
      _ = ∫ omega, G omega * (∫ x in U, layerCoefficient M Sfull omega x * φ x)
            ∂M.P.toMeasure := by
          rw [← hsetG]
          refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
          exact henergy Sfull omega
      _ = ∫ omega, G omega * (∫ x in U, layerCoefficient M Ssp omega x * φ x)
            ∂M.P.toMeasure := hcond
      _ = ∫ omega in {omega | n omega = m},
            dirichletEnergyOn' (layerCoefficient M Ssp omega) U p
              (w m).toH1Function.grad ∂M.P.toMeasure := by
          rw [← hsetG]
          refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
          exact (henergy Ssp omega).symm
      _ ≤ ∫ omega in {omega | n omega = m},
            (dirichletInfOn (layerCoefficient M Ssp omega) U p + eps)
              ∂M.P.toMeasure := by
          refine setIntegral_mono_on ?_
            (((hinf_int Ssp).add (integrable_const eps)).integrableOn)
            hFmeas fun omega homega => ?_
          · simp only [henergy Ssp]
            exact (henint Ssp).integrableOn
          · have hmem : n omega = m := homega
            have hstep1 := hbound m (layerCoefficient M Ssp omega)
              (continuous_layerCoefficient M Ssp omega)
            have hstep2 := hnspec omega
            rw [hmem] at hstep2
            exact le_of_lt (lt_of_le_of_lt hstep1 hstep2)
  have hint2 : Integrable (fun omega : PotentialSample (n0 + 1) =>
      dirichletInfOn (layerCoefficient M Ssp omega) U p + eps) M.P.toMeasure :=
    (hinf_int Ssp).add (integrable_const eps)
  have hmain := integral_le_of_setIntegral_fiber_le hnmeas (hinf_int Sfull) hint2 hfiber
  have hval : ∫ omega, (dirichletInfOn (layerCoefficient M Ssp omega) U p + eps)
        ∂M.P.toMeasure =
      (∫ omega, dirichletInfOn (layerCoefficient M Ssp omega) U p ∂M.P.toMeasure)
        + eps := by
    rw [integral_add (hinf_int Ssp) (integrable_const eps), integral_const,
      smul_eq_mul, show (M.P.toMeasure).real Set.univ = (1 : ℝ) by simp, one_mul]
  rw [hval] at hmain
  exact hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
