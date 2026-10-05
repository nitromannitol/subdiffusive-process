module

public import SubdiffusiveProcess.Section10.RetainedPrefixCoefficient
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseComparison

@[expose] public section

/-!
# Actual continuum comparison of full and retained-prefix fields

Adapt the countable epsilon-optimal competitor argument of SparseComparison
on the actual retained block. Each selection fiber fixes a deterministic
competitor; spatial Fubini and D0 conditioning remove the omitted layers.
This proves a variational comparison, not just a scalar reinsertion identity.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory ProbabilityTheory Set
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (potentialIndexSigma potentialIndexSigma_le_borel)
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

noncomputable section

/-- The full cutoff minimum is dominated in expectation by the actual retained
minimum whenever all retained indices fit inside the cutoff. -/
theorem integral_layerCoefficient_full_le_retainedPrefix {n0 : ℕ} (M : GMCModel (n0 + 1))
    {ell R N m : ℕ} (hm : ell + N * R ≤ m) {Q : TriadicCube (n0 + 1)}
    {U : Set (Vec (n0 + 1))} (hU : IsOpenBoundedConvexDomain U)
    (hUQ : U ⊆ openCubeSet Q) (p : Vec (n0 + 1)) :
    ∫ omega, dirichletInfOn (layerCoefficient M (Finset.range (m + 1)) omega)
        U p ∂M.P.toMeasure ≤
      ∫ omega, dirichletInfOn (layerCoefficient M (retainedPrefixIndices ell R N) omega)
        U p ∂M.P.toMeasure := by
  classical
  have hUmeas : MeasurableSet U := hU.isOpen.measurableSet
  have hUb : Bornology.IsBounded U := hU.isBoundedDomain.isBounded
  have : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hU.isBoundedDomain.volume_lt_top⟩
  -- the two coefficient families
  set Sfull : Finset ℕ := Finset.range (m + 1) with hSfull
  set Ssp : Finset ℕ := retainedPrefixIndices ell R N with hSsp
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
      have hc : (∫ omega, G omega * layerCoefficient M Sfull omega x ∂M.P.toMeasure) =
          ∫ omega, G omega * layerCoefficient M Ssp omega x ∂M.P.toMeasure := by
        simpa only [aCutoff_eq_layerCoefficient, retainedPrefixCoefficient, hSfull, hSsp] using
          integral_mul_aCutoff_eq_retainedPrefix M hm hGsigma x
      rw [hc]
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

/-- Comparison on the genuine GMC carrier, for every dimension admitted by the
model, every starting scale and generation, and every later full cutoff. -/
theorem integral_aCutoff_dirichletInfOn_le_retainedPrefix {d : ℕ} (M : GMCModel d)
    {ell R N m : ℕ} (hm : ell + N * R ≤ m) {Q : TriadicCube d}
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hUQ : U ⊆ openCubeSet Q) (p : Vec d) :
    ∫ omega, dirichletInfOn (aCutoff M m omega) U p ∂M.P.toMeasure ≤
      ∫ omega, dirichletInfOn (retainedPrefixCoefficient M ell R N omega) U p
        ∂M.P.toMeasure := by
  obtain ⟨n0, rfl⟩ : ∃ n0 : ℕ, d = n0 + 1 :=
    ⟨d - 1, by have := M.shellPrefix.dimension; omega⟩
  have hfield (omega : PotentialSample (n0 + 1)) :
      aCutoff M m omega = layerCoefficient M (Finset.range (m + 1)) omega :=
    funext fun x => aCutoff_eq_layerCoefficient M m omega x
  simp_rw [hfield]
  exact integral_layerCoefficient_full_le_retainedPrefix M hm hU hUQ p

end

end SubdiffusiveProcess.Section10
