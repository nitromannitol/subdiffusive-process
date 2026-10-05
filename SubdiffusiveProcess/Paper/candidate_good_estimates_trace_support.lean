module

public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.EstimateLimits
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.OneStepDatum
public import SubdiffusiveProcess.Paper.killed_continuous_boundary_zero
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.cor_energy_measures
public import SubdiffusiveProcess.Paper.candidate_good_estimates_trace_passage
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.in_deterministic
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.lem_primitive
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.WeakGraphMaxPrinciple
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import SubdiffusiveProcess.Paper.lem_prefix_limit
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.candidate_good_estimates_finite_bank_support
public import SubdiffusiveProcess.Sobolev.CampanatoWindowLimit

@[expose] public section

/-! Actual source compactness, arbitrary-cube growth, and Campanato-to-Hölder glue used by the candidate trace passage. This module proves support facts and does not assert the candidate conclusion. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A response on an arbitrary cube is a killed weak solution with the prescribed source. -/
lemma aux_candidate_good_estimates_trace_support_response_killed
    {d : ℕ} (Ω : Opens (SpatialCoordinates d)) (S : ResponseSpace Ω)
    (hS : S.space = killedSobolevGraph Ω) (a : PositiveCoefficient Ω)
    (f : SpatialCoordinates d → ℝ) (fL2 : DomainL2 Ω)
    (hf : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))] f) :
    ∃ u : killedSobolevGraph Ω,
      u.val = (responseSolution S a ((sobolevVolumeLoad fL2).comp S.space.subtypeL)).val ∧
      ∀ psi : killedSobolevGraph Ω,
        sobolevCoefficientForm a u.val psi.val =
          ∫ x in (Ω : Set (SpatialCoordinates d)), f x * psi.val.1 x := by
  let ur := responseSolution S a ((sobolevVolumeLoad fL2).comp S.space.subtypeL)
  have hu : ur.val ∈ killedSobolevGraph Ω := hS ▸ ur.property
  refine ⟨⟨ur.val, hu⟩, rfl, ?_⟩
  intro psi
  let ps : S.space := ⟨psi.val, hS.symm ▸ psi.property⟩
  have he := responseSolution_spec S a ((sobolevVolumeLoad fL2).comp S.space.subtypeL) ps
  change sobolevCoefficientForm a ur.val psi.val = sobolevVolumeLoad fL2 psi.val at he
  rw [he, sobolevVolumeLoad_apply]
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  simp only [hx]

/-- A continuous function on a compact cube closure is square-integrable on its cube. -/
lemma aux_candidate_good_estimates_trace_support_cont_memLp
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    MemLp U 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hc := (centeredCube_isBounded z hr).isCompact_closure
  obtain ⟨C, hC⟩ := bddAbove_def.mp (hc.bddAbove_image hU.norm)
  refine MemLp.of_bound
    ((hU.mono subset_closure).aestronglyMeasurable (centeredCube z r hr).isOpen.measurableSet) C ?_
  filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx
  exact hC _ ⟨x, subset_closure hx, rfl⟩

private lemma aux_cge_growth_global_c2_zero {d : ℕ} (S : Set (SpatialCoordinates d)) :
    c2Norm S (fun _ => (0 : ℝ)) = 0 := by
  have hz : sSup {v : ℝ | ∃ x ∈ S, v = 0} = 0 := by
    apply le_antisymm
    · exact Real.sSup_le (by rintro v ⟨x, hx, rfl⟩; exact le_rfl) le_rfl
    · exact Real.sSup_nonneg (by rintro v ⟨x, hx, rfl⟩; exact le_rfl)
  simp only [c2Norm, abs_zero, fderiv_fun_const, fderiv_zero, Pi.zero_apply,
    ContinuousLinearMap.opNorm_zero, hz, add_zero]
/-- Smooth source responses on any positive cube have a global zero-boundary Hölder bound with a moment-controlled constant. -/
theorem candidate_good_estimates_trace_support
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Poin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hb : beta ∈ Ioo (0 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        ∃ (K : ℕ → BilateralField d → ℝ) (C : ℝ), 0 ≤ C ∧
          (∀ n, MemLp (K n) 1 (chaosSampleLaw M).toMeasure) ∧
          (∀ n, eLpNorm (K n) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ n, 1 ≤ K n om) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ (n : ℕ) (f : SpatialCoordinates d → ℝ) (Kf : ℝ),
            ContDiff ℝ ∞ f → 0 ≤ Kf →
            (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
              |f x| ≤ Kf) →
          ∀ u : killedSobolevGraph (centeredCube z r hr),
            (∀ psi : killedSobolevGraph (centeredCube z r hr),
              sobolevCoefficientForm (cutoffPositiveCoefficient M H om n z hr)
                u.val psi.val = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
                  f x * psi.val.1 x) →
            ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
              ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U) ∧
              (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0) ∧
              IsHolderOn beta (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
              cAlphaNorm beta (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ K n om * Kf := by
  obtain ⟨delta0, hd0, hG⟩ := prop_growth d hd I Poin X W Cp Sob
    ((d : ℝ) - 1 / 2) beta 1 (fun _ => 1) (by linarith) (by linarith) hb.1 hb.2
    (fun _ => le_rfl)
  obtain ⟨delta0', hd0', hG'⟩ := prop_growth_large_root d hd I Poin X W Cp Sob
    ((d : ℝ) - 1 / 2) beta 1 (fun _ => 1) (by linarith) (by linarith) hb.1 hb.2
    (fun _ => le_rfl)
  refine ⟨min delta0 delta0', lt_min hd0 hd0', ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr
  by_cases hr1 : r ≤ 1
  · obtain ⟨K, C, hmem, hnorm, hge, hsource⟩ :=
      hG M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)) z r hr hr1
    let Cpos : ℝ := max (C 0) 0
    have hCpos : 0 ≤ Cpos := le_max_right _ _
    have hnormPos : ∀ n, eLpNorm (K n) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cpos := by
      intro n
      simpa only [Cpos, ENNReal.ofReal_one] using
        (hnorm 0 n).trans
          (ENNReal.ofReal_le_ofReal (le_max_left (C 0) (0 : ℝ)))
    refine ⟨K, Cpos, hCpos, ?_, hnormPos, hge, ?_⟩
    · simpa only [ENNReal.ofReal_one] using hmem 0
    filter_upwards [hsource] with om hom
    intro n f Kf hf hKf hfbound u hsolve
    let uw : weakSobolevGraph (centeredCube z r hr) :=
      ⟨u.val, killedSobolevGraph_le_weakSobolevGraph u.property⟩
    have hsol : SolvesDirichlet (cutoffPositiveCoefficient M H om n z hr) f 0 uw := by
      refine ⟨?_, hsolve⟩
      simpa only [ZeroMemClass.coe_zero, sub_zero] using u.property
    have hzero : (((0 : weakSobolevGraph (centeredCube z r hr)).val.1) :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (fun _ => 0) :=
      Lp.coeFn_zero _ _ _
    obtain ⟨U, hUc, hUrep, hUH, hUbound⟩ := (hom n f Kf hKf
      hf.continuous.measurable.aemeasurable hfbound (fun _ => 0) 0 contDiff_const
      (aux_cge_growth_global_c2_zero _).le 0 uw hzero hsol).2
    refine ⟨U, hUc, hUrep, ?_, hUH, ?_⟩
    · intro x hx
      apply killed_continuous_boundary_zero d z r hr u.val u.property U hUc hUrep x
      · have hc := frontier_subset_closure hx
        change x ∈ closure (Metric.ball z (r / 2)) at hc
        exact closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hc
      · simpa only [(centeredCube z r hr).isOpen.interior_eq] using hx.2
    · simpa only [add_zero] using hUbound
  · push Not at hr1
    obtain ⟨K, C, hmem, hnorm, hge, hsource⟩ :=
      hG' M Rm Sreg It H hIR (hdelta.trans (min_le_right _ _)) z r hr hr1
    let Cpos : ℝ := max (C 0) 0
    have hCpos : 0 ≤ Cpos := le_max_right _ _
    have hnormPos : ∀ n, eLpNorm (K n) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cpos := by
      intro n
      simpa only [Cpos, ENNReal.ofReal_one] using
        (hnorm 0 n).trans
          (ENNReal.ofReal_le_ofReal (le_max_left (C 0) (0 : ℝ)))
    refine ⟨K, Cpos, hCpos, ?_, hnormPos, hge, ?_⟩
    · simpa only [ENNReal.ofReal_one] using hmem 0
    filter_upwards [hsource] with om hom
    intro n f Kf hf hKf hfbound u hsolve
    let uw : weakSobolevGraph (centeredCube z r hr) :=
      ⟨u.val, killedSobolevGraph_le_weakSobolevGraph u.property⟩
    have hsol : SolvesDirichlet (cutoffPositiveCoefficient M H om n z hr) f 0 uw := by
      refine ⟨?_, hsolve⟩
      simpa only [ZeroMemClass.coe_zero, sub_zero] using u.property
    have hzero : (((0 : weakSobolevGraph (centeredCube z r hr)).val.1) :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (fun _ => 0) :=
      Lp.coeFn_zero _ _ _
    obtain ⟨U, hUc, hUrep, hUH, hUbound⟩ := (hom n f Kf hKf
      hf.continuous.measurable.aemeasurable hfbound (fun _ => 0) 0 contDiff_const
      (aux_cge_growth_global_c2_zero _).le 0 uw hzero hsol).2
    refine ⟨U, hUc, hUrep, ?_, hUH, ?_⟩
    · intro x hx
      apply killed_continuous_boundary_zero d z r hr u.val u.property U hUc hUrep x
      · have hc := frontier_subset_closure hx
        change x ∈ closure (Metric.ball z (r / 2)) at hc
        exact closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hc
      · simpa only [(centeredCube z r hr).isOpen.interior_eq] using hx.2
    · simpa only [add_zero] using hUbound
section CgeCompactSection
open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

/-- Compactness of the actual response representatives.  All probabilistic and
PDE suppliers are discharged before this small deterministic declaration. -/
lemma aux_candidate_good_estimates_trace_support_compact_rep
    {d : ℕ} [NeZero d]
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (uN : ℕ → DomainL2 (centeredCube Qcentre Qside hQside))
    (BN : ℕ → SpatialCoordinates d → ℝ)
    (hBNrep : ∀ n : ℕ,
      (uN n : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] BN n)
    (hBNboundary : ∀ n : ℕ, ∀ x ∈ frontier
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), BN n x = 0)
    (hEqui : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ∀ x ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
        |BN n x - BN n y| ≤ K * dist x y ^ beta)
    (hPoint : ∃ x ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, |BN n x| ≤ K)
    (u : DomainL2 (centeredCube Qcentre Qside hQside))
    (hrecLp : Tendsto uN atTop (𝓝 u)) :
    ∃ (U : SpatialCoordinates d → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
      ((u : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) ∧
      (∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), U x = 0) ∧
      (∀ x ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
        Tendsto (fun n => BN (φ n) x) atTop (𝓝 (U x))) ∧
      TendstoUniformlyOn (fun n => BN (φ n)) U atTop
        (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) := by
  classical
  let K : Set (SpatialCoordinates d) :=
    closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))
  have hKmeas : MeasurableSet K := by
    dsimp [K]
    exact measurableSet_closure
  have hKnonempty : K.Nonempty := by
    refine ⟨Qcentre, ?_⟩
    apply subset_closure
    change Qcentre ∈ Metric.ball Qcentre (Qside / 2)
    exact Metric.mem_ball_self (by linarith)
  obtain ⟨x₀, hx₀K, K₀, hK₀, hpoint⟩ := hPoint
  obtain ⟨K₁, hK₁, hEqui'⟩ := hEqui
  have hbeta_pos : 0 < beta := by linarith [hbeta.1]
  have hpow' : ContinuousAt (fun t : ℝ => t ^ beta) 0 :=
    (Real.continuous_rpow_const hbeta_pos.le).continuousAt
  have hpow : Tendsto (fun t : ℝ => t ^ beta) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow hbeta_pos.ne'] using
      hpow'.tendsto
  have hmod : Tendsto (fun t : ℝ => K₁ * t ^ beta) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hpow)
  have heq : Equicontinuous (fun n (x : K) => BN n x) := by
    apply Metric.equicontinuous_of_continuity_modulus
      (fun t : ℝ => K₁ * t ^ beta) hmod
    intro x y n
    simpa only [Real.dist_eq, Subtype.dist_eq, Subtype.coe_mk] using!
      hEqui' n x.1 x.2 y.1 y.2
  have hbound : ∀ x : K, ∃ M : ℝ, ∀ n, ‖BN n x‖ ≤ M := by
    intro x
    refine ⟨K₀ + K₁ * dist (x : SpatialCoordinates d) x₀ ^ beta, ?_⟩
    intro n
    rw [Real.norm_eq_abs]
    calc
      |BN n (x : SpatialCoordinates d)| =
          |(BN n (x : SpatialCoordinates d) - BN n x₀) + BN n x₀| := by
            congr 1; ring
      _ ≤ |BN n (x : SpatialCoordinates d) - BN n x₀| + |BN n x₀| := by
        simpa only [Real.norm_eq_abs] using
          (norm_add_le (BN n (x : SpatialCoordinates d) - BN n x₀) (BN n x₀))
      _ ≤ K₁ * dist (x : SpatialCoordinates d) x₀ ^ beta + K₀ := by
        exact add_le_add (hEqui' n (x : SpatialCoordinates d) x.2 x₀ hx₀K)
          (hpoint n)
      _ = K₀ + K₁ * dist (x : SpatialCoordinates d) x₀ ^ beta := by ring
  let : Nonempty K := hKnonempty.to_subtype
  obtain ⟨g, φ, hφ, hgcont, hglim⟩ :=
    exists_pointwise_subseq_of_equicontinuous heq hbound
  let U : SpatialCoordinates d → ℝ := fun x =>
    if hx : x ∈ K then g ⟨x, hx⟩ else 0
  have hUcont : ContinuousOn U K := by
    rw [continuousOn_iff_continuous_domRestrict]
    simpa [U] using hgcont
  have hrecφ : Tendsto (fun n => uN (φ n)) atTop (𝓝 u) := by
    simpa only [Function.comp_apply] using! hrecLp.comp hφ.tendsto_atTop
  have hmeasure : TendstoInMeasure
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
      (fun n => uN (φ n)) atTop (u : SpatialCoordinates d → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp hrecφ
  obtain ⟨ψ, hψ, huae⟩ := hmeasure.exists_seq_tendsto_ae
  have haeall : ∀ᵐ x ∂(volume.restrict
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))),
      ∀ n : ℕ, uN n x = BN n x := by
    apply ae_all_iff.mpr
    intro n
    exact (hBNrep n).mono (fun _ h => h)
  have hUae : ((u : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) := by
    have hQmeas : MeasurableSet
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
      exact measurableSet_ball
    have hQK : ∀ᵐ x ∂(volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))), x ∈ K :=
      ae_restrict_of_forall_mem hQmeas (fun x hx => subset_closure hx)
    filter_upwards [haeall, hQK, huae] with x hx hxK hxu
    have hgpt : Tendsto (fun i => BN (φ (ψ i)) x) atTop
        (𝓝 (g ⟨x, hxK⟩)) := by
      simpa only [Function.comp_apply] using! (hglim ⟨x, hxK⟩).comp hψ.tendsto_atTop
    have heqseq : (fun i => BN (φ (ψ i)) x) =ᶠ[atTop]
        (fun i => uN (φ (ψ i)) x) :=
      Filter.Eventually.of_forall (fun i => (hx (φ (ψ i))).symm)
    have hgeq : (u : SpatialCoordinates d → ℝ) x = g ⟨x, hxK⟩ :=
      tendsto_nhds_unique hxu (Filter.Tendsto.congr' heqseq hgpt)
    simpa [U, hxK] using hgeq
  have hUb : ∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), U x = 0 := by
    intro x hx
    by_cases hxK : x ∈ K
    · have hgxb : g ⟨x, hxK⟩ = 0 := by
        apply tendsto_nhds_unique_of_eventuallyEq (hglim ⟨x, hxK⟩)
          tendsto_const_nhds
        exact Filter.Eventually.of_forall (fun n => hBNboundary (φ n) x hx)
      simpa [U, hxK] using hgxb
    · simp [U, hxK]
  refine ⟨U, φ, hφ, hUcont, hUae, hUb, ?_, ?_⟩
  · intro x hx
    have hxK : x ∈ K := hx
    simpa only [U, dite_eq_left hxK] using hglim ⟨x, hxK⟩
  · let : CompactSpace K :=
      isCompact_iff_compactSpace.mp (centeredCube_isBounded Qcentre hQside).isCompact_closure
    have hguni : TendstoUniformly (fun n (x : K) => BN (φ n) x) g atTop := by
      apply UniformFun.tendsto_iff_tendstoUniformly.mp
      exact ((heq.comp φ).tendsto_uniformFun_iff_pi atTop g).mpr
        (tendsto_pi_nhds.mpr hglim)
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa [U, Function.comp_def] using hguni


end CgeCompactSection
/-- Almost-everywhere equality of continuous functions on a cube closure gives equality of their Holder norms. -/
lemma aux_candidate_good_estimates_trace_support_cAlphaNorm_congr_on
    {d : ℕ} (alpha : ℝ) (S : Set (SpatialCoordinates d))
    (f g : SpatialCoordinates d → ℝ) (h : ∀ x ∈ S, f x = g x) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S f = _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S g := by
  have hsup : {v : ℝ | ∃ x ∈ S, v = |f x|} = {v : ℝ | ∃ x ∈ S, v = |g x|} := by
    ext v
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [h x hx]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [h x hx]⟩
  have hratio : _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha S f = _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha S g := by
    ext v
    simp only [_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet, mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, y, hy, hxy, rfl⟩
      exact ⟨x, hx, y, hy, hxy, by rw [h x hx, h y hy]⟩
    · rintro ⟨x, hx, y, hy, hxy, rfl⟩
      exact ⟨x, hx, y, hy, hxy, by rw [h x hx, h y hy]⟩
  simp only [_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm, _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm, hsup, hratio]
/-- Uniform finite-horizon Campanato bounds yield the Holder trace on the closed cube. -/
lemma aux_candidate_good_estimates_trace_support_holder_from_horizons
    {d : ℕ} (alpha : ℝ) (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (Qset : Set (SpatialCoordinates d)) (hQ : IsOpen Qset)
    (qcenter : SpatialCoordinates d) (qside : ℝ) (hqpos : 0 < qside)
    (hqpQ : Metric.ball qcenter (3 * qside / 2) ⊆ Qset)
    (hclQ : closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) ⊆ Qset)
    (hscaleQ : ∀ x ∈ closedCube (0 : SpatialCoordinates d) 1 one_pos,
      qcenter + qside • x ∈ Qset)
    (hcenterQ : qcenter ∈ Qset)
    (U : SpatialCoordinates d → ℝ) (Uh : ℕ → SpatialCoordinates d → ℝ)
    (hUcont : ContinuousOn U Qset)
    (hUhcont : ∀ h, ContinuousOn (Uh h) Qset)
    (hUae : ∀ h, U =ᵐ[volume.restrict Qset] Uh h)
    (C1 Cbound a t S : ℝ) (hC1 : 0 ≤ C1) (hC1b : C1 ≤ Cbound)
    (hCh : 2 * aux_in_deterministic_regularity_holderConst d alpha * C1 ≤ Cbound)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hsub : Cbound * t < 1 - alpha) (hS : 0 ≤ S)
    (hcamp : ∀ h : ℕ, ∀ (D : ℕ), D ≤ h →
      ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
        let B : Set (SpatialCoordinates d) :=
          Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
            (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))
        normalizedL2On B (fun y => Uh h y - (volume.real B)⁻¹ * ∫ t in B, Uh h t) ≤
          C1 * (3 : ℝ) ^ (C1 * a) * (3 : ℝ) ^ (C1 * t * (D : ℝ)) *
            (3 : ℝ) ^ (-(D : ℝ)) *
            (normalizedL2On (Metric.ball qcenter (3 * qside / 2))
              (fun y => Uh h y - (volume.real (Metric.ball qcenter (3 * qside / 2)))⁻¹ *
                ∫ t in Metric.ball qcenter (3 * qside / 2), Uh h t) + S)) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) U ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
          (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
          (fun x => U (qcenter + qside • x) - U qcenter) ≤
        Cbound * (3 : ℝ) ^ (Cbound * a) *
          (normalizedL2On (Metric.ball qcenter (3 * qside / 2))
            (fun x => U x - (volume.real (Metric.ball qcenter (3 * qside / 2)))⁻¹ *
              ∫ y in Metric.ball qcenter (3 * qside / 2), U y) + S) := by
  have hEq : ∀ h, EqOn U (Uh h) Qset := fun h =>
    Measure.eqOn_open_of_ae_eq (hUae h) hQ hUcont (hUhcont h)
  obtain ⟨hHolder, hCa⟩ :=
    aux_in_deterministic_regularity_glue_holder alpha halpha Qset hQ qcenter qside hqpos
      hqpQ U Uh hUhcont hUae C1 Cbound a t S hC1 hC1b hCh ha ht hsub hS hcamp
  have hHolderU : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
      (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) U := by
    have hratio : _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha
        (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) U =
      _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha
        (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) (Uh 0) := by
      ext v
      simp only [_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet, mem_ofPred_eq]
      constructor
      · rintro ⟨x, hx, y, hy, hxy, rfl⟩
        exact ⟨x, hx, y, hy, hxy, by rw [hEq 0 (hclQ hx), hEq 0 (hclQ hy)]⟩
      · rintro ⟨x, hx, y, hy, hxy, rfl⟩
        exact ⟨x, hx, y, hy, hxy, by rw [hEq 0 (hclQ hx), hEq 0 (hclQ hy)]⟩
    change BddAbove (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha
      (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) U)
    rw [hratio]
    exact hHolder
  have hoscEq := aux_in_deterministic_regularity_osc_congr Metric.isOpen_ball.measurableSet
    (fun x hx => hEq 0 (hqpQ hx))
  have hCaEq := aux_candidate_good_estimates_trace_support_cAlphaNorm_congr_on alpha
    (closedCube (0 : SpatialCoordinates d) 1 one_pos)
    (fun x => U (qcenter + qside • x) - U qcenter)
    (fun x => Uh 0 (qcenter + qside • x) - Uh 0 qcenter)
    (fun x hx => by
      rw [hEq 0 (hscaleQ x hx), hEq 0 hcenterQ])
  rw [← hCaEq, ← hoscEq] at hCa
  exact ⟨hHolderU, hCa⟩

/-- Uniformly convergent source banks pass finite Campanato windows to their trace and yield the Hölder trace bound. -/
lemma aux_candidate_good_estimates_trace_support_campanato_limit_bank
    {d : ℕ} (alpha : ℝ) (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (Qset : Set (SpatialCoordinates d)) (hQopen : IsOpen Qset)
    (hQcompact : IsCompact (closure Qset))
    (qcenter : SpatialCoordinates d) (qside : ℝ) (hqpos : 0 < qside)
    (hqpQ : Metric.ball qcenter (3 * qside / 2) ⊆ Qset)
    (hclQ : closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) ⊆ Qset)
    (hscaleQ : ∀ x ∈ closedCube (0 : SpatialCoordinates d) 1 one_pos,
      qcenter + qside • x ∈ Qset)
    (hcenterQ : qcenter ∈ Qset)
    (U : SpatialCoordinates d → ℝ) (Uh : ℕ → SpatialCoordinates d → ℝ)
    (VN : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (hUcont : ContinuousOn U Qset)
    (hUhcont : ∀ h, ContinuousOn (Uh h) (closure Qset))
    (hVNcont : ∀ h n, ContinuousOn (VN h n) (closure Qset))
    (hUae : ∀ h, U =ᵐ[volume.restrict Qset] Uh h)
    (hUni : ∀ h, TendstoUniformlyOn (fun n => VN h n) (Uh h) atTop (closure Qset))
    (aN : ℕ → ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hA : ∀ h, Tendsto (aN h) atTop (𝓝 a))
    (C1 Cbound aexp t F fsup : ℝ)
    (hC1 : 0 ≤ C1) (hC1b : C1 ≤ Cbound)
    (hCh : 2 * aux_in_deterministic_regularity_holderConst d alpha * C1 ≤ Cbound)
    (haexp : 0 ≤ aexp) (ht : 0 ≤ t) (hsub : Cbound * t < 1 - alpha)
    (hfsup : 0 ≤ fsup) (hFle : F ≤ fsup)
    (hfinite : ∀ h : ℕ, ∀ (D : ℕ), D ≤ h →
      ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
        ∀ᶠ n in atTop,
          let W : Set (SpatialCoordinates d) :=
            Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℝ)) / 2) ∩
              (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))
          normalizedL2On W (fun y => VN h n y - (volume.real W)⁻¹ * ∫ z in W, VN h n z) ≤
            C1 * (3 : ℝ) ^ (C1 * aexp) * (3 : ℝ) ^ (C1 * t * (D : ℝ)) *
              (3 : ℝ) ^ (-(D : ℝ)) *
              (normalizedL2On (Metric.ball qcenter (3 * qside / 2))
                (fun y => VN h n y - (volume.real (Metric.ball qcenter (3 * qside / 2)))⁻¹ *
                  ∫ z in Metric.ball qcenter (3 * qside / 2), VN h n z) +
                qside ^ 2 * (aN h n)⁻¹ * F)) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) U ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (closedCube (0 : SpatialCoordinates d) 1 one_pos)
        (fun x => U (qcenter + qside • x) - U qcenter) ≤
        Cbound * (3 : ℝ) ^ (Cbound * aexp) *
          (normalizedL2On (Metric.ball qcenter (3 * qside / 2))
            (fun x => U x - (volume.real (Metric.ball qcenter (3 * qside / 2)))⁻¹ *
              ∫ y in Metric.ball qcenter (3 * qside / 2), U y) +
            qside ^ 2 * a⁻¹ * fsup) := by
  let p : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
  have hpPos : 0 < volume.real p := by
    simpa only [p, Set.inter_univ] using
      (SubdiffusiveProcess.volume_real_ball_inter_pos (Set.univ : Set (SpatialCoordinates d))
        isOpen_univ qcenter (Set.mem_univ _) (3 * qside / 2) (by positivity))
  have hpTop : volume p ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hqOpen : IsOpen (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) := by
    exact Metric.isOpen_ball
  have hqQ : (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) ⊆ Qset :=
    subset_closure.trans hclQ
  have hMemLpWindow {W : Set (SpatialCoordinates d)} (hWm : MeasurableSet W)
      (hWtop : volume W ≠ ⊤) (hWQ : W ⊆ Qset)
      (g : SpatialCoordinates d → ℝ) (hg : ContinuousOn g (closure Qset)) :
      MemLp g 2 (volume.restrict W) := by
    let : IsFiniteMeasure (volume.restrict W) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact hWtop.lt_top⟩
    obtain ⟨B, hB⟩ := bddAbove_def.mp (hQcompact.bddAbove_image hg.norm)
    refine MemLp.of_bound
      ((hg.mono (hWQ.trans subset_closure)).aestronglyMeasurable hWm) (max B 0) ?_
    filter_upwards [ae_restrict_mem hWm] with x hx
    have hb := hB _ ⟨x, subset_closure (hWQ hx), rfl⟩
    have hb' : |g x| ≤ B := by simpa only [Real.norm_eq_abs] using hb
    exact hb'.trans (le_max_left _ _)
  have hcamp : ∀ h : ℕ, ∀ (D : ℕ), D ≤ h →
      ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
        normalizedL2On
            (Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℝ)) / 2) ∩
              (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)))
            (fun y => Uh h y - (volume.real
              (Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℝ)) / 2) ∩
                (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))))⁻¹ *
              ∫ z in Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℝ)) / 2) ∩
                (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)), Uh h z) ≤
          C1 * (3 : ℝ) ^ (C1 * aexp) * (3 : ℝ) ^ (C1 * t * (D : ℝ)) *
            (3 : ℝ) ^ (-(D : ℝ)) *
            (normalizedL2On p (fun y => Uh h y - (volume.real p)⁻¹ * ∫ z in p, Uh h z) +
              qside ^ 2 * a⁻¹ * fsup) := by
    intro h D hDh x hx
    let W : Set (SpatialCoordinates d) :=
      Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℝ)) / 2) ∩
        (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))
    have hrad : 0 < qside * (3 : ℝ) ^ (-(D : ℝ)) / 2 := by positivity
    have hWm : MeasurableSet W := by
      dsimp [W]
      exact measurableSet_ball.inter hqOpen.measurableSet
    have hWpos : 0 < volume.real W := by
      dsimp [W]
      exact SubdiffusiveProcess.volume_real_ball_inter_pos
        (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) hqOpen x hx _ hrad
    have hWtop : volume W ≠ ⊤ := by
      apply ne_of_lt
      exact (measure_mono inter_subset_left).trans_lt Metric.isBounded_ball.measure_lt_top
    have hWQ : W ⊆ Qset := inter_subset_right.trans hqQ
    have hlimW : TendstoUniformlyOn (fun n => VN h n) (Uh h) atTop W := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hUni h) ε hε] with n hn
      intro y hy
      exact hn y (subset_closure (hWQ hy))
    have hlimP : TendstoUniformlyOn (fun n => VN h n) (Uh h) atTop p := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hUni h) ε hε] with n hn
      intro y hy
      exact hn y (subset_closure (hqpQ hy))
    have hbound := SubdiffusiveProcess.campanato_bound_of_tendstoUniformlyOn
      W p hWm measurableSet_ball hWpos hpPos hWtop hpTop
      (VN h) (Uh h)
      (fun n => hMemLpWindow hWm hWtop hWQ (VN h n) (hVNcont h n))
      (fun n => hMemLpWindow measurableSet_ball hpTop hqpQ (VN h n) (hVNcont h n))
      (hMemLpWindow hWm hWtop hWQ (Uh h) (hUhcont h))
      (hMemLpWindow measurableSet_ball hpTop hqpQ (Uh h) (hUhcont h))
      hlimW hlimP (aN h) a ha.ne' (hA h)
      (C1 * (3 : ℝ) ^ (C1 * aexp) * (3 : ℝ) ^ (C1 * t * (D : ℝ)) *
        (3 : ℝ) ^ (-(D : ℝ))) qside F (hfinite h D hDh x hx)
    have hFterm : qside ^ 2 * a⁻¹ * F ≤ qside ^ 2 * a⁻¹ * fsup :=
      mul_le_mul_of_nonneg_left hFle (mul_nonneg (sq_nonneg qside) (inv_nonneg.mpr ha.le))
    have hcoeff : 0 ≤ C1 * (3 : ℝ) ^ (C1 * aexp) *
        (3 : ℝ) ^ (C1 * t * (D : ℝ)) * (3 : ℝ) ^ (-(D : ℝ)) := by positivity
    calc
      normalizedL2On W (fun y => Uh h y - (volume.real W)⁻¹ * ∫ z in W, Uh h z) ≤
        C1 * (3 : ℝ) ^ (C1 * aexp) * (3 : ℝ) ^ (C1 * t * (D : ℝ)) *
          (3 : ℝ) ^ (-(D : ℝ)) *
          (normalizedL2On p (fun y => Uh h y - (volume.real p)⁻¹ * ∫ z in p, Uh h z) +
            qside ^ 2 * a⁻¹ * F) := hbound
      _ ≤ C1 * (3 : ℝ) ^ (C1 * aexp) * (3 : ℝ) ^ (C1 * t * (D : ℝ)) *
          (3 : ℝ) ^ (-(D : ℝ)) *
          (normalizedL2On p (fun y => Uh h y - (volume.real p)⁻¹ * ∫ z in p, Uh h z) +
            qside ^ 2 * a⁻¹ * fsup) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hFterm) hcoeff
  have hcamp' : ∀ h : ℕ, ∀ (D : ℕ), D ≤ h →
      ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
        let B : Set (SpatialCoordinates d) :=
          Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
            (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))
        normalizedL2On B (fun y => Uh h y - (volume.real B)⁻¹ * ∫ y in B, Uh h y) ≤
          C1 * (3 : ℝ) ^ (C1 * aexp) * (3 : ℝ) ^ (C1 * t * (D : ℝ)) *
            (3 : ℝ) ^ (-(D : ℝ)) *
            (normalizedL2On p (fun y => Uh h y - (volume.real p)⁻¹ * ∫ y in p, Uh h y) +
              qside ^ 2 * a⁻¹ * fsup) := by
    intro h D hDh x hx
    have hpow : (3 : ℝ) ^ (-(D : ℝ)) = (3 : ℝ) ^ (-(D : ℤ)) := by
      rw [← Real.rpow_intCast (3 : ℝ) (-(D : ℤ))]
      simp only [Int.cast_neg, Int.cast_natCast]
    have hW :
        Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℝ)) / 2) ∩
            (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) =
          Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
            (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) := by
      rw [hpow]
    simpa only [p, hW] using hcamp h D hDh x hx
  have hS : 0 ≤ qside ^ 2 * a⁻¹ * fsup :=
    mul_nonneg (mul_nonneg (sq_nonneg qside) (inv_nonneg.mpr ha.le)) hfsup
  exact aux_candidate_good_estimates_trace_support_holder_from_horizons alpha halpha Qset hQopen
    qcenter qside hqpos hqpQ hclQ hscaleQ hcenterQ U Uh hUcont
    (fun h => (hUhcont h).mono subset_closure) hUae
    C1 Cbound aexp t (qside ^ 2 * a⁻¹ * fsup) hC1 hC1b hCh haexp ht hsub hS hcamp'

/-- The self and one-level padded roots locate the source windows and scaled trace cell in the limit cube. -/
lemma aux_candidate_good_estimates_trace_support_root_geometry
    {d : ℕ} {Enl Shift : Type*}
    (k : ℕ) (qside : ℝ) (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
    (hqpos : 0 < qside)
    (qcenter z : SpatialCoordinates d) (_hqcenter : qcenter = z)
    (qRoot : Enl × Shift) (selfE : Enl) (selfShift : Shift)
    (hqRoot : qRoot = (selfE, selfShift))
    (factor : Enl → ℕ) (hfactor : factor selfE = 0)
    (padE : Enl) (hpad : factor padE = 1)
    (shift : Shift → SpatialCoordinates d) (hshift : shift selfShift = 0)
    (rootLevel : Enl × Shift → ℤ)
    (hrootLevel : ∀ e t, rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
    (rootSide : Enl × Shift → ℝ)
    (hrootSide : ∀ U, rootSide U = (3 : ℝ) ^ (-rootLevel U))
    (rootCentre : Enl × Shift → SpatialCoordinates d)
    (hrootCentre : ∀ e t, rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
    (rootPos : ∀ U, 0 < rootSide U)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (hRootsQ : ∀ U : Enl × Shift,
      closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
        Set (SpatialCoordinates d)) ⊆
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) :
    Metric.ball qcenter (3 * qside / 2) ⊆
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ∧
      closure (centeredCube qcenter qside hqpos :
        Set (SpatialCoordinates d)) ⊆
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ∧
      (∀ x ∈ closedCube (0 : SpatialCoordinates d) 1 one_pos,
        qcenter + qside • x ∈
          (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
      qcenter ∈ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
  have hselfCentre : rootCentre qRoot = qcenter := by
    rw [hqRoot, hrootCentre, hshift]
    simp only [smul_zero, add_zero]
  have hselfLevel : rootLevel qRoot = (k : ℤ) := by
    rw [hqRoot, hrootLevel, hfactor]
    simp only [Nat.cast_zero, sub_zero]
  have hselfSide : rootSide qRoot = qside := by
    calc
      rootSide qRoot = (3 : ℝ) ^ (-rootLevel qRoot) := hrootSide qRoot
      _ = (3 : ℝ) ^ (-(k : ℤ)) := by rw [hselfLevel]
      _ = qside := hqside.symm
  have hpadCentre : rootCentre (padE, selfShift) = qcenter := by
    rw [hrootCentre, hshift]
    simp only [smul_zero, add_zero]
  have hpadLevel : rootLevel (padE, selfShift) = (k : ℤ) - 1 := by
    rw [hrootLevel, hpad]
    norm_num
  have hpadSide : rootSide (padE, selfShift) = 3 * qside := by
    calc
      rootSide (padE, selfShift) = (3 : ℝ) ^ (-rootLevel (padE, selfShift)) :=
        hrootSide _
      _ = (3 : ℝ) ^ (-(k : ℤ) + 1) := by rw [hpadLevel]; congr 1; omega
      _ = (3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ (1 : ℤ) := by
        rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      _ = 3 * qside := by rw [zpow_one, ← hqside]; ring
  have hselfCube : centeredCube qcenter qside hqpos =
      centeredCube (rootCentre qRoot) (rootSide qRoot) (rootPos qRoot) := by
    apply Opens.ext
    change Metric.ball qcenter (qside / 2) =
      Metric.ball (rootCentre qRoot) (rootSide qRoot / 2)
    rw [hselfCentre, hselfSide]
  have hpadBall :
      (centeredCube (rootCentre (padE, selfShift)) (rootSide (padE, selfShift))
        (rootPos (padE, selfShift)) : Set (SpatialCoordinates d)) =
        Metric.ball qcenter (3 * qside / 2) := by
    change Metric.ball (rootCentre (padE, selfShift))
      (rootSide (padE, selfShift) / 2) = _
    rw [hpadCentre, hpadSide]
  have hqpQ : Metric.ball qcenter (3 * qside / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
    rw [← hpadBall]
    exact fun x hx => hRootsQ (padE, selfShift) (subset_closure hx)
  have hclQ : closure (centeredCube qcenter qside hqpos :
      Set (SpatialCoordinates d)) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
    rw [hselfCube]
    exact hRootsQ qRoot
  have hscaleQ : ∀ x ∈ closedCube (0 : SpatialCoordinates d) 1 one_pos,
      qcenter + qside • x ∈
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
    intro x hx
    have hxnorm : ‖x‖ ≤ (1 : ℝ) / 2 := by
      change dist x 0 ≤ (1 : ℝ) / 2 at hx
      simpa only [dist_eq_norm, sub_zero] using hx
    have hdist : dist (qcenter + qside • x) qcenter ≤ qside / 2 := by
      calc
        dist (qcenter + qside • x) qcenter = ‖qcenter + qside • x - qcenter‖ := by
          rw [dist_eq_norm]
        _ = ‖qside • x‖ := by congr 1; abel
        _ = qside * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hqpos]
        _ ≤ qside * ((1 : ℝ) / 2) := mul_le_mul_of_nonneg_left hxnorm hqpos.le
        _ = qside / 2 := by ring
    have hclosure : qcenter + qside • x ∈
        closure (centeredCube qcenter qside hqpos :
          Set (SpatialCoordinates d)) := by
      change qcenter + qside • x ∈ closure (Metric.ball qcenter (qside / 2))
      have hr : 0 < qside / 2 := div_pos hqpos (by norm_num)
      rw [closure_ball qcenter hr.ne']
      exact Metric.mem_closedBall.mpr hdist
    exact hclQ hclosure
  have hcenterQ : qcenter ∈
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
    rw [← hselfCentre]
    have hmem : rootCentre qRoot ∈
        (centeredCube (rootCentre qRoot) (rootSide qRoot) (rootPos qRoot) :
          Set (SpatialCoordinates d)) := by
      change rootCentre qRoot ∈ Metric.ball (rootCentre qRoot) (rootSide qRoot / 2)
      exact Metric.mem_ball_self (half_pos (rootPos qRoot))
    exact hRootsQ qRoot (subset_closure hmem)
  exact ⟨hqpQ, hclQ, hscaleQ, hcenterQ⟩
end SubdiffusiveProcess.Paper
end
