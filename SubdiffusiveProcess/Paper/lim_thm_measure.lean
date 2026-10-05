module

public import Mathlib
public import SubdiffusiveProcess.Section10.LimitMeasureLawsAssembly
public import SubdiffusiveProcess.Section10.SpatialVagueBorelConsumer
public import SubdiffusiveProcess.Processes.E7.FellerFromResolvent
public import SubdiffusiveProcess.Section10.PhysicalAttachmentRestart
public import SubdiffusiveProcess.Processes.E7.E7Main
public import SubdiffusiveProcess.Probability.Diffusion.AnalyticBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierGrowth
public import SubdiffusiveProcess.Paper.Support.LimitPropertiesSuppliers
public import SubdiffusiveProcess.Paper.lim_invariance
public import SubdiffusiveProcess.Paper.prop_chaos_growth
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.inputs_local_coefficients_c11
public import SubdiffusiveProcess.Paper.inputs_classical_fot_part_process

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SubdiffusiveProcess.Paper

section MeasureInvarianceAttachment
/-! Attach the supplied actual chaos limit to the supplied actual S9 limit.
The universal-measure conclusion of prop_limit_properties is consumed here;
no invariance event or source-measure root is assumed. -/

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.Section10
open scoped ENNReal NNReal CompactlySupported


def aux_lim_thm_measure_SameLimitInvariant {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (w : BilateralField d) : Prop :=
  SemigroupSymmetric (P w) (infraredWeightedLimit H mu0 w) ∧
  (∀ (t : ℝ≥0) (f : SpatialCoordinates d → ℝ≥0∞), Measurable f →
    ∫⁻ x, (∫⁻ y, f y ∂P w t x) ∂infraredWeightedLimit H mu0 w =
      ∫⁻ x, f x ∂infraredWeightedLimit H mu0 w) ∧
  (∀ (t : ℝ≥0) (f : SpatialCoordinates d → ℝ≥0∞), Measurable f →
    ∫⁻ x, (∫⁻ path, f (path t) ∂K (w, x)) ∂infraredWeightedLimit H mu0 w =
      ∫⁻ x, f x ∂infraredWeightedLimit H mu0 w)

/-- Symmetry and conservativity imply both literal semigroup and path-law
formulas, through the actual singleton finite-dimensional identification. -/
theorem aux_lim_thm_measure_same_limit_invariant_of_symmetric {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (w : BilateralField d) (hP : (P w).IsConservative)
    (hlim : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (w, x) =
      SubMarkovKernelSemigroup.finiteSetKernel (P w) I x)
    (hs : SemigroupSymmetric (P w) (infraredWeightedLimit H mu0 w)) :
    aux_lim_thm_measure_SameLimitInvariant H mu0 P K w := by
  have hinv := aux_lim_invariance_of_symmetric (P w) hP
    (infraredWeightedLimit H mu0 w) hs
  refine ⟨hs, hinv, ?_⟩
  intro t f hf
  have hinner (x : SpatialCoordinates d) :
      ∫⁻ path, f (path t) ∂K (w, x) = ∫⁻ y, f y ∂P w t x := by
    have hmap := map_eval_eq_of_finsetEvaluation (P w) (K (w, x)) x t (by
      rw [← Kernel.map_apply K (ContinuousPath.measurable_finsetEvaluation _)]
      exact hlim {t} x)
    rw [← hmap, lintegral_map hf (continuous_eval_const t).measurable]
  simp_rw [hinner]
  exact hinv t f hf

/-- Actual-model application of the proved universal-measure symmetry
export. The supplied mu0 is the same actual unweighted cutoff vague limit;
the required speed-measure premise is derived, not assumed separately. -/
theorem aux_lim_thm_measure_same_limit_invariance_actual {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : ∀ w, (P w).IsConservative)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (hin : in_crossing M H PN KN)
    (hinput : aux_cutoff_lifetime_package_LocalInput M H KN)
    (hlim : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (w, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (P w) I x)
    (hconv : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      Tendsto (fun N => (chaosSampleLaw M).toMeasure
        {w : BilateralField d | ∃ x ∈ B, eps ≤ pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN N) (hKN N) w x)
          (jointPathProbabilityMeasure K hK w x)}) atTop (nhds 0))
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => chaosCutoff M N w) (mu0 w)) :
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, aux_lim_thm_measure_SameLimitInvariant H mu0 P K w := by
  have hwc := hc.mono fun w hw => infraredWeightedLimit_same_vague M H mu0 w hw
  have hmu : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      ∃ mu : Measure (SpatialCoordinates d),
        MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H w N) mu ∧
        IsLocallyFiniteMeasure mu := by
    filter_upwards [hwc] with w hw
    exact ⟨infraredWeightedLimit H mu0 w, by
      simpa only [cutoffSpeedMeasure_eq_weightedChaosCutoff] using hw,
      infraredWeightedLimit_locallyFinite H mu0 hl w⟩
  have hs := aux_prop_limit_properties_of_suppliers hd M H hH PN P hP KN hKN K hK
    hin hinput hlim hconv hmu
  filter_upwards [hs, hwc, hlim] with w hs hw hfdd
  exact aux_lim_thm_measure_same_limit_invariant_of_symmetric H mu0 P K w (hP w) hfdd
    (hs.2.2.2 (infraredWeightedLimit H mu0 w) (by
      simpa only [cutoffSpeedMeasure_eq_weightedChaosCutoff] using hw)
      (infraredWeightedLimit_locallyFinite H mu0 hl w))

/-- Select one measurable conull event after the complete pointwise bundle
has been proved AE. No measurable predicate or countability of starts/times
is required, and those quantifiers stay inside the one bundle. -/
theorem aux_lim_thm_measure_exists_common_measurable_event {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law] (Q : Ω → Prop)
    (hQ : ∀ᵐ w ∂law, Q w) :
    ∃ E : Set Ω, MeasurableSet E ∧ law E = 1 ∧ ∀ w ∈ E, Q w := by
  obtain ⟨N, hNsub, hNm, hNz⟩ := exists_measurable_superset_of_null (ae_iff.mp hQ)
  refine ⟨Nᶜ, hNm.compl, ?_, ?_⟩
  · rw [measure_compl hNm (by simp [hNz]), hNz, measure_univ, tsub_zero]
  · intro w hw
    by_contra hn
    exact hw (hNsub hn)
end MeasureInvarianceAttachment

section LimitMeasureProcessProperties
/-! Literal all-start S9 output and same-measure attachment. The process
predicate is copied from the current mfd_convergence AE conclusion. -/

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.Section10
open scoped ENNReal NNReal CompactlySupported


def aux_lim_thm_measure_ActualLimitProcessProperties {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (omega : BilateralField d) : Prop :=
            Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∧
            (∀ N, ∃ D :
                SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
                  (SpatialCoordinates d),
              (∀ mu, DenseRange (D.operator mu)) ∧
              SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
                (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
              ∀ (mu : Semigroup.PositiveShift)
                (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
                (x : SpatialCoordinates d),
                D.solution mu f x =
                  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
                    kernelIntegral (PN N omega (Real.toNNReal t)) f x) ∧
            (∀ N I x,
              (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
                SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) ∧
            (∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
            (∀ B : Set (SpatialCoordinates d), IsCompact B →
              ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ B,
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x) < epsilon) ∧
            (∀ (t : ℝ≥0) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
              Continuous (kernelIntegral (P omega t) f)) ∧
            (∃ mu : Measure (SpatialCoordinates d),
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure mu ∧ NullSingletonClass mu ∧ mu.IsOpenPosMeasure ∧
              SemigroupSymmetric (P omega) mu) ∧
            HasStrongMarkovRestart K omega ∧ HasFiniteMeanExits K omega

/-- Regularity of the same pair of measures; local finiteness is retained
explicitly for both measures. -/
def aux_lim_thm_measure_SameLimitMeasureRegular {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (w : BilateralField d) : Prop :=
  IsLocallyFiniteMeasure (mu0 w) ∧ NullSingletonClass (mu0 w) ∧ (mu0 w).IsOpenPosMeasure ∧
  IsLocallyFiniteMeasure (infraredWeightedLimit H mu0 w) ∧
  NullSingletonClass (infraredWeightedLimit H mu0 w) ∧
  (infraredWeightedLimit H mu0 w).IsOpenPosMeasure

/-- Transport the S9 speed-measure witness's regularity and symmetry by
uniqueness of the actual weighted vague limit. The returned measure is the
retained density-divergence mu0, not S9's existential auxiliary witness. -/
theorem aux_lim_thm_measure_same_limit_measure_attachment_of_process {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : ∀ w, (P w).IsConservative)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hs : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      aux_lim_thm_measure_ActualLimitProcessProperties M H PN P KN hKN K hK w)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, SameLimitDensityProperties M H mu0 w) :
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      aux_lim_thm_measure_SameLimitMeasureRegular H mu0 w ∧ aux_lim_thm_measure_SameLimitInvariant H mu0 P K w := by
  filter_upwards [hs, hc] with w hw hc
  rcases hw with ⟨_, _, _, hlim, _, _, _,
    ⟨mu, hmc, hml, hma, hms, hsym⟩, _, _⟩
  have hwl := infraredWeightedLimit_locallyFinite H mu0 hl w
  have heq : mu = infraredWeightedLimit H mu0 w := by
    let := hml
    let := hwl
    apply aux_lim_measure_vague_unique (fun N => weightedChaosCutoff M H N w)
      mu (infraredWeightedLimit H mu0 w)
    · simpa only [cutoffSpeedMeasure_eq_weightedChaosCutoff] using hmc
    · exact hc.2.2.2.2.1
  rw [heq] at hma hms hsym
  obtain ⟨ha0, hs0⟩ := unweighted_regularity_of_infrared_weighted (H w) (mu0 w) hma hms
  exact ⟨⟨hl w, ha0, hs0, hwl, hma, hms⟩,
    aux_lim_thm_measure_same_limit_invariant_of_symmetric H mu0 P K w (hP w) hlim hsym⟩
end LimitMeasureProcessProperties

section LimitMeasureUniversalInvariance
/-! The existing path/semigroup symmetry-limit proof, applied to a specified
locally finite actual speed-measure limit and an arbitrary convergent K.
The finite-cutoff local-diffusion supplier is kept explicit under a distinct
helper name; no reviewed root statement is changed. -/

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal CompactlySupported



/-- Actual finite-cutoff attachment needed at the reviewed root header.
The kernel in this interface is literally the supplied KN, at every start. -/
def aux_lim_thm_measure_CutoffLocalDiffusionSupplier (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] : Prop :=
  ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
  ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
    (∀ N, IsMarkovKernel (KN N)) → in_crossing M H PN KN →
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ N,
      LocalDiffusion (cutoffCoefficient M H w N) (cutoffSpeedDensity M H w N)
        (((KN N).comap (Prod.mk w) measurable_prodMk_left).map LifetimePath.ofContinuousPath)

/-- Universal-K invariance transport for the supplied SAME actual limit.
The local-diffusion premise belongs to this distinctly named helper only. -/
theorem aux_lim_thm_measure_same_limit_invariance_of_cutoff_localDiffusion
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN)
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ N w x, (KN N (w, x)).map LifetimePath.ofContinuousPath = L N w x)
    (hLloc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ N,
      LocalDiffusion (cutoffCoefficient M H w N) (cutoffSpeedDensity M H w N) (L N w))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hconv : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
        pathLevyProkhorovDist (jointPathProbabilityMeasure (KN N) (hKN N) w x)
          (jointPathProbabilityMeasure K hK w x) < eps)
    (mu : BilateralField d → Measure (SpatialCoordinates d))
    (hl : ∀ w, IsLocallyFiniteMeasure (mu w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H w N) (mu w)) :
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      ∀ (t : ℝ≥0) (f : SpatialCoordinates d → ℝ≥0∞), Measurable f →
        (∫⁻ x, (∫⁻ path, f (path t) ∂K (w, x)) ∂mu w) = ∫⁻ x, f x ∂mu w := by
  classical
  have hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N, StrongMarkov (L N omega) := by
    filter_upwards [hLloc] with omega hω N
    exact (hω N).1
  have hlocal := tight_fixed_cutoff hd M H hH PN KN hKN hin L hL hLloc
  have hstartN := in_cutoff_start_continuity hd M H hH PN KN hKN hin hlocal
  have hKcont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure K hK omega x) := by
    exact aux_lim_invariance_continuous_limit M
      (fun N omega x => jointPathProbabilityMeasure (KN N) (hKN N) omega x)
      (fun omega x => jointPathProbabilityMeasure K hK omega x) hconv hstartN
  have hrestartN := aux_limit_kernel_markov_passage_cutoff_restart hd M H PN KN hKN hin
  have hattachN := aux_limit_kernel_markov_passage_cutoff_attachment M H PN KN hin
  let κ : BilateralField d → Kernel (SpatialCoordinates d) (DiffusionPath d) := fun omega =>
    K.comap (Prod.mk omega) measurable_prodMk_left
  have hκ : ∀ omega, IsMarkovKernel (κ omega) := fun omega =>
    ⟨fun x => hK.isProbabilityMeasure (omega, x)⟩
  let Q : BilateralField d → Prop := fun omega =>
    (∀ x, (κ omega x).map (fun p => p 0) = Measure.dirac x) ∧
      (∀ x (t : ℝ≥0), (κ omega x).map (fun p => (p t, ContinuousPath.shift t p)) =
        ((κ omega x).map (fun p => p t)) ⊗ₘ κ omega)
  have hQ : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, Q omega := by
    filter_upwards [hKcont, hrestartN, hattachN.2, hconv] with omega hc hr ha hω
    let κs : ℕ → Kernel (SpatialCoordinates d) (DiffusionPath d) := fun N =>
      (KN N).comap (Prod.mk omega) measurable_prodMk_left
    have : ∀ N, IsMarkovKernel (κs N) := fun N =>
      ⟨fun x => (hKN N).isProbabilityMeasure (omega, x)⟩
    refine aux_limit_kernel_markov_passage_good κs (κ omega) hc ?_ ?_ ?_
    · intro B hB ε hε
      obtain ⟨N0, hN0⟩ := hω B hB ε hε
      filter_upwards [eventually_ge_atTop N0] with N hN y hy
      exact hN0 N hN y hy
    · intro N x
      have hmev : Measurable (ContinuousPath.finsetEvaluation
          (alpha := SpatialCoordinates d) ({0} : Finset ℝ≥0)) :=
        measurable_pi_iff.mpr (fun t => (continuous_eval_const ((t : ℝ≥0))).measurable)
      have h0 := map_eval_eq_of_finsetEvaluation (PN N omega) (KN N (omega, x)) x 0
        (by rw [← Kernel.map_apply _ hmev]; exact ha N {0} x)
      rw [(PN N omega).kernel_zero, Kernel.id_apply] at h0
      exact h0
    · intro N x t A hA F hF
      exact hr N x t A hA F hF
  let P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d) := fun omega =>
    if h : Q omega then
      aux_limit_kernel_markov_passage_marginalSemigroup (κ omega) h.1 h.2
    else idSemigroup
  have hP : ∀ omega, (P omega).IsConservative := by
    intro omega
    by_cases hω : Q omega
    · simp only [P, dite_eq_left hω]
      exact aux_limit_kernel_markov_passage_marginalSemigroup_isConservative _ _ _
    · simp only [P, dite_eq_right hω]
      exact isConservative_idSemigroup
  have hlim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x := by
    filter_upwards [hQ] with omega hω I x
    simp only [P, dite_eq_left hω]
    have hmev : Measurable (ContinuousPath.finsetEvaluation
        (alpha := SpatialCoordinates d) I) :=
      measurable_pi_iff.mpr (fun t => (continuous_eval_const ((t : ℝ≥0))).measurable)
    rw [Kernel.map_apply _ hmev]
    exact aux_limit_kernel_markov_passage_map_finsetEvaluation (κ omega) hω.1 hω.2 I x
  have hcutoff : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N, SemigroupSymmetric (PN N omega) (cutoffSpeedMeasure M H omega N) :=
    prop_limit_properties_cutoff_symmetry M H PN KN hin L hL hLloc hLstrong
  have hsym : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      SemigroupSymmetric (P omega) (mu omega) := by
    filter_upwards [hQ, hKcont, hstartN, hcutoff, hin.2.2, hconv, hlim, hc]
      with omega hQω hKω hNω hcutω hattω hconvω hlimω hmc
    exact aux_prop_limit_properties_symmetry_limit_fixed KN hKN K hK
      (fun N => PN N omega) (P omega) omega hlimω
      (fun N I x => hattω N I x) hNω hKω
      (fun N => cutoffSpeedMeasure M H omega N)
      (fun N => by
        simpa only [cutoffSpeedMeasure_eq_weightedChaosCutoff] using
          weightedChaosCutoff_isLocallyFinite M H N omega)
      hcutω (fun j => j) tendsto_id (by
        intro B hB eps heps
        obtain ⟨N0, hN0⟩ := hconvω B hB eps heps
        exact ⟨N0, fun j hj x hx => hN0 j hj x hx⟩) (mu omega) hmc (hl omega)
  filter_upwards [hsym, hQ, hKcont, hlim] with omega hsymω hQω hKω hlimω
  intro t f hf
  have hinv := aux_lim_invariance_of_symmetric (P omega) (hP omega) (mu omega) hsymω t f hf
  have hmap : ∀ x : SpatialCoordinates d,
      (K (omega, x)).map (fun w : DiffusionPath d => w t) = P omega t x := by
    intro x
    apply SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation (P omega) (K (omega, x)) x t
    rw [← Kernel.map_apply K (ContinuousPath.measurable_finsetEvaluation _)]
    exact hlimω ({t} : Finset ℝ≥0) x
  have hinner : ∀ x : SpatialCoordinates d,
      ∫⁻ y, f y ∂P omega t x =
        ∫⁻ w, f (w t) ∂K (omega, x) := by
    intro x
    rw [← hmap x, lintegral_map]
    · exact hf
    · exact (continuous_eval_const t).measurable
  calc
    ∫⁻ x, (∫⁻ w, f (w t) ∂K (omega, x)) ∂mu omega =
        ∫⁻ x, (∫⁻ y, f y ∂P omega t x) ∂mu omega := by
      congr 1
      funext x
      exact (hinner x).symm
    _ = ∫⁻ x, f x ∂mu omega := hinv
end LimitMeasureUniversalInvariance

section LimitMeasureRootData
/-! Actual limiting-measure data for the reviewed Section 10 roots.
Regularity is attached to the retained density/spatial witness by uniqueness,
independently of any choice of a limiting process. -/

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.Section10
open scoped ENNReal NNReal CompactlySupported



/-- The SAME measurable chaos limit has the complete density, spatial,
regularity and growth data needed by the specified roots. The extra witness
from `prop_chaos_growth` is identified with its weighted version and discarded. -/
theorem aux_lim_thm_measure_exists_same_limit_measure_root_data
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
      ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
      ∃ (mu0 : BilateralField d → Measure (SpatialCoordinates d))
        (hm : Measurable mu0) (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w)),
        Measurable (infraredWeightedLimit H mu0) ∧
        (∀ w, IsLocallyFiniteMeasure (infraredWeightedLimit H mu0 w)) ∧
        (∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          SameLimitDensityProperties M H mu0 w ∧ aux_lim_thm_measure_SameLimitMeasureRegular H mu0 w) ∧
        SameLimitSpatialLaws M mu0 ∧ SameLimitGrowthMoments M H mu0 p ∧
        (∀ᵐ w ∂(chaosSampleLaw M).toMeasure, SameLimitGrowth H mu0 w) ∧
        Tendsto (localRescaledCutoffLaw M) atTop (𝓝 (localLimitLaw M mu0 hl hm)) := by
  obtain ⟨deltaD, hdD, hD⟩ := exists_same_limit_spatial_growth_rescaledLaw hd p hp
  have heps : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  have hpG : (d : ℝ) < (4 * d + 1 : ℕ) * (1 / 2 : ℝ) := by
    push_cast
    nlinarith
  obtain ⟨deltaG, hdG, hG⟩ := prop_chaos_growth hd (1 / 2) heps (4 * d + 1) hpG
  refine ⟨min deltaD deltaG, lt_min hdD hdG, ?_⟩
  intro M hsmall H hH
  obtain ⟨mu0, hm, hl, hwm, hwl, hdensity, hspatial, hmoment, hgrowth, hlaw⟩ :=
    hD M H hH (hsmall.trans (min_le_left _ _))
  obtain ⟨muG, _, hreg, _⟩ := hG M H hH (hsmall.trans (min_le_right _ _))
  refine ⟨mu0, hm, hl, hwm, hwl, ?_, hspatial, hmoment, hgrowth, hlaw⟩
  filter_upwards [hdensity, hreg] with w hdw hgw
  have heq : muG w = infraredWeightedLimit H mu0 w := by
    let := hgw.2.1
    let := hwl w
    exact aux_lim_measure_vague_unique (fun N => weightedChaosCutoff M H N w)
      (muG w) (infraredWeightedLimit H mu0 w) hgw.1 hdw.2.2.2.2.1
  have ha : NullSingletonClass (infraredWeightedLimit H mu0 w) := heq ▸ hgw.2.2.2.1
  have hs : (infraredWeightedLimit H mu0 w).IsOpenPosMeasure := heq ▸ hgw.2.2.1
  obtain ⟨ha0, hs0⟩ := unweighted_regularity_of_infrared_weighted (H w) (mu0 w) ha hs
  exact ⟨hdw, hl w, ha0, hs0, hwl w, ha, hs⟩
end LimitMeasureRootData

section LimitMeasureCutoffAttachment
/-! The literal cutoff attachment already implies Feller semigroups.
This conclusion is discharged from the source resolvent and full FDDs;
local killed-generator/density properties remain separate suppliers. -/

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent



theorem aux_lim_thm_measure_actual_cutoff_feller_attachment
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN) :
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ N,
      ∃ D : C0ResolventDatum (SpatialCoordinates d),
      ∃ hdense : ∀ mu, DenseRange (D.operator mu),
        IsWeakEllipticResolvent (cutoffCoefficient M H w N) (cutoffSpeedDensity M H w N) D ∧
        PN N w = D.fellerKernelSemigroup hdense ∧ (PN N w).IsFellerKernelSemigroup := by
  filter_upwards [hin.1, hin.2.2] with w hres hfdd
  intro N
  obtain ⟨D, hdense, hweak, hlap⟩ := hres N
  let L := (KN N).comap (Prod.mk w) measurable_prodMk_left
  let : IsMarkovKernel (KN N) := hKN N
  let : IsMarkovKernel L := by dsimp [L]; infer_instance
  have hLfdd : ∀ I x, L.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (PN N w) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _),
      Kernel.comap_apply, ← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _)]
    exact hfdd N I x
  have h := E7.isFeller_of_realization_and_datum (PN N w) D hdense hlap L hLfdd
  exact ⟨D, hdense, hweak, h.1, h.2⟩
end LimitMeasureCutoffAttachment

section LimitMeasureCutoffLocalDiffusion
/-! Discharge the actual finite-cutoff local-diffusion interface from the
proved FOT part-process, Feller restart and native coefficient regularity.
The process is the supplied KN from in_crossing, at every starting point. -/

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Assumptions.CoefficientRegularity
open scoped ENNReal NNReal



theorem aux_limit_measure_fotPartProcess : E7.FOTPartProcess := by
  intro d m hm hpos E hE P hP hF K hK hfdd hassoc U hU
  exact inputs_classical_fot_part_process d m hm hpos E hE P hP hF K hK hfdd hassoc U hU

/-- Actual supplier, with no killed-density input and no small-disorder input.
Every-start identification comes from all FDDs of the supplied cutoff law. -/
theorem aux_lim_thm_measure_actual_cutoff_localDiffusion_supplier
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    aux_lim_thm_measure_CutoffLocalDiffusionSupplier d := by
  intro M H hH PN KN hKN hin
  have hc11 := inputs_local_coefficients_c11 M H hd hH
  filter_upwards [hin.1, hin.2.2, hc11] with w hres hfdd hregular
  intro N
  obtain ⟨D, hdense, hweak, hlap⟩ := hres N
  let L := (KN N).comap (Prod.mk w) measurable_prodMk_left
  let : IsMarkovKernel (KN N) := hKN N
  have hL : IsMarkovKernel L := by dsimp [L]; infer_instance
  have hLfdd : ∀ I x, L.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (PN N w) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _),
      Kernel.comap_apply, ← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _)]
    exact hfdd N I x
  have hcpos : ∀ x, 0 < cutoffCoefficient M H w N x := by
    intro x
    exact mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  have hrpos : ∀ x, 0 < cutoffSpeedDensity M H w N x := fun x => Real.exp_pos _
  have hc := E7.continuous_of_locallyC11 (hregular N).1
  have hr := E7.continuous_of_locallyC11 (hregular N).2
  have hgen := E7.e7_of_leaves SubdiffusiveProcess.Section10.PhysicalAttachment.fellerRestart
    aux_limit_measure_fotPartProcess d _ _ hcpos hrpos (hregular N).1 (hregular N).2
    (PN N w) (hin.2.1 N w) D hdense hweak hlap L hL hLfdd
  refine ⟨SubdiffusiveProcess.Probability.Diffusion.strongMarkov_of_restart hgen.1, ?_, ?_⟩
  · intro C hC
    exact ⟨coefficientOn_of_continuous_pos hc hcpos hC.isBounded,
      coefficientOn_of_continuous_pos hr hrpos hC.isBounded⟩
  · intro U hU hUb s hs f hf
    exact SubdiffusiveProcess.Probability.Diffusion.killedResolvent_clause_of_killedGenerator hgen.2 hU hUb
      (coefficientOn_of_continuous_pos hc hcpos hUb)
      (coefficientOn_of_continuous_pos hr hrpos hUb) hs hf
end LimitMeasureCutoffLocalDiffusion

section LimitMeasureRootConsumer
open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10
open scoped ENNReal NNReal




/-- The reversible measure `μ = e^H μ⁰` of the limiting process, from the stationary limit `μ⁰`
(`mu0`) and the infrared field `H`. -/
def aux_lim_thm_measure_weighted {d : ℕ} (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (omega : BilateralField d) :
    Measure (SpatialCoordinates d) :=
  (mu0 omega).withDensity (fun y => ENNReal.ofReal (Real.exp (H omega y)))

/-- Convergence of the quenched path laws `K_{N,x}^ω → K_x^ω`, uniformly in `x` on every compact
set, at the single environment `omega` (Theorem A(i), `eq:mfd-main-as`), for the rescaled cutoff
path kernels `KN` (attached by `in_crossing`); `K` is the limit kernel of Theorem A. -/
def aux_lim_thm_measure_ConvAt {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (omega : BilateralField d) : Prop :=
  ∀ B : Set (SpatialCoordinates d), IsCompact B →
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
      pathLevyProkhorovDist
        (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
        (jointPathProbabilityMeasure K hK omega x) < epsilon

/-! Complete reviewed measure-root conclusion, conditional only on the explicitly
named, separately routed actual cutoff attachment supplier. This helper does not
close the source root until that supplier is proved. -/

theorem aux_lim_thm_measure_of_cutoff_supplier
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (hlocal : aux_lim_thm_measure_CutoffLocalDiffusionSupplier d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        ∃ mu0 : BilateralField d → Measure (SpatialCoordinates d), Measurable mu0 ∧
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            MeasuresConvergeLocally (fun N => chaosCutoff M N omega) (mu0 omega) ∧
            MeasuresConvergeLocally (fun N => weightedChaosCutoff M H N omega)
              (aux_lim_thm_measure_weighted H mu0 omega) ∧
            IsLocallyFiniteMeasure (mu0 omega) ∧ NullSingletonClass (mu0 omega) ∧
            (mu0 omega).IsOpenPosMeasure ∧
            IsLocallyFiniteMeasure (aux_lim_thm_measure_weighted H mu0 omega) ∧
            NullSingletonClass (aux_lim_thm_measure_weighted H mu0 omega) ∧
            (aux_lim_thm_measure_weighted H mu0 omega).IsOpenPosMeasure ∧
            (∀ᵐ y ∂(volume : Measure (SpatialCoordinates d)),
              Tendsto (fun N => fineDensity M N omega y) atTop (𝓝 0)) ∧
            (∀ᵐ y ∂(mu0 omega), Tendsto (fun N => fineDensity M N omega y) atTop atTop) ∧
            (∀ᵐ y ∂(aux_lim_thm_measure_weighted H mu0 omega),
              Tendsto (fun N => fineDensity M N omega y) atTop atTop) ∧
            mu0 omega ⟂ₘ (volume : Measure (SpatialCoordinates d)) ∧
            aux_lim_thm_measure_weighted H mu0 omega ⟂ₘ (volume : Measure (SpatialCoordinates d))) ∧
          (¬ ∃ m : Measure (SpatialCoordinates d),
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, mu0 omega = m) ∧
          (∀ A : Set (SpatialCoordinates d), MeasurableSet A →
            (∫⁻ omega, mu0 omega A ∂(chaosSampleLaw M).toMeasure) = volume A) ∧
          (∀ z : SpatialCoordinates d,
            (chaosSampleLaw M).toMeasure.map (fun omega => (mu0 omega).map (fun y => y + z)) =
              (chaosSampleLaw M).toMeasure.map mu0) ∧
          (∀ A B : Set (SpatialCoordinates d), MeasurableSet A → MeasurableSet B →
            (∃ c : ℝ, (d : ℝ) < c ∧ ∀ a ∈ A, ∀ b ∈ B, c ≤ ∑ i, (a i - b i) ^ 2) →
            Indep (MeasurableSpace.comap (fun omega => (mu0 omega).restrict A) inferInstance)
              (MeasurableSpace.comap (fun omega => (mu0 omega).restrict B) inferInstance)
              (chaosSampleLaw M).toMeasure) ∧
          (∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
            (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
            (hKN : ∀ N, IsMarkovKernel (KN N)), in_crossing M H PN KN →
            ∀ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
              (hK : IsMarkovKernel K),
              (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                aux_lim_thm_measure_ConvAt KN hKN K hK omega) →
              ∃ Omega0 : Set (BilateralField d), MeasurableSet Omega0 ∧
                (chaosSampleLaw M).toMeasure Omega0 = 1 ∧
                ∀ omega ∈ Omega0,
                  aux_lim_thm_measure_ConvAt KN hKN K hK omega ∧
                  MeasuresConvergeLocally (fun N => weightedChaosCutoff M H N omega)
                    (aux_lim_thm_measure_weighted H mu0 omega) ∧
                  ∀ (t : ℝ≥0) (f : SpatialCoordinates d → ℝ≥0∞), Measurable f →
                    (∫⁻ x, (∫⁻ w, f (w t) ∂K (omega, x))
                      ∂(aux_lim_thm_measure_weighted H mu0 omega)) =
                      ∫⁻ x, f x ∂(aux_lim_thm_measure_weighted H mu0 omega)) := by
  obtain ⟨delta0, hd0, hdata⟩ := aux_lim_thm_measure_exists_same_limit_measure_root_data hd 1 (by norm_num)
  refine ⟨delta0, hd0, ?_⟩
  intro M hsmall H hH
  obtain ⟨mu0, hm, hl, hwm, hwl, hall, hspatial, _, _, _⟩ := hdata M hsmall H hH
  rcases hspatial with ⟨hmean, hnd, hstat, hind⟩
  refine ⟨mu0, hm, ?_, hnd, hmean, hstat, hind, ?_⟩
  · filter_upwards [hall] with w hw
    rcases hw.1 with ⟨hc, hs0, hvol, h0, hwc, hsw, hw'⟩
    rcases hw.2 with ⟨hl0, ha0, hp0, hlw, haw, hpw⟩
    exact ⟨hc, hwc, hl0, ha0, hp0, hlw, haw, hpw, hvol, h0, hw', hs0, hsw⟩
  · intro PN KN hKN hin K hK hconv
    let L := fun N w =>
      ((KN N).comap (Prod.mk w) measurable_prodMk_left).map LifetimePath.ofContinuousPath
    have hL : ∀ N w x, (KN N (w, x)).map LifetimePath.ofContinuousPath = L N w x := by
      intro N w x
      rw [Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath, Kernel.comap_apply]
    have hloc := hlocal M H hH PN KN hKN hin
    have hweighted : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
        MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H w N)
          (infraredWeightedLimit H mu0 w) := by
      filter_upwards [hall] with w hw
      simpa only [cutoffSpeedMeasure_eq_weightedChaosCutoff] using hw.1.2.2.2.2.1
    have hinv := aux_lim_thm_measure_same_limit_invariance_of_cutoff_localDiffusion hd M H hH PN KN hKN
      hin L hL hloc K hK hconv (infraredWeightedLimit H mu0) hwl hweighted
    have hevent : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
        aux_lim_thm_measure_ConvAt KN hKN K hK w ∧
        MeasuresConvergeLocally (fun N => weightedChaosCutoff M H N w)
          (aux_lim_thm_measure_weighted H mu0 w) ∧
        ∀ (t : ℝ≥0) (f : SpatialCoordinates d → ℝ≥0∞), Measurable f →
          (∫⁻ x, (∫⁻ path, f (path t) ∂K (w, x))
            ∂aux_lim_thm_measure_weighted H mu0 w) =
            ∫⁻ x, f x ∂aux_lim_thm_measure_weighted H mu0 w := by
      filter_upwards [hconv, hall, hinv] with w hw hdw hiw
      exact ⟨hw, hdw.1.2.2.2.2.1, hiw⟩
    exact aux_lim_thm_measure_exists_common_measurable_event _ _ hevent
end LimitMeasureRootConsumer

section LimMeasurePrincipal
open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal


/-- Theorem `lim:thm-measure` (The limiting measures), paper label `lim:thm-measure` (with the
definitions of `μ⁰`, `μ = e^H μ⁰` of the preceding paragraph, paper label `lim:thm-measure`).

`μ⁰` is the measurable (in the layers) limit of the stationary martingale `μ_N⁰ = ρ_N dx`
(`chaosCutoff`, `ρ_N = fineDensity`), and `μ = e^H μ⁰` the limit of `μ_N` (`weightedChaosCutoff`);
both are locally finite, nonatomic, of full support.
(i) Stationarity: `μ⁰` is stationary (its law is invariant under every translation), not
deterministic, `𝐄[μ⁰(dx)] = dx`, and its restrictions to two sets at distance greater than `√d`
(some `c > d` with all squared distances `≥ c`) are independent.
(ii) Singularity: almost surely `ρ_N(x) → 0` for Lebesgue-almost every `x`, and `ρ_N(x) → ∞` for
`μ⁰`-almost every and `μ`-almost every `x`; both limits are singular with respect to Lebesgue.
(iii) Invariance: for every limit kernel `K` of the quenched path laws (Theorem A(i)) there is an
event `Ω_0` of full probability, on which the path laws converge and `μ_N → μ` locally weakly, such
that for every environment in `Ω_0`, every `t ≥ 0` and every nonnegative Borel `f`,
`∫ P_t^ω f dμ^ω = ∫ f dμ^ω`. -/
theorem lim_thm_measure
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        ∃ mu0 : BilateralField d → Measure (SpatialCoordinates d), Measurable mu0 ∧
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            MeasuresConvergeLocally (fun N => chaosCutoff M N omega) (mu0 omega) ∧
            MeasuresConvergeLocally (fun N => weightedChaosCutoff M H N omega)
              (aux_lim_thm_measure_weighted H mu0 omega) ∧
            IsLocallyFiniteMeasure (mu0 omega) ∧ NullSingletonClass (mu0 omega) ∧
            (mu0 omega).IsOpenPosMeasure ∧
            IsLocallyFiniteMeasure (aux_lim_thm_measure_weighted H mu0 omega) ∧
            NullSingletonClass (aux_lim_thm_measure_weighted H mu0 omega) ∧
            (aux_lim_thm_measure_weighted H mu0 omega).IsOpenPosMeasure ∧
            (∀ᵐ y ∂(volume : Measure (SpatialCoordinates d)),
              Tendsto (fun N => fineDensity M N omega y) atTop (𝓝 0)) ∧
            (∀ᵐ y ∂(mu0 omega), Tendsto (fun N => fineDensity M N omega y) atTop atTop) ∧
            (∀ᵐ y ∂(aux_lim_thm_measure_weighted H mu0 omega),
              Tendsto (fun N => fineDensity M N omega y) atTop atTop) ∧
            mu0 omega ⟂ₘ (volume : Measure (SpatialCoordinates d)) ∧
            aux_lim_thm_measure_weighted H mu0 omega ⟂ₘ (volume : Measure (SpatialCoordinates d))) ∧
          (¬ ∃ m : Measure (SpatialCoordinates d),
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, mu0 omega = m) ∧
          (∀ A : Set (SpatialCoordinates d), MeasurableSet A →
            (∫⁻ omega, mu0 omega A ∂(chaosSampleLaw M).toMeasure) = volume A) ∧
          (∀ z : SpatialCoordinates d,
            (chaosSampleLaw M).toMeasure.map (fun omega => (mu0 omega).map (fun y => y + z)) =
              (chaosSampleLaw M).toMeasure.map mu0) ∧
          (∀ A B : Set (SpatialCoordinates d), MeasurableSet A → MeasurableSet B →
            (∃ c : ℝ, (d : ℝ) < c ∧ ∀ a ∈ A, ∀ b ∈ B, c ≤ ∑ i, (a i - b i) ^ 2) →
            Indep (MeasurableSpace.comap (fun omega => (mu0 omega).restrict A) inferInstance)
              (MeasurableSpace.comap (fun omega => (mu0 omega).restrict B) inferInstance)
              (chaosSampleLaw M).toMeasure) ∧
          (∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
            (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
            (hKN : ∀ N, IsMarkovKernel (KN N)), in_crossing M H PN KN →
            ∀ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
              (hK : IsMarkovKernel K),
              (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                aux_lim_thm_measure_ConvAt KN hKN K hK omega) →
              ∃ Omega0 : Set (BilateralField d), MeasurableSet Omega0 ∧
                (chaosSampleLaw M).toMeasure Omega0 = 1 ∧
                ∀ omega ∈ Omega0,
                  aux_lim_thm_measure_ConvAt KN hKN K hK omega ∧
                  MeasuresConvergeLocally (fun N => weightedChaosCutoff M H N omega)
                    (aux_lim_thm_measure_weighted H mu0 omega) ∧
                  ∀ (t : ℝ≥0) (f : SpatialCoordinates d → ℝ≥0∞), Measurable f →
                    (∫⁻ x, (∫⁻ w, f (w t) ∂K (omega, x))
                      ∂(aux_lim_thm_measure_weighted H mu0 omega)) =
                      ∫⁻ x, f x ∂(aux_lim_thm_measure_weighted H mu0 omega)) := by
  exact aux_lim_thm_measure_of_cutoff_supplier hd (aux_lim_thm_measure_actual_cutoff_localDiffusion_supplier hd)

end LimMeasurePrincipal

end SubdiffusiveProcess.Paper
