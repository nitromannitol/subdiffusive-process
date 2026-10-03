module

public import SubdiffusiveProcess.Paper.prop_conc_resampled_layer_coefficient
public import SubdiffusiveProcess.Probability.ResampledLimit
public import SubdiffusiveProcess.Lnorm.CutoffVolumeResponseMeasurability
public import SubdiffusiveProcess.Sobolev.PotentialResponses
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.Tactic

@[expose] public section

/-! Law transfer for weighted identification.  Resampling one non-positive layer of the chaos sample
law by an independent layer draw preserves the law (the resampled field is again a typical field), and
almost sure properties of the represented field that are measurable events of the field pass to the
chaos law and hence to the resampled configuration.  The measurable events are the convergence of
the actual cutoff volume-response operators (operator norm) and of the actual affine responses. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
namespace Paper
noncomputable section

section Resampling

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Replacing the layer `j` of a chaos-distributed field by an independent draw from the law of that
layer gives a chaos-distributed field. -/
theorem aux_prop_conc_weighted_identification_transfer_update_pair
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℤ) :
    MeasurePreserving
      (fun w : BilateralField d × C(SpatialCoordinates d, ℝ) => Function.update w.1 j w.2)
      ((chaosSampleLaw M).toMeasure.prod
        (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure)
      (chaosSampleLaw M).toMeasure := by
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let νlayer : Measure (C(SpatialCoordinates d, ℝ)) :=
    (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure
  have hμ : μ = Measure.infinitePi (fun i : ℤ =>
      (scaledLayerLaw d (chaosRootFieldLaw M) i : Measure C(SpatialCoordinates d, ℝ))) := rfl
  have hlayer : νlayer = (scaledLayerLaw d (chaosRootFieldLaw M) j :
      Measure C(SpatialCoordinates d, ℝ)) := rfl
  have hmap_eval : Measure.map (fun e : BilateralField d => e j) μ = νlayer := by
    rw [hμ, hlayer]
    exact Measure.infinitePi_map_eval _ j
  have hg_meas : Measurable fun z : BilateralField d × BilateralField d => (z.1, z.2 j) :=
    Measurable.prod (f := fun z : BilateralField d × BilateralField d => (z.1, z.2 j))
      measurable_fst ((measurable_pi_apply j).comp measurable_snd)
  have hg_map : Measure.map (fun z : BilateralField d × BilateralField d => (z.1, z.2 j))
      (μ.prod μ) = μ.prod νlayer := by
    have h := Measure.map_prod_map μ μ measurable_id (measurable_pi_apply j)
    rw [Measure.map_id, hmap_eval] at h
    exact h.symm
  have hmp := SubdiffusiveProcess.Probability.measurePreserving_update_infinitePi
    (fun i : ℤ => (scaledLayerLaw d (chaosRootFieldLaw M) i :
      Measure C(SpatialCoordinates d, ℝ))) j
  have hmp' : MeasurePreserving
      (fun z : BilateralField d × BilateralField d => Function.update z.1 j (z.2 j))
      (μ.prod μ) μ := by
    rw [hμ]
    exact hmp
  have hU : Measurable
      (fun w : BilateralField d × C(SpatialCoordinates d, ℝ) => Function.update w.1 j w.2) :=
    aux_prop_conc_resampled_update_measurable j
  refine ⟨hU, ?_⟩
  have hcomp : (fun w : BilateralField d × C(SpatialCoordinates d, ℝ) => Function.update w.1 j w.2) ∘
      (fun z : BilateralField d × BilateralField d => (z.1, z.2 j)) =
      fun z : BilateralField d × BilateralField d => Function.update z.1 j (z.2 j) := rfl
  calc Measure.map (fun w : BilateralField d × C(SpatialCoordinates d, ℝ) =>
        Function.update w.1 j w.2) (μ.prod νlayer)
      = Measure.map (fun w : BilateralField d × C(SpatialCoordinates d, ℝ) =>
          Function.update w.1 j w.2)
          (Measure.map (fun z : BilateralField d × BilateralField d => (z.1, z.2 j))
            (μ.prod μ)) := by rw [hg_map]
    _ = Measure.map ((fun w : BilateralField d × C(SpatialCoordinates d, ℝ) =>
          Function.update w.1 j w.2) ∘
          (fun z : BilateralField d × BilateralField d => (z.1, z.2 j))) (μ.prod μ) :=
        Measure.map_map hU hg_meas
    _ = μ := by rw [hcomp]; exact hmp'.map_eq

/-- The resampling map of a represented field, on the product with the layer law, is measure preserving
onto the chaos law. -/
theorem prop_conc_weighted_identification_transfer
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℤ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure) :
    MeasurePreserving
      (fun w : Ω × C(SpatialCoordinates d, ℝ) => Function.update (field w.1) j w.2)
      (P.prod (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure)
      (chaosSampleLaw M).toMeasure := by
  have h1 : MeasurePreserving (Prod.map field id)
      (P.prod (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure)
      ((chaosSampleLaw M).toMeasure.prod (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure) :=
    MeasurePreserving.prod hfield
      (MeasurePreserving.id (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure)
  exact (aux_prop_conc_weighted_identification_transfer_update_pair M j).comp h1

end Resampling

section Transfer

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- An almost sure statement about a represented field whose event is measurable holds for a.e. point
of the law. -/
theorem aux_prop_conc_weighted_identification_transfer_ae
    {P : Measure Ω} {μ : Measure X} {field : Ω → X}
    (hfield : MeasurePreserving field P μ) {S : Set X} (hS : MeasurableSet S)
    (h : ∀ᵐ ω ∂P, field ω ∈ S) : ∀ᵐ x ∂μ, x ∈ S := by
  rw [← hfield.map_eq]
  exact (ae_map_iff hfield.measurable.aemeasurable hS).2 h

/-- Existence of a limit of a strongly measurable sequence transfers from a represented field to its
law; the codomain is complete but need not be separable. -/
theorem aux_prop_conc_weighted_identification_transfer_tendsto
    {P : Measure Ω} {μ : Measure X} {field : Ω → X}
    (hfield : MeasurePreserving field P μ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (u : ℕ → X → E) (hu : ∀ n, StronglyMeasurable (u n))
    (h : ∀ᵐ ω ∂P, ∃ c, Tendsto (fun n => u n (field ω)) atTop (𝓝 c)) :
    ∀ᵐ x ∂μ, ∃ c, Tendsto (fun n => u n x) atTop (𝓝 c) :=
  aux_prop_conc_weighted_identification_transfer_ae hfield
    (StronglyMeasurable.measurableSet_exists_tendsto hu) h

/-- Convergence in operator norm of strongly measurable operators on a Hilbert domain is a measurable
event; the space of bounded operators is complete but not separable. -/
theorem aux_prop_conc_weighted_identification_transfer_operator_event
    {d : ℕ} {X : Type*} [MeasurableSpace X] (Q : Opens (SpatialCoordinates d))
    (u : ℕ → X → (DomainL2 Q →L[ℝ] DomainL2 Q)) (hu : ∀ n, StronglyMeasurable (u n)) :
    MeasurableSet {x | ∃ G, Tendsto (fun n => u n x) atTop (𝓝 G)} := by
  haveI : IsCompletelyMetrizableSpace (DomainL2 Q →L[ℝ] DomainL2 Q) :=
    @MetricSpace.toIsCompletelyMetrizableSpace _ _ inferInstance
  exact StronglyMeasurable.measurableSet_exists_tendsto hu

end Transfer

section Measurability

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The actual volume-response operator of the cutoff coefficient is strongly measurable in the field. -/
theorem aux_prop_conc_weighted_identification_transfer_operator_measurable
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) :
    StronglyMeasurable (fun om : BilateralField d =>
      volumeResponseOperator S (Lane4.cutoffPositiveCoefficient M H om N z hr)) :=
  stronglyMeasurable_cutoffVolumeResponseOperator M H hH N z r hr S

/-- The actual affine Dirichlet response of the cutoff coefficient is measurable in the field. -/
theorem aux_prop_conc_weighted_identification_transfer_response_measurable
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (p : Fin d → ℝ) :
    Measurable (fun om : BilateralField d =>
      affineDirichletResponse (centeredCube_isBounded z hr) hP
        (Lane4.cutoffPositiveCoefficient M H om N z hr) p) := by
  have hpot := Lnorm.stronglyMeasurable_cutoffPotential_Lp M H hH N z r hr
  have hcont := continuous_dirichletResponse_potential (killedResponseSpace hP)
    (affineSobolev (centeredCube_isBounded z hr) p 0)
  have hsm := hcont.comp_stronglyMeasurable hpot
  have hfun : (fun om : BilateralField d =>
      affineDirichletResponse (centeredCube_isBounded z hr) hP
        (Lane4.cutoffPositiveCoefficient M H om N z hr) p) =
      (fun g => dirichletResponse (killedResponseSpace hP) (expPotentialCoefficient g)
        (affineSobolev (centeredCube_isBounded z hr) p 0)) ∘
      (fun om : BilateralField d => Lnorm.proxy_pot (H om) M N om z r hr) := by
    funext om
    simp only [Function.comp_apply, affineDirichletResponse, Lnorm.proxy_pot_eq_coefficient]
  rw [hfun]
  exact hsm.measurable

end Measurability

end
end Paper
