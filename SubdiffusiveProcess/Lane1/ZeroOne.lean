import SubdiffusiveProcess.Lane1.TailNull
import SubdiffusiveProcess.Lane1.LayerFiltration
import SubdiffusiveProcess.Lane3.LevyUpward

/-!
# The zero-one law for the limiting chaos

An open set is null for the limiting chaos exactly when the tail functional of
every Urysohn function of its exhaustion vanishes, and that condition reads
only the layers beyond any fixed generation.  The indicator of the event is
therefore almost surely equal to a tail-measurable variable at every stage, so
its conditional expectation along the head filtration is its mean at every
stage, and Levy's upward theorem makes it almost surely constant.  An indicator
that is almost surely constant has probability zero or one.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped CompactlySupported ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Kolmogorov's zero-one law for the event that the limiting chaos gives an
open set no mass. -/
theorem chaos_zero_one_open
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu : BilateralField d → Measure (SpatialCoordinates d))
    (hmeas : Measurable mu)
    (hlocfin : ∀ omega, IsLocallyFiniteMeasure (mu omega))
    (hconv : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally
        (fun N => weightedChaosCutoff M H N omega) (mu omega))
    {U : Set (SpatialCoordinates d)} (hU : IsOpen U) :
    (chaosSampleLaw M).toMeasure {omega | mu omega U = 0} = 0 ∨
      (chaosSampleLaw M).toMeasure {omega | mu omega U = 0} = 1 := by
  classical
  haveI : IsProbabilityMeasure ((chaosSampleLaw M).toMeasure) := inferInstance
  set P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  set A : Set (BilateralField d) := {omega | mu omega U = 0} with hAdef
  have hAmeas : MeasurableSet A :=
    ((Measure.measurable_coe hU.measurableSet).comp hmeas)
      (measurableSet_singleton 0)
  set g : BilateralField d → ℝ := A.indicator (fun _ => 1) with hgdef
  have hgint : Integrable g P := (integrable_const (1 : ℝ)).indicator hAmeas
  set B : ℕ → Set (BilateralField d) := fun k =>
    ⋂ n : ℕ, {omega | tailTestLimsup M (urysohnSeq hU n) (k + 1) omega = 0}
    with hBdef
  have hBmeas : ∀ k, MeasurableSet[tailSigma (d := d) k] (B k) := by
    intro k
    refine MeasurableSet.iInter fun n => ?_
    exact (measurable_tailTestLimsup_comap M (urysohnSeq hU n) (k + 1))
      (measurableSet_singleton 0)
  have hABae : ∀ k, A =ᵐ[P] B k := by
    intro k
    refine Filter.eventuallyEq_set.mpr ?_
    filter_upwards [hconv] with omega homega
    haveI := hlocfin omega
    have hiff := measure_eq_zero_iff_tail M H k omega (mu omega) homega hU
    constructor
    · intro hmem
      exact Set.mem_iInter.mpr fun n => hiff.mp hmem n
    · intro hmem
      exact hiff.mpr fun n => Set.mem_iInter.mp hmem n
  have hgB : ∀ k, g =ᵐ[P] (B k).indicator (fun _ => (1 : ℝ)) := fun k =>
    indicator_ae_eq_of_ae_eq_set (hABae k)
  have hcondmc : ∀ k, g =ᵐ[P] P[g|tailSigma (d := d) k] := by
    intro k
    have hstr : StronglyMeasurable[tailSigma (d := d) k]
        ((B k).indicator (fun _ => (1 : ℝ))) :=
      stronglyMeasurable_const.indicator (hBmeas k)
    have hintB : Integrable ((B k).indicator (fun _ => (1 : ℝ))) P :=
      hgint.congr (hgB k)
    refine (hgB k).trans (Filter.EventuallyEq.trans ?_ (condExp_congr_ae (hgB k).symm))
    exact Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable (tailSigma_le k) hstr hintB).symm
  have hconstk : ∀ k, P[g|layerFiltration (d := d) k] =ᵐ[P] fun _ => ∫ w, g w ∂P :=
    fun k => Lane3.condExp_eq_integral_of_ae_condExp_of_indep
      (tailSigma (d := d) k) (headSigma (d := d) k) (tailSigma_le k)
      (headSigma_le k) (indep_tailSigma_headSigma M k) g hgint (hcondmc k)
  have hgmeas : StronglyMeasurable[⨆ n : ℕ, layerFiltration (d := d) n] g :=
    (stronglyMeasurable_const.indicator hAmeas).mono le_iSup_headSigma
  have hfinal : g =ᵐ[P] fun _ => ∫ w, g w ∂P :=
    Lane3.ae_eq_const_of_condExp_eq_const layerFiltration g (∫ w, g w ∂P)
      hgint hgmeas hconstk
  by_cases hc1 : (∫ w, g w ∂P) = 1
  · right
    have hcompl : P Aᶜ = 0 := by
      have hae : ∀ᵐ omega ∂P, omega ∈ A := by
        filter_upwards [hfinal] with omega hom
        by_contra hmem
        rw [hgdef, Set.indicator_of_notMem hmem] at hom
        exact zero_ne_one (hom.trans hc1)
      rw [ae_iff] at hae
      simpa using hae
    exact (prob_compl_eq_zero_iff hAmeas).mp hcompl
  · left
    have hae : ∀ᵐ omega ∂P, omega ∉ A := by
      filter_upwards [hfinal] with omega hom
      intro hmem
      rw [hgdef, Set.indicator_of_mem hmem] at hom
      exact hc1 hom.symm
    rw [ae_iff] at hae
    simpa using hae

end SubdiffusiveProcess
