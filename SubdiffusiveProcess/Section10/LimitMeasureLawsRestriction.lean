module

public import SubdiffusiveProcess.Section10.LimitMeasureLawsRestrictionLocal

@[expose] public section

/-!
# The same limit's local Giry-measurable restriction representatives

A bind of the supplied measure against Mathlib's existing conditional kernel
is a local measure-valued map. The local open-mass representatives force its
agreement with that very same restriction. A countable open pi-system and a
finite ball cover put measure equality on one event. This does not construct
another chaos limit or assume a law property of the supplied limit.
-/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess Filter Topology

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Countably many open mass equalities determine the same locally finite
measure on one event. The other measure need not be locally finite beforehand. -/
theorem ae_measure_eq_of_open_mass_ae {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (mu nu : Omega → Measure (SpatialCoordinates d))
    (hl : ∀ᵐ w ∂P, IsLocallyFiniteMeasure (mu w))
    (ho : ∀ O : Set (SpatialCoordinates d), IsOpen O →
      (fun w => mu w O) =ᵐ[P] fun w => nu w O) : mu =ᵐ[P] nu := by
  classical
  let I := Sum (TopologicalSpace.countableBasis (SpatialCoordinates d)) ℕ
  let D : I → Set (SpatialCoordinates d) := Sum.elim (fun b => b.1)
    (fun n => Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1))
  have hD : ∀ i, IsOpen (D i) := by
    intro i
    cases i with
    | inl b => exact TopologicalSpace.isOpen_of_mem_countableBasis b.property
    | inr n => exact Metric.isOpen_ball
  let sets (s : Finset I) : Set (SpatialCoordinates d) := ⋂ i ∈ s, D i
  let C := Set.range sets
  have hsets : ∀ s, IsOpen (sets s) := fun s => isOpen_biInter_finset (fun i _ => hD i)
  have hsingle (i : I) : sets {i} = D i := by simp only [sets, Finset.mem_singleton,
    Set.iInter_iInter_eq_left]
  have hCopen : ∀ O ∈ C, IsOpen O := by
    rintro O ⟨s, rfl⟩
    exact hsets s
  have hCpi : IsPiSystem C := by
    rintro O ⟨s, rfl⟩ V ⟨t, rfl⟩ _
    refine ⟨s ∪ t, ?_⟩
    ext x
    simp only [sets, Set.mem_iInter, Finset.mem_union, or_imp, forall_and,
      Set.mem_inter_iff]
  have hbsub : TopologicalSpace.countableBasis (SpatialCoordinates d) ⊆ C := by
    intro O hO
    exact ⟨{Sum.inl ⟨O, hO⟩}, hsingle _⟩
  have hgen : (inferInstance : MeasurableSpace (SpatialCoordinates d)) =
      MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · calc
        (inferInstance : MeasurableSpace (SpatialCoordinates d)) =
            MeasurableSpace.generateFrom (TopologicalSpace.countableBasis (SpatialCoordinates d)) := by
              exact (BorelSpace.measurable_eq (α := SpatialCoordinates d)).trans
                (TopologicalSpace.isBasis_countableBasis _).borel_eq_generateFrom
        _ ≤ MeasurableSpace.generateFrom C := MeasurableSpace.generateFrom_mono hbsub
    · exact MeasurableSpace.generateFrom_le (fun O hO => (hCopen O hO).measurableSet)
  have heq : ∀ᵐ w ∂P, ∀ s : Finset I, mu w (sets s) = nu w (sets s) := by
    rw [ae_all_iff]
    intro s
    exact ho _ (hsets s)
  have hcover : (⋃ n : ℕ, Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt (dist x (0 : SpatialCoordinates d))
    exact Set.mem_iUnion.mpr ⟨n, Metric.mem_ball.mpr (by linarith)⟩
  filter_upwards [hl, heq] with w hw hweq
  let : IsLocallyFiniteMeasure (mu w) := hw
  apply Measure.ext_of_generateFrom_of_iUnion C
    (fun n => Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) hgen hCpi hcover
  · intro n
    exact ⟨{Sum.inr n}, hsingle _⟩
  · intro n
    exact (measure_ball_lt_top (μ := mu w) (x := (0 : SpatialCoordinates d))
      (r := (n : ℝ) + 1)).ne
  · rintro O ⟨s, rfl⟩
    exact hweq s

/-- A local version built by averaging the SAME supplied restriction through
the existing conditional kernel. Its equality to the actual restriction is
proved below, rather than postulated as a new premise. -/
def localRestrictionVersion {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (U : Set (SpatialCoordinates d)) (w : BilateralField d) : Measure (SpatialCoordinates d) :=
  (condExpKernel (chaosSampleLaw M).toMeasure (fineSpatialSigma U) w).bind
    (fun v => (mu0 v).restrict U)

/-- The version uses the literal Giry sigma algebra, hence all Borel mass
evaluations are locally measurable simultaneously. -/
theorem measurable_local_restriction_version {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (U : Set (SpatialCoordinates d)) (hU : MeasurableSet U) :
    @Measurable (BilateralField d) (Measure (SpatialCoordinates d))
      (fineSpatialSigma U) inferInstance (localRestrictionVersion M mu0 U) :=
  (Measure.measurable_bind' (same_limit_restriction_measurable mu0 hm U hU)).comp
    (condExpKernel (chaosSampleLaw M).toMeasure (fineSpatialSigma U)).measurable

/-- The version agrees with the SAME actual limit restriction on one event.
Every open set is allowed, including empty and unbounded regions. -/
theorem local_restriction_version_ae {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (hl : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, IsLocallyFiniteMeasure (mu0 w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => chaosCutoff M N w) (mu0 w))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) :
    localRestrictionVersion M mu0 U =ᵐ[(chaosSampleLaw M).toMeasure]
      fun w => (mu0 w).restrict U := by
  apply (ae_measure_eq_of_open_mass_ae (chaosSampleLaw M).toMeasure
    (fun w => (mu0 w).restrict U) (localRestrictionVersion M mu0 U)
    (hl.mono (fun w hw => by let := hw; infer_instance)) ?_).symm
  intro O hO
  obtain ⟨g, hg, heq⟩ := same_limit_open_mass_local M mu0 hl hc U O hU hO
  have hk := conditional_kernel_local_lintegral_ae (fineSpatialSigma U)
    (chaosSampleLaw M).toMeasure (fine_spatial_sigma_le U)
    (fun w => (mu0 w).restrict U O) g hg heq.symm
  filter_upwards [hk] with w hw
  exact (Measure.bind_apply hO.measurableSet
    (same_limit_restriction_measurable mu0 hm U hU.measurableSet).aemeasurable).trans hw |>.symm

/-- The requested same-limit local Giry representative, for every Borel
subset of an open source region, including arbitrary unbounded subsets. -/
theorem same_limit_borel_restriction_local {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (hl : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, IsLocallyFiniteMeasure (mu0 w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => chaosCutoff M N w) (mu0 w))
    (U A : Set (SpatialCoordinates d)) (hU : IsOpen U) (hA : MeasurableSet A) (hAU : A ⊆ U) :
    ∃ F : BilateralField d → Measure (SpatialCoordinates d),
      @Measurable (BilateralField d) (Measure (SpatialCoordinates d))
        (fineSpatialSigma U) inferInstance F ∧
      F =ᵐ[(chaosSampleLaw M).toMeasure] fun w => (mu0 w).restrict A := by
  refine ⟨fun w => (localRestrictionVersion M mu0 U w).restrict A,
    (measurable_measure_restriction A hA).comp
      (measurable_local_restriction_version M mu0 hm U hU.measurableSet), ?_⟩
  filter_upwards [local_restriction_version_ae M mu0 hm hl hc U hU] with w hw
  rw [hw, Measure.restrict_restrict hA, Set.inter_eq_left.mpr hAU]

end SubdiffusiveProcess.Section10
