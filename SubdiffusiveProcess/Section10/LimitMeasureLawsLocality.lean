module

public import SubdiffusiveProcess.Section10.LimitMeasureLawsStationarity

@[expose] public section

/-!
# Bounded local measurability suppliers for the actual chaos limit

The spatial source sigma algebra uses precisely the actual negative layer
evaluations. Finite-cutoff restrictions are measurable into the literal Giry
sigma algebra for every Borel set, including unbounded sets. For the same
locally weak limit, nonnegative compact tests supported in that set have
local measurable representatives. This is a bounded supplier; no independence
of the final restriction maps is asserted here.
-/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess Filter Topology
open scoped CompactlySupported ENNReal

noncomputable section

namespace SubdiffusiveProcess.Section10

/-- Information carried by all actual negative layer values on a deterministic
spatial set. This is a source sigma algebra, not a new field or measure law. -/
def fineSpatialSigma {d : ℕ} (A : Set (SpatialCoordinates d)) :
    MeasurableSpace (BilateralField d) :=
  ⨆ (n : ℕ) (x : A), (borel ℝ).comap (fun omega => omega (-(n : ℤ)) x)

theorem fine_spatial_sigma_mono {d : ℕ} {A B : Set (SpatialCoordinates d)}
    (hAB : A ⊆ B) : fineSpatialSigma A ≤ fineSpatialSigma B := by
  refine iSup₂_le fun n x => ?_
  exact le_iSup_of_le n (le_iSup_of_le (⟨x, hAB x.property⟩ : B) le_rfl)

theorem measurable_negative_layer_local {d : ℕ} (A : Set (SpatialCoordinates d))
    (n : ℕ) (x : A) :
    @Measurable (BilateralField d) ℝ (fineSpatialSigma A) (borel ℝ)
      (fun omega => omega (-(n : ℤ)) x) := by
  exact Measurable.of_comap_le
    (le_iSup_of_le n (le_iSup_of_le x le_rfl))

/-- The source sigma algebra is contained in the actual field carrier's
measurable space; no new measure-space instance is imposed on that carrier. -/
theorem fine_spatial_sigma_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (A : Set (SpatialCoordinates d)) :
    fineSpatialSigma A ≤ (inferInstance : MeasurableSpace (BilateralField d)) := by
  refine iSup₂_le fun n x => ?_
  exact ((continuous_eval_const (x : SpatialCoordinates d)).measurable.comp
    (measurable_pi_apply (-(n : ℤ)))).comap_le

/-- Joint local measurability over the Borel spatial subtype. Continuity in
space and measurability in the actual negative layers supply the joint map. -/
theorem measurable_fine_density_local_subtype {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (A : Set (SpatialCoordinates d)) :
    @Measurable (BilateralField d × A) ℝ
      ((fineSpatialSigma A).prod inferInstance) (borel ℝ)
      (fun q => fineDensity M N q.1 q.2) := by
  letI : MeasurableSpace (BilateralField d) := fineSpatialSigma A
  have heval (x : A) : Measurable (fun omega => fineDensity M N omega x) := by
    unfold fineDensity finePotential
    exact ((Finset.measurable_sum _ (fun n _ =>
      measurable_negative_layer_local A n x)).sub measurable_const).exp
  have hcont (omega : BilateralField d) : Continuous (fun x : A => fineDensity M N omega x) :=
    (continuous_fineDensity M N omega).comp continuous_subtype_val
  have hswap := measurable_uncurry_of_continuous_of_measurable hcont heval
  exact hswap.comp measurable_swap

/-- Every actual finite-cutoff restriction is local and measure-valued
measurable, for arbitrary deterministic Borel sets, bounded or unbounded. -/
theorem measurable_chaos_cutoff_restriction_local {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) :
    @Measurable (BilateralField d) (Measure (SpatialCoordinates d))
      (fineSpatialSigma A) inferInstance (fun omega => (chaosCutoff M N omega).restrict A) := by
  classical
  letI : MeasurableSpace (BilateralField d) := fineSpatialSigma A
  let nu : Measure A := (volume : Measure (SpatialCoordinates d)).comap Subtype.val
  have hnu : SigmaFinite (nu.map Subtype.val) := by
    rw [show nu.map Subtype.val = volume.restrict A from map_comap_subtype_coe hA volume]
    infer_instance
  letI : SigmaFinite nu := SigmaFinite.of_map nu measurable_subtype_coe.aemeasurable hnu
  apply Measure.measurable_of_measurable_coe
  intro B hB
  have hjoint := (measurable_fine_density_local_subtype M N A).ennreal_ofReal
  have hBsub : MeasurableSet {q : BilateralField d × A | (q.2 : SpatialCoordinates d) ∈ B} :=
    hB.preimage (measurable_subtype_coe.comp measurable_snd)
  have hind : Measurable (fun q : BilateralField d × A =>
      B.indicator (fun x => ENNReal.ofReal (fineDensity M N q.1 x)) q.2) := by
    simpa only [Set.indicator_apply, Set.piecewise, Set.mem_setOf_eq] using! hjoint.piecewise hBsub measurable_const
  have hmass := Measurable.lintegral_prod_right' (ν := nu) hind
  have heq (omega : BilateralField d) :
      ((chaosCutoff M N omega).restrict A) B =
        ∫⁻ x : A, B.indicator (fun y => ENNReal.ofReal (fineDensity M N omega y)) x ∂nu := by
    rw [Measure.restrict_apply hB, chaosCutoff, withDensity_apply _ (hB.inter hA),
      lintegral_subtype_comap hA, setLIntegral_indicator hB]
    rfl
  simpa only [← heq] using hmass

/-- Restriction itself is Giry-measurable. This is a measurability theorem,
and makes no assertion of vague continuity of Borel restriction. -/
theorem measurable_measure_restriction {d : ℕ}
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) :
    Measurable (fun mu : Measure (SpatialCoordinates d) => mu.restrict A) := by
  apply Measure.measurable_of_measurable_coe
  intro B hB
  simpa only [Measure.restrict_apply hB] using Measure.measurable_coe (hB.inter hA)

/-- Consequently the same supplied measurable limit has measurable restriction
maps for all Borel sets, without requiring any restriction convergence. -/
theorem same_limit_restriction_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu0)
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) :
    Measurable (fun omega => (mu0 omega).restrict A) :=
  (measurable_measure_restriction A hA).comp hm

/-- A literal local representative for positive compact-test integrals. -/
def localPositiveTestLimit {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (A : Set (SpatialCoordinates d)) (f : C_c(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) : ℝ≥0∞ :=
  limsup (fun N => ∫⁻ x, ENNReal.ofReal (f x) ∂(chaosCutoff M N omega).restrict A) atTop

theorem measurable_local_positive_test_limit {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (A : Set (SpatialCoordinates d))
    (hA : MeasurableSet A) (f : C_c(SpatialCoordinates d, ℝ)) :
    @Measurable (BilateralField d) ℝ≥0∞ (fineSpatialSigma A) (borel ℝ≥0∞)
      (localPositiveTestLimit M A f) := by
  apply Measurable.limsup
  intro N
  exact (Measure.measurable_lintegral f.continuous.measurable.ennreal_ofReal).comp
    (measurable_chaos_cutoff_restriction_local M N A hA)

/-- The local representative agrees with the compact-test integral of the
same actual locally weak limit. Its AE event comes from the given convergence
event, and no martingale, density divergence or new random measure is built. -/
theorem same_chaos_limit_positive_test_local {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (hl : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, IsLocallyFiniteMeasure (mu0 omega))
    (hc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => chaosCutoff M N omega) (mu0 omega))
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A)
    (f : C_c(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (hsupp : Function.support f ⊆ A) :
    localPositiveTestLimit M A f =ᵐ[(chaosSampleLaw M).toMeasure]
      fun omega => ∫⁻ x, ENNReal.ofReal (f x) ∂(mu0 omega).restrict A := by
  have hind : A.indicator (fun x => ENNReal.ofReal (f x)) = fun x => ENNReal.ofReal (f x) := by
    funext x
    by_cases hx : x ∈ A
    · exact Set.indicator_of_mem hx _
    · have hzero : f x = 0 := by
        by_contra h
        exact hx (hsupp h)
      simp only [Set.indicator_of_notMem hx, hzero, ENNReal.ofReal_zero]
  have hrestrict (nu : Measure (SpatialCoordinates d)) :
      (∫⁻ x, ENNReal.ofReal (f x) ∂nu.restrict A) = ∫⁻ x, ENNReal.ofReal (f x) ∂nu := by
    rw [← lintegral_indicator hA, hind]
  filter_upwards [hl, hc] with omega hloc hconv
  letI : IsLocallyFiniteMeasure (mu0 omega) := hloc
  have ht := Paper.aux_lim_measure_vague_positive_lintegral _ _
    (fun N => chaosCutoff_isLocallyFinite M N omega) hconv f hf
  unfold localPositiveTestLimit
  simp only [hrestrict]
  exact ht.limsup_eq

end SubdiffusiveProcess.Section10
