import SubdiffusiveProcess.Section10.LimitMeasureLawsRestrictionConsumer
import SubdiffusiveProcess.Section10.LimitMeasureGrowthConsumer




open MeasureTheory ProbabilityTheory SubdiffusiveProcess Filter Topology
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

def SameLimitDensityProperties {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (w : BilateralField d) : Prop :=
  MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w) ∧
  mu0 w ⟂ₘ volume ∧
  (∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
    Tendsto (fun n => fineDensity M n w x) atTop (𝓝 0)) ∧
  (∀ᵐ x ∂mu0 w, Tendsto (fun n => fineDensity M n w x) atTop atTop) ∧
  MeasuresConvergeLocally (fun n => weightedChaosCutoff M H n w)
    (infraredWeightedLimit H mu0 w) ∧
  infraredWeightedLimit H mu0 w ⟂ₘ volume ∧
  (∀ᵐ x ∂infraredWeightedLimit H mu0 w,
    Tendsto (fun n => fineDensity M n w x) atTop atTop)

def SameLimitSpatialLaws {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) : Prop :=
  (∀ D : Set (SpatialCoordinates d), MeasurableSet D →
    (∫⁻ w, mu0 w D ∂(chaosSampleLaw M).toMeasure) = volume D) ∧
  (¬ ∃ m : Measure (SpatialCoordinates d),
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, mu0 w = m) ∧
  (∀ y : SpatialCoordinates d,
    (chaosSampleLaw M).toMeasure.map (fun w => (mu0 w).map (fun z => z + y)) =
      (chaosSampleLaw M).toMeasure.map mu0) ∧
  (∀ A B : Set (SpatialCoordinates d), MeasurableSet A → MeasurableSet B →
    (∃ c : ℝ, (d : ℝ) < c ∧ ∀ a ∈ A, ∀ b ∈ B, c ≤ ∑ i, (a i - b i) ^ 2) →
    Indep (MeasurableSpace.comap (fun w => (mu0 w).restrict A) inferInstance)
      (MeasurableSpace.comap (fun w => (mu0 w).restrict B) inferInstance)
      (chaosSampleLaw M).toMeasure)

def SameLimitGrowth {d : ℕ} (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (w : BilateralField d) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ∈ Metric.closedBall (0 : SpatialCoordinates d) n,
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        mu0 w (Metric.ball x r) ≤ ENNReal.ofReal (C * r ^ ((d : ℝ) - 1 / 2)) ∧
        infraredWeightedLimit H mu0 w (Metric.ball x r)
          ≤ ENNReal.ofReal (C * r ^ ((d : ℝ) - 1 / 2))

def SameLimitGrowthMoments {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu0 : BilateralField d → Measure (SpatialCoordinates d)) (p : ℝ) : Prop :=
  ∀ R : Set (SpatialCoordinates d), Bornology.IsBounded R →
    ∃ C : BilateralField d → ℝ, Measurable C ∧
      MemLp C (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
      (∀ w, 0 ≤ C w) ∧
      ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
        ∀ x ∈ R, ∀ r : ℝ, 0 < r → r ≤ 1 →
          mu0 w (Metric.ball x r) + infraredWeightedLimit H mu0 w (Metric.ball x r)
            ≤ ENNReal.ofReal (C w * r ^ ((d : ℝ) - 1 / 2))



theorem exists_same_limit_density_spatial_growth {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    ∃ mu0 : BilateralField d → Measure (SpatialCoordinates d),
      Measurable mu0 ∧ Measurable (infraredWeightedLimit H mu0) ∧
      (∀ w, IsLocallyFiniteMeasure (mu0 w)) ∧
      (∀ w, IsLocallyFiniteMeasure (infraredWeightedLimit H mu0 w)) ∧
      (∀ᵐ w ∂(chaosSampleLaw M).toMeasure, SameLimitDensityProperties M H mu0 w) ∧
      SameLimitSpatialLaws M mu0 ∧ SameLimitGrowthMoments M H mu0 p ∧
      (∀ᵐ w ∂(chaosSampleLaw M).toMeasure, SameLimitGrowth H mu0 w) := by
  obtain ⟨deltaG, hG, hg⟩ := same_limit_growth_moment_bank hd p hp
  obtain ⟨deltaQ, hQ, hq⟩ := same_limit_quenched_growth hd
  refine ⟨min (1 / 4) (min deltaG deltaQ), by positivity, ?_⟩
  intro M H hH hdelta
  have hdquarter : M.delta ≤ 1 / 4 := hdelta.trans (min_le_left _ _)
  have hdG : M.delta ≤ deltaG :=
    (hdelta.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hdQ : M.delta ≤ deltaQ :=
    (hdelta.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨mu0, hm, hl, hwl, hall, hmean, hnd, hs, hi⟩ :=
    exists_density_divergence_limit_with_spatial_laws (by omega) M hdquarter H
  have hc := hall.mono fun w hw => hw.1
  exact ⟨mu0, hm, infraredWeightedLimit_measurable H hH.1 mu0 hm hl,
    hl, hwl, hall, ⟨hmean, hnd, hs, hi⟩,
    hg M H hH hdG mu0 hl hc, hq M H hH hdQ mu0 hl hc⟩

/-- Strictly positive continuous infrared weights preserve all null sets. -/
theorem infrared_weighted_null_iff {d : ℕ} (h : C(SpatialCoordinates d, ℝ))
    (mu : Measure (SpatialCoordinates d)) (A : Set (SpatialCoordinates d)) :
    mu.withDensity (fun x => ENNReal.ofReal (Real.exp (h x))) A = 0 ↔ mu A = 0 := by
  rw [withDensity_apply_eq_zero (h.continuous.measurable.exp.ennreal_ofReal)]
  have hpos : {x : SpatialCoordinates d | ENNReal.ofReal (Real.exp (h x)) ≠ 0} = Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  rw [hpos, Set.univ_inter]

/-- Full support and absence of atoms of the supplied weighted measure imply
the same conclusions for its literal unweighted measure. -/
theorem unweighted_regularity_of_infrared_weighted {d : ℕ}
    (h : C(SpatialCoordinates d, ℝ)) (mu : Measure (SpatialCoordinates d))
    (ha : NoAtoms (mu.withDensity (fun x => ENNReal.ofReal (Real.exp (h x)))))
    (hs : (mu.withDensity (fun x => ENNReal.ofReal (Real.exp (h x)))).IsOpenPosMeasure) :
    NoAtoms mu ∧ mu.IsOpenPosMeasure := by
  letI := ha
  letI := hs
  refine ⟨⟨fun x => (infrared_weighted_null_iff h mu {x}).mp (measure_singleton x)⟩, ?_⟩
  refine ⟨fun U hU hne hz => ?_⟩
  exact (hU.measure_ne_zero _ hne) ((infrared_weighted_null_iff h mu U).mpr hz)

end SubdiffusiveProcess.Section10
