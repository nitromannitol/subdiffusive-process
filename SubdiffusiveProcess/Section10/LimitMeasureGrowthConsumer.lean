module

public import SubdiffusiveProcess.Section10.LimitMeasureGrowthBank
public import SubdiffusiveProcess.Section10.DensityHalfMomentConsumer

@[expose] public section

/-! Concrete application to the previously chosen actual limiting measure.
The two quenched conclusions have exactly the growth-premise shape used by
the transition-law consumer. No stationarity or restriction law is asserted. -/

open MeasureTheory SubdiffusiveProcess Filter Topology Set
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Countable-window growth for both literal limiting measures, on one
environment event. This supplies the `hg` premise of the quenched consumer. -/
theorem same_limit_quenched_growth {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (mu0 : BilateralField d → Measure (SpatialCoordinates d)),
        (∀ w, IsLocallyFiniteMeasure (mu0 w)) →
        (∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w)) →
        ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
            ∀ x ∈ Metric.closedBall (0 : SpatialCoordinates d) n,
              ∀ r : ℝ, 0 < r → r ≤ 1 →
                mu0 w (Metric.ball x r) ≤ ENNReal.ofReal (C * r ^ ((d : ℝ) - 1 / 2)) ∧
                infraredWeightedLimit H mu0 w (Metric.ball x r)
                  ≤ ENNReal.ofReal (C * r ^ ((d : ℝ) - 1 / 2)) := by
  obtain ⟨delta0, hd0, hg⟩ := same_limit_growth_moment_bank hd 1 (by norm_num)
  refine ⟨delta0, hd0, ?_⟩
  intro M H hH hdelta mu0 hl hc
  apply ae_all_iff.mpr
  intro n
  obtain ⟨K, _, _, hK, hb⟩ := hg M H hH hdelta mu0 hl hc
    (Metric.closedBall 0 (n : ℝ)) Metric.isBounded_closedBall
  filter_upwards [hb] with w hw
  refine ⟨K w, hK w, ?_⟩
  intro x hx r hr hr1
  have h := hw x hx r hr hr1
  exact ⟨(le_add_right le_rfl).trans h, (le_add_left le_rfl).trans h⟩

/-- The actual density-divergence representative also has the source's
locally uniform growth bank. All measurability and everywhere local finiteness
properties are retained; no new limiting-measure construction is used. -/
theorem exists_same_limit_density_divergence_growth {d : ℕ}
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
        (∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu0 w) ∧
          mu0 w ⟂ₘ volume ∧
          (∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
            Tendsto (fun n => fineDensity M n w x) atTop (𝓝 0)) ∧
          (∀ᵐ x ∂mu0 w, Tendsto (fun n => fineDensity M n w x) atTop atTop) ∧
          MeasuresConvergeLocally (fun n => weightedChaosCutoff M H n w)
            (infraredWeightedLimit H mu0 w) ∧
          infraredWeightedLimit H mu0 w ⟂ₘ volume ∧
          (∀ᵐ x ∂infraredWeightedLimit H mu0 w,
            Tendsto (fun n => fineDensity M n w x) atTop atTop)) ∧
        (∀ D : Set (SpatialCoordinates d), MeasurableSet D →
          (∫⁻ w, mu0 w D ∂(chaosSampleLaw M).toMeasure) = volume D) ∧
        (¬ ∃ m : Measure (SpatialCoordinates d),
          ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, mu0 w = m) ∧
        (∀ R : Set (SpatialCoordinates d), Bornology.IsBounded R →
          ∃ K : BilateralField d → ℝ, Measurable K ∧
            MemLp K (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
            (∀ w, 0 ≤ K w) ∧
            ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
              ∀ x ∈ R, ∀ r : ℝ, 0 < r → r ≤ 1 →
                mu0 w (Metric.ball x r) + infraredWeightedLimit H mu0 w (Metric.ball x r)
                  ≤ ENNReal.ofReal (K w * r ^ ((d : ℝ) - 1 / 2))) ∧
        (∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
            ∀ x ∈ Metric.closedBall (0 : SpatialCoordinates d) n,
              ∀ r : ℝ, 0 < r → r ≤ 1 →
                mu0 w (Metric.ball x r) ≤ ENNReal.ofReal (C * r ^ ((d : ℝ) - 1 / 2)) ∧
                infraredWeightedLimit H mu0 w (Metric.ball x r)
                  ≤ ENNReal.ofReal (C * r ^ ((d : ℝ) - 1 / 2))) := by
  obtain ⟨deltaG, hG, hg⟩ := same_limit_growth_moment_bank hd p hp
  obtain ⟨deltaQ, hQ, hq⟩ := same_limit_quenched_growth hd
  refine ⟨min (1 / 4) (min deltaG deltaQ), by positivity, ?_⟩
  intro M H hH hdelta
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdquarter : M.delta ≤ 1 / 4 := hdelta.trans (min_le_left _ _)
  have hdG : M.delta ≤ deltaG :=
    (hdelta.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hdQ : M.delta ≤ deltaQ :=
    (hdelta.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨mu0, hm, hl, hwl, hall, hmean, hnd⟩ :=
    exists_same_limit_with_density_divergence hdpos M hdquarter H
  have hc := hall.mono fun w hw => hw.1
  exact ⟨mu0, hm, infraredWeightedLimit_measurable H hH.1 mu0 hm hl,
    hl, hwl, hall, hmean, hnd, hg M H hH hdG mu0 hl hc, hq M H hH hdQ mu0 hl hc⟩

end SubdiffusiveProcess.Section10
