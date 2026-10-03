module

public import SubdiffusiveProcess.Section10.LimitMeasureRescaledLawCarrier

@[expose] public section




open MeasureTheory SubdiffusiveProcess Filter Topology

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Almost-sure convergence of measurable variables on a Borel topological
carrier implies convergence of their probability laws. -/
theorem probabilityLaw_tendsto_of_ae_tendsto {Ω X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (P : ProbabilityMeasure Ω) (F : ℕ → Ω → X) (G : Ω → X)
    (hF : ∀ n, Measurable (F n)) (hG : Measurable G)
    (hc : ∀ᵐ w ∂P.toMeasure, Tendsto (fun n => F n w) atTop (𝓝 (G w))) :
    Tendsto (fun n => P.map (F n)) atTop (𝓝 (P.map G)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hmap (n : ℕ) : (∫ x, f x ∂(P.map (F n)).toMeasure) =
      ∫ w, f (F n w) ∂P.toMeasure := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact integral_map (hF n).aemeasurable f.continuous.measurable.aestronglyMeasurable
  have hmapG : (∫ x, f x ∂(P.map G).toMeasure) =
      ∫ w, f (G w) ∂P.toMeasure := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact integral_map hG.aemeasurable f.continuous.measurable.aestronglyMeasurable
  simp only [hmap, hmapG]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp (hF n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall fun w => f.norm_coe_le_norm (F n w)
  · exact hc.mono fun w hw => (f.continuous.tendsto (G w)).comp hw

/-- Internal measure-law consumer on the actual locally finite carrier.
The finite equality in law is already discharged. The remaining input is
topological convergence of the original same-limit representatives under
the intended vague topology, with its Borel-space instance. -/
theorem localRescaledCutoffLaw_tendsto_of_ae_tendsto {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    [TopologicalSpace (LocallyFiniteSpatialMeasure d)]
    [BorelSpace (LocallyFiniteSpatialMeasure d)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w)) (hm : Measurable mu0)
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      Tendsto (fun n => localChaosCutoff M n w) atTop
        (𝓝 (localMeasureRepresentative mu0 hl w))) :
    Tendsto (localRescaledCutoffLaw M) atTop (𝓝 (localLimitLaw M mu0 hl hm)) := by
  have ht := probabilityLaw_tendsto_of_ae_tendsto (chaosSampleLaw M)
    (localChaosCutoff M) (localMeasureRepresentative mu0 hl)
    (measurable_localChaosCutoff M) (measurable_localMeasureRepresentative mu0 hl hm) hc
  have heq : localRescaledCutoffLaw M = localChaosCutoffLaw M :=
    funext (localRescaledCutoffLaw_eq M)
  rw [heq]
  exact ht

end SubdiffusiveProcess.Section10
