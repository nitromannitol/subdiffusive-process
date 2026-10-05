module

public import SubdiffusiveProcess.Section10.LimitMeasureRescaledLawFinite
public import SubdiffusiveProcess.Section10.ChaosVagueMartingale

@[expose] public section




open MeasureTheory ProbabilityTheory SubdiffusiveProcess

noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Locally finite spatial measures, with the inherited evaluation sigma
algebra. This definition does not equip the carrier with a topology. -/
abbrev LocallyFiniteSpatialMeasure (d : ℕ) :=
  {mu : Measure (SpatialCoordinates d) // IsLocallyFiniteMeasure mu}

def localMeasureRepresentative {d : ℕ} {Ω : Type*}
    (mu : Ω → Measure (SpatialCoordinates d)) (hl : ∀ w, IsLocallyFiniteMeasure (mu w)) :
    Ω → LocallyFiniteSpatialMeasure d := fun w => ⟨mu w, hl w⟩

theorem measurable_localMeasureRepresentative {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (mu : Ω → Measure (SpatialCoordinates d)) (hl : ∀ w, IsLocallyFiniteMeasure (mu w))
    (hm : Measurable mu) : Measurable (localMeasureRepresentative mu hl) :=
  hm.subtype_mk

/-- Equality of laws of these representatives is determined by the law of
their literal measure values, since the subtype sigma algebra is induced. -/
theorem localMeasure_law_eq_of_coe_law_eq {d : ℕ}
    (P Q : Measure (LocallyFiniteSpatialMeasure d))
    (h : Measure.map Subtype.val P = Measure.map Subtype.val Q) : P = Q := by
  apply Measure.ext
  intro s hs
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have heq := congrArg (fun R : Measure (Measure (SpatialCoordinates d)) => R t) h
  simpa only [Measure.map_apply measurable_subtype_coe ht] using heq

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

def localRescaledCutoffMeasure (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    _root_.SubdiffusiveProcess.Model.PotentialSample d → LocallyFiniteSpatialMeasure d :=
  localMeasureRepresentative (rescaledCutoffMeasure M N) (rescaledCutoffMeasure_locallyFinite M N)

def localChaosCutoff (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    BilateralField d → LocallyFiniteSpatialMeasure d :=
  localMeasureRepresentative (chaosCutoff M N) (chaosCutoff_isLocallyFinite M N)

theorem measurable_localRescaledCutoffMeasure (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (N : ℕ) : Measurable (localRescaledCutoffMeasure M N) :=
  measurable_localMeasureRepresentative _ _ (measurable_rescaledCutoffMeasure M N)

theorem measurable_localChaosCutoff (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (N : ℕ) : Measurable (localChaosCutoff M N) :=
  measurable_localMeasureRepresentative _ _ (_root_.SubdiffusiveProcess.Paper.aux_lim_measure_cutoff_measurable M N)

/-- Exact finite measure-valued equality in law on the same locally finite
carrier that contains the actual limit representative. -/
theorem localRescaledCutoffMeasure_law (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    Measure.map (localRescaledCutoffMeasure M N) M.P.toMeasure =
      Measure.map (localChaosCutoff M N) (chaosSampleLaw M).toMeasure := by
  apply localMeasure_law_eq_of_coe_law_eq
  rw [Measure.map_map measurable_subtype_coe (measurable_localRescaledCutoffMeasure M N),
    Measure.map_map measurable_subtype_coe (measurable_localChaosCutoff M N)]
  exact rescaledCutoffMeasure_law M N

theorem localRescaledCutoffMeasure_identDistrib
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    IdentDistrib (localRescaledCutoffMeasure M N) (localChaosCutoff M N)
      M.P.toMeasure (chaosSampleLaw M).toMeasure :=
  ⟨(measurable_localRescaledCutoffMeasure M N).aemeasurable,
    (measurable_localChaosCutoff M N).aemeasurable, localRescaledCutoffMeasure_law M N⟩

/-- The literal natural-environment finite law, now as a probability measure
on the locally finite carrier. -/
def localRescaledCutoffLaw (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    ProbabilityMeasure (LocallyFiniteSpatialMeasure d) :=
  M.P.map (localRescaledCutoffMeasure M N)

def localChaosCutoffLaw (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    ProbabilityMeasure (LocallyFiniteSpatialMeasure d) :=
  (chaosSampleLaw M).map (localChaosCutoff M N)

/-- The law of the SAME actual limiting measure representative. -/
def localLimitLaw (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (mu0 : BilateralField d → Measure (SpatialCoordinates d))
    (hl : ∀ w, IsLocallyFiniteMeasure (mu0 w)) (_hm : Measurable mu0) :
    ProbabilityMeasure (LocallyFiniteSpatialMeasure d) :=
  (chaosSampleLaw M).map (localMeasureRepresentative mu0 hl)

theorem localRescaledCutoffLaw_eq (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    localRescaledCutoffLaw M N = localChaosCutoffLaw M N :=
  by
    apply ProbabilityMeasure.toMeasure_injective
    simpa only [localRescaledCutoffLaw, localChaosCutoffLaw, ProbabilityMeasure.toMeasure_map,
      (measurable_localRescaledCutoffMeasure M N).aemeasurable,
      (measurable_localChaosCutoff M N).aemeasurable] using localRescaledCutoffMeasure_law M N

end SubdiffusiveProcess.Section10
