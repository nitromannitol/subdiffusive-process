module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeProcessAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeCanonicalReduction
public import MarkovProcess.Main

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.Frozen.Section7
open scoped ENNReal NNReal

noncomputable section

variable {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}

/-! ### Measure-level finite-dimensional identification -/

/-- **A finite measure on continuous paths is determined by its
finite-dimensional marginals.**  This is the measure-level form of
`MarkovProcess.Kernel.eq_of_map_denseFiniteEvaluation_eq`. -/
theorem measure_eq_of_map_finsetEvaluation_eq
    {mu nu : Measure (ContinuousPath (State d))}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (h : ∀ I : Finset NNReal,
      mu.map (ContinuousPath.finsetEvaluation I) =
        nu.map (ContinuousPath.finsetEvaluation I)) :
    mu = nu := by
  have hconst : (Kernel.const Unit mu) = (Kernel.const Unit nu) := by
    apply Kernel.eq_of_map_denseFiniteEvaluation_eq
    intro I
    apply Kernel.ext
    intro u
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _),
      Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _),
      Kernel.const_apply, Kernel.const_apply, h _]
  calc mu = Kernel.const Unit mu () := (Kernel.const_apply mu ()).symm
    _ = Kernel.const Unit nu () := by rw [hconst]
    _ = nu := Kernel.const_apply nu ()

/-! ### The time-changed process as a continuous-path transform -/

/-- The inverse-clock transform, read back as a total measurable map into
continuous paths.  Since the lifetime-path transform always has infinite
lifetime, no information is lost. -/
def measurableTimeChangedContinuousPath
    (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d))
    (omega : ContinuousPath (State d)) : ContinuousPath (State d) :=
  continuousPathOfLifetimePath default
    (measurableTimeChangedLifetimePath a theta ha hapos omega)

omit [MeasurableSpace Theta] in
theorem measurable_measurableTimeChangedContinuousPath
    {a : Theta → State d → ℝ} {theta : Theta}
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) :
    Measurable (measurableTimeChangedContinuousPath a theta ha hapos default) :=
  (measurable_continuousPathOfLifetimePath default).comp
    (measurable_measurableTimeChangedLifetimePath ha hapos)

omit [MeasurableSpace Theta] in
/-- The lifetime-path transform is the infinite-lifetime embedding of the
continuous-path transform. -/
theorem ofContinuousPath_measurableTimeChangedContinuousPath
    (a : Theta → State d → ℝ) (theta : Theta)
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default omega : ContinuousPath (State d)) :
    LifetimePath.ofContinuousPath
        (measurableTimeChangedContinuousPath a theta ha hapos default omega) =
      measurableTimeChangedLifetimePath a theta ha hapos omega := by
  rw [measurableTimeChangedContinuousPath,
    continuousPathOfLifetimePath_of_lifetime_eq_top default _
      (measurableTimeChangedLifetimePath_lifetime a theta ha hapos omega),
    LifetimePath.ofContinuousPath_toContinuousPath]

/-! ### The reduction -/

/-- **The frozen time-change predicate from finite-dimensional marginals.**
Once the reciprocal clock is almost surely unbounded, it suffices to know that
every finite-dimensional marginal of the time-changed process is the
corresponding marginal of the target process. -/
theorem isIntrinsicTimeChange_of_unbounded_of_finiteDimensional
    (a : Theta → State d → ℝ)
    (ha_pos : ∀ theta x, 0 < a theta x)
    (ha_cont : ∀ theta, Continuous (a theta))
    (QX QY : Kernel (Theta × State d) (ContinuousPath (State d)))
    [IsMarkovKernel QX] [IsMarkovKernel QY]
    (default : Theta → State d → ContinuousPath (State d))
    (hunbounded : ∀ theta x, ∀ᵐ omega ∂QX (theta, x),
      omega ∈ timeChangeUnboundedEvent a theta)
    (hfdd : ∀ theta x (I : Finset NNReal),
      ((QX (theta, x)).map (measurableTimeChangedContinuousPath a theta
          (ha_cont theta) (ha_pos theta) (default theta x))).map
        (ContinuousPath.finsetEvaluation I) =
      (QY (theta, x)).map (ContinuousPath.finsetEvaluation I)) :
    IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel QX) (Kernel.toLifetimePathKernel QY) := by
  refine isIntrinsicTimeChange_of_unbounded_of_map a ha_pos ha_cont QX QY
    hunbounded ?_
  intro theta x
  have hmeas : Measurable (measurableTimeChangedContinuousPath a theta
      (ha_cont theta) (ha_pos theta) (default theta x)) :=
    measurable_measurableTimeChangedContinuousPath _ _ _
  haveI : IsProbabilityMeasure ((QX (theta, x)).map
      (measurableTimeChangedContinuousPath a theta
        (ha_cont theta) (ha_pos theta) (default theta x))) :=
    inferInstance
  have hlaw : (QX (theta, x)).map (measurableTimeChangedContinuousPath a theta
      (ha_cont theta) (ha_pos theta) (default theta x)) = QY (theta, x) :=
    measure_eq_of_map_finsetEvaluation_eq (hfdd theta x)
  rw [Kernel.toLifetimePathKernel_eq_map,
    Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath, ← hlaw,
    Measure.map_map LifetimePath.measurable_ofContinuousPath hmeas]
  apply Measure.map_congr
  refine Filter.Eventually.of_forall fun omega ↦ ?_
  exact (ofContinuousPath_measurableTimeChangedContinuousPath a theta
    (ha_cont theta) (ha_pos theta) (default theta x) omega).symm

/-- **The exact residual producer for the frozen v3 anchor, in
finite-dimensional form.**  Given almost-sure clock divergence and the
transition marginals of the time-changed canonical `(a,a)` process, the frozen
intrinsic-time-change conclusion holds for every pair of `CemeteryDiffusion`
records.  Both hypotheses are statements about the time-changed process only;
no equality of path-space laws and no field of `GeneratedDiffusionFamily` is
assumed. -/
theorem isIntrinsicTimeChange_of_finiteDimensional_marginals
    (a : Theta → State d → ℝ)
    (ha_pos : ∀ theta x, 0 < a theta x)
    (ha_cont : ∀ theta, Continuous (a theta))
    {DXDatum DYDatum : Theta →
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}
    (DX : GeneratedDiffusionFamily Theta d a a DXDatum)
    (DY : GeneratedDiffusionFamily Theta d a (fun _ _ ↦ 1) DYDatum)
    (PX : CemeteryDiffusion d DX) (PY : CemeteryDiffusion d DY)
    (default : Theta → State d → ContinuousPath (State d))
    (hunbounded : ∀ theta x, ∀ᵐ omega ∂
      ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
        DX.semigroup DX.conservative (theta, x),
      omega ∈ timeChangeUnboundedEvent a theta)
    (hfdd : ∀ theta x (I : Finset NNReal),
      ((ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
            DX.semigroup DX.conservative (theta, x)).map
          (measurableTimeChangedContinuousPath a theta
            (ha_cont theta) (ha_pos theta) (default theta x))).map
        (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel
        (DY.semigroup.toSubMarkovKernelSemigroup theta) I x) :
    IsIntrinsicTimeChange a
      (Kernel.toLifetimePathKernel PX.law)
      (Kernel.toLifetimePathKernel PY.law) := by
  refine isIntrinsicTimeChange_of_continuousProcesses a ha_pos ha_cont DX DY PX PY ?_
  refine isIntrinsicTimeChange_of_unbounded_of_finiteDimensional a ha_pos ha_cont
    _ _ default hunbounded ?_
  intro theta x I
  rw [hfdd theta x I]
  have hFeller : ∀ theta,
      (DY.semigroup.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup := by
    intro theta
    rw [DY.semigroup_eq theta]
    exact (DYDatum theta).isFellerKernelSemigroup_fellerKernelSemigroup
      (DY.denseRange theta)
  obtain ⟨p, q, M, hmom⟩ := DY.displacementMoments
  have hK : DY.semigroup.KolmogorovRegular DY.conservative :=
    ParameterizedSubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments
      DY.semigroup DY.conservative hmom
  exact (ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_map_finiteEvaluation
    DY.semigroup DY.conservative hFeller hK theta x I).symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
