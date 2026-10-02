import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.FixedClockMassLoss
import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.ResolventBridge
import MarkovProcess.Parameterized.ContinuousProcessProperties
import MarkovProcess.Trajectory.PathModulus




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Process

open MeasureTheory ProbabilityTheory MarkovProcess Homogenization Set Filter
open SubdiffusiveProcess.Frozen.Section7
open scoped ENNReal NNReal Topology

noncomputable section

variable {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}

/-! ### The live value read off an infinite-lifetime path -/

/-- The live value of a lifetime path is the cemetery coordinate with the
cemetery state replaced by the fallback state. -/
theorem lifetimeValue_eq_sumElim (x : State d) (t : NNReal)
    (path : LifetimePath (State d)) :
    lifetimeValue x t path =
      Sum.elim id (fun _ ↦ x) (LifetimePath.coordinate t path) := by
  rcases h : LifetimePath.coordinate t path with y | u
  · simp only [lifetimeValue, h, Sum.elim_inl, id_eq]
  · cases u
    simp only [lifetimeValue, h, Sum.elim_inr]

theorem measurable_lifetimeValue (x : State d) (t : NNReal) :
    Measurable (fun path : LifetimePath (State d) ↦ lifetimeValue x t path) := by
  have hsum : Measurable (Sum.elim id (fun _ : Unit ↦ x)) :=
    Measurable.sumElim measurable_id measurable_const
  simpa only [lifetimeValue_eq_sumElim] using
    hsum.comp (LifetimePath.measurable_coordinate t)

/-- On the image of a continuous path, the live value is the value of the path. -/
@[simp]
theorem lifetimeValue_ofContinuousPath (x : State d) (t : NNReal)
    (omega : ContinuousPath (State d)) :
    lifetimeValue x t (LifetimePath.ofContinuousPath omega) = omega t :=
  lifetimeValue_of_coordinate_eq_alive (LifetimePath.coordinate_ofContinuousPath omega t)

/-! ### The lifetime-path law -/

variable (P : ParameterizedSubMarkovKernelSemigroup Theta (State d)) (hP : P.IsConservative)

/-- **The Section 7 lifetime-path law of a conservative parameterized semigroup.**
The library's continuous-path process, embedded in lifetime-path space with
lifetime `∞`. -/
def lifetimePathProcess : Kernel (Theta × State d) (LifetimePath (State d)) :=
  (ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess P hP).map
    LifetimePath.ofContinuousPath

instance isMarkovKernel_lifetimePathProcess : IsMarkovKernel (lifetimePathProcess P hP) :=
  ProbabilityTheory.Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath

theorem lifetimePathProcess_apply (theta : Theta) (x : State d) :
    lifetimePathProcess P hP (theta, x) =
      (ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess P hP
        (theta, x)).map LifetimePath.ofContinuousPath :=
  ProbabilityTheory.Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath _

/-- Every lifetime path in the support of the law is nonexplosive. -/
theorem lifetime_eq_top_of_mem_range {path : LifetimePath (State d)}
    (h : path ∈ Set.range (LifetimePath.ofContinuousPath (α := State d))) :
    path.lifetime = ∞ := by
  obtain ⟨omega, rfl⟩ := h
  rfl

/-! ### The one-time marginals -/

/-- The one-time marginal of the continuous-path process at **every** nonnegative
real time, not only at rational ones: the deterministic Markov property at time
`t`, read at the time-zero coordinate. -/
theorem map_eval_continuousProcess
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (theta : Theta) (x : State d) (t : NNReal) :
    (ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess P hP (theta, x)).map
        (fun omega ↦ omega t) = (P.toSubMarkovKernelSemigroup theta) t x := by
  have hmeas0 : Measurable (fun omega : ContinuousPath (State d) ↦ omega 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := State d) 0
  have hmeasshift : Measurable (ContinuousPath.shift (alpha := State d) t) :=
    ContinuousPath.measurable_shift_fixed t
  have hshift :=
    ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_map_shift
      P hP hFeller hK theta x t
  have hcompose : (fun omega : ContinuousPath (State d) ↦ omega t)
      = (fun omega : ContinuousPath (State d) ↦ omega 0) ∘ ContinuousPath.shift t := by
    funext omega
    simp
  rw [hcompose, ← Measure.map_map hmeas0 hmeasshift, hshift]
  have hgmeas : Measurable (fun y : State d ↦
      ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess P hP (theta, y)) :=
    (ProbabilityTheory.Kernel.measurable _).comp (measurable_const.prodMk measurable_id)
  refine Measure.ext fun A hA ↦ ?_
  rw [Measure.map_apply hmeas0 hA, Measure.bind_apply (hmeas0 hA) hgmeas.aemeasurable]
  have hpt : ∀ y : State d,
      ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess P hP (theta, y)
        ((fun omega : ContinuousPath (State d) ↦ omega 0) ⁻¹' A) = A.indicator 1 y := by
    intro y
    have hzero :=
      ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_map_eval_zero
        P hP hK theta y
    rw [← Measure.map_apply hmeas0 hA, hzero, Measure.dirac_apply' _ hA]
  simp_rw [hpt]
  rw [lintegral_indicator_one hA]

/-- **The frozen `coordinateLaw` clause.**  Every one-time marginal of the
lifetime-path law is the cemetery extension of the transition kernel started at
the live starting point.  Conservativity is what makes the cemetery part of the
extension vanish. -/
theorem lifetimePathProcess_map_coordinate
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (theta : Theta) (x : State d) (t : NNReal) :
    (lifetimePathProcess P hP (theta, x)).map (LifetimePath.coordinate t) =
      Kernel.cemeteryExtension (P theta t) (Cemetery.alive x) := by
  have hmeast : Measurable (fun omega : ContinuousPath (State d) ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := State d) t
  rw [lifetimePathProcess_apply, Measure.map_map (LifetimePath.measurable_coordinate t)
    LifetimePath.measurable_ofContinuousPath]
  have hcomp : LifetimePath.coordinate t ∘ LifetimePath.ofContinuousPath
      = (Cemetery.alive (α := State d)) ∘ fun omega : ContinuousPath (State d) ↦ omega t := by
    funext omega
    exact LifetimePath.coordinate_ofContinuousPath omega t
  rw [hcomp, ← Measure.map_map measurable_inl hmeast,
    map_eval_continuousProcess P hP hFeller hK theta x t,
    Kernel.cemeteryExtension_alive_apply]
  have hmass : (P theta t) x Set.univ = 1 := hP theta t x
  simp [hmass]

/-! ### The frozen Kolmogorov clause -/

/-- **The frozen `kolmogorovRegularAt` clause.**  The live-value process of the
lifetime-path law satisfies the Kolmogorov condition with the semigroup's own
displacement exponents and constant, uniformly in the parameter and the starting
point. -/
theorem isKolmogorovProcess_lifetimePathProcess {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) (hK : P.KolmogorovRegular hP)
    (theta : Theta) (x : State d) :
    IsKolmogorovProcess (fun t path ↦ lifetimeValue x t path)
      (lifetimePathProcess P hP (theta, x)) p q M := by
  have hfib := SubMarkovKernelSemigroup.IsConservative.isKolmogorovProcess_continuousProcess
    (P.toSubMarkovKernelSemigroup theta) (hP theta) (hmom theta) (hK theta) x
  refine IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun t ↦ measurable_lifetimeValue x t) ?_ hfib.p_pos hfib.q_pos
  intro s t
  have hint : Measurable fun path : LifetimePath (State d) ↦
      edist (lifetimeValue x s path) (lifetimeValue x t path) ^ p :=
    ENNReal.continuous_rpow_const.measurable.comp
      ((measurable_lifetimeValue x s).edist (measurable_lifetimeValue x t))
  rw [lifetimePathProcess_apply,
    ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_apply,
    lintegral_map hint LifetimePath.measurable_ofContinuousPath]
  simpa only [lifetimeValue_ofContinuousPath] using hfib.kolmogorovCondition s t

/-- The frozen `PerStartKolmogorovRegular` predicate for the lifetime-path law of
a conservative semigroup with a displacement moment bound. -/
theorem perStartKolmogorovRegular_lifetimePathProcess {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) (hK : P.KolmogorovRegular hP) :
    PerStartKolmogorovRegular (lifetimePathProcess P hP) := by
  intro theta x
  have hfib := isKolmogorovProcess_lifetimePathProcess P hP hmom hK theta x
  have hp : 0 < p := hfib.p_pos
  have hq : 1 < q := (hmom theta).one_lt_q
  have hquot : 0 < (q - 1) / p := div_pos (by linarith) hp
  exact ⟨p, q, (q - 1) / p / 2, M, hfib, by linarith, by linarith⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Process
