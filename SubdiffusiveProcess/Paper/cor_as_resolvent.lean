module

public import SubdiffusiveProcess.Paper.lem_band
public import SubdiffusiveProcess.Paper.catalog_cutoff_existence
public import SubdiffusiveProcess.ResponseMoments.LocalEnergyAux
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.VariationalResponses.CellAssembly
public import SubdiffusiveProcess.Sobolev.GradientEnergyMeasure
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.ConditionalFineFiltration
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.SemigroupSymmetric
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.HasStrongMarkovRestart
public import SubdiffusiveProcess.Main.HasFiniteMeanExits
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.Main.PhysicalTimeFactor
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.Main.MeasureTraceCharacterization
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.ResponseMoments.DirichletForm
public import SubdiffusiveProcess.VariationalResponses.KilledInverse
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.prop_as_forms
public import SubdiffusiveProcess.Paper.lem_as_coarse
public import SubdiffusiveProcess.Paper.lem_as_regularity
public import SubdiffusiveProcess.Paper.prop_chaos_growth
public import SubdiffusiveProcess.Paper.prop_uniform_resolvent
public import SubdiffusiveProcess.Paper.prop_speed_resolvent
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.limiting_local_energy
public import SubdiffusiveProcess.Paper.speed_trace_completion
public import SubdiffusiveProcess.Paper.lem_19
public import SubdiffusiveProcess.Paper.in_killed_inverse
public import SubdiffusiveProcess.Paper.cutoff_campanato_bound
public import SubdiffusiveProcess.Paper.cutoff_lifetime_package
public import SubdiffusiveProcess.Paper.car_resolvent_abs_cont
public import SubdiffusiveProcess.Paper.car_rn_continuous_version
public import SubdiffusiveProcess.Paper.car_variational

public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Data.Finset.Lattice.Fold
public import SubdiffusiveProcess.Paper.torsion_bound
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKernel

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology Set TopologicalSpace
open MarkovProcess
open Metric
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The Laplace-type normalizing integral for the killed resolvent's time kernel:
`∫_{(0,∞)} exp(-λ t) dt = 1/λ` for `λ > 0`. This is the elementary fact behind the
operator bound `‖R^Q_{N,λ}‖_{∞→∞} ≤ λ^{-1}` cited in the proof of
 ("the bounds ... and the resolvent
identity extend the assertion to all f, λ"). -/
theorem aux_cor_as_resolvent_integral_exp_Ioi (lam : ℝ) (hlam : 0 < lam) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) = 1 / lam := by
  calc
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t)
        = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(lam * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      simp [neg_mul]
    _ = lam⁻¹ • ∫ t in Set.Ioi (lam * (0 : ℝ)), Real.exp (-t) := by
      rw [integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 0 hlam]
    _ = lam⁻¹ • ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) := by simp
    _ = lam⁻¹ • (1 : ℝ) := by rw [integral_exp_neg_Ioi_zero]
    _ = lam⁻¹ := by simp
    _ = 1 / lam := by rw [one_div]

/-- Abstract pointwise bound on the inner (time) integral shape used to define the cutoff
resolvent kernel `RN`: for any set `S` and any function `g0` bounded in absolute value
by `C ≥ 0`, the `t`-integral of `indicator S (fun s => exp(-λ s) * g0 s)` over `(0,∞)`
is bounded by `C / λ`. Builds on the normalizing integral estimate. -/
theorem aux_cor_as_resolvent_indicator_exp_bound
    (lam C : ℝ) (hlam : 0 < lam) (hC : 0 ≤ C)
    (S : Set ℝ) (g0 : ℝ → ℝ) (hg0 : ∀ s, |g0 s| ≤ C) :
    |∫ t in Set.Ioi (0 : ℝ), Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t|
      ≤ C / lam := by
  have h_pointwise : ∀ t, |Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t| ≤ C * Real.exp (-lam * t) := by
    intro t
    calc
      |Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t|
          ≤ ‖Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ‖(fun s => Real.exp (-lam * s) * g0 s) t‖ := norm_indicator_le_norm_self _ _
      _ = |Real.exp (-lam * t) * g0 t| := by simp [Real.norm_eq_abs]
      _ = |Real.exp (-lam * t)| * |g0 t| := by rw [abs_mul]
      _ = Real.exp (-lam * t) * |g0 t| := by rw [Real.abs_exp (-lam * t)]
      _ ≤ Real.exp (-lam * t) * C := by
        nlinarith [hg0 t, Real.exp_pos (-lam * t)]
      _ = C * Real.exp (-lam * t) := by ring
  have h_int_g : IntegrableOn (fun t => C * Real.exp (-lam * t)) (Set.Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi (0 : ℝ) hlam).const_mul C
  have h_int_abs : |∫ t in Set.Ioi (0 : ℝ), Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t|
      ≤ ∫ t in Set.Ioi (0 : ℝ), |Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t| :=
    abs_integral_le_integral_abs (μ := Measure.restrict volume (Set.Ioi (0 : ℝ)))
      (f := Set.indicator S (fun s => Real.exp (-lam * s) * g0 s))
  have h_int_bound : ∫ t in Set.Ioi (0 : ℝ), |Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t|
      ≤ ∫ t in Set.Ioi (0 : ℝ), C * Real.exp (-lam * t) := by
    by_cases h_int_f : IntegrableOn (fun t => |Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t|)
      (Set.Ioi (0 : ℝ))
    · refine integral_mono (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) h_int_f h_int_g ?_
      intro t
      simpa [Real.norm_eq_abs] using h_pointwise t
    · rw [integral_undef h_int_f]
      exact setIntegral_nonneg measurableSet_Ioi (fun t ht => by positivity)
  have h_int_Cexp : ∫ t in Set.Ioi (0 : ℝ), C * Real.exp (-lam * t) = C / lam := by
    calc
      ∫ t in Set.Ioi (0 : ℝ), C * Real.exp (-lam * t) = C * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) := by
        rw [integral_const_mul]
      _ = C * (1 / lam) := by rw [aux_cor_as_resolvent_integral_exp_Ioi lam hlam]
      _ = C / lam := by ring
  linarith



theorem aux_cor_as_resolvent_RN_inner_bound
    {d : ℕ} (Q : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (path : DiffusionPath d) :
    |∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t|
      ≤ ‖f‖ / lam := by
  set S := {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
  set g0 := fun s : ℝ => f (path (Real.toNNReal s))
  have hg0 : ∀ s, |g0 s| ≤ ‖f‖ := by
    intro s
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (path (Real.toNNReal s))
  exact aux_cor_as_resolvent_indicator_exp_bound lam ‖f‖ hlam (norm_nonneg f) S g0 hg0

/-- Integrating the pathwise occupation integral bound over any probability kernel gives the
uniform-in-`N` resolvent bound `|RN n N ω λ f x| ≤ ‖f‖ / λ`. This is exactly the
operator-norm estimate `‖R^Q_{N,λ}‖_{∞→∞} ≤ λ^{-1}` (for `‖f‖ ≤ 1`) that 
cites, together with the resolvent identity, to extend the a.s. convergence from a
countable dense family of `f, λ` to all `f ∈ C(closure Q), λ > 0` on the same event;
it also literally proves the fifth conjunct of `cor_as_resolvent`'s conclusion,
`|Rlim n ω λ f x| ≤ ‖f‖ / λ`, once combined (elsewhere) with the limit `RN → Rlim`. -/
theorem aux_cor_as_resolvent_RN_bound
    {d : ℕ} (Q : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (kappa : Measure (DiffusionPath d)) [IsProbabilityMeasure kappa] :
    |∫ path : DiffusionPath d, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
      ∂kappa|
      ≤ ‖f‖ / lam := by
  have h_ae_bound : ∀ᵐ path ∂kappa, ‖(∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
        (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)‖ ≤ ‖f‖ / lam := by
    refine Eventually.of_forall fun path => ?_
    simpa [Real.norm_eq_abs] using aux_cor_as_resolvent_RN_inner_bound Q lam hlam f path
  have h_norm_int : ‖∫ path : DiffusionPath d, (∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
        (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂kappa‖
      ≤ (‖f‖ / lam) * kappa.real univ :=
    norm_integral_le_of_norm_le_const h_ae_bound
  simpa [Real.norm_eq_abs, MeasureTheory.probReal_univ, mul_one] using h_norm_int

/-- A pointwise real bound that is preserved by a limit: if `F N → a` and `|F N| ≤ C`
for every `N`, then `|a| ≤ C`. This is exactly the mechanism that transports the
uniform resolvent bound `|RN n N ω λ f x| ≤ ‖f‖/λ` to its limit
`|Rlim n ω λ f x| ≤ ‖f‖/λ`, the fifth conjunct of `cor_as_resolvent`'s conclusion
-/
theorem aux_cor_as_resolvent_abs_limit_bound
    (F : ℕ → ℝ) (a C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ N, |F N| ≤ C)
    (hconv : Filter.Tendsto F Filter.atTop (nhds a)) :
    |a| ≤ C := by
  exact abs_le.mpr ⟨ge_of_tendsto' hconv (fun N => (abs_le.mp (hbound N)).1),
    le_of_tendsto' hconv (fun N => (abs_le.mp (hbound N)).2)⟩

/-- A pointwise limit of measurable real-valued functions is measurable. This is the
mechanism that transports the (assumed) measurability of each cutoff resolvent
`RN n N` to the measurability of the limit `Rlim n`, the first conjunct of
`cor_as_resolvent`'s conclusion. -/
theorem aux_cor_as_resolvent_measurable_limit
    {α : Type*} [MeasurableSpace α] (F : ℕ → α → ℝ) (G : α → ℝ)
    (hF : ∀ N, Measurable (F N))
    (hconv : ∀ a, Filter.Tendsto (fun N => F N a) Filter.atTop (nhds (G a))) :
    Measurable G := by
  exact measurable_of_tendsto_metrizable hF
    (tendsto_pi_nhds.mpr hconv)



theorem aux_cor_as_resolvent_Rlim_measurable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (RN : ℕ → BilateralField d × SpatialCoordinates d → ℝ)
    (Rlim : BilateralField d × SpatialCoordinates d → ℝ)
    (hRN_meas : ∀ N, Measurable (RN N))
    (hconv : ∀ p, Filter.Tendsto (fun N => RN N p) Filter.atTop (nhds (Rlim p))) :
    Measurable Rlim := by
  exact aux_cor_as_resolvent_measurable_limit RN Rlim hRN_meas hconv

/-- Instantiates the limit bound at the exact shape of `cor_as_resolvent`'s conclusion:
given the uniform-in-`N` bound `|RN N x| ≤ ‖f‖/λ` (proved, `aux_cor_as_resolvent_RN_bound`) and the pointwise
convergence `RN N x → Rlim x`, the limit obeys the same bound. -/
theorem aux_cor_as_resolvent_Rlim_bound
    {d : ℕ} (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (RN : ℕ → SpatialCoordinates d → ℝ) (Rlim : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d)
    (hRN_bound : ∀ N, |RN N x| ≤ ‖f‖ / lam)
    (hconv : Filter.Tendsto (fun N => RN N x) Filter.atTop (nhds (Rlim x))) :
    |Rlim x| ≤ ‖f‖ / lam := by
  have hC : 0 ≤ ‖f‖ / lam := (abs_nonneg (RN 0 x)).trans (hRN_bound 0)
  exact aux_cor_as_resolvent_abs_limit_bound (fun N => RN N x) (Rlim x) (‖f‖ / lam)
    hC hRN_bound hconv


/-- Corrected-hypothesis companion to `aux_cor_as_resolvent_RN_measurable`, proved: joint
measurability of the same kernel-integral resolvent holds when `Q` is open, which is the
shape of every actual call site of this formula in `cor_as_resolvent` (`Qn n :
Opens (SpatialCoordinates d)`, coerced to `Set`). The original aux's plain
`hQ : MeasurableSet Q` hypothesis needs `Measurable (ContinuousPath.exitTime Q)` for a
merely measurable (not open) `Q`: a genuine "hitting time of a Borel set is measurable"
/ debut-theorem-level fact. An exhaustive search of `MarkovProcess` (every `exitTime`,
`measurable_exitTime`, `measurableSet_lt_exitTime`, `isStoppingTime_exitTime` result in
`Path/ExitTime.lean`, `Path/ExitTimeShift.lean`, `Killed/*.lean`, `Trajectory/*.lean`,
`Killed/Nested.lean`) and of Mathlib (no `debut`/`capacitab` hits anywhere) confirms no
such general-`Q` measurability lemma is available: every one of them requires `IsOpen`
(dualized to `IsClosed` via complementation). The underlying reason a merely measurable
`Q` cannot be reduced to a countable check the way an open (or closed) `Q` can: writing
the survival set as `{(path,t) | ∀ v : NNReal, v ≤ t → path v ∈ Q}` is literally correct
for any `Q`, but restricting that intersection to countably many rational `v` (the trick
that makes the open/closed cases measurable) changes the set unless `Q` is open, so the
defining intersection is over an uncountable index with no available countable-reduction
argument for general Borel `Q`. Formalizing the general case would need a real
debut-theorem effort, not available in this development's toolset. -/
theorem aux_cor_as_resolvent_RN_measurable_open
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel KN]
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q)
    (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Measurable (fun p : BilateralField d × SpatialCoordinates d =>
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
        ∂(KN p)) := by
  have hExit : Measurable (ContinuousPath.exitTime Q : DiffusionPath d → ℝ≥0∞) :=
    ContinuousPath.measurable_exitTime Q hQ
  set Sset : Set (DiffusionPath d × ℝ) :=
    {q : DiffusionPath d × ℝ | ENNReal.ofReal q.2 < ContinuousPath.exitTime Q q.1} with hSdef
  set B : DiffusionPath d × ℝ → ℝ :=
    fun q => Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2)) with hBdef
  have hSmeas : MeasurableSet Sset :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hExit.comp measurable_fst)
  have heval : Measurable (fun q : DiffusionPath d × ℝ => q.1 (Real.toNNReal q.2)) :=
    ContinuousEval.continuous_eval.measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hfeval : Measurable (fun q : DiffusionPath d × ℝ => f (q.1 (Real.toNNReal q.2))) :=
    f.continuous.measurable.comp heval
  have hexp : Measurable (fun q : DiffusionPath d × ℝ => Real.exp (-lam * q.2)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
      measurable_snd
  have hBmeas : Measurable B := hexp.mul hfeval
  have hFmeas : StronglyMeasurable (Sset.indicator B) :=
    hBmeas.stronglyMeasurable.indicator hSmeas
  have hgFmeas : StronglyMeasurable
      (fun path : DiffusionPath d => ∫ t, Sset.indicator B (path, t)
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))) :=
    hFmeas.integral_prod_right'
  have hgeq : (fun path : DiffusionPath d =>
      ∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) =
      (fun path : DiffusionPath d => ∫ t, Sset.indicator B (path, t)
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))) := by
    funext path
    congr 1
  rw [hgeq]
  exact (hgFmeas.integral_kernel (κ := KN)).measurable




/-- One deterministic subsequence gives simultaneous almost sure convergence of a countable
family. No independence or almost sure convergence of the original sequence is assumed. -/
theorem aux_cor_as_resolvent_nat_family_subsequence
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]
    (P : Measure Ω) (X : ℕ → ℕ → Ω → E) (L : ℕ → Ω → E)
    (hX : ∀ j, TendstoInMeasure P (X j) atTop (L j)) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      ∀ᵐ ω ∂P, ∀ j, Tendsto (fun n => X j (t n) ω) atTop (𝓝 (L j ω)) := by
  classical
  let b : ℕ → ℕ := fun n => (Finset.range (n + 1)).sup
    (fun j => ExistsSeqTendstoAe.seqTendstoAeSeqAux (hX j) n)
  let t : ℕ → ℕ := fun n => ∑ k ∈ Finset.range (n + 1), (b k + 1)
  have ht : StrictMono t := by
    apply strictMono_nat_of_lt_succ
    intro n
    have heq : t (n + 1) = t n + (b (n + 1) + 1) :=
      Finset.sum_range_succ _ (n + 1)
    rw [heq]
    omega
  have hbt (n : ℕ) : b n ≤ t n := by
    dsimp only [t]
    rw [Finset.sum_range_succ]
    omega
  refine ⟨t, ht, ae_all_iff.2 fun j => ?_⟩
  let S : ℕ → Set Ω := fun n => if j ≤ n then
    {ω | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (X j (t n) ω) (L j ω)} else ∅
  have hbound (n : ℕ) : P (S n) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    by_cases hj : j ≤ n
    · rw [show S n = {ω | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (X j (t n) ω) (L j ω)}
        from ite_eq_left hj]
      apply Classical.choose_spec (ExistsSeqTendstoAe.exists_nat_measure_lt_two_inv (hX j) n)
      exact (Finset.le_sup (Finset.mem_range.2 (Nat.lt_succ_of_le hj))).trans (hbt n)
    · simp only [S, ite_eq_right hj, measure_empty, zero_le]
  have hsum : (∑' n, P (S n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hbound)
    simp only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  apply EMetric.tendsto_atTop.2
  intro ε hε
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_two_pow_lt hε.ne'
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨max j (max k N), fun n hn => ?_⟩
  have hjn : j ≤ n := (le_max_left _ _).trans hn
  have hkn : k ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hNn : N ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have he : edist (X j (t n) ω) (L j ω) < (2 : ℝ≥0∞)⁻¹ ^ n := by
    have := hN n hNn
    simpa only [S, ite_eq_left hjn, mem_ofPred_eq, not_le] using this
  exact he.trans_le ((pow_le_pow_of_le_one (by simp) (by simp) hkn).trans hk.le)

/-- The subsequence principle for a countable family, on the original probability space. -/
theorem aux_cor_as_resolvent_countable_family_subsequence
    {Ω I E : Type*} [MeasurableSpace Ω] [Countable I] [PseudoEMetricSpace E]
    (P : Measure Ω) (X : I → ℕ → Ω → E) (L : I → Ω → E)
    (hX : ∀ j, TendstoInMeasure P (X j) atTop (L j))
    (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      ∀ᵐ ω ∂P, ∀ j, Tendsto (fun n => X j (s (t n)) ω) atTop (𝓝 (L j ω)) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
    exact ⟨id, strictMono_id, Eventually.of_forall fun _ j => isEmptyElim j⟩
  | inr hI =>
    obtain ⟨e, he⟩ := exists_surjective_nat I
    obtain ⟨t, ht, hconv⟩ := aux_cor_as_resolvent_nat_family_subsequence P
      (fun j n ω => X (e j) (s n) ω) (fun j => L (e j))
      (fun j => (hX (e j)).comp hs.tendsto_atTop)
    refine ⟨t, ht, hconv.mono fun ω hω j => ?_⟩
    obtain ⟨k, rfl⟩ := he j
    exact hω k


/-- Construct the represented-sequence event on the original probability space.
The convergence hypotheses cover both the responses and the attached constants;
moment bounds alone do not supply either hypothesis. -/
theorem aux_cor_as_resolvent_original_represented_sequence
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) (resp constants : I → ℕ → Ω → ℝ)
    (respLim constLim : I → Ω → ℝ)
    (hresp : ∀ i, TendstoInMeasure P (resp i) atTop (respLim i))
    (hconst : ∀ i, TendstoInMeasure P (constants i) atTop (constLim i))
    (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ ∃ G : Set Ω,
      conv_represented_sequence P
        (fun i n ω => resp i (s (t n)) ω) respLim
        (fun i n ω => constants i (s (t n)) ω) G ∧
      (∀ i : I, ∀ ω ∈ G, ∃ c : ℝ, Tendsto (fun n => constants i (s (t n)) ω) atTop (𝓝 c)) := by
  classical
  let X : I × Bool → ℕ → Ω → ℝ := fun i =>
    if i.2 then resp i.1 else constants i.1
  let L : I × Bool → Ω → ℝ := fun i =>
    if i.2 then respLim i.1 else constLim i.1
  have hX : ∀ i, TendstoInMeasure P (X i) atTop (L i) := by
    rintro ⟨i, b⟩
    cases b
    · exact hconst i
    · exact hresp i
  obtain ⟨t, ht, hae⟩ := aux_cor_as_resolvent_countable_family_subsequence P X L hX s hs
  let Bad : Set Ω := {ω | ¬ ∀ i, Tendsto (fun n => X i (s (t n)) ω) atTop (𝓝 (L i ω))}
  have hBad : P Bad = 0 := hae
  obtain ⟨B, hsub, hBm, hB0⟩ := exists_measurable_superset_of_null hBad
  have hconv : ∀ ω ∈ Bᶜ, ∀ i,
      Tendsto (fun n => X i (s (t n)) ω) atTop (𝓝 (L i ω)) := by
    intro ω hω
    by_contra h
    exact hω (hsub h)
  refine ⟨t, ht, Bᶜ, ⟨inferInstance, hBm.compl, by simpa using hB0, ?_, ?_⟩, ?_⟩
  · intro i ω hω
    exact hconv ω hω (i, true)
  · intro i ω hω
    have hc : Tendsto (fun n => constants i (s (t n)) ω) atTop (𝓝 (constLim i ω)) :=
      hconv ω hω (i, false)
    obtain ⟨M, hM⟩ := hc.abs.bddAbove_range
    exact ⟨M, fun n => hM ⟨n, rfl⟩⟩
  · intro i ω hω
    exact ⟨constLim i ω, hconv ω hω (i, false)⟩


theorem aux_cor_as_resolvent_core_hunif_of_coreOn {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (s : ℕ → ℕ) (omega : BilateralField d)
    (hCore : ∀ (GNi : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
        (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)),
      (∀ (n : ℕ) (f : DomainL2 (centeredCube z r hr)), GNi n f =
        (_root_.SubdiffusiveProcess.Paper.in_killed_inverse M H HI omega (s n) z hr hP f :
          SobolevData (centeredCube z r hr)).1) →
      Tendsto GNi atTop (𝓝 G) →
      ∀ (F : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
        (_hF : ∀ u, F.toClosedForm.energy u = limitFormEnergy G u),
        ∃ C : Set (DomainL2 (centeredCube z r hr)),
          _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
            (centeredCube z r hr : Set (SpatialCoordinates d)) C) :
    _root_.SubdiffusiveProcess.Paper.aux_limiting_local_energy_HUNIFProp M H HI z r hr hP s omega := by
  intro GNi G hGNi hTendsto F hF f0 hf0cont hf0supp hf0tsupp ε hε
  obtain ⟨C, hC⟩ := hCore GNi G hGNi hTendsto F hF
  obtain ⟨w, hwC, g, hgcont, hgsupp, hgtsupp, hwg, hgf0⟩ :=
    hC.denseUniform f0 hf0cont hf0supp hf0tsupp ε hε
  exact ⟨w, (hC.memCoreOn w hwC).1, g, hgcont, hgsupp, hgtsupp, hwg, hgf0⟩


/-- The unnormalized occupation resolvent on a bounded open set. -/
def aux_cor_as_resolvent_occupation {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (Q : Set (SpatialCoordinates d)) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∫ p, (∫ t in Set.Ioi (0 : ℝ),
    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q p}
      (fun s => Real.exp (-lam * s) * f (p (Real.toNNReal s))) t) ∂K x

/-- Fubini for the actual bounded-datum occupation integral. -/
theorem aux_cor_as_resolvent_occupation_swap {d : ℕ}
    (ν : Measure (DiffusionPath d)) [IsProbabilityMeasure ν]
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    (∫ p, (∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q p}
        (fun s => Real.exp (-lam * s) * f (p (Real.toNNReal s))) t) ∂ν) =
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) *
      ∫ p in {p : DiffusionPath d | ENNReal.ofReal t < ContinuousPath.exitTime Q p},
        f (p (Real.toNNReal t)) ∂ν := by
  let F : DiffusionPath d × ℝ → ℝ := fun q =>
    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q q.1}
      (fun s => Real.exp (-lam * s) * f (q.1 (Real.toNNReal s))) q.2
  have heval : Measurable (fun q : DiffusionPath d × ℝ => q.1 (Real.toNNReal q.2)) :=
    ContinuousEval.continuous_eval.measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hF : Measurable F := by
    change Measurable
      ({q : DiffusionPath d × ℝ | ENNReal.ofReal q.2 < ContinuousPath.exitTime Q q.1}.indicator
        (fun q => Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2))))
    exact ((Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
      (f.continuous.measurable.comp heval)).indicator
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
        ((ContinuousPath.measurable_exitTime Q hQ).comp measurable_fst))
  have hint : Integrable F (ν.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hdom : Integrable (fun q : DiffusionPath d × ℝ =>
        ‖f‖ * Real.exp (-lam * q.2)) (ν.prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
      Integrable.mul_prod (integrable_const ‖f‖) (exp_neg_integrableOn_Ioi 0 hlam)
    refine hdom.mono' hF.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    calc ‖F q‖ ≤ ‖Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2))‖ :=
        norm_indicator_le_norm_self _ _
      _ = Real.exp (-lam * q.2) * ‖f (q.1 (Real.toNNReal q.2))‖ := by
        rw [norm_mul, Real.norm_eq_abs, Real.abs_exp]
      _ ≤ Real.exp (-lam * q.2) * ‖f‖ :=
        mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (Real.exp_pos _).le
      _ = ‖f‖ * Real.exp (-lam * q.2) := mul_comm _ _
  have hswap := integral_integral_swap (f := fun p t => F (p, t)) hint
  change (∫ p, ∫ t, F (p,t) ∂(volume.restrict (Set.Ioi (0 : ℝ))) ∂ν) = _
  rw [hswap]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have hset : MeasurableSet {p : DiffusionPath d |
      ENNReal.ofReal t < ContinuousPath.exitTime Q p} :=
    measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime Q hQ)
  have heq : (fun p => F (p,t)) =
      {p : DiffusionPath d | ENNReal.ofReal t < ContinuousPath.exitTime Q p}.indicator
        (fun p => Real.exp (-lam * t) * f (p (Real.toNNReal t))) := by
    funext p
    rfl
  dsimp only
  rw [heq, integral_indicator hset, integral_const_mul]

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- Correct normalization of the Section 9 resolvent for a general bounded datum. -/
theorem aux_cor_as_resolvent_killed_normalization {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (law : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ x, Measure.map LifetimePath.ofContinuousPath (K x) = law x)
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) :
    killedResolvent law Q lam⁻¹ f x =
      lam * aux_cor_as_resolvent_occupation K Q lam f x := by
  have : BorelSpace (MarkovProcess.Cemetery (SpatialCoordinates d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  have hmass (t : ℝ) : (∫ w in {w : Path d |
      ENNReal.ofReal t < LifetimePath.exitTime Q w}, f (position (Real.toNNReal t) w) ∂law x) =
      ∫ p in {p : DiffusionPath d | ENNReal.ofReal t < ContinuousPath.exitTime Q p},
        f (p (Real.toNNReal t)) ∂K x := by
    have hS : MeasurableSet {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime Q w} :=
      measurableSet_lt measurable_const (LifetimePath.measurable_exitTime Q hQ)
    rw [← hL x, ← integral_indicator hS]
    rw [integral_map LifetimePath.measurable_ofContinuousPath.aemeasurable]
    · rw [← integral_indicator (measurableSet_lt measurable_const
        (ContinuousPath.measurable_exitTime Q hQ))]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        simp only [Set.indicator, mem_ofPred_eq, LifetimePath.exitTime_ofContinuousPath,
          SubdiffusiveProcess.Model.LifetimeProcess.position_ofContinuousPath]
    · exact ((f.continuous.measurable.comp
        (SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration.position_fixed_measurable (Real.toNNReal t))).indicator hS).aestronglyMeasurable
  unfold aux_cor_as_resolvent_occupation
  rw [aux_cor_as_resolvent_occupation_swap (K x) Q hQ lam hlam f]
  unfold killedResolvent
  rw [inv_inv]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [hmass t]
  congr 2
  field_simp


open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
theorem aux_cor_as_resolvent_weak_ident {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d))) [IsMarkovKernel K]
    (law : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ x, Measure.map LifetimePath.ofContinuousPath (K x) = law x)
    (hLD : LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) law)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    ∃ u : killedSobolevGraph (centeredCube z r hr),
      ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          (fun x => aux_cor_as_resolvent_occupation K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) ∧
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) u.val w.val =
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            (f x - lam * aux_cor_as_resolvent_occupation K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) *
              (w : SobolevData (centeredCube z r hr)).1 x ∂(cutoffSpeedMeasure M H omega N) := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : Set (SpatialCoordinates d),
      Q = (centeredCube z r hr : Set (SpatialCoordinates d)) := ⟨_, rfl⟩
  have hQo : IsOpen Q := hQdef ▸ (centeredCube z r hr).isOpen
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hQb : Bornology.IsBounded Q := hQdef ▸ centeredCube_isBounded z hr
  obtain ⟨S, hSdef⟩ : ∃ S : SpatialCoordinates d → ℝ,
      S = fun x => aux_cor_as_resolvent_occupation K Q lam f x := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : SpatialCoordinates d → ℝ, ρ = cutoffSpeedDensity M H omega N :=
    ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : SpatialCoordinates d → ℝ, c = cutoffCoefficient M H omega N :=
    ⟨_, rfl⟩
  have hρc : Continuous ρ := hρdef ▸ aux_torsion_bound_density_continuous M H omega N
  have hρpos : ∀ x, 0 < ρ x := fun x => hρdef ▸ aux_torsion_bound_density_pos M H omega N x
  have hcc : Continuous c := hcdef ▸ _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N
  obtain ⟨Cρ, hCρ0, hCρ⟩ := aux_torsion_bound_cube_bound ρ hρc z hr
  obtain ⟨Cc, hCc0, hCc⟩ := aux_torsion_bound_cube_bound c hcc z hr
  rw [← hQdef] at hCρ hCc
  have hρb : ∀ᵐ x ∂volume.restrict Q, |ρ x| ≤ Cρ := by
    filter_upwards [ae_restrict_mem hQm] with x hx using hCρ x hx
  have hcb : ∀ᵐ x ∂volume.restrict Q, |c x| ≤ Cc := by
    filter_upwards [ae_restrict_mem hQm] with x hx using hCc x hx
  -- the weighted measure on the cube is finite and equivalent to Lebesgue
  have hfinW : IsFiniteMeasure ((weightedMeasure ρ).restrict Q) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, weightedMeasure, withDensity_apply _ hQm]
    calc (∫⁻ x in Q, ENNReal.ofReal (ρ x)) ≤ ∫⁻ _x in Q, ENNReal.ofReal Cρ := by
          refine setLIntegral_mono' hQm (fun x hx => ENNReal.ofReal_le_ofReal ?_)
          exact (le_abs_self _).trans (hCρ x hx)
      _ = ENNReal.ofReal Cρ * volume Q := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQb.measure_lt_top
  have hac : volume.restrict Q ≪ (weightedMeasure ρ).restrict Q := by
    rw [weightedMeasure, restrict_withDensity hQm]
    exact withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp hρc.measurable).aemeasurable
      (ae_of_all _ (fun x => by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hρpos x))
  have hmem1 : MemLp f 2
      ((weightedMeasure ρ).restrict Q) :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖ (Eventually.of_forall f.norm_coe_le_norm)
  have hsol := hLD.2.2 Q hQo hQb lam⁻¹ (inv_pos.2 hlam) f
    (by rw [← hρdef]; exact hmem1)
  obtain ⟨u0, hu0a, hu0w⟩ := hsol
  rw [← hρdef] at hu0a
  rw [← hρdef, ← hcdef, inv_inv] at hu0w
  -- `u0 = λ S` Lebesgue-a.e. on the cube
  have hu0S : ∀ᵐ x ∂volume.restrict Q, u0.toH1Function.toFun x = lam * S x := by
    filter_upwards [hac.ae_le hu0a] with x hx
    rw [hx, aux_cor_as_resolvent_killed_normalization K law hL Q hQo lam hlam f x, hSdef]
  -- the killed carrier of `u0`
  subst hQdef
  have hK := _root_.SubdiffusiveProcess.EllipticRegularity.exists_killedSobolevGraph_of_nativeH10 (Ω := centeredCube z r hr) u0
  obtain ⟨U, hUv, hUg⟩ := hK
  refine ⟨lam⁻¹ • U, ?_, ?_⟩
  · have hsm := Lp.coeFn_smul lam⁻¹ (U : SobolevData (centeredCube z r hr)).1
    have hc1 : ((lam⁻¹ • U : killedSobolevGraph (centeredCube z r hr)) :
        SobolevData (centeredCube z r hr)).1 = lam⁻¹ • (U : SobolevData (centeredCube z r hr)).1 :=
      rfl
    rw [hc1]
    filter_upwards [hsm, hUv, hu0S] with x h1 h2 h3
    rw [h1, Pi.smul_apply, smul_eq_mul, h2, h3, hSdef, ← mul_assoc, inv_mul_cancel₀ hlam.ne',
      one_mul]
  · intro w
    have hφ := exists_nativeH10Function_of_killedSobolevGraph w
    obtain ⟨φ, hφv, hφg⟩ := hφ
    have heq := hu0w φ
    -- left side: the coefficient form
    have hL1 : sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        (lam⁻¹ • U : killedSobolevGraph (centeredCube z r hr)).val w.val =
        lam⁻¹ * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
          U.val w.val := by
      rw [Submodule.coe_smul, map_smul, smul_apply, smul_eq_mul]
    have hgradU : ∀ i : Fin d, MemLp (fun x => u0.toH1Function.grad x i) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      fun i => u0.toH1Function.gradMemL2 i
    have hgradφ : ∀ i : Fin d, MemLp (fun x => φ.toH1Function.grad x i) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      fun i => φ.toH1Function.gradMemL2 i
    have hcm : AEStronglyMeasurable c
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hcc.aestronglyMeasurable
    have hL2 : sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        U.val w.val =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          Homogenization.vecDot (c x • u0.toH1Function.grad x) (φ.toH1Function.grad x) := by
      rw [_root_.SubdiffusiveProcess.EllipticRegularity.sobolevCoefficientForm_eq_sum_integral]
      have hsum : (fun x => Homogenization.vecDot (c x • u0.toH1Function.grad x) (φ.toH1Function.grad x)) =
          fun x => ∑ i : Fin d, c x * (u0.toH1Function.grad x i * φ.toH1Function.grad x i) := by
        funext x
        simp only [Homogenization.vecDot, Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [hsum, integral_finsetSum _ (fun i _ =>
        aux_torsion_bound_int_w_mul _ c _ _ Cc hcm hcb (hgradU i) (hgradφ i))]
      refine Finset.sum_congr rfl (fun i _ => integral_congr_ae ?_)
      filter_upwards [aux_torsion_bound_coef_ae M H omega N z hr, hUg i] with x hx1 hx2
      rw [hx1, hx2, ← hcdef]
      have hw : (w : SobolevData (centeredCube z r hr)).2 i x = φ.toH1Function.grad x i := by
        rw [hφg]
      rw [hw]
    -- right side: the speed-measure pairing
    have hR1 : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (f x - lam * aux_cor_as_resolvent_occupation K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) *
          (w : SobolevData (centeredCube z r hr)).1 x ∂(cutoffSpeedMeasure M H omega N)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          (ρ x * (f x * φ.toH1Function.toFun x) - ρ x * u0.toH1Function.toFun x * φ.toH1Function.toFun x) := by
      rw [aux_torsion_bound_speed_integral M H omega N _ hQm, ← hρdef]
      refine integral_congr_ae ?_
      filter_upwards [hu0S] with x hx
      have hw : (w : SobolevData (centeredCube z r hr)).1 x = φ.toH1Function.toFun x := by
        have := congrFun hφv x
        exact this.symm
      have hS' : (aux_cor_as_resolvent_occupation K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) = S x := by rw [hSdef]
      rw [hw, hS', ← hx]
      ring
    have hφL2 : MemLp φ.toH1Function.toFun 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      φ.toH1Function.memL2
    have hu0L2 : MemLp u0.toH1Function.toFun 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      u0.toH1Function.memL2
    have hρm : AEStronglyMeasurable ρ
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hρc.aestronglyMeasurable
    have hi1 : Integrable (fun x => ρ x * (f x * φ.toH1Function.toFun x))
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      aux_torsion_bound_int_w_mul _ ρ f _ Cρ hρm hρb
        (MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
          (Eventually.of_forall f.norm_coe_le_norm)) hφL2
    have hi2 : Integrable (fun x => ρ x * (u0.toH1Function.toFun x * φ.toH1Function.toFun x))
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      aux_torsion_bound_int_w_mul _ ρ _ _ Cρ hρm hρb hu0L2 hφL2
    have hi2' : Integrable (fun x => ρ x * u0.toH1Function.toFun x * φ.toH1Function.toFun x)
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hi2.congr (ae_of_all _ (fun x => by ring))
    have hRHS := hR1.trans (integral_sub hi1 hi2')
    have hsrc : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ρ x * (lam * f x) * φ.toH1Function.toFun x) =
        lam * ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ρ x * (f x * φ.toH1Function.toFun x) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ (fun x => by ring))
    rw [hsrc] at heq
    have hv : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        Homogenization.vecDot (c x • u0.toH1Function.grad x) (φ.toH1Function.grad x)) =
        lam * ((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ρ x * (f x * φ.toH1Function.toFun x)) -
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ρ x * u0.toH1Function.toFun x * φ.toH1Function.toFun x) := by
      linarith
    exact hL1.trans ((congrArg (fun y => lam⁻¹ * y) (hL2.trans hv)).trans
      ((inv_mul_cancel_left₀ hlam.ne' _).trans hRHS.symm))


theorem aux_cor_as_resolvent_hcamp_glue {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : IsOpen W) {f g : SpatialCoordinates d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : f =ᵐ[volume.restrict W] g) : Set.EqOn f g (closure W) := by
  have hWmeas : MeasurableSet W := hW.measurableSet
  have hWeq : Set.EqOn f g W := by
    intro x hx
    by_contra hne
    set c : ℝ := |f x - g x| / 2 with hcdef
    have hcpos : 0 < |f x - g x| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hc : 0 < c := by rw [hcdef]; linarith
    have hcontabs : Continuous (fun w => |f w - g w|) := (hf.sub hg).abs
    have hWx : IsOpen (W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c)) :=
      hW.inter (hcontabs.isOpen_preimage _ isOpen_Ioi)
    have hxW : x ∈ W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c) := by
      refine ⟨hx, ?_⟩
      simp only [Set.mem_preimage, Set.mem_Ioi, hcdef]
      linarith
    have hWpos : 0 < volume (W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c)) :=
      hWx.measure_pos volume ⟨x, hxW⟩
    have hbad : volume (W ∩ {w | f w ≠ g w}) = 0 := by
      have h1 : volume.restrict W {w | f w ≠ g w} = 0 := ae_iff.mp hfg
      rwa [Measure.restrict_apply' hWmeas, Set.inter_comm] at h1
    have hsub : W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c) ⊆ W ∩ {w | f w ≠ g w} := by
      rintro w ⟨hw1, hw2⟩
      refine ⟨hw1, ?_⟩
      simp only [Set.mem_preimage, Set.mem_Ioi] at hw2
      intro heq
      rw [heq] at hw2
      simp at hw2
      linarith
    have : volume (W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c)) ≤
        volume (W ∩ {w | f w ≠ g w}) := measure_mono hsub
    rw [hbad] at this
    exact absurd (le_antisymm this (bot_le)) (ne_of_gt hWpos)
  exact hWeq.closure hf hg

/-- The Euclidean coordinate distance is controlled by `Real.sqrt d` times the ambient
(sup-norm) `dist`. -/
theorem aux_cor_as_resolvent_hcamp_euclid_le {d : ℕ} (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * dist x y := by
  have hcoord : ∀ j : Fin d, (x j - y j) ^ 2 ≤ (dist x y) ^ 2 := by
    intro j
    have hj : dist (x j) (y j) ≤ dist x y := dist_le_pi_dist x y j
    rw [Real.dist_eq] at hj
    have h0 : 0 ≤ |x j - y j| := abs_nonneg _
    calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
      _ ≤ (dist x y) ^ 2 := pow_le_pow_left₀ h0 hj 2
  have hsum : (∑ j : Fin d, (x j - y j) ^ 2) ≤ (d : ℝ) * (dist x y) ^ 2 := by
    calc (∑ j : Fin d, (x j - y j) ^ 2) ≤ ∑ _j : Fin d, (dist x y) ^ 2 :=
          Finset.sum_le_sum fun j _ => hcoord j
      _ = (d : ℝ) * (dist x y) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt ((d : ℝ) * (dist x y) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * dist x y := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq dist_nonneg]

/-- Pointwise Hölder increment on a closed cube of side `r ≤ 1`, in terms of the ambient
`dist` (sup-norm) rather than the Euclidean coordinate distance baked into
`holderSeminorm`. -/
theorem aux_cor_as_resolvent_hcamp_holder_pt {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) {alpha : ℝ} (ha0 : 0 < alpha)
    {U : SpatialCoordinates d → ℝ}
    (hH : IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U)
    {K : ℝ} (hKle : holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ K)
    (hK0 : 0 ≤ K)
    {x y : SpatialCoordinates d}
    (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)))
    (hy : y ∈ (closedCube z r hr : Set (SpatialCoordinates d))) :
    |U x - U y| ≤ K * (Real.sqrt d) ^ alpha * dist x y ^ alpha := by
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero]
    positivity
  · set e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with hedef
    have he0 : 0 < e := by
      rw [hedef, Real.sqrt_pos]
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra h
        push Not at h
        exact hxy (funext h)
      have hjpos : 0 < (x j - y j) ^ 2 := by
        have hne : x j - y j ≠ 0 := sub_ne_zero.mpr hj
        positivity
      exact lt_of_lt_of_le hjpos
        (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ j))
    have hea : 0 < e ^ alpha := Real.rpow_pos_of_pos he0 _
    have hratio : |U x - U y| / e ^ alpha ≤
        holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U :=
      le_csSup hH ⟨x, hx, y, hy, hxy, rfl⟩
    have h1 : |U x - U y| ≤
        holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U * e ^ alpha :=
      (div_le_iff₀ hea).mp hratio
    have h2 : holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U * e ^ alpha
        ≤ K * e ^ alpha := mul_le_mul_of_nonneg_right hKle hea.le
    have hele := aux_cor_as_resolvent_hcamp_euclid_le x y
    have he3 : e ^ alpha ≤ (Real.sqrt d * dist x y) ^ alpha :=
      Real.rpow_le_rpow he0.le hele ha0.le
    have he4 : (Real.sqrt d * dist x y) ^ alpha =
        (Real.sqrt d) ^ alpha * (dist x y) ^ alpha :=
      Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg
    calc |U x - U y| ≤
          holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U * e ^ alpha :=
          h1
      _ ≤ K * e ^ alpha := h2
      _ ≤ K * (Real.sqrt d * dist x y) ^ alpha := mul_le_mul_of_nonneg_left he3 hK0
      _ = K * ((Real.sqrt d) ^ alpha * (dist x y) ^ alpha) := by rw [he4]
      _ = K * (Real.sqrt d) ^ alpha * dist x y ^ alpha := by ring


/-- Elementary 1-D interval overlap: a ball of radius `rad ≤ r` centred anywhere in the
open interval of half-width `r/2` around `c` meets that interval in a set of length at
least `rad`. -/
theorem aux_cor_as_resolvent_hcamp_overlap1d {c t r rad : ℝ}
    (hrad : 0 < rad) (hle : rad ≤ r) (ht0 : c - r / 2 < t) (ht1 : t < c + r / 2) :
    rad ≤ min (t + rad) (c + r / 2) - max (t - rad) (c - r / 2) := by
  rcases le_total (t + rad) (c + r / 2) with h1 | h1 <;>
    rcases le_total (t - rad) (c - r / 2) with h2 | h2 <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h1, h2] <;>
    linarith

/-- `d`-dimensional density: the (sup-norm) ball of radius `rad ≤ 1` around an interior
point `x'` of the unit-side cube centred at `c` meets that cube in a set whose volume is
at least `2⁻ᵈ` times the volume of the whole ball. -/
theorem aux_cor_as_resolvent_hcamp_density {d : ℕ} (c x' : SpatialCoordinates d) {rad : ℝ}
    (hrad : 0 < rad) (hrad1 : rad ≤ 1)
    (hx' : x' ∈ (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) :
    volume.real (Metric.ball x' rad) ≤
      (2 : ℝ) ^ d * volume.real (Metric.ball x' rad ∩
        (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) := by
  have hballpi : Metric.ball x' rad = Set.pi Set.univ (fun i => Set.Ioo (x' i - rad) (x' i + rad)) := by
    rw [ball_pi x' hrad]
    congr 1
    funext i
    rw [Real.ball_eq_Ioo]
  have hcubepi : (centeredCube c 1 one_pos : Set (SpatialCoordinates d)) =
      Set.pi Set.univ (fun i => Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    rw [centeredCube_eq_pi]
  have hinterpi : Metric.ball x' rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)) =
      Set.pi Set.univ (fun i => Set.Ioo (x' i - rad) (x' i + rad) ∩
        Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    rw [hballpi, hcubepi]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies, forall_and]
  have hx'i : ∀ i, c i - 1 / 2 < x' i ∧ x' i < c i + 1 / 2 := by
    intro i
    have h := hx'
    rw [hcubepi] at h
    exact Set.mem_univ_pi.mp h i
  have hover : ∀ i, rad ≤ volume.real (Set.Ioo (x' i - rad) (x' i + rad) ∩
      Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    intro i
    rw [Set.Ioo_inter_Ioo, Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by
        have := aux_cor_as_resolvent_hcamp_overlap1d (c := c i) (t := x' i) (r := 1) (rad := rad)
          hrad hrad1 (hx'i i).1 (hx'i i).2
        linarith)]
    exact aux_cor_as_resolvent_hcamp_overlap1d (c := c i) (t := x' i) (r := 1) (rad := rad)
      hrad hrad1 (hx'i i).1 (hx'i i).2
  have hballvol : volume.real (Metric.ball x' rad) = (2 * rad) ^ d := by
    rw [Measure.real, hballpi, volume_pi_pi]
    have : ∀ i : Fin d, volume (Set.Ioo (x' i - rad) (x' i + rad)) =
        ENNReal.ofReal (2 * rad) := by
      intro i; rw [Real.volume_Ioo]; ring_nf
    rw [Finset.prod_congr rfl (fun i _ => this i)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by linarith)]
    exact ENNReal.toReal_ofReal (by positivity)
  have hinterval : volume.real (Metric.ball x' rad ∩
      (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) =
      ∏ i : Fin d, volume.real (Set.Ioo (x' i - rad) (x' i + rad) ∩
        Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    rw [Measure.real, hinterpi, volume_pi_pi, ENNReal.toReal_prod]
    rfl
  have hprodle : (rad : ℝ) ^ d ≤ ∏ i : Fin d, volume.real (Set.Ioo (x' i - rad) (x' i + rad) ∩
      Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    calc (rad : ℝ) ^ d = ∏ _i : Fin d, rad := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => hrad.le) (fun i _ => hover i)
  rw [hballvol, hinterval]
  calc (2 * rad) ^ d = (2:ℝ) ^ d * rad ^ d := by ring
    _ ≤ (2:ℝ) ^ d * ∏ i : Fin d, volume.real (Set.Ioo (x' i - rad) (x' i + rad) ∩
        Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) :=
      mul_le_mul_of_nonneg_left hprodle (by positivity)


/-- The mean minimizes the `L²` oscillation: for any competitor constant `c`, the
`L²(S)` distance to the mean of `u` over `S` is at most the `L²(S)` distance to `c`. -/
theorem aux_cor_as_resolvent_hcamp_variance {d : ℕ} {S : Set (SpatialCoordinates d)}
    (hSfin : volume S ≠ ⊤)
    {u : SpatialCoordinates d → ℝ} (hu : IntegrableOn u S volume)
    (hu2 : IntegrableOn (fun x => u x ^ 2) S volume) (c : ℝ) :
    (∫ y in S, (u y - (volume.real S)⁻¹ * ∫ w in S, u w) ^ 2) ≤ ∫ y in S, (u y - c) ^ 2 := by
  set m : ℝ := (volume.real S)⁻¹ * ∫ w in S, u w with hmdef
  by_cases hS0 : volume.real S = 0
  · have hSz : volume S = 0 := by
      rwa [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left hSfin] at hS0
    have hRz : volume.restrict S = 0 := Measure.restrict_eq_zero.mpr hSz
    simp [hRz]
  · have hconstInt : ∀ k : ℝ, IntegrableOn (fun _ : SpatialCoordinates d => k) S volume :=
      fun k => integrableOn_const hSfin
    have hmuInt : IntegrableOn (fun y => m * u y) S volume := hu.const_mul m
    have hu_m_sq : IntegrableOn (fun y => (u y - m) ^ 2) S volume := by
      have hEq : (fun y => (u y - m) ^ 2) =
          (fun y => u y ^ 2 - 2 * m * u y + m ^ 2) := funext fun y => by ring
      rw [hEq]
      exact ((hu2.sub ((hu.const_mul (2 * m)))).add (hconstInt (m ^ 2)))
    have hu_c_sq : IntegrableOn (fun y => (u y - c) ^ 2) S volume := by
      have hEq : (fun y => (u y - c) ^ 2) =
          (fun y => u y ^ 2 - 2 * c * u y + c ^ 2) := funext fun y => by ring
      rw [hEq]
      exact ((hu2.sub ((hu.const_mul (2 * c)))).add (hconstInt (c ^ 2)))
    have hInt2u : IntegrableOn (fun y => 2 * u y - (c + m)) S volume :=
      (hu.const_mul 2).sub (hconstInt (c + m))
    have hdiffPt : ∀ y, (u y - c) ^ 2 - (u y - m) ^ 2 = (m - c) * (2 * u y - (c + m)) := by
      intro y; ring
    have hSumEq : (fun y => (u y - c) ^ 2) =
        (fun y => (u y - m) ^ 2 + (m - c) * (2 * u y - (c + m))) := by
      funext y; have := hdiffPt y; linarith
    have hInt3 : IntegrableOn (fun y => (m - c) * (2 * u y - (c + m))) S volume :=
      hInt2u.const_mul (m - c)
    have hsplit : (∫ y in S, (u y - c) ^ 2) =
        (∫ y in S, (u y - m) ^ 2) + ∫ y in S, (m - c) * (2 * u y - (c + m)) := by
      rw [hSumEq]
      exact integral_add hu_m_sq hInt3
    have hcrossVal : (∫ y in S, (m - c) * (2 * u y - (c + m))) = (m - c) ^ 2 * volume.real S := by
      rw [integral_const_mul]
      have hInt2uEq : (∫ y in S, (2 * u y - (c + m))) =
          2 * (∫ y in S, u y) - (c + m) * volume.real S := by
        rw [integral_sub (hu.const_mul 2) (hconstInt (c + m)), integral_const_mul,
          MeasureTheory.setIntegral_const]
        simp [Measure.real, smul_eq_mul, mul_comm]
      rw [hInt2uEq]
      have hmuEq : (∫ y in S, u y) = m * volume.real S := by
        rw [hmdef]; field_simp
      rw [hmuEq]; ring
    rw [hsplit, hcrossVal]
    have hnn : 0 ≤ (m - c) ^ 2 * volume.real S := by positivity
    linarith


/-- A locally integrable function with locally integrable square is `MemLp 2` on any
cube. -/
theorem aux_cor_as_resolvent_hcamp_memLp {d : ℕ} {u : SpatialCoordinates d → ℝ}
    (hLIu : LocallyIntegrable u volume) (hLIu2 : LocallyIntegrable (fun x => u x ^ 2) volume)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    MemLp u 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hIntClosed : IntegrableOn u (closedCube z r hr : Set (SpatialCoordinates d)) volume :=
    hLIu.integrableOn_isCompact (closedCube z r hr).isCompact
  have hInt2Closed : IntegrableOn (fun x => u x ^ 2) (closedCube z r hr : Set (SpatialCoordinates d))
      volume := hLIu2.integrableOn_isCompact (closedCube z r hr).isCompact
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube z r hr : Set (SpatialCoordinates d)) := centeredCube_subset_closedCube z hr
  have hInt2 : IntegrableOn (fun x => u x ^ 2) (centeredCube z r hr : Set (SpatialCoordinates d))
      volume := hInt2Closed.mono_set hsub
  have hMeas : AEStronglyMeasurable u (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (hIntClosed.mono_set hsub).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hMeas).mpr hInt2


/-- Transfer the whole-space (unintersected-ball) `L²` oscillation hypothesis to the
Campanato hypothesis on a side-`1` cube, at a centre `x'` inside the cube and any radius
`rad ≤ 1`: the mean-minimizing property (`variance`) plus the `2^d` density bound. -/
theorem aux_cor_as_resolvent_hcamp_osc1 {d : ℕ} {u : SpatialCoordinates d → ℝ} {A alpha : ℝ}
    (hLIu : LocallyIntegrable u volume) (hLIu2 : LocallyIntegrable (fun x => u x ^ 2) volume)
    (hosc : ∀ (x : SpatialCoordinates d) (rad : ℝ), 0 < rad → rad ≤ 1 →
      (∫ y in Metric.ball x rad, (u y - (volume.real (Metric.ball x rad))⁻¹ *
        ∫ w in Metric.ball x rad, u w) ^ 2) ≤
        A ^ 2 * volume.real (Metric.ball x rad) * rad ^ (2 * alpha))
    (c : SpatialCoordinates d) (x' : SpatialCoordinates d)
    (hx' : x' ∈ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)))
    (rad : ℝ) (hrad : 0 < rad) (hrad1 : rad ≤ 1) :
    (∫ y in Metric.ball x' rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)),
        (u y - (volume.real (Metric.ball x' rad ∩
              (centeredCube c 1 one_pos : Set (SpatialCoordinates d))))⁻¹ *
            ∫ w in Metric.ball x' rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)),
              u w) ^ 2) ≤
      (A * (2 : ℝ) ^ ((d : ℝ) / 2)) ^ 2 * rad ^ (2 * alpha) *
        volume.real (Metric.ball x' rad ∩
          (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) := by
  set B : Set (SpatialCoordinates d) := Metric.ball x' rad with hBdef
  set S : Set (SpatialCoordinates d) := B ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d))
    with hSdef
  set mB : ℝ := (volume.real B)⁻¹ * ∫ w in B, u w with hmBdef
  have hBfin : volume B ≠ ⊤ := (measure_ball_lt_top).ne
  have hSfin : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono (hSdef ▸ Set.inter_subset_left))
  have hIntBClosed : IntegrableOn u (Metric.closedBall x' rad) volume :=
    hLIu.integrableOn_isCompact (isCompact_closedBall x' rad)
  have hInt2BClosed : IntegrableOn (fun x => u x ^ 2) (Metric.closedBall x' rad) volume :=
    hLIu2.integrableOn_isCompact (isCompact_closedBall x' rad)
  have hBsub : B ⊆ Metric.closedBall x' rad := Metric.ball_subset_closedBall
  have hIntB : IntegrableOn u B volume := hIntBClosed.mono_set hBsub
  have hInt2B : IntegrableOn (fun x => u x ^ 2) B volume := hInt2BClosed.mono_set hBsub
  have hSsub : S ⊆ B := hSdef ▸ Set.inter_subset_left
  have hIntS : IntegrableOn u S volume := hIntB.mono_set hSsub
  have hInt2S : IntegrableOn (fun x => u x ^ 2) S volume := hInt2B.mono_set hSsub
  have hconstIntB : IntegrableOn (fun _ : SpatialCoordinates d => mB) B volume :=
    integrableOn_const hBfin
  have hsqIntB : IntegrableOn (fun y => (u y - mB) ^ 2) B volume := by
    have hEq : (fun y => (u y - mB) ^ 2) = (fun y => u y ^ 2 - 2 * mB * u y + mB ^ 2) :=
      funext fun y => by ring
    rw [hEq]
    exact ((hInt2B.sub (hIntB.const_mul (2 * mB))).add (integrableOn_const hBfin))
  -- Step 1: the mean over `S` minimizes the `L²(S)` distance among all constants,
  -- in particular the competitor `mB`.
  have hstep1 := aux_cor_as_resolvent_hcamp_variance (S := S) hSfin hIntS hInt2S mB
  -- Step 2: extending the domain of integration from `S` to `B ⊇ S` only adds a
  -- nonnegative amount (the integrand is a square).
  have hstep2 : (∫ y in S, (u y - mB) ^ 2) ≤ ∫ y in B, (u y - mB) ^ 2 :=
    setIntegral_mono_set hsqIntB
      (Filter.Eventually.of_forall fun y => sq_nonneg _) hSsub.eventuallyLE
  -- Step 3: the global hypothesis at the centre `x'`, radius `rad`.
  have hstep3 : (∫ y in B, (u y - mB) ^ 2) ≤ A ^ 2 * volume.real B * rad ^ (2 * alpha) :=
    hosc x' rad hrad hrad1
  -- Step 4: `2^d`-density of `S` inside `B`.
  have hstep4 : volume.real B ≤ (2 : ℝ) ^ d * volume.real S :=
    aux_cor_as_resolvent_hcamp_density c x' hrad hrad1 hx'
  have hA2nn : (0:ℝ) ≤ A ^ 2 := sq_nonneg _
  have hradnn : (0:ℝ) ≤ rad ^ (2 * alpha) := by positivity
  have hchain : (∫ y in S, (u y - (volume.real S)⁻¹ * ∫ w in S, u w) ^ 2) ≤
      A ^ 2 * ((2 : ℝ) ^ d * volume.real S) * rad ^ (2 * alpha) := by
    calc (∫ y in S, (u y - (volume.real S)⁻¹ * ∫ w in S, u w) ^ 2)
        ≤ ∫ y in S, (u y - mB) ^ 2 := hstep1
      _ ≤ ∫ y in B, (u y - mB) ^ 2 := hstep2
      _ ≤ A ^ 2 * volume.real B * rad ^ (2 * alpha) := hstep3
      _ ≤ A ^ 2 * ((2:ℝ) ^ d * volume.real S) * rad ^ (2 * alpha) := by
          have := mul_le_mul_of_nonneg_left hstep4 hA2nn
          exact mul_le_mul_of_nonneg_right this hradnn
  have hfinal : A ^ 2 * ((2:ℝ) ^ d * volume.real S) * rad ^ (2 * alpha) =
      (A * (2:ℝ) ^ ((d:ℝ)/2)) ^ 2 * rad ^ (2 * alpha) * volume.real S := by
    have h2d : ((2:ℝ) ^ ((d:ℝ)/2)) ^ 2 = (2:ℝ) ^ d := by
      rw [← Real.rpow_natCast (2:ℝ) d, ← Real.rpow_two, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [mul_pow]
    rw [h2d]
    ring
  rw [hfinal] at hchain
  exact hchain


/-- The Campanato representative on a single side-`1` cube centred at `c`, built from
`Cp` and the whole-space oscillation hypothesis, with the `2^{d/2}`-inflated seminorm
bound. -/
theorem aux_cor_as_resolvent_hcamp_cell {d : ℕ} (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    {u : SpatialCoordinates d → ℝ} {A : ℝ} (hA0 : 0 ≤ A)
    (hLIu : LocallyIntegrable u volume) (hLIu2 : LocallyIntegrable (fun x => u x ^ 2) volume)
    (hosc : ∀ (x : SpatialCoordinates d) (rad : ℝ), 0 < rad → rad ≤ 1 →
      (∫ y in Metric.ball x rad, (u y - (volume.real (Metric.ball x rad))⁻¹ *
        ∫ w in Metric.ball x rad, u w) ^ 2) ≤
        A ^ 2 * volume.real (Metric.ball x rad) * rad ^ (2 * alpha))
    (c : SpatialCoordinates d) :
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      U =ᵐ[volume.restrict (centeredCube c 1 one_pos : Set (SpatialCoordinates d))] u ∧
      IsHolderOn alpha (closedCube c 1 one_pos : Set (SpatialCoordinates d)) U ∧
      holderSeminorm alpha (closedCube c 1 one_pos : Set (SpatialCoordinates d)) U ≤
        Cp.C alpha * (A * (2 : ℝ) ^ ((d : ℝ) / 2)) := by
  have hMemLp := aux_cor_as_resolvent_hcamp_memLp hLIu hLIu2 c 1 one_pos
  set uk : DomainL2 (centeredCube c 1 one_pos) := hMemLp.toLp u with hukdef
  have hukAE : (uk : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube c 1 one_pos : Set (SpatialCoordinates d))] u := by
    rw [hukdef]; exact MemLp.coeFn_toLp hMemLp
  have hAK0 : (0:ℝ) ≤ A * (2:ℝ) ^ ((d:ℝ)/2) := by positivity
  have hoscHyp : ∀ x ∈ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)),
      ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
      (∫ y in Metric.ball x rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)),
          (uk y - setAverage (Metric.ball x rad ∩
              (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) uk) ^ 2
          ∂volume.restrict (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) ≤
        (A * (2:ℝ) ^ ((d:ℝ)/2)) ^ 2 * rad ^ (2 * alpha) *
          volume.real (Metric.ball x rad ∩
            (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) := by
    intro x hx rad hrad hrad1
    set S : Set (SpatialCoordinates d) :=
      Metric.ball x rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)) with hSdef
    have hSsub : S ⊆ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)) :=
      hSdef ▸ Set.inter_subset_right
    have hukAES : (uk : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict S] u :=
      ae_restrict_of_ae_restrict_of_subset hSsub hukAE
    have hRestr : (volume.restrict (centeredCube c 1 one_pos : Set (SpatialCoordinates d))).restrict
        S = volume.restrict S := Measure.restrict_restrict_of_subset hSsub
    have hAvgEq : setAverage S uk = (volume.real S)⁻¹ * ∫ w in S, u w := by
      unfold setAverage
      rw [hRestr, integral_congr_ae hukAES]
    have hintEq : (∫ y in S, (uk y - setAverage S uk) ^ 2
        ∂volume.restrict (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) =
        ∫ y in S, (u y - (volume.real S)⁻¹ * ∫ w in S, u w) ^ 2 := by
      rw [hRestr, hAvgEq]
      exact integral_congr_ae (hukAES.mono fun y hy => by simp only [hy])
    rw [hintEq]
    exact aux_cor_as_resolvent_hcamp_osc1 hLIu hLIu2 hosc c x hx rad hrad hrad1
  obtain ⟨U, hUcont, hUae, hUholder, hUsemi⟩ := Cp.holder_of_campanato alpha ha0 ha1 c 1 one_pos
    le_rfl uk (A * (2:ℝ) ^ ((d:ℝ)/2)) hAK0 hoscHyp
  exact ⟨U, hUcont, hUae.symm.trans hukAE, hUholder, hUsemi⟩


/-- If `x` lies in an open set `A` and in the closure of `B`, it lies in the closure of
`A ∩ B`. (No delicate boundary/tangency argument needed: `IsOpen.closure_inter` does the
work.) -/
theorem aux_cor_as_resolvent_hcamp_mem_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} {x : X} (hA : IsOpen A) (hxA : x ∈ A) (hxB : x ∈ closure B) :
    x ∈ closure (A ∩ B) := by
  have hmem : x ∈ closure (B ∩ A) := (hA.closure_inter (s := B)) ⟨hxB, hxA⟩
  rwa [Set.inter_comm] at hmem


/-- Two Campanato representatives on side-`1` cells that both approximate the same `u`
agree pointwise at any point `x` that lies in the (open) first cell and in the closure
of the second. -/
theorem aux_cor_as_resolvent_hcamp_bridge {d : ℕ} {u : SpatialCoordinates d → ℝ}
    {k1 k2 : SpatialCoordinates d} {U1 U2 : SpatialCoordinates d → ℝ}
    (hU1cont : Continuous U1) (hU2cont : Continuous U2)
    (hU1ae : U1 =ᵐ[volume.restrict (centeredCube k1 1 one_pos : Set (SpatialCoordinates d))] u)
    (hU2ae : U2 =ᵐ[volume.restrict (centeredCube k2 1 one_pos : Set (SpatialCoordinates d))] u)
    {x : SpatialCoordinates d} (hx1 : x ∈ (centeredCube k1 1 one_pos : Set (SpatialCoordinates d)))
    (hx2 : x ∈ closure (centeredCube k2 1 one_pos : Set (SpatialCoordinates d))) :
    U1 x = U2 x := by
  have hW : IsOpen ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d))) :=
    (centeredCube k1 1 one_pos).isOpen.inter (centeredCube k2 1 one_pos).isOpen
  have hxW : x ∈ closure ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d))) :=
    aux_cor_as_resolvent_hcamp_mem_closure_inter (centeredCube k1 1 one_pos).isOpen hx1 hx2
  have h1 : U1 =ᵐ[volume.restrict ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d)))] u :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hU1ae
  have h2 : U2 =ᵐ[volume.restrict ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d)))] u :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hU2ae
  exact aux_cor_as_resolvent_hcamp_glue hW hU1cont hU2cont (h1.trans h2.symm) hxW


/-- Two points at sup-norm distance `≤ 1` both lie in the closure of the side-`1` cube
centred at their coordinatewise midpoint. -/
theorem aux_cor_as_resolvent_hcamp_midpoint_mem {d : ℕ} (x y : SpatialCoordinates d)
    (hxy : dist x y ≤ 1) :
    x ∈ closure (centeredCube (fun i => (x i + y i) / 2) 1 one_pos :
        Set (SpatialCoordinates d)) ∧
    y ∈ closure (centeredCube (fun i => (x i + y i) / 2) 1 one_pos :
        Set (SpatialCoordinates d)) := by
  set m : SpatialCoordinates d := fun i => (x i + y i) / 2 with hmdef
  have hclos : closure (centeredCube m 1 one_pos : Set (SpatialCoordinates d)) =
      (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := by
    show closure (Metric.ball m (1 / 2)) = Metric.closedBall m (1 / 2)
    exact closure_ball m (by norm_num)
  have hxyi : ∀ i, |x i - y i| ≤ dist x y := by
    intro i
    have h := dist_le_pi_dist x y i
    rwa [Real.dist_eq] at h
  have hdxm : dist x m ≤ 1 / 2 := by
    rw [dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 1/2)]
    intro i
    rw [Real.dist_eq]
    have hxi : x i - m i = (x i - y i) / 2 := by rw [hmdef]; ring
    rw [hxi, abs_div]
    have h2 : |(2:ℝ)| = 2 := by norm_num
    rw [h2]
    linarith [hxyi i]
  have hdym : dist y m ≤ 1 / 2 := by
    rw [dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 1/2)]
    intro i
    rw [Real.dist_eq]
    have hyi : y i - m i = -(x i - y i) / 2 := by rw [hmdef]; ring
    rw [hyi, abs_div, abs_neg]
    have h2 : |(2:ℝ)| = 2 := by norm_num
    rw [h2]
    linarith [hxyi i]
  refine ⟨hclos ▸ ?_, hclos ▸ ?_⟩
  · exact Metric.mem_closedBall.mpr hdxm
  · exact Metric.mem_closedBall.mpr hdym


/-- The lattice index of `x` on the spacing-`1/3` grid (`Fin d → ℤ` is countable — this
is what keeps the assembled `v` a.e. equal to `u`: a countable union of null sets is
null, but a per-point-own-cell construction would not have this property since its
index set (all of `SpatialCoordinates d`) is uncountable). -/
def aux_cor_as_resolvent_hcamp_idx {d : ℕ} (x : SpatialCoordinates d) : Fin d → ℤ :=
  fun i => round (3 * x i)

/-- The real centre of lattice cell `k`. -/
def aux_cor_as_resolvent_hcamp_center {d : ℕ} (k : Fin d → ℤ) : SpatialCoordinates d :=
  fun i => ((k i : ℤ) : ℝ) / 3

/-- The "home" cell centre of `x`: rounding each coordinate of `3x` to the nearest
integer and dividing by `3` lies strictly inside the open side-`1` cell centred there
(margin `1/2 - 1/6 = 1/3 > 0`, so no boundary/tie case is an issue, unlike a
spacing-`1/2` grid). -/
def aux_cor_as_resolvent_hcamp_home {d : ℕ} (x : SpatialCoordinates d) : SpatialCoordinates d :=
  aux_cor_as_resolvent_hcamp_center (aux_cor_as_resolvent_hcamp_idx x)

theorem aux_cor_as_resolvent_hcamp_home_mem {d : ℕ} (x : SpatialCoordinates d) :
    x ∈ (centeredCube (aux_cor_as_resolvent_hcamp_home x) 1 one_pos :
        Set (SpatialCoordinates d)) := by
  show x ∈ Metric.ball (aux_cor_as_resolvent_hcamp_home x) (1 / 2)
  rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num : (0:ℝ) < 1 / 2)]
  intro i
  rw [Real.dist_eq]
  have hr := abs_sub_round (3 * x i)
  have heq : x i - aux_cor_as_resolvent_hcamp_home x i =
      (3 * x i - ((round (3 * x i) : ℤ) : ℝ)) / 3 := by
    unfold aux_cor_as_resolvent_hcamp_home aux_cor_as_resolvent_hcamp_center
      aux_cor_as_resolvent_hcamp_idx
    ring
  rw [heq, abs_div]
  have h3 : |(3:ℝ)| = 3 := by norm_num
  rw [h3]
  linarith


/-- Assembling cellwise-a.e.-equal representatives along `aux_cor_as_resolvent_hcamp_idx`
gives a globally a.e.-equal function, because the index set `Fin d → ℤ` is countable. -/
theorem aux_cor_as_resolvent_hcamp_ae_of_cellwise {d : ℕ} {u : SpatialCoordinates d → ℝ}
    {Uf : (Fin d → ℤ) → SpatialCoordinates d → ℝ}
    (hUfae : ∀ k : Fin d → ℤ, Uf k =ᵐ[volume.restrict
        (centeredCube (aux_cor_as_resolvent_hcamp_center k) 1 one_pos :
          Set (SpatialCoordinates d))] u) :
    (fun x => Uf (aux_cor_as_resolvent_hcamp_idx x) x) =ᵐ[volume] u := by
  apply ae_iff.mpr
  have hsub : {x | ¬ Uf (aux_cor_as_resolvent_hcamp_idx x) x = u x} ⊆
      ⋃ k : Fin d → ℤ, {x | aux_cor_as_resolvent_hcamp_idx x = k} ∩
        {x | ¬ Uf k x = u x} := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_inter_iff, mem_ofPred_eq]
    exact ⟨aux_cor_as_resolvent_hcamp_idx x, rfl, hx⟩
  have hnull : ∀ k : Fin d → ℤ, volume ({x | aux_cor_as_resolvent_hcamp_idx x = k} ∩
      {x | ¬ Uf k x = u x}) = 0 := by
    intro k
    have hsub2 : {x | aux_cor_as_resolvent_hcamp_idx x = k} ∩ {x | ¬ Uf k x = u x} ⊆
        (centeredCube (aux_cor_as_resolvent_hcamp_center k) 1 one_pos :
          Set (SpatialCoordinates d)) ∩ {x | ¬ Uf k x = u x} := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨?_, hx2⟩
      have hhome := aux_cor_as_resolvent_hcamp_home_mem x
      unfold aux_cor_as_resolvent_hcamp_home at hhome
      rwa [hx1] at hhome
    have hnull2 : volume ((centeredCube (aux_cor_as_resolvent_hcamp_center k) 1 one_pos :
        Set (SpatialCoordinates d)) ∩ {x | ¬ Uf k x = u x}) = 0 := by
      have h := ae_iff.mp (hUfae k)
      rwa [Measure.restrict_apply' (centeredCube (aux_cor_as_resolvent_hcamp_center k) 1
        one_pos).isOpen.measurableSet, Set.inter_comm] at h
    exact measure_mono_null hsub2 hnull2
  exact measure_mono_null hsub (measure_iUnion_null hnull)


/-- Final assembly: Campanato's criterion in the whole-space, plain-function form
consumed by `torsion_bound` (the `aux_cor_as_resolvent_hcamp` estimate). -/
theorem aux_cor_as_resolvent_hcamp_final {d : ℕ} (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d) :
    ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
          ∃ C : ℝ, 0 < C ∧
            ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
              (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
              LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
              (∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), u x = 0) →
              (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
                (∫ y in Metric.ball x r,
                    (u y - (volume.real (Metric.ball x r))⁻¹ *
                      ∫ w in Metric.ball x r, u w) ^ 2) ≤
                  A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
              ∃ v : SpatialCoordinates d → ℝ,
                v =ᵐ[volume] u ∧
                (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                  |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
                ∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), v x = 0 := by
  intro alpha halpha
  obtain ⟨ha0, ha1⟩ := halpha
  refine ⟨Cp.C alpha * (2 : ℝ) ^ ((d : ℝ) / 2) * (Real.sqrt d + 1) ^ alpha, ?_, ?_⟩
  · have hCpos := Cp.C_pos alpha ha0 ha1
    have hsd1 : (0:ℝ) < Real.sqrt d + 1 := by positivity
    have hrp : (0:ℝ) < (Real.sqrt d + 1) ^ alpha := Real.rpow_pos_of_pos hsd1 alpha
    positivity
  intro z rQ hrQ u A hA0 hLIu hLIu2 hvanish hosc
  have hcell : ∀ k : SpatialCoordinates d, ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      U =ᵐ[volume.restrict (centeredCube k 1 one_pos : Set (SpatialCoordinates d))] u ∧
      IsHolderOn alpha (closedCube k 1 one_pos : Set (SpatialCoordinates d)) U ∧
      holderSeminorm alpha (closedCube k 1 one_pos : Set (SpatialCoordinates d)) U ≤
        Cp.C alpha * (A * (2 : ℝ) ^ ((d : ℝ) / 2)) :=
    fun k => aux_cor_as_resolvent_hcamp_cell Cp ha0 ha1 hA0 hLIu hLIu2 hosc k
  choose Uf hUfcont hUfae hUfholder hUfsemi using hcell
  set v : SpatialCoordinates d → ℝ :=
    fun x => Uf (aux_cor_as_resolvent_hcamp_center (aux_cor_as_resolvent_hcamp_idx x)) x with hvdef
  have hAK0 : (0:ℝ) ≤ A * (2:ℝ) ^ ((d:ℝ)/2) := by positivity
  refine ⟨v, ?_, ?_, ?_⟩
  · exact aux_cor_as_resolvent_hcamp_ae_of_cellwise
      (u := u) (Uf := fun k => Uf (aux_cor_as_resolvent_hcamp_center k))
      (fun k => hUfae (aux_cor_as_resolvent_hcamp_center k))
  · intro x y hxy
    obtain ⟨hxm, hym⟩ := aux_cor_as_resolvent_hcamp_midpoint_mem x y hxy
    set m : SpatialCoordinates d := fun i => (x i + y i) / 2 with hmdef
    have hvx : v x = Uf m x :=
      aux_cor_as_resolvent_hcamp_bridge (hUfcont _) (hUfcont m) (hUfae _) (hUfae m)
        (aux_cor_as_resolvent_hcamp_home_mem x) hxm
    have hvy : v y = Uf m y :=
      aux_cor_as_resolvent_hcamp_bridge (hUfcont _) (hUfcont m) (hUfae _) (hUfae m)
        (aux_cor_as_resolvent_hcamp_home_mem y) hym
    have hclos : closure (centeredCube m 1 one_pos : Set (SpatialCoordinates d)) =
        (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := by
      show closure (Metric.ball m (1 / 2)) = Metric.closedBall m (1 / 2)
      exact closure_ball m (by norm_num)
    have hxclosed : x ∈ (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := hclos ▸ hxm
    have hyclosed : y ∈ (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := hclos ▸ hym
    have hCK0 : (0:ℝ) ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) := by
      have := Cp.C_pos alpha ha0 ha1
      positivity
    have hpt := aux_cor_as_resolvent_hcamp_holder_pt m one_pos ha0
      (hUfholder m) (hUfsemi m) hCK0 hxclosed hyclosed
    rw [hvx, hvy]
    have hmono : (Real.sqrt d) ^ alpha ≤ (Real.sqrt d + 1) ^ alpha :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) (by linarith) ha0.le
    have hdxynn : (0:ℝ) ≤ dist x y ^ alpha := by positivity
    calc |Uf m x - Uf m y|
        ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) * (Real.sqrt d) ^ alpha * dist x y ^ alpha := hpt
      _ ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) * (Real.sqrt d + 1) ^ alpha * dist x y ^ alpha := by
          gcongr
      _ = Cp.C alpha * (2:ℝ) ^ ((d:ℝ)/2) * (Real.sqrt d + 1) ^ alpha * A * dist x y ^ alpha := by
          ring
  · intro x hx
    have hhome := aux_cor_as_resolvent_hcamp_home_mem x
    set k : SpatialCoordinates d := aux_cor_as_resolvent_hcamp_home x with hkdef
    -- `x ≠ z`, since `x` is outside the open cube but `z` is its centre.
    have hxz : x ≠ z := by
      rintro rfl
      exact hx (Metric.mem_ball_self (by positivity))
    have : Nontrivial (SpatialCoordinates d) := ⟨x, z, hxz⟩
    -- the interior of the closed support cube is exactly the open support cube.
    have hint : interior (closedCube z rQ hrQ : Set (SpatialCoordinates d)) =
        (centeredCube z rQ hrQ : Set (SpatialCoordinates d)) :=
      interior_closedBall' z (rQ / 2)
    have hxclB : x ∈ closure ((closedCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ) := by
      rw [closure_compl, hint]
      exact hx
    set W : Set (SpatialCoordinates d) :=
      (centeredCube k 1 one_pos : Set (SpatialCoordinates d)) ∩
        (closedCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ with hWdef
    have hWopen : IsOpen W :=
      (centeredCube k 1 one_pos).isOpen.inter (closedCube z rQ hrQ).isCompact.isClosed.isOpen_compl
    have hxW : x ∈ closure W :=
      aux_cor_as_resolvent_hcamp_mem_closure_inter (centeredCube k 1 one_pos).isOpen hhome hxclB
    have hsub : (closedCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ ⊆
        (centeredCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ :=
      Set.compl_subset_compl.mpr (centeredCube_subset_closedCube z hrQ)
    have huW : ∀ y ∈ W, u y = 0 := fun y hy => hvanish y (hsub hy.2)
    have hUf0 : Uf k =ᵐ[volume.restrict W] (fun _ : SpatialCoordinates d => (0:ℝ)) := by
      have h1 : Uf k =ᵐ[volume.restrict W] u :=
        ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hUfae k)
      refine h1.trans ?_
      apply ae_iff.mpr
      have hz0 : W ∩ {y | ¬ u y = (0:ℝ)} = ∅ := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, mem_ofPred_eq]
        rintro ⟨hyW, hyne⟩
        exact hyne (huW y hyW)
      rw [Measure.restrict_apply' hWopen.measurableSet, Set.inter_comm, hz0]
      exact measure_empty
    have hUfzero : Set.EqOn (Uf k) (fun _ => (0:ℝ)) (closure W) :=
      aux_cor_as_resolvent_hcamp_glue hWopen (hUfcont k) continuous_const hUf0
    exact hUfzero hxW



theorem aux_cor_as_resolvent_occupation_measurable {d : ℕ}
    (KN : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel KN]
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Measurable (aux_cor_as_resolvent_occupation KN Q lam f) := by
  unfold aux_cor_as_resolvent_occupation

  have hExit : Measurable (ContinuousPath.exitTime Q : DiffusionPath d → ℝ≥0∞) :=
    ContinuousPath.measurable_exitTime Q hQ
  set Sset : Set (DiffusionPath d × ℝ) :=
    {q : DiffusionPath d × ℝ | ENNReal.ofReal q.2 < ContinuousPath.exitTime Q q.1} with hSdef
  set B : DiffusionPath d × ℝ → ℝ :=
    fun q => Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2)) with hBdef
  have hSmeas : MeasurableSet Sset :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hExit.comp measurable_fst)
  have heval : Measurable (fun q : DiffusionPath d × ℝ => q.1 (Real.toNNReal q.2)) :=
    ContinuousEval.continuous_eval.measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hfeval : Measurable (fun q : DiffusionPath d × ℝ => f (q.1 (Real.toNNReal q.2))) :=
    f.continuous.measurable.comp heval
  have hexp : Measurable (fun q : DiffusionPath d × ℝ => Real.exp (-lam * q.2)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
      measurable_snd
  have hBmeas : Measurable B := hexp.mul hfeval
  have hFmeas : StronglyMeasurable (Sset.indicator B) :=
    hBmeas.stronglyMeasurable.indicator hSmeas
  have hgFmeas : StronglyMeasurable
      (fun path : DiffusionPath d => ∫ t, Sset.indicator B (path, t)
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))) :=
    hFmeas.integral_prod_right'
  have hgeq : (fun path : DiffusionPath d =>
      ∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) =
      (fun path : DiffusionPath d => ∫ t, Sset.indicator B (path, t)
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))) := by
    funext path
    congr 1
  rw [hgeq]
  exact (hgFmeas.integral_kernel (κ := KN)).measurable


theorem aux_cor_as_resolvent_occupation_bound {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (Q : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) :
    |aux_cor_as_resolvent_occupation K Q lam f x| ≤ ‖f‖ / lam :=
  aux_cor_as_resolvent_RN_bound Q lam hlam f (K x)

theorem aux_cor_as_resolvent_occupation_source {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (Q : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) :
    |f x - lam * aux_cor_as_resolvent_occupation K Q lam f x| ≤ 2 * ‖f‖ := by
  have hR := aux_cor_as_resolvent_occupation_bound K Q lam hlam f x
  have hmul : lam * |aux_cor_as_resolvent_occupation K Q lam f x| ≤ ‖f‖ := by
    calc lam * |aux_cor_as_resolvent_occupation K Q lam f x| ≤ lam * (‖f‖ / lam) :=
        mul_le_mul_of_nonneg_left hR hlam.le
      _ = ‖f‖ := mul_div_cancel₀ _ hlam.ne'
  calc |f x - lam * aux_cor_as_resolvent_occupation K Q lam f x|
      ≤ |f x| + |lam * aux_cor_as_resolvent_occupation K Q lam f x| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (f x) (0 : ℝ) (lam * aux_cor_as_resolvent_occupation K Q lam f x)
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
      (by simpa only [abs_mul, abs_of_pos hlam] using hmul)
    _ = 2 * ‖f‖ := (two_mul _).symm

theorem aux_cor_as_resolvent_occupation_zero {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (hstart : ∀ x, ∀ᵐ p ∂K x, p 0 = x)
    (Q : Set (SpatialCoordinates d)) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (x : SpatialCoordinates d) (hx : x ∉ Q) :
    aux_cor_as_resolvent_occupation K Q lam f x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hstart x] with p hp
  have he : ContinuousPath.exitTime Q p = 0 := by
    apply le_antisymm _ (bot_le)
    simpa only [ENNReal.coe_zero] using!
      ContinuousPath.exitTime_le_of_notMem Q p 0 (by rw [hp]; exact hx)
  have hs : {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q p} = ∅ := by
    simp only [he, not_lt_zero, ofPred_false]
  simp only [hs, Set.indicator_empty, integral_zero, Pi.zero_apply]


/-- At one environment, the coercivity, bounded-source regularity, and speed-growth
estimates give a common local Hölder bound for all finite-cutoff occupation resolvents. -/
theorem aux_cor_as_resolvent_fixed_representatives
    {d : ℕ} (hd : 2 ≤ d) (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (K : ℕ → Kernel (SpatialCoordinates d) (DiffusionPath d))
    (hK : ∀ N, IsMarkovKernel (K N))
    (law : ℕ → Kernel (SpatialCoordinates d) (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ N x, Measure.map LifetimePath.ofContinuousPath (K N x) = law N x)
    (hLD : ∀ N, SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
      (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (law N))
    (Kmu : ℝ) (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (hgrowth : ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ N,
      cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
        ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)))
    (K1 Cext K2 : ℝ) (hK1 : 0 ≤ K1) (hCext : 0 ≤ Cext)
    (hcf : ∀ N (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)),
      cubeFractionalSqNorm hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri)
        hr threeQuarterOrder v.val.1 ≤
        K1 * sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N
          (Homogenization.cubeCenter Qtri) hr) v.val v.val)
    (hext : ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      globalFractionalSqNorm (3 / 4)
        (Set.indicator (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))
          (fun x => v.val.1 x)) ≤
        ENNReal.ofReal (Cext * cubeFractionalSqNorm hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder v.val.1))
    (hDir : ∀ N, aux_limiting_local_energy_DirProp (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr
      (cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr) K2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∃ v : SpatialCoordinates d → ℝ, Continuous v ∧
        aux_cor_as_resolvent_occupation (K N)
          (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)
          lam f =ᵐ[volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))] v ∧
        (∀ x y, dist x y ≤ 1 → |v x - v y| ≤ C * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
        ∀ x ∉ (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), v x = 0 := by
  classical
  let Q := centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr
  let aN := fun N => cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr
  let muN := fun N => cutoffSpeedMeasure M H omega N
  let RN := fun N lam f => aux_cor_as_resolvent_occupation (K N) Q lam f
  let E := fun N (v w : killedSobolevGraph Q) => sobolevCoefficientForm (aN N) v.val w.val
  have hex : ∀ (N : ℕ) (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
      ∃ u : killedSobolevGraph Q, 0 < lam →
        ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          RN N lam f) ∧
        ∀ w : killedSobolevGraph Q, E N u w =
          ∫ x in (Q : Set (SpatialCoordinates d)), (f x - lam * RN N lam f x) * w.val.1 x ∂muN N := by
    intro N lam f
    by_cases h : 0 < lam
    · have := hK N
      obtain ⟨u, hu, hw⟩ := aux_cor_as_resolvent_weak_ident M H omega N (K N)
        (law N) (hL N) (hLD N) (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr lam h f
      exact ⟨u, fun _ => ⟨hu, hw⟩⟩
    · exact ⟨0, fun hp => (h hp).elim⟩
  choose uN huN using hex
  let uN0 := fun N lam f => (Q : Set (SpatialCoordinates d)).indicator (fun x => (uN N lam f).val.1 x)
  have hmeas : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      AEMeasurable (RN N lam f) ((muN N).restrict (Q : Set (SpatialCoordinates d))) := by
    intro N lam _ f
    have := hK N
    exact (aux_cor_as_resolvent_occupation_measurable (K N) Q Q.isOpen lam f).aemeasurable
  have hsource : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ᵐ x ∂((muN N).restrict (Q : Set (SpatialCoordinates d))), |f x - lam * RN N lam f x| ≤ 2 * ‖f‖ := by
    intro N lam hlam f
    have := hK N
    exact Eventually.of_forall (aux_cor_as_resolvent_occupation_source (K N) Q lam hlam f)
  have hcoer := fun N => aux_torsion_bound_hcoer hd (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr (aN N) K1 Cext hK1 hCext hext (hcf N)
  have hhol := fun N => aux_torsion_bound_hHol (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr (aN N) K2 (hDir N)
  have hac : ∀ N, (muN N).restrict (Q : Set (SpatialCoordinates d)) ≪ volume := by
    intro N
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
      (withDensity_absolutelyContinuous _ _)
  obtain ⟨A, hA, hosc⟩ := aux_prop_uniform_resolvent_cutoff_oscillation_omega hd epsilon
    hepsilon hepsilon' Qtri hr muN E RN uN uN0 aN (fun _ _ _ => rfl)
    hmeas hsource Kmu (fun _ => K1 * ((Homogenization.cubeScaleFactor Qtri) ^ d + Cext))
    (fun _ => K2 * Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ))
    (by constructor <;> exact ⟨_, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩) Region hNeighborhood
    (fun N lam hlam f => (huN N lam f hlam).2) (fun _ _ _ _ => rfl) hgrowth hcoer hhol hac
  obtain ⟨Cc, hCc, hcamp⟩ := aux_cor_as_resolvent_hcamp_final Cp (1 / 4) ⟨by norm_num, by norm_num⟩
  refine ⟨Cc * A, mul_nonneg hCc.le hA, ?_⟩
  intro N lam hlam f
  have hbeta : (1 / 4 : ℝ) ≤ 1 / 2 - ((d : ℝ) + 2) * epsilon :=
    (aux_prop_uniform_resolvent_cutoff_oscillation_exponent hd epsilon hepsilon hepsilon').le
  obtain ⟨v, hvc, hvae, hvhol, hv0⟩ := aux_prop_uniform_resolvent_camp_holder
    (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr Cc hcamp
    (1 / 2 - ((d : ℝ) + 2) * epsilon) hbeta (A * ‖f‖)
    (mul_nonneg hA (norm_nonneg f)) (uN N lam f).val.1 (hosc N lam hlam f)
  refine ⟨v, hvc, ?_, ?_, hv0⟩
  · have hrep : (uN N lam f).val.1 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] v := by
      filter_upwards [ae_restrict_of_ae hvae, ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
      change v x = (Q : Set (SpatialCoordinates d)).indicator (fun y => (uN N lam f).val.1 y) x at hx
      rw [Set.indicator_of_mem hxQ] at hx
      exact hx.symm
    exact (huN N lam f hlam).1.symm.trans hrep
  · intro x y hxy
    simpa only [mul_assoc] using hvhol x y hxy


/-- Time-zero attachment from the finite-dimensional distributions. -/
theorem aux_cor_as_resolvent_start {d : ℕ}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (ν : Measure (DiffusionPath d)) (x : SpatialCoordinates d)
    (hfdd : ν.map (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d)
      ({0} : Finset ℝ≥0)) = P.finiteSetKernel ({0} : Finset ℝ≥0) x) :
    ∀ᵐ p ∂ν, p 0 = x := by
  have heval := map_eval_eq_of_finsetEvaluation P ν x 0 hfdd
  have hev0 : Measurable (fun p : DiffusionPath d => p 0) :=
    (ContinuousPath.continuous_eval (alpha := SpatialCoordinates d) 0).measurable
  rw [ae_iff]
  change ν ((fun p : DiffusionPath d => p 0) ⁻¹' ({x}ᶜ)) = 0
  rw [← Measure.map_apply hev0 (measurableSet_singleton x).compl, heval,
    P.kernel_zero, Kernel.id_apply]
  simp

/-- A local Hölder bound together with the resolvent contraction gives a global bound,
uniform on each positive compact range of the discount parameter. -/
theorem aux_cor_as_resolvent_compact_range
    {d : ℕ} (Q : Set (SpatialCoordinates d)) (lam0 C : ℝ)
    (hlam0 : 0 < lam0) (hC : 0 ≤ C)
    (R : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (habs : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x, |R N lam f x| ≤ ‖f‖ / lam)
    (hlocal : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x ∈ closure Q, ∀ y ∈ closure Q, dist x y ≤ 1 →
        |R N lam f x - R N lam f y| ≤ C * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) :
    ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
        (∀ x ∈ closure Q, |R N lam f x| ≤ Kom) ∧
        ∀ x ∈ closure Q, ∀ y ∈ closure Q,
          |R N lam f x - R N lam f y| ≤ Kom * dist x y ^ (1 / 4 : ℝ) := by
  let Kom := 1 + C + 2 / lam0
  have hKom : 0 < Kom := by dsimp [Kom]; positivity
  have hCK : C ≤ Kom := by
    have hdiv : 0 ≤ 2 / lam0 := by positivity
    dsimp [Kom]; linarith
  have h2K : 2 / lam0 ≤ Kom := by dsimp [Kom]; linarith
  refine ⟨Kom, hKom, ?_⟩
  intro N lam hlam f hf
  have hlampos := hlam0.trans_le hlam
  have hb : ∀ x, |R N lam f x| ≤ 1 / lam0 := by
    intro x
    exact ((habs N lam hlampos f x).trans
      (div_le_div_of_nonneg_right hf hlampos.le)).trans (one_div_le_one_div_of_le hlam0 hlam)
  refine ⟨fun x _ => (hb x).trans ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hlam0.le).trans h2K
  · intro x hx y hy
    by_cases hxy : dist x y ≤ 1
    · refine (hlocal N lam hlampos f x hx y hy hxy).trans ?_
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
      exact (mul_le_of_le_one_right hC hf).trans hCK
    · have hpow : 1 ≤ dist x y ^ (1 / 4 : ℝ) :=
        Real.one_le_rpow (le_of_lt (lt_of_not_ge hxy)) (by norm_num)
      calc
        |R N lam f x - R N lam f y| ≤ |R N lam f x| + |R N lam f y| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            abs_sub_le (R N lam f x) (0 : ℝ) (R N lam f y)
        _ ≤ 1 / lam0 + 1 / lam0 := add_le_add (hb x) (hb y)
        _ = 2 / lam0 := by ring
        _ ≤ Kom := h2K
        _ ≤ Kom * dist x y ^ (1 / 4 : ℝ) := le_mul_of_one_le_right hKom.le hpow


lemma aux_cor_as_resolvent_cube_cutoff_holder_p_choice
    {d : ℕ} (hd : 2 ≤ d) :
    (d : ℝ) < ((16 * d * (d + 2) + 1 : ℕ) : ℝ) * (1 / (16 * ((d : ℝ) + 2))) := by
  have hpos : (0 : ℝ) < 16 * ((d : ℝ) + 2) := by positivity
  push_cast
  rw [mul_one_div, lt_div_iff₀ hpos]
  nlinarith


lemma aux_cor_as_resolvent_cube_cutoff_holder_eps_choice {d : ℕ} (hd : 2 ≤ d) :
    0 < 1 / (16 * ((d : ℝ) + 2)) ∧ 1 / (16 * ((d : ℝ) + 2)) < 1 / (8 * ((d : ℝ) + 2)) := by
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by
    have h : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  constructor
  · positivity
  · exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)


lemma aux_cor_as_resolvent_centeredCube_eq_ball {d : ℕ}
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri) :
    ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) =
      Metric.ball (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri / 2) := by
  exact centeredCube_coe_eq_ball _ _ hr


lemma aux_cor_as_resolvent_cube_cutoff_holder_w_hregion {d : ℕ}
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri) :
    Bornology.IsBounded (Metric.ball (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri / 2 + 1)) ∧
      (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))),
        Metric.ball x 1 ⊆ Metric.ball (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri / 2 + 1)) := by
  refine ⟨Metric.isBounded_ball, ?_⟩
  intro x hx y hy
  rw [Metric.mem_ball] at hy ⊢
  have hcube : (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) = Metric.ball (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri / 2) :=
    centeredCube_coe_eq_ball _ _ hr
  rw [hcube] at hx
  have hxc : x ∈ Metric.closedBall (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri / 2) :=
    Metric.closure_ball_subset_closedBall hx
  rw [Metric.mem_closedBall] at hxc
  calc dist y (Homogenization.cubeCenter Qtri) ≤ dist y x + dist x (Homogenization.cubeCenter Qtri) := dist_triangle _ _ _
    _ < 1 + Homogenization.cubeScaleFactor Qtri / 2 := by linarith
    _ = Homogenization.cubeScaleFactor Qtri / 2 + 1 := by ring



/-- Uniform cutoff resolvent bounds on a fixed cube. Coercivity and Dirichlet regularity
come from the original-field suppliers; the weak equation, Campanato estimate, and
continuous-version identification preserve the given occupation resolvent pointwise. -/
theorem aux_cor_as_resolvent_cube_cutoff_holder
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Interp : CubeFractionalInterpolationInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M)
        (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg), M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ N, IsMarkovKernel (KN N)) → in_crossing M H PN KN →
        aux_cutoff_lifetime_package_LocalInput M H KN →
      ∀ (Qtri : ℕ → Homogenization.TriadicCube d)
        (hr : ∀ n : ℕ, 0 < Homogenization.cubeScaleFactor (Qtri n))
        (RN : ℕ → ℕ → BilateralField d → ℝ →
            BoundedContinuousFunction (SpatialCoordinates d) ℝ →
            SpatialCoordinates d → ℝ)
        (_hRN_formula : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
            (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
            (x : SpatialCoordinates d),
          RN n N omega lam f x =
            ∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Set.indicator
                {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  (centeredCube (Homogenization.cubeCenter (Qtri n))
                    (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
              ∂(KN N (omega, x)))
        (n0 : ℕ),
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (lam0 lam1 : ℝ), 0 < lam0 → lam0 ≤ lam1 →
          ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
              (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                  (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x| ≤ Kom) ∧
              ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                  (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                  (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                  Kom * dist x y ^ (1 / 4 : ℝ)  := by


  classical
  let epsilon : ℝ := 1 / (16 * ((d : ℝ) + 2))
  have heps := aux_cor_as_resolvent_cube_cutoff_holder_eps_choice hd
  have heps1 : epsilon < 1 := by
    dsimp only [epsilon]
    apply (div_lt_one (by positivity)).2
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨δg, hδg, hgrowth⟩ := prop_chaos_growth hd epsilon ⟨heps.1, heps1⟩
    (16 * d * (d + 2) + 1) (aux_cor_as_resolvent_cube_cutoff_holder_p_choice hd)
  obtain ⟨δc, hδc, hcoarse⟩ := lem_as_coarse d hd Jc Pc Xc Sf W Cp D aux_lem_band_rcJ_hES Step Dbase Interp 1 (3 / 4)
    ⟨one_pos, le_rfl⟩ ⟨by norm_num, by norm_num⟩
  obtain ⟨δr, hδr, hregular⟩ := lem_as_regularity d hd Jc Pc Xc W D Cp Sf Step Dbase Interp
    (1 / 2) (3 / 4) ((d : ℝ) - 3 / 4) ((d : ℝ) - 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
  refine ⟨min δg (min 1 (min δc δr)), lt_min hδg (lt_min one_pos (lt_min hδc hδr)), ?_⟩
  intro M Rm Sreg It hδ H HI PN KN hKN hin hinput Qtri hr RN hRN n0
  have hδg' : M.delta ≤ δg := hδ.trans (min_le_left _ _)
  have hδ1 : M.delta ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδc' : M.delta ≤ δc := hδ.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδr' : M.delta ≤ δr := hδ.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let Q := centeredCube (Homogenization.cubeCenter (Qtri n0))
    (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
  let Region := Metric.ball (Homogenization.cubeCenter (Qtri n0))
    (Homogenization.cubeScaleFactor (Qtri n0) / 2 + 1)
  have hRegion := aux_cor_as_resolvent_cube_cutoff_holder_w_hregion (Qtri n0) (hr n0)
  obtain ⟨mu, _, _, hg⟩ := hgrowth M H HI hδg'
  obtain ⟨Kmu, _, hKmu⟩ := hg Region hRegion.1
  have eC := hcoarse M Rm Sreg It H HI (le_min hδ1 hδc')
    (Homogenization.cubeCenter (Qtri n0)) (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
    ⟨(Qtri n0).scale, rfl⟩
  have eR := hregular M Rm Sreg It H HI (le_min hδ1 hδr')
    (Homogenization.cubeCenter (Qtri n0)) (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
  obtain ⟨Cext, hCext, hext, _⟩ := killed_zero_extension_bound hd Sf
    (Homogenization.cubeCenter (Qtri n0)) (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
  have hac := car_resolvent_abs_cont hd M H HI PN KN hKN hin hinput
  have hpoint := car_rn_continuous_version hd M H HI PN KN hKN hin hinput hac Qtri hr RN hRN
  filter_upwards [eC, eR, hKmu, hinput.localDiffusion, hpoint, hin.2.2] with omega hC hR hgω hLD hpointω hfdd
  obtain ⟨K1, hK1, hcf⟩ := hC
  obtain ⟨K2, hK2, hDir⟩ := hR
  let K := fun N => (KN N).comap (fun x : SpatialCoordinates d => (omega,x))
    (measurable_const.prodMk measurable_id)
  have hK : ∀ N, IsMarkovKernel (K N) := by
    intro N
    have := hKN N
    dsimp only [K]
    infer_instance
  have hL : ∀ N x, Measure.map LifetimePath.ofContinuousPath (K N x) =
      aux_cutoff_lifetime_package_kernel KN N omega x :=
    fun N x => aux_cutoff_lifetime_package_spec KN N omega x
  have hgr : ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ N,
      cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
        ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) := by
    intro x hx r hr0 hr1 N
    rw [cutoffSpeedMeasure_eq_weightedChaosCutoff]
    exact hgω.2.1 N x hx r hr0 hr1
  have hD : ∀ N, aux_limiting_local_energy_DirProp (Homogenization.cubeCenter (Qtri n0))
      (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
      (cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter (Qtri n0)) (hr n0)) K2 := by
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
    exact ((hDir N).1 F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol).2
  obtain ⟨C, hC0, hrep⟩ := aux_cor_as_resolvent_fixed_representatives hd Cp epsilon heps.1 heps.2
    (Qtri n0) (hr n0) M H omega K hK (fun N => aux_cutoff_lifetime_package_kernel KN N omega)
    hL hLD (Kmu omega) Region hRegion.2 hgr K1 Cext K2 hK1.le hCext.le
    (fun N v => (hcf true).2.1 N v) hext hD
  have hRN' : ∀ N lam f, RN n0 N omega lam f = aux_cor_as_resolvent_occupation (K N) Q lam f := by
    intro N lam f
    funext x
    exact hRN n0 N omega lam f x
  have hstart : ∀ N x, ∀ᵐ p ∂K N x, p 0 = x := by
    intro N x
    apply aux_cor_as_resolvent_start (PN N omega) (K N x) x
    change (KN N (omega,x)).map _ = _
    rw [← Kernel.map_apply (KN N) (ContinuousPath.measurable_finsetEvaluation
      (alpha := SpatialCoordinates d) ({0} : Finset ℝ≥0)) (omega,x)]
    exact hfdd N ({0} : Finset ℝ≥0) x
  have habs : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x, |RN n0 N omega lam f x| ≤ ‖f‖ / lam := by
    intro N lam hlam f x
    have := hK N
    rw [hRN']
    exact aux_cor_as_resolvent_occupation_bound (K N) Q lam hlam f x
  have hlocal : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ y ∈ closure (Q : Set (SpatialCoordinates d)),
        dist x y ≤ 1 → |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
          C * ‖f‖ * dist x y ^ (1 / 4 : ℝ) := by
    intro N lam hlam f
    obtain ⟨v, hvc, hvae, hvhol, hv0⟩ := hrep N lam hlam f
    have hRv : RN n0 N omega lam f = v := by
      funext x
      by_cases hx : x ∈ (Q : Set (SpatialCoordinates d))
      · apply hpointω n0 N lam hlam f v hvc.continuousOn
        · rw [hRN']; exact hvae
        · exact hx
      · rw [hRN', aux_cor_as_resolvent_occupation_zero (K N) (hstart N) Q lam f x hx, hv0 x hx]
    intro x _ y _ hxy
    rw [hRv]
    exact hvhol x y hxy
  intro lam0 lam1 hlam0 _
  obtain ⟨Kom, hKom, hKomall⟩ := aux_cor_as_resolvent_compact_range (Q : Set (SpatialCoordinates d))
    lam0 C hlam0 hC0 (fun N lam f => RN n0 N omega lam f) habs hlocal
  exact ⟨Kom, hKom, fun N lam hlow _ f hf => hKomall N lam hlow f hf⟩


section CutoffSupplyProofs
open scoped ContDiff Manifold

/-- A native harmonic function with the given zero trace difference satisfies
the project's Dirichlet equation with zero source, with unchanged value and gradient. -/
theorem aux_cor_as_resolvent_harmonic_dirichlet_bridge
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (A : PositiveCoefficient Q) (a : SpatialCoordinates d → ℝ)
    (hA : (fun x => A.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] a)
    (u b : Homogenization.H1Function (Q : Set (SpatialCoordinates d)))
    (hu : SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn a
      (Q : Set (SpatialCoordinates d)) u)
    (hb : SubdiffusiveProcess.CoarseGrainingVocab.HasZeroTraceDifferenceOn
      (Q : Set (SpatialCoordinates d)) u b) :
    SolvesDirichlet A (fun _ => 0)
      ⟨sobolevDataOfH1 b, sobolevDataOfH1_mem_weak b⟩
      ⟨sobolevDataOfH1 u, sobolevDataOfH1_mem_weak u⟩ := by
  obtain ⟨v, hv, hv1, hv2⟩ := killed_of_zeroTraceDifference hb
  have heq : sobolevDataOfH1 u - sobolevDataOfH1 b = v := by
    refine Prod.ext ?_ ?_
    · apply Lp.ext
      exact ((Lp.coeFn_sub _ _).trans
        ((sobolevDataOfH1_fst_coeFn u).sub (sobolevDataOfH1_fst_coeFn b))).trans hv1.symm
    · funext i
      apply Lp.ext
      exact ((Lp.coeFn_sub _ _).trans
        ((sobolevDataOfH1_snd_coeFn u i).sub
          (sobolevDataOfH1_snd_coeFn b i))).trans (hv2 i).symm
  refine ⟨heq ▸ hv, ?_⟩
  intro w
  obtain ⟨wH, _, hwgrad⟩ := exists_nativeH10Function_of_killedSobolevGraph w
  rw [sobolevCoefficientForm_eq_upstream_integral A a hA]
  simp only [zero_mul, integral_zero]
  rw [← hu wH]
  apply integral_congr_ae
  have hgu := ae_all_iff.2 (fun i => sobolevDataOfH1_snd_coeFn u i)
  filter_upwards [hgu] with x hx
  rw [hwgrad]
  rw [vecDot_matVecMul_scalarCoeffField]
  simp only [Homogenization.vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]; ring

/-- The native harmonic energy is the graph energy of the same Sobolev datum. -/
theorem aux_cor_as_resolvent_harmonic_energy
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (A : PositiveCoefficient Q) (a : SpatialCoordinates d → ℝ)
    (hA : (fun x => A.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] a)
    (u : Homogenization.H1Function (Q : Set (SpatialCoordinates d))) :
    sobolevCoefficientForm A (sobolevDataOfH1 u) (sobolevDataOfH1 u) =
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.energy a (Q : Set (SpatialCoordinates d)) u := by
  rw [sobolevCoefficientForm_eq_upstream_integral A a hA]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.2 (fun i => sobolevDataOfH1_snd_coeFn u i)] with x hx
  rw [vecDot_matVecMul_scalarCoeffField]
  simp only [Homogenization.vecDot]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]


/-- Smooth plateau data for the harmonic mesh construction, without a catalogue choice. -/
theorem aux_cor_as_resolvent_smooth_plateau {d : ℕ}
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (K O : Set (SpatialCoordinates d)) (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ θ : SpatialCoordinates d → ℝ, ∃ W : Set (SpatialCoordinates d),
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ O ∧
      IsOpen W ∧ K ⊆ W ∧ W ⊆ O ∧
      (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧ ∀ x ∈ W, θ x = 1 := by
  obtain ⟨U, hU, hKU, hUO⟩ := normal_exists_closure_subset hK.isClosed hO hKO
  obtain ⟨f, hf1, hf0, hfr⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, SpatialCoordinates d)) hK.isClosed
    (show K ⊆ interior U by simpa only [hU.interior_eq] using hKU)
  obtain ⟨V, hV, hKV, hVf⟩ := mem_nhdsSet_iff_exists.1 hf1
  have hs : Function.support (fun x => f x) ⊆ U := by
    intro x hx
    by_contra h
    exact hx (hf0 x h)
  have hts : tsupport (fun x => f x) ⊆ O := (closure_mono hs).trans hUO
  have hcomp : HasCompactSupport (fun x => f x) :=
    IsCompact.of_isClosed_subset (isCompact_closure_centeredCube z hR)
      (isClosed_tsupport _) ((hts.trans (subset_closure.trans hOQ)).trans subset_closure)
  refine ⟨(fun x => f x), V ∩ U, ?_, hcomp, hts, hV.inter hU,
    fun x hx => ⟨hKV hx, hKU hx⟩, fun x hx => hUO (subset_closure hx.2),
    hfr, fun x hx => hVf hx.1⟩
  exact contMDiff_iff_contDiff.1 f.contMDiff

/-- Extend an interior ball-growth estimate to boundary centers, using the total
mass for radii above one half. -/
theorem aux_cor_as_resolvent_growth_on_closure
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (Q : Set X) (E t : ℝ) (hE : 0 ≤ E) (ht : 0 ≤ t)
    (htotal : ν Set.univ ≤ ENNReal.ofReal E)
    (hinside : ∀ x ∈ Q, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ν (Metric.ball x r) ≤ ENNReal.ofReal (E * r ^ t)) :
    ∀ x ∈ closure Q, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ν (Metric.ball x r) ≤ ENNReal.ofReal ((2 : ℝ) ^ t * (E + E) * r ^ t) := by
  intro x hx r hr _
  have heq : (E + E) * (2 * r) ^ t = (2 : ℝ) ^ t * (E + E) * r ^ t := by
    rw [Real.mul_rpow (by norm_num) hr.le]
    ring
  by_cases hsmall : r ≤ 1 / 2
  · obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx r hr
    have hsub : Metric.ball x r ⊆ Metric.ball y (2 * r) := by
      intro a ha
      apply lt_of_le_of_lt (dist_triangle a x y)
      have har : dist a x < r := ha
      linarith
    refine ((measure_mono hsub).trans (hinside y hy (2 * r) (by positivity)
      (by linarith))).trans ?_
    apply ENNReal.ofReal_le_ofReal
    rw [← heq]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hE)
      (Real.rpow_nonneg (by positivity) _)
  · refine ((measure_mono (Set.subset_univ _)).trans htotal).trans ?_
    apply ENNReal.ofReal_le_ofReal
    rw [← heq]
    have hp : 1 ≤ (2 * r) ^ t := Real.one_le_rpow (by linarith) ht
    exact (le_add_of_nonneg_right hE).trans
      (le_mul_of_one_le_right (add_nonneg hE hE) hp)

/-- The energy measure in HCUT is exactly the existing local gradient energy. -/
theorem aux_cor_as_resolvent_energy_measure
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (A : PositiveCoefficient Q) (u : SobolevData Q)
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) :
    ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun x => ENNReal.ofReal (A.val x * ∑ i : Fin d, (u.2 i x) ^ 2))) S =
      ENNReal.ofReal (localGradientEnergy A hS (sobolevGradient u)) := by
  let ν := (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
    (fun x => ENNReal.ofReal (∑ i : Fin d, A.val x * (u.2 i x) ^ 2))
  have hν := gradientEnergy_withDensity_finite_and_real A (sobolevGradient u)
  have : IsFiniteMeasure ν := hν.1
  calc
    _ = ν S := by simp only [ν, Finset.mul_sum]
    _ = ENNReal.ofReal (ν.real S) := (ENNReal.ofReal_toReal (measure_ne_top ν S)).symm
    _ = _ := congrArg ENNReal.ofReal (hν.2 S hS)

theorem aux_cor_as_resolvent_local_energy_inter_domain
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (A : PositiveCoefficient Q) (g : HilbertGradient Q)
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) :
    localGradientEnergy A hS g =
      localGradientEnergy A (hS.inter Q.isOpen.measurableSet) g := by
  simp only [localGradientEnergy_eq_integral, Measure.restrict_restrict hS,
    Measure.restrict_restrict (hS.inter Q.isOpen.measurableSet),
    Set.inter_assoc, Set.inter_self]


/-- Uniform zero-source Dirichlet estimates, with the exponents needed for cutoffs. -/
def aux_cor_as_resolvent_ZeroDirProp {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (A : PositiveCoefficient (centeredCube z r hr)) (K : ℝ) : Prop :=
  ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ), ContDiff ℝ 2 phi →
    c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
    ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet A (fun _ => 0) b u →
      (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        0 < rad → rad ≤ 1 →
        localGradientEnergy A
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
            K * Cphi ^ 2 * rad ^ ((d : ℝ) - 1 / 2)) ∧
      ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
        ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        IsHolderOn (1 / 2) (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
        cAlphaNorm (1 / 2) (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ K * Cphi

/-- The original-field regularity event, projected before constructing any plateau. -/
theorem aux_cor_as_resolvent_zero_dir_event {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Jc : in_J d) (Pc : in_poincare d hd Jc)
    (Xc : in_extension d hd Jc) (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
            ∀ N, aux_cor_as_resolvent_ZeroDirProp z r hr
              (cutoffPositiveCoefficient M H omega N z hr) K := by
  obtain ⟨δ, hδ, hregular⟩ := lem_as_regularity d hd Jc Pc Xc W D Cp Sf Step Dbase Interp
    (1 / 2) (3 / 4) ((d : ℝ) - 1 / 2) ((d : ℝ) - 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
  refine ⟨min 1 δ, lt_min one_pos hδ, ?_⟩
  intro M Rm Sreg It H HI hM z r hr
  filter_upwards [hregular M Rm Sreg It H HI hM z r hr] with omega homega
  obtain ⟨K, hK, hreg⟩ := homega
  refine ⟨K, hK, ?_⟩
  intro N phi Cphi hphi hC b u hb hu
  simpa only [zero_add] using! (hreg N).1 (fun _ => 0) 0 le_rfl aemeasurable_const
    (by simp) phi Cphi hphi hC b u hb hu



/-- The countable mesh-regularity event on one parent cube. -/
def aux_cor_as_resolvent_MeshRegProp {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) : Prop :=
  ∀ J : ℕ, ∀ k : OddGridIndex d (triadicHalf J), ∃ K : ℝ, 0 < K ∧
      ∀ N, aux_cor_as_resolvent_ZeroDirProp
        (oddGridCenter z R (triadicHalf J) k) (R / (2 * (triadicHalf J : ℝ) + 1))
        (div_pos hR (by positivity))
        (cutoffPositiveCoefficient (r := R / (2 * (triadicHalf J : ℝ) + 1))
          M H omega N (oddGridCenter z R (triadicHalf J) k)
          (div_pos hR (by positivity))) K


/-- A smooth compact plateau admits a fine mesh whose transition cells stay in the prescribed annulus. -/
theorem aux_cor_as_resolvent_plateau_mesh {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (K O : Set (SpatialCoordinates d)) (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ (θ : SpatialCoordinates d → ℝ) (V₀ : Set (SpatialCoordinates d)) (J : ℕ),
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ O ∧
      IsOpen V₀ ∧ K ⊆ V₀ ∧ V₀ ⊆ O ∧
      (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧ (∀ x ∈ V₀, θ x = 1) ∧
      R / (2 * (triadicHalf J : ℝ) + 1) ≤ 1 ∧
      ∀ k : OddGridIndex d (triadicHalf J),
        (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
          {x | 0 < θ x ∧ θ x < 1}).Nonempty →
        closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ⊆ O \ K := by
  obtain ⟨θ, V₀, hθ, hθcomp, hθsupp, hV₀, hKV₀, hV₀O, hθ01, hθ1⟩ :=
    aux_cor_as_resolvent_smooth_plateau z R hR K O hK hO hKO hOQ
  obtain ⟨δO, hδO, hthO⟩ := hθcomp.exists_thickening_subset_open hO hθsupp
  obtain ⟨δV, hδV, hthV⟩ := hK.exists_thickening_subset_open hV₀ hKV₀
  obtain ⟨J, hJ⟩ := aux_catalog_cutoff_existence_mesh_scale (R := R) (δ := min (min δO δV) 1) hR
    (lt_min (lt_min hδO hδV) (one_pos : (0 : ℝ) < 1))
  have hmesh : R / (3 : ℝ) ^ J < min δO δV := hJ.trans_le (min_le_left _ _)
  have hside : R / (2 * (triadicHalf J : ℝ) + 1) ≤ 1 := by
    rw [triadic_denominator]
    exact (hJ.trans_le (min_le_right _ _)).le
  have htrans := aux_catalog_cutoff_existence_transition_cells_apply z R hR θ K V₀ O
    hθ1 δO δV hthO hthV J hmesh
  exact ⟨θ, V₀, J, hθ, hθcomp, hθsupp, hV₀, hKV₀, hV₀O, hθ01, hθ1, hside, htrans⟩


/-- Native cell energy, ball growth, and Holder bounds for one coefficient. -/
def aux_cor_as_resolvent_HarmonicBound {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (a : SpatialCoordinates d → ℝ) (bH : Homogenization.H1Function (Q : Set (SpatialCoordinates d)))
    (E Gr Ho : ℝ) : Prop :=
  ∀ w : Homogenization.H1Function (Q : Set (SpatialCoordinates d)),
    SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn a (Q : Set (SpatialCoordinates d)) w →
    SubdiffusiveProcess.CoarseGrainingVocab.HasZeroTraceDifferenceOn (Q : Set (SpatialCoordinates d)) w bH →
    ContinuousOn w.toFun (closure (Q : Set (SpatialCoordinates d))) →
    SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.energy a (Q : Set (SpatialCoordinates d)) w ≤ E ∧
    (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ r : ℝ, 0 < r → r ≤ 1 →
      ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal (a y * ∑ i : Fin d, (w.grad y i) ^ 2))) (Metric.ball x r) ≤
          ENNReal.ofReal (Gr * r ^ ((d : ℝ) - 1 / 2))) ∧
    (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ y ∈ closure (Q : Set (SpatialCoordinates d)),
      |w.toFun x - w.toFun y| ≤ Ho * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ (1 / 2 : ℝ))

/-- Original-field zero-source regularity bounds all native cell solutions with a fixed datum. -/
theorem aux_cor_as_resolvent_zero_cell_bounds {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hside : r ≤ 1)
    (θ : SpatialCoordinates d → ℝ) (hθ : ContDiff ℝ 2 θ)
    (bH : Homogenization.H1Function (centeredCube c r hr : Set (SpatialCoordinates d)))
    (hbH : bH.toFun = θ) (Kc : ℝ) (hKc : 0 < Kc)
    (hreg : ∀ N, aux_cor_as_resolvent_ZeroDirProp c r hr
      (cutoffPositiveCoefficient M H omega N c hr) Kc) :
    ∃ E Gr Ho : ℝ, 0 ≤ E ∧ 0 ≤ Gr ∧ 0 ≤ Ho ∧
      ∀ N, aux_cor_as_resolvent_HarmonicBound (centeredCube c r hr)
        (cutoffCoefficient M H omega N) bH E Gr Ho := by
  let Q := centeredCube c r hr
  let t : ℝ := (d : ℝ) - 1 / 2
  have ht : 0 ≤ t := by
    dsimp [t]
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  let Cθ := max 1 (c2Norm (closedCube c r hr : Set (SpatialCoordinates d)) θ)
  have hCθ : 0 ≤ Cθ := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  let E := Kc * Cθ ^ 2
  have hE : 0 ≤ E := mul_nonneg hKc.le (sq_nonneg _)
  refine ⟨E, (2 : ℝ) ^ t * (E + E), Kc * Cθ, hE, by positivity, by positivity, ?_⟩
  intro N w hwh hwt hwc
  let A := cutoffPositiveCoefficient M H omega N c hr
  let wS : weakSobolevGraph Q := ⟨sobolevDataOfH1 w, sobolevDataOfH1_mem_weak w⟩
  let bS : weakSobolevGraph Q := ⟨sobolevDataOfH1 bH, sobolevDataOfH1_mem_weak bH⟩
  have hA := aux_lem_cutoffs_positiveCoefficient_ae M H omega N c hr
  have hsolve : SolvesDirichlet A (fun _ => 0) bS wS :=
    aux_cor_as_resolvent_harmonic_dirichlet_bridge A _ hA w bH hwh hwt
  have hbval : ((bS : SobolevData Q).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] θ :=
    (sobolevDataOfH1_fst_coeFn bH).trans (Filter.Eventually.of_forall (fun x => congrFun hbH x))
  obtain ⟨hg, U, hUc, hwU, hUh, hUn⟩ := (hreg N) θ Cθ hθ (le_max_right _ _)
    bS wS hbval hsolve
  have hcenter : c ∈ (Q : Set (SpatialCoordinates d)) := Metric.mem_ball_self (half_pos hr)
  have hsub : (Q : Set (SpatialCoordinates d)) ⊆ Metric.ball c 1 :=
    Metric.ball_subset_ball (by linarith [hside])
  have hballQ : Metric.ball c 1 ∩ (centeredCube c r hr : Set (SpatialCoordinates d)) =
      (centeredCube c r hr : Set (SpatialCoordinates d)) :=
    Set.inter_eq_right.2 hsub
  have hgraph : sobolevCoefficientForm A (wS : SobolevData Q) (wS : SobolevData Q) ≤ E := by
    have hb := hg c 1 hcenter one_pos le_rfl
    rw [← localGradientEnergy_domain_eq_sobolevCoefficientForm A (wS : SobolevData Q)]
    simpa only [localGradientEnergy_eq_integral, hballQ, Real.one_rpow, mul_one] using hb
  let ν := (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
    (fun x => ENNReal.ofReal (A.val x * ∑ i : Fin d, ((wS : SobolevData Q).2 i x) ^ 2))
  have htotal : ν Set.univ ≤ ENNReal.ofReal E := by
    rw [aux_cor_as_resolvent_energy_measure A (wS : SobolevData Q) Set.univ MeasurableSet.univ,
      _root_.SubdiffusiveProcess.ResponseMoments.localGradientEnergy_univ]
    exact ENNReal.ofReal_le_ofReal hgraph
  have hinside : ∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ s : ℝ, 0 < s → s ≤ 1 →
      ν (Metric.ball x s) ≤ ENNReal.ofReal (E * s ^ t) := by
    intro x hx s hs hs1
    rw [aux_cor_as_resolvent_energy_measure A (wS : SobolevData Q) _ isOpen_ball.measurableSet,
      aux_cor_as_resolvent_local_energy_inter_domain]
    apply ENNReal.ofReal_le_ofReal
    simpa only [zero_add] using hg x s hx hs hs1
  have hbound := aux_cor_as_resolvent_growth_on_closure ν (Q : Set (SpatialCoordinates d))
    E t hE ht htotal hinside
  have hden : (fun x => ENNReal.ofReal (A.val x * ∑ i : Fin d,
      ((wS : SobolevData Q).2 i x) ^ 2)) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      (fun x => ENNReal.ofReal (cutoffCoefficient M H omega N x * ∑ i : Fin d, (w.grad x i) ^ 2)) :=
    aux_lem_cutoffs_cc_density_congr _ _ _ _ hA (fun i => sobolevDataOfH1_snd_coeFn w i)
  have hEq := withDensity_congr_ae hden
  have hcl : closure (Q : Set (SpatialCoordinates d)) =
      (closedCube c r hr : Set (SpatialCoordinates d)) :=
    aux_lem_cutoffs_geom_closure_eq c r hr
  have hwUpoint := aux_lem_cutoffs_eqOn_closure (Q : Set (SpatialCoordinates d)) Q.isOpen
    w.toFun U hwc hUc.continuousOn ((sobolevDataOfH1_fst_coeFn w).symm.trans hwU)
  have hUbound := aux_lem_cutoffs_pair_bound_of_holder (by norm_num : (0 : ℝ) < 1 / 2)
    hUh (by simpa only [zero_add] using hUn)
  refine ⟨?_, ?_, ?_⟩
  · rw [← aux_cor_as_resolvent_harmonic_energy A _ hA w]
    exact hgraph
  · intro x hx s hs hs1
    rw [← hEq]
    exact hbound x hx s hs hs1
  · intro x hx y hy
    rw [hwUpoint x hx, hwUpoint y hy]
    exact hUbound x (hcl ▸ hx) y (hcl ▸ hy)


/-- Uniform energy and Holder bounds for the actual cutoff sequence. -/
def aux_cor_as_resolvent_CutoffFamily {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
      ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖)
    (K O : Set (SpatialCoordinates d)) : Prop :=
  ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (killedResponseSpace hP).space)
      (chic : ℕ → SpatialCoordinates d → ℝ) (B C : ℝ),
    IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ 0 ≤ C ∧ ∀ n : ℕ,
      ContinuousOn (chic n) (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      ((chi n).val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] chic n ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        0 ≤ chic n x ∧ chic n x ≤ 1) ∧
      (∀ x ∈ V, chic n x = 1) ∧
      (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
      responseForm (killedResponseSpace hP)
        (cutoffPositiveCoefficient M H omega n z hR) (chi n) (chi n) ≤ B ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)), ∀ rr : ℝ,
        0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((cutoffPositiveCoefficient M H omega n z hR).val y *
            ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ ((d : ℝ) - 1 / 2))) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        ∀ y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        |chic n x - chic n y| ≤ C * (Real.sqrt (∑ i : Fin d, (x i - y i)^2)) ^ (1 / 2 : ℝ))


/-- Finite-cell Dirichlet regularity constructs the cutoff family on a fixed cube. -/
theorem aux_cor_as_resolvent_strong_cutoffs {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
      ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖)
    (omega : BilateralField d)
    (homega : aux_cor_as_resolvent_MeshRegProp M H omega z R hR) :
    ∀ (K O : Set (SpatialCoordinates d)), IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      aux_cor_as_resolvent_CutoffFamily M H omega z R hR hP K O := by
  classical
  have : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  intro K O hK hO hKO hOQ
  obtain ⟨θ, V₀, J, hθ, hθcomp, hθsupp, hV₀, hKV₀, hV₀O, hθ01, hθ1, hside, htrans⟩ :=
    aux_cor_as_resolvent_plateau_mesh z R hR K O hK hO hKO hOQ
  let θH := Homogenization.H1Function.ofContDiff (centeredCube z R hR).isOpen
    (hθ.of_le (by simp)) hθcomp
  let t : ℝ := (d : ℝ) - 1 / 2
  have ht : 0 ≤ t := by
    dsimp [t]
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcell : ∀ k : OddGridIndex d (triadicHalf J), ∃ E Gr Ho : ℝ,
      0 ≤ E ∧ 0 ≤ Gr ∧ 0 ≤ Ho ∧ ∀ N, aux_cor_as_resolvent_HarmonicBound
        (oddGridCell z R hR (triadicHalf J) k) (cutoffCoefficient M H omega N)
        (θH.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
          (oddGridCell_subset z hR (triadicHalf J) k)) E Gr Ho := by
    intro k
    obtain ⟨Kc, hKc, hreg⟩ := homega J k
    exact aux_cor_as_resolvent_zero_cell_bounds hd M H omega
      (oddGridCenter z R (triadicHalf J) k) (R / (2 * (triadicHalf J : ℝ) + 1))
      (div_pos hR (by positivity)) hside θ (hθ.of_le (by decide))
      (θH.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k)) rfl Kc hKc hreg
  obtain ⟨chiH, chiS, chic, V, BE, BG, BH, hV, hKV, hVO, hBE, hBG, hBH, hchi, _⟩ :=
    aux_lem_cutoffs_plateau_generic hd z R hR (killedResponseSpace hP) rfl
      (fun N => cutoffCoefficient M H omega N)
      (fun N => cutoffCoefficient_continuous M H omega N)
      (fun N => cutoffCoefficient_pos M H omega N)
      (fun N => cutoffPositiveCoefficient M H omega N z hR)
      (fun N => aux_lem_cutoffs_positiveCoefficient_ae M H omega N z hR)
      t (1 / 2) ht (by norm_num) θ θH rfl hθ K O V₀ J hO hOQ hKV₀ hV₀O
      hθ01 hθ1 hθsupp htrans hcell
  refine ⟨V, chiS, chic, max BE BG, BH, hV, hKV, hVO,
    hBE.trans (le_max_left _ _), hBH, ?_⟩
  intro N
  obtain ⟨_, hcc, hcae, hcrange, hc1, hc0, _, _, hce, hcg, hhol, hnorm⟩ := hchi N
  refine ⟨hcc, hcae, hcrange, hc1, hc0, hce.trans (le_max_left _ _), ?_, ?_⟩
  · intro x hx r hr hr1
    refine (hcg x hx r hr hr1).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _)
  · exact aux_lem_cutoffs_pair_bound_of_holder (by norm_num) hhol hnorm


/-- A compactly supported representative may be restricted to a smaller killed
Sobolev graph. Both its value and weak gradient are preserved on the smaller domain. -/
theorem aux_cor_as_resolvent_restrict_compact_datum
    {d : ℕ} {Q P : Opens (SpatialCoordinates d)}
    (hQ : Homogenization.IsOpenBoundedConvexDomain (Q : Set (SpatialCoordinates d)))
    (hQP : (Q : Set (SpatialCoordinates d)) ⊆ P)
    (u : killedSobolevGraph P) (f : SpatialCoordinates d → ℝ)
    (hae : (u.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (hf : ∀ x ∉ K, f x = 0) :
    ∃ v : killedSobolevGraph Q,
      (v.val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f ∧
      ∀ i : Fin d, (v.val.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] (u.val.2 i : SpatialCoordinates d → ℝ) := by
  obtain ⟨w, hw, hwgrad⟩ := exists_nativeH10Function_of_killedSobolevGraph u
  let b := H1ofAEEq (w.toH1Function.restrict Q.isOpen hQP) f
    (by simpa only [Homogenization.H1Function.restrict, hw] using hae.symm)
  obtain ⟨v, hv⟩ := Homogenization.memH10_of_compactSupport hQ b hK hKQ hf
  have hval : (sobolevDataOfH1 v.toH1Function).1 = (sobolevDataOfH1 b).1 := by
    apply Lp.ext
    exact (sobolevDataOfH1_fst_coeFn v.toH1Function).trans
      (Filter.EventuallyEq.trans (Filter.Eventually.of_forall (fun x => congrFun hv x))
        (sobolevDataOfH1_fst_coeFn b).symm)
  have hgrad : (sobolevDataOfH1 v.toH1Function).2 = (sobolevDataOfH1 b).2 := by
    apply weakSobolevGraph_gradient_unique (sobolevDataOfH1_mem_weak v.toH1Function)
    change ((sobolevDataOfH1 v.toH1Function).1, (sobolevDataOfH1 b).2) ∈ weakSobolevGraph Q
    rw [hval]
    exact sobolevDataOfH1_mem_weak b
  refine ⟨⟨sobolevDataOfH1 v.toH1Function, sobolevDataOfH1_mem_killed v⟩, ?_, ?_⟩
  · exact (sobolevDataOfH1_fst_coeFn v.toH1Function).trans
      (Filter.Eventually.of_forall (fun x => congrFun hv x))
  · intro i
    change (fun x => (sobolevDataOfH1 v.toH1Function).2 i x) =ᵐ[_] _
    rw [hgrad]
    have hb := sobolevDataOfH1_snd_coeFn b i
    change (fun x => (sobolevDataOfH1 b).2 i x) =ᵐ[_] fun x => w.toH1Function.grad x i at hb
    simpa only [hwgrad] using hb

/-- Local energy measures agree with restriction when coefficients and weak gradients agree. -/
theorem aux_cor_as_resolvent_restrict_energy_measure
    {d : ℕ} {Q P : Opens (SpatialCoordinates d)}
    (hQP : (Q : Set (SpatialCoordinates d)) ⊆ P)
    (A : PositiveCoefficient Q) (B : PositiveCoefficient P)
    (u : SobolevData Q) (v : SobolevData P)
    (hA : (fun x => A.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fun x => B.val x)
    (hg : ∀ i : Fin d, (u.2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] (v.2 i : SpatialCoordinates d → ℝ)) :
    (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
        (fun x => ENNReal.ofReal (A.val x * ∑ i : Fin d, (u.2 i x)^2)) =
      ((volume.restrict (P : Set (SpatialCoordinates d))).withDensity
        (fun x => ENNReal.ofReal (B.val x * ∑ i : Fin d, (v.2 i x)^2))).restrict Q := by
  rw [restrict_withDensity Q.isOpen.measurableSet,
    Measure.restrict_restrict Q.isOpen.measurableSet, Set.inter_eq_left.2 hQP]
  exact withDensity_congr_ae (aux_lem_cutoffs_cc_density_congr _ _ _ _ hA hg)



/-- Restrict compactly supported cutoff data with its energy bound preserved. -/
theorem aux_cor_as_resolvent_restrict_cutoff_sequence {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
      ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖)
    (z' : SpatialCoordinates d) (R' : ℝ) (hR' : 0 < R')
    (hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z' R' hR'),
      ‖(u : SobolevData (centeredCube z' R' hR')).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z' R' hR')) u‖)
    (hQP : (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆ centeredCube z' R' hR')
    (O : Set (SpatialCoordinates d))
    (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (chi : ℕ → (killedResponseSpace hP').space) (chic : ℕ → SpatialCoordinates d → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hae : ∀ n, ((chi n).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z' R' hR' : Set (SpatialCoordinates d))] chic n)
    (hz : ∀ n, ∀ x ∈ (centeredCube z' R' hR' : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0)
    (he : ∀ n, responseForm (killedResponseSpace hP')
      (cutoffPositiveCoefficient M H omega n z' hR') (chi n) (chi n) ≤ B) :
    ∃ chiQ : ℕ → (killedResponseSpace hP).space, ∀ n,
      ((chiQ n).val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] chic n ∧
      responseForm (killedResponseSpace hP)
        (cutoffPositiveCoefficient M H omega n z hR) (chiQ n) (chiQ n) ≤ B := by
  classical
  let Q := centeredCube z R hR
  let P := centeredCube z' R' hR'
  have hsub : (Q : Set (SpatialCoordinates d)) ⊆ P := hQP
  have hOcompact : IsCompact (closure O) :=
    (isCompact_closure_centeredCube z hR).of_isClosed_subset isClosed_closure
      (hOQ.trans subset_closure)
  let f := fun n => (P : Set (SpatialCoordinates d)).indicator (chic n)
  have hprops : ∀ n, ∃ v : killedSobolevGraph Q,
      (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f n ∧
      ∀ i : Fin d, (v.val.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] ((chi n).val.2 i : SpatialCoordinates d → ℝ) := by
    intro n
    apply aux_cor_as_resolvent_restrict_compact_datum
      (isOpenBoundedConvexDomain_centeredCube z hR) hsub (chi n) (f n) ?_
      (closure O) hOcompact hOQ ?_
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hae n),
        ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
      simpa only [f, Set.indicator_of_mem (hsub hxQ)] using hx
    · intro x hx
      by_cases hxP : x ∈ (P : Set (SpatialCoordinates d))
      · rw [show f n x = chic n x from Set.indicator_of_mem hxP _]
        exact hz n x hxP (fun hxO => hx (subset_closure hxO))
      · exact Set.indicator_of_notMem hxP _
  choose chiQ hchiQ hgrad using hprops
  refine ⟨chiQ, ?_⟩
  intro n
  have hden := aux_cor_as_resolvent_restrict_energy_measure hsub
    (cutoffPositiveCoefficient M H omega n z hR)
    (cutoffPositiveCoefficient M H omega n z' hR') (chiQ n).val (chi n).val
    ((aux_lem_cutoffs_positiveCoefficient_ae M H omega n z hR).trans
      (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hsub
        (aux_lem_cutoffs_positiveCoefficient_ae M H omega n z' hR')))) (hgrad n)
  have hmono := le_of_eq_of_le hden Measure.restrict_le_self
  constructor
  · filter_upwards [hchiQ n, ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
    simpa only [f, Set.indicator_of_mem (hsub hxQ)] using hx
  · apply (ENNReal.ofReal_le_ofReal_iff hB).1
    have hm := hmono Set.univ
    rw [aux_cor_as_resolvent_energy_measure _ _ Set.univ MeasurableSet.univ,
      aux_cor_as_resolvent_energy_measure _ _ Set.univ MeasurableSet.univ,
      _root_.SubdiffusiveProcess.ResponseMoments.localGradientEnergy_univ, _root_.SubdiffusiveProcess.ResponseMoments.localGradientEnergy_univ] at hm
    exact hm.trans (ENNReal.ofReal_le_ofReal (he n))


/-- Uniform convergence of representatives on the cube implies convergence in its L2 space. -/
theorem aux_cor_as_resolvent_lp_of_uniform {d : ℕ}
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (uN : ℕ → DomainL2 (centeredCube z R hR)) (u : DomainL2 (centeredCube z R hR))
    (fN : ℕ → SpatialCoordinates d → ℝ) (f : SpatialCoordinates d → ℝ)
    (hN : ∀ n, (uN n : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] fN n)
    (hu : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] f)
    (hconv : TendstoUniformlyOn fN f atTop (centeredCube z R hR : Set (SpatialCoordinates d))) :
    Tendsto uN atTop (𝓝 u) := by
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  have hQmeas : MeasurableSet Q := (centeredCube z R hR).isOpen.measurableSet
  have hQfin : (volume.restrict Q) Q ≠ ⊤ := measure_ne_top _ _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let L : ℝ := Real.sqrt ((volume.restrict Q) Q).toReal
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  let δ : ℝ := ε / (L + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hbound : δ * L < ε := by
    have heq : δ * (L + 1) = ε := div_mul_cancel₀ ε (by linarith)
    nlinarith
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv δ hδ] with n hn
  have hae : ∀ᵐ x ∂volume.restrict Q,
      ‖(uN n - u) x‖ ≤ Q.indicator (fun _ => δ) x := by
    filter_upwards [Lp.coeFn_sub (uN n) u, hN n, hu, ae_restrict_mem hQmeas]
      with x hx hxN hxu hxQ
    rw [hx, Pi.sub_apply, hxN, hxu, Real.norm_eq_abs, Set.indicator_of_mem hxQ]
    have hh := hn x hxQ
    simpa only [Real.dist_eq, abs_sub_comm] using hh.le
  rw [dist_eq_norm]
  exact (_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.norm_le_of_ae_indicator_bound hQmeas hQfin hδ.le hae).trans_lt hbound

/-- A uniformly bounded-energy, equicontinuous plateau has a plateau in the limit form domain. -/
theorem aux_cor_as_resolvent_limit_plateau {d : ℕ}
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hF : ∀ u, F.toClosedForm.energy u = limitFormEnergy G u)
    (hresponse : ∀ f : DomainL2 (centeredCube z R hR),
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (𝓝 (inner ℝ f (G f))))
    (K O : Set (SpatialCoordinates d)) (hKO : K ⊆ O)
    (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (chi : ℕ → S.space) (chic : ℕ → SpatialCoordinates d → ℝ) (B C : ℝ) (hC : 0 ≤ C)
    (hchi : ∀ n,
      ContinuousOn (chic n) (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      ((chi n).val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] chic n ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        0 ≤ chic n x ∧ chic n x ≤ 1) ∧
      (∀ x ∈ K, chic n x = 1) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
      responseForm S (a n) (chi n) (chi n) ≤ B ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        ∀ y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        |chic n x - chic n y| ≤ C * (Real.sqrt (∑ i : Fin d, (x i - y i)^2)) ^ (1 / 2 : ℝ))) :
    ∃ w ∈ F.toClosedForm.domain, ∃ g : SpatialCoordinates d → ℝ,
      Continuous g ∧ HasCompactSupport g ∧
      tsupport g ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      (w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] g ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧ (∀ x ∈ K, g x = 1) ∧ ∀ x ∉ O, g x = 0 := by
  classical
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  have hQopen : IsOpen Q := (centeredCube z R hR).isOpen
  have hQcomp : IsCompact (closure Q) := isCompact_closure_centeredCube z hR
  obtain ⟨σ, hσ, f, hfc, hconv⟩ := aux_lem_cutoffs_subseq_uniform (closure Q) hQcomp chic
    (fun n => (hchi n).1) (by norm_num : (0 : ℝ) < 1 / 2) hC
    (B := 1) (fun n x hx => by
      rw [abs_of_nonneg ((hchi n).2.2.1 x hx).1]
      exact ((hchi n).2.2.1 x hx).2)
    (fun n => (hchi n).2.2.2.2.2.2)
  have hf0 : ∀ x ∈ closure Q, x ∉ O → f x = 0 := by
    intro x hx hxo
    have hz : Tendsto (fun n => chic (σ n) x) atTop (𝓝 0) := by
      simpa only [(hchi _).2.2.2.2.1 x hx hxo] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (hconv.tendsto_at hx) hz
  have hf1 : ∀ x ∈ K, f x = 1 := by
    intro x hx
    have hxQ : x ∈ closure Q := subset_closure (hOQ (subset_closure (hKO hx)))
    have hz : Tendsto (fun n => chic (σ n) x) atTop (𝓝 1) := by
      simpa only [(hchi _).2.2.2.1 x hx] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    exact tendsto_nhds_unique (hconv.tendsto_at hxQ) hz
  have hfr : ∀ x ∈ closure Q, 0 ≤ f x ∧ f x ≤ 1 := by
    intro x hx
    exact ⟨ge_of_tendsto (hconv.tendsto_at hx)
      (Eventually.of_forall fun n => ((hchi (σ n)).2.2.1 x hx).1),
      le_of_tendsto (hconv.tendsto_at hx)
        (Eventually.of_forall fun n => ((hchi (σ n)).2.2.1 x hx).2)⟩
  let g : SpatialCoordinates d → ℝ := (closure Q).piecewise f 0
  have hgf : ∀ x ∈ closure Q, g x = f x := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have hgc : Continuous g := by
    apply continuous_piecewise _ _ continuousOn_const
    · intro x hx
      rw [isClosed_closure.frontier_eq] at hx
      apply hf0 x hx.1
      intro hxo
      have hxQ := hOQ (subset_closure hxo)
      exact hx.2 (interior_maximal subset_closure hQopen hxQ)
    · simpa only [closure_closure] using hfc
  have hgzero : ∀ x ∉ O, g x = 0 := by
    intro x hxo
    by_cases hxQ : x ∈ closure Q
    · rw [hgf x hxQ]; exact hf0 x hxQ hxo
    · exact Set.piecewise_eq_of_notMem _ _ _ hxQ
  have hgs : tsupport g ⊆ closure O := by
    apply closure_mono
    intro x hx
    by_contra hxo
    exact hx (hgzero x hxo)
  have hgcs : HasCompactSupport g :=
    hQcomp.of_isClosed_subset (isClosed_tsupport g) (hgs.trans (hOQ.trans subset_closure))
  have hgLp : MemLp g 2 (volume.restrict Q) := hgc.memLp_of_hasCompactSupport hgcs
  let w : DomainL2 (centeredCube z R hR) := hgLp.toLp g
  have hw : (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] g := hgLp.coeFn_toLp
  have hconvg : TendstoUniformlyOn (fun n => chic (σ n)) g atTop Q := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv ε hε] with n hn x hx
    rw [hgf x (subset_closure hx)]
    exact hn x (subset_closure hx)
  have hlp := aux_cor_as_resolvent_lp_of_uniform z R hR
    (fun n => (chi (σ n)).val.1) w (fun n => chic (σ n)) g
    (fun n => (hchi (σ n)).2.1) hw hconvg
  have hlow := quadraticDual_le_liminf_responseForm S (fun n => a (σ n)) G
    (fun n => chi (σ n)) w (fun f => tendsto_const_nhds.inner hlp)
    (fun f => (hresponse f).comp hσ.tendsto_atTop)
  have hlim : liminf (fun n => ((responseForm S (a (σ n)) (chi (σ n)) (chi (σ n)) : ℝ) : EReal))
      atTop ≤ (B : EReal) := by
    apply liminf_le_of_frequently_le
    · exact (Eventually.of_forall fun n => EReal.coe_le_coe_iff.mpr
        (hchi (σ n)).2.2.2.2.2.1).frequently
    · exact isBoundedUnder_of_eventually_ge (a := (0 : EReal))
        (Eventually.of_forall fun n => EReal.coe_nonneg.mpr (responseForm_nonneg S _ _))
  have hwdom : w ∈ F.toClosedForm.domain := by
    apply F.toClosedForm.mem_domain_of_energy_lt_top
    rw [hF]
    exact hlow.trans_lt (hlim.trans_lt (EReal.coe_lt_top B))
  refine ⟨w, hwdom, g, hgc, hgcs, hgs.trans hOQ, hw, ?_, ?_, hgzero⟩
  · intro x
    by_cases hxQ : x ∈ closure Q
    · rw [hgf x hxQ]; exact hfr x hxQ
    · rw [show g x = 0 from Set.piecewise_eq_of_notMem _ _ _ hxQ]
      exact ⟨le_rfl, zero_le_one⟩
  · intro x hx
    rw [hgf x (subset_closure (hOQ (subset_closure (hKO hx))))]
    exact hf1 x hx


/-- Sums of level cutoffs approximate a nonnegative number to one mesh unit. -/
lemma aux_cor_as_resolvent_level_sum (δ : ℝ) (hδ : 0 < δ) (N : ℕ)
    (q : ℝ) (hq : 0 ≤ q) (hqN : q ≤ N * δ) (c : ℕ → ℝ)
    (hc : ∀ i < N, 0 ≤ c i ∧ c i ≤ 1)
    (hc1 : ∀ i < N, (i + 1 : ℕ) * δ ≤ q → c i = 1)
    (hc0 : ∀ i < N, q ≤ i * δ → c i = 0) :
    |δ * (∑ i ∈ Finset.range N, c i) - q| ≤ δ := by
  induction N with
  | zero =>
    have hq0 : q = 0 := by
      simp only [Nat.cast_zero, zero_mul] at hqN
      exact le_antisymm hqN hq
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, hq0, sub_self, abs_zero]
    exact hδ.le
  | succ N ih =>
    by_cases hq' : q ≤ N * δ
    · rw [Finset.sum_range_succ, hc0 N (Nat.lt_succ_self N) hq', add_zero]
      exact ih hq' (fun i hi => hc i (Nat.lt_succ_of_lt hi))
        (fun i hi => hc1 i (Nat.lt_succ_of_lt hi))
        (fun i hi => hc0 i (Nat.lt_succ_of_lt hi))
    · have hsum : (∑ i ∈ Finset.range N, c i) = N := by
        calc
          _ = ∑ i ∈ Finset.range N, (1 : ℝ) := Finset.sum_congr rfl fun i hi =>
            hc1 i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))
              ((mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.mem_range.mp hi :
                  ((i + 1 : ℕ) : ℝ) ≤ N) hδ.le).trans (le_of_not_ge hq'))
          _ = N := by simp
      rw [Finset.sum_range_succ, hsum]
      have hcn := hc N (Nat.lt_succ_self N)
      rw [Nat.cast_add, Nat.cast_one] at hqN
      apply abs_le.mpr
      constructor <;> nlinarith

/-- A real vector space containing continuous plateau cutoffs uniformly
approximates every compactly supported continuous function. -/
theorem aux_cor_as_resolvent_positive_density_of_plateaus
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (A : Submodule ℝ (X → ℝ)) (Q : Set X)
    (hcut : ∀ (K O : Set X), IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ Q →
      ∃ g ∈ A, (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
        (∀ x ∈ K, g x = 1) ∧ ∀ x ∉ O, g x = 0)
    (f : X → ℝ) (hf : Continuous f) (hfcs : HasCompactSupport f)
    (hfs : tsupport f ⊆ Q) (hf0 : ∀ x, 0 ≤ f x) (δ : ℝ) (hδ : 0 < δ) :
    ∃ g ∈ A, ∀ x, |g x - f x| ≤ δ := by
  classical
  obtain ⟨B, hB⟩ := hfcs.exists_bound_of_continuous hf
  obtain ⟨N, hN⟩ := exists_nat_gt (B / δ)
  have hBN : B ≤ N * δ := ((div_lt_iff₀ hδ).mp hN).le
  let K : ℕ → Set X := fun i => {x | ((i + 1 : ℕ) : ℝ) * δ ≤ f x}
  let O : ℕ → Set X := fun i => {x | (i : ℝ) * δ < f x}
  have hKsupport : ∀ i, K i ⊆ tsupport f := by
    intro i x hx
    apply subset_tsupport f
    have hipos : 0 < ((i + 1 : ℕ) : ℝ) * δ := mul_pos (by positivity) hδ
    exact ne_of_gt (hipos.trans_le hx)
  have hOcl : ∀ i, closure (O i) ⊆ tsupport f := by
    intro i
    apply closure_minimal _ (isClosed_tsupport f)
    intro x hx
    apply subset_tsupport f
    exact ne_of_gt ((mul_nonneg (Nat.cast_nonneg i) hδ.le).trans_lt hx)
  have hg : ∀ i : ℕ, ∃ g ∈ A, (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      (∀ x ∈ K i, g x = 1) ∧ ∀ x ∉ O i, g x = 0 := by
    intro i
    apply hcut (K i) (O i)
    · exact hfcs.of_isClosed_subset (isClosed_le continuous_const hf) (hKsupport i)
    · exact isOpen_lt continuous_const hf
    · intro x hx
      have hi : (i : ℝ) * δ < ((i + 1 : ℕ) : ℝ) * δ := by
        push_cast
        nlinarith
      exact hi.trans_le hx
    · exact (hOcl i).trans hfs
  choose g hgA hgr hg1 hg0 using hg
  refine ⟨δ • ∑ i ∈ Finset.range N, g i,
    A.smul_mem δ (A.sum_mem fun i hi => hgA i), ?_⟩
  intro x
  have hfx : f x ≤ N * δ := (le_abs_self _).trans ((hB x).trans hBN)
  have hx := aux_cor_as_resolvent_level_sum δ hδ N (f x) (hf0 x) hfx
    (fun i => g i x) (fun i _ => hgr i x)
    (fun i _ hi => hg1 i x hi) (fun i _ hi => hg0 i x (not_lt.mpr hi))
  simpa only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using hx

/-- A real vector space containing continuous plateau cutoffs uniformly
approximates every compactly supported continuous function. -/
theorem aux_cor_as_resolvent_uniform_density_of_plateaus
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (A : Submodule ℝ (X → ℝ)) (Q : Set X)
    (hcut : ∀ (K O : Set X), IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ Q →
      ∃ g ∈ A, (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
        (∀ x ∈ K, g x = 1) ∧ ∀ x ∉ O, g x = 0)
    (f : X → ℝ) (hf : Continuous f) (hfcs : HasCompactSupport f)
    (hfs : tsupport f ⊆ Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ A, ∀ x, |g x - f x| < ε := by
  classical
  let fp : X → ℝ := fun x => max (f x) 0
  let fm : X → ℝ := fun x => max (-f x) 0
  have hfp : Continuous fp := hf.max continuous_const
  have hfm : Continuous fm := hf.neg.max continuous_const
  have hfps : tsupport fp ⊆ tsupport f := tsupport_comp_subset (g := fun t : ℝ => max t 0) (by simp) f
  have hfms : tsupport fm ⊆ tsupport f := tsupport_comp_subset (g := fun t : ℝ => max (-t) 0) (by simp) f
  have hfpc : HasCompactSupport fp := hfcs.comp_left (g := fun t : ℝ => max t 0) (by simp)
  have hfmc : HasCompactSupport fm := hfcs.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)
  obtain ⟨gp, hgp, hp⟩ := aux_cor_as_resolvent_positive_density_of_plateaus A Q hcut fp hfp hfpc (hfps.trans hfs)
    (fun x => le_max_right _ _) (ε / 3) (by positivity)
  obtain ⟨gm, hgm, hm⟩ := aux_cor_as_resolvent_positive_density_of_plateaus A Q hcut fm hfm hfmc (hfms.trans hfs)
    (fun x => le_max_right _ _) (ε / 3) (by positivity)
  refine ⟨gp - gm, A.sub_mem hgp hgm, ?_⟩
  intro x
  have hdecomp : f x = fp x - fm x := by
    dsimp [fp, fm]
    rcases le_total (f x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  have heq : (gp - gm) x - f x = (gp x - fp x) - (gm x - fm x) := by
    rw [hdecomp]
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  exact (abs_sub (gp x - fp x) (gm x - fm x)).trans_lt
    ((add_le_add (hp x) (hm x)).trans_lt (by linarith))


/-- The vector space of continuous compactly supported representatives in a form domain. -/
def aux_cor_as_resolvent_continuous_core {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))) :
    Submodule ℝ (SpatialCoordinates d → ℝ) where
  carrier := {g | Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ (Q : Set (SpatialCoordinates d)) ∧
    ∃ w ∈ F.toClosedForm.domain, (w : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] g}
  zero_mem' := by
    refine ⟨continuous_const, ?_, ?_, 0, F.toClosedForm.domain.zero_mem, Lp.coeFn_zero ℝ 2 _⟩ <;>
      simp only [HasCompactSupport, tsupport_zero, isCompact_empty, empty_subset]
  add_mem' := by
    rintro f g ⟨hfc, hfcs, hfs, u, hu, hue⟩ ⟨hgc, hgcs, hgs, v, hv, hve⟩
    refine ⟨hfc.add hgc, hfcs.add hgcs, ?_, u + v, F.toClosedForm.domain.add_mem hu hv,
      (Lp.coeFn_add u v).trans (hue.add hve)⟩
    exact ((closure_mono (Function.support_add f g)).trans closure_union.le).trans
      (union_subset hfs hgs)
  smul_mem' := by
    rintro c f ⟨hfc, hfcs, hfs, u, hu, hue⟩
    exact ⟨hfc.const_smul c, hfcs.smul_left,
      (tsupport_smul_subset_right (fun _ => c) f).trans hfs,
      c • u, F.toClosedForm.domain.smul_mem c hu, (Lp.coeFn_smul c u).trans (hue.const_smul c)⟩

/-- On every cube inside a parent regularity event, every convergent inverse
subsequence has a uniformly dense continuous compact core. -/
theorem aux_cor_as_resolvent_hunif_fixed {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (omega : BilateralField d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
      ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖)
    (z' : SpatialCoordinates d) (R' : ℝ) (hR' : 0 < R')
    (hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z' R' hR'),
      ‖(u : SobolevData (centeredCube z' R' hR')).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z' R' hR')) u‖)
    (hQP : closure (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆ centeredCube z' R' hR')
    (hreg : aux_cor_as_resolvent_MeshRegProp M H omega z' R' hR')
    (s : ℕ → ℕ)
    (GNi : ℕ → DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (hGNi : ∀ n f, GNi n f =
      (in_killed_inverse M H HI omega (s n) z hR hP f : SobolevData (centeredCube z R hR)).1)
    (hconv : Tendsto GNi atTop (𝓝 G))
    (F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hF : ∀ u, F.toClosedForm.energy u = limitFormEnergy G u) :
    ∀ f0 : SpatialCoordinates d → ℝ, Continuous f0 → HasCompactSupport f0 →
      tsupport f0 ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∀ ε : ℝ, 0 < ε → ∃ w ∈ F.toClosedForm.domain, ∃ g : SpatialCoordinates d → ℝ,
        Continuous g ∧ HasCompactSupport g ∧
        tsupport g ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (w : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] g ∧
        ∀ x, |g x - f0 x| < ε := by
  let Q := centeredCube z R hR
  let P := centeredCube z' R' hR'
  let A := aux_cor_as_resolvent_continuous_core Q F
  have hsub : (Q : Set (SpatialCoordinates d)) ⊆ P := subset_closure.trans hQP
  have hresponse : ∀ f : DomainL2 Q,
      Tendsto (fun n => inverseResponse (killedResponseSpace hP)
        (cutoffPositiveCoefficient M H omega (s n) z hR)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)) atTop
        (𝓝 (inner ℝ f (G f))) := by
    intro f
    have hev : Tendsto (fun n => GNi n f) atTop (𝓝 (G f)) :=
      ((continuous_id.clm_apply continuous_const).tendsto G).comp hconv
    have hh : Tendsto (fun n => inner ℝ f (GNi n f)) atTop (𝓝 (inner ℝ f (G f))) :=
      tendsto_const_nhds.inner hev
    simpa only [hGNi, in_killed_inverse, inverseResponse_eq_load] using! hh
  have hcut : ∀ (K O : Set (SpatialCoordinates d)), IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ Q →
      ∃ g ∈ A, (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧ (∀ x ∈ K, g x = 1) ∧ ∀ x ∉ O, g x = 0 := by
    intro K O hK hO hKO hOQ
    obtain ⟨V, chi, chic, B, C, hV, hKV, hVO, hB, hC, hc⟩ :=
      aux_cor_as_resolvent_strong_cutoffs hd M H z' R' hR' hP' omega hreg K O hK hO hKO
        (hOQ.trans hsub)
    obtain ⟨chiQ, hchiQ⟩ := aux_cor_as_resolvent_restrict_cutoff_sequence M H omega
      z R hR hP z' R' hR' hP' hsub O hOQ chi chic B hB
      (fun n => (hc n).2.1) (fun n => (hc n).2.2.2.2.1) (fun n => (hc n).2.2.2.2.2.1)
    have hdata : ∀ n,
        ContinuousOn (chic (s n)) (closure (Q : Set (SpatialCoordinates d))) ∧
        ((chiQ (s n)).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic (s n) ∧
        (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 ≤ chic (s n) x ∧ chic (s n) x ≤ 1) ∧
        (∀ x ∈ K, chic (s n) x = 1) ∧
        (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), x ∉ O → chic (s n) x = 0) ∧
        responseForm (killedResponseSpace hP) (cutoffPositiveCoefficient M H omega (s n) z hR)
          (chiQ (s n)) (chiQ (s n)) ≤ B ∧
        (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ y ∈ closure (Q : Set (SpatialCoordinates d)),
          |chic (s n) x - chic (s n) y| ≤ C * (Real.sqrt (∑ i : Fin d, (x i - y i)^2)) ^ (1 / 2 : ℝ)) := by
      intro n
      obtain ⟨hcc, hae, hcr, hc1, hc0, he, hg, hhol⟩ := hc (s n)
      exact ⟨hcc.mono (hQP.trans subset_closure), (hchiQ (s n)).1,
        fun x hx => hcr x (subset_closure (hQP hx)), fun x hx => hc1 x (hKV hx),
        fun x hx hxo => hc0 x (hQP hx) hxo, (hchiQ (s n)).2,
        fun x hx y hy => hhol x (subset_closure (hQP hx)) y (subset_closure (hQP hy))⟩
    obtain ⟨w, hw, g, hgc, hgcs, hgs, hwg, hgr, hg1, hg0⟩ :=
      aux_cor_as_resolvent_limit_plateau z R hR (killedResponseSpace hP)
        (fun n => cutoffPositiveCoefficient M H omega (s n) z hR) G F hF hresponse K O hKO hOQ
        (fun n => chiQ (s n)) (fun n => chic (s n)) B C hC hdata
    exact ⟨g, ⟨hgc, hgcs, hgs, w, hw, hwg⟩, hgr, hg1, hg0⟩
  intro f0 hf0 hfcs hfs ε hε
  obtain ⟨g, hg, hgf⟩ := aux_cor_as_resolvent_uniform_density_of_plateaus A Q hcut f0 hf0 hfcs hfs ε hε
  obtain ⟨hgc, hgcs, hgs, w, hw, hwg⟩ := hg
  exact ⟨w, hw, g, hgc, hgcs, hgs, hwg, hgf⟩


/-- A cutoff supported inside a smaller cube retains its energy bounds there. -/
theorem aux_cor_as_resolvent_hcut_restrict {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
      ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖)
    (z' : SpatialCoordinates d) (R' : ℝ) (hR' : 0 < R')
    (hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z' R' hR'),
      ‖(u : SobolevData (centeredCube z' R' hR')).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z' R' hR')) u‖)
    (hQP : closure (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆ centeredCube z' R' hR')
    (hcut : aux_limiting_local_energy_HCUTProp M H z' R' hR' hP' id omega) :
    aux_limiting_local_energy_HCUTProp M H z R hR hP id omega := by
  classical
  let Q := centeredCube z R hR
  let P := centeredCube z' R' hR'
  have hsub : (Q : Set (SpatialCoordinates d)) ⊆ P := subset_closure.trans hQP
  intro K O hK hO hKO hOQ
  obtain ⟨V, chi, chic, B, hV, hKV, hVO, hB, hchi⟩ :=
    hcut K O hK hO hKO (hOQ.trans hsub)
  have hOcompact : IsCompact (closure O) :=
    (isCompact_closure_centeredCube z hR).of_isClosed_subset isClosed_closure
      (hOQ.trans subset_closure)
  let f := fun n => (P : Set (SpatialCoordinates d)).indicator (chic n)
  have hprops : ∀ n, ∃ v : killedSobolevGraph Q,
      (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f n ∧
      ∀ i : Fin d, (v.val.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] ((chi n).val.2 i : SpatialCoordinates d → ℝ) := by
    intro n
    apply aux_cor_as_resolvent_restrict_compact_datum
      (isOpenBoundedConvexDomain_centeredCube z hR) hsub (chi n) (f n) ?_
      (closure O) hOcompact hOQ ?_
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hchi n).2.1,
        ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
      simpa only [f, Set.indicator_of_mem (hsub hxQ)] using hx
    · intro x hx
      by_cases hxP : x ∈ (P : Set (SpatialCoordinates d))
      · rw [show f n x = chic n x from Set.indicator_of_mem hxP _]
        exact (hchi n).2.2.2.2.1 x hxP (fun hxO => hx (subset_closure hxO))
      · exact Set.indicator_of_notMem hxP _
  choose chiQ hchiQ hgrad using hprops
  refine ⟨V, chiQ, chic, B, hV, hKV, hVO, hB, ?_⟩
  intro n
  have hden := aux_cor_as_resolvent_restrict_energy_measure hsub
    (cutoffPositiveCoefficient M H omega n z hR)
    (cutoffPositiveCoefficient M H omega n z' hR') (chiQ n).val (chi n).val
    ((aux_lem_cutoffs_positiveCoefficient_ae M H omega n z hR).trans
      (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hsub
        (aux_lem_cutoffs_positiveCoefficient_ae M H omega n z' hR')))) (hgrad n)
  have hmono := le_of_eq_of_le hden Measure.restrict_le_self
  refine ⟨(hchi n).1.mono (hQP.trans subset_closure), ?_,
    fun x hx => (hchi n).2.2.1 x (hsub hx), (hchi n).2.2.2.1,
    fun x hx hxo => (hchi n).2.2.2.2.1 x (hsub hx) hxo, ?_, ?_⟩
  · filter_upwards [hchiQ n, ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
    simpa only [f, Set.indicator_of_mem (hsub hxQ)] using hx
  · apply (ENNReal.ofReal_le_ofReal_iff hB).1
    have hm := hmono Set.univ
    rw [aux_cor_as_resolvent_energy_measure _ _ Set.univ MeasurableSet.univ,
      aux_cor_as_resolvent_energy_measure _ _ Set.univ MeasurableSet.univ,
      _root_.SubdiffusiveProcess.ResponseMoments.localGradientEnergy_univ, _root_.SubdiffusiveProcess.ResponseMoments.localGradientEnergy_univ] at hm
    exact hm.trans (ENNReal.ofReal_le_ofReal (hchi n).2.2.2.2.2.1)
  · intro x hx r hr hr1
    exact (hmono (Metric.ball x r)).trans ((hchi n).2.2.2.2.2.2 x (subset_closure (hQP hx)) r hr hr1)


/-- Finite-cell Dirichlet regularity constructs the cutoff family on a fixed cube. -/
theorem aux_cor_as_resolvent_hcut_of_mesh_regularity {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
      ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖)
    (omega : BilateralField d)
    (homega : aux_cor_as_resolvent_MeshRegProp M H omega z R hR) :
    aux_limiting_local_energy_HCUTProp M H z R hR hP id omega := by
  intro K O hK hO hKO hOQ
  obtain ⟨V, chi, chic, B, C, hV, hKV, hVO, hB, hC, hc⟩ :=
    aux_cor_as_resolvent_strong_cutoffs hd M H z R hR hP omega homega K O hK hO hKO hOQ
  refine ⟨V, chi, chic, B, hV, hKV, hVO, hB, ?_⟩
  intro n
  obtain ⟨hcc, hae, hcr, hc1, hc0, he, hg, _⟩ := hc n
  exact ⟨hcc, hae, fun x hx => hcr x (subset_closure hx), hc1, hc0, he, hg⟩


/-- Original-space HCUT on a fixed cube. The event contains every finite mesh
before the compact set, open set, and smooth plateau are chosen. -/
theorem aux_cor_as_resolvent_hcut_cube_event {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Jc : in_J d) (Pc : in_poincare d hd Jc)
    (Xc : in_extension d hd Jc) (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ →
        ∀ (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
          (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
            ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
              K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖),
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            aux_limiting_local_energy_HCUTProp M H z R hR hP id omega := by
  obtain ⟨δ, hδ, hregular⟩ := aux_cor_as_resolvent_zero_dir_event hd Jc Pc Xc W Cp D Sf Step Dbase Interp
  refine ⟨δ, hδ, ?_⟩
  intro M Rm Sreg It H HI hM z R hR hP
  have hevents := ae_all_iff.2 fun J : ℕ => ae_all_iff.2 fun k : OddGridIndex d (triadicHalf J) =>
    hregular M Rm Sreg It H HI hM (oddGridCenter z R (triadicHalf J) k)
      (R / (2 * (triadicHalf J : ℝ) + 1)) (div_pos hR (by positivity))
  filter_upwards [hevents] with omega homega
  exact aux_cor_as_resolvent_hcut_of_mesh_regularity hd M H z R hR hP omega homega


/-- Original-space HCUT on a fixed cube. The event contains every finite mesh
before the compact set, open set, and smooth plateau are chosen. -/
theorem aux_cor_as_resolvent_mesh_cube_event {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Jc : in_J d) (Pc : in_poincare d hd Jc)
    (Xc : in_extension d hd Jc) (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ →
        ∀ (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            aux_cor_as_resolvent_MeshRegProp M H omega z R hR := by
  obtain ⟨δ, hδ, hregular⟩ := aux_cor_as_resolvent_zero_dir_event hd Jc Pc Xc W Cp D Sf Step Dbase Interp
  refine ⟨δ, hδ, ?_⟩
  intro M Rm Sreg It H HI hM z R hR
  have hevents := ae_all_iff.2 fun J : ℕ => ae_all_iff.2 fun k : OddGridIndex d (triadicHalf J) =>
    hregular M Rm Sreg It H HI hM (oddGridCenter z R (triadicHalf J) k)
      (R / (2 * (triadicHalf J : ℝ) + 1)) (div_pos hR (by positivity))
  filter_upwards [hevents] with omega homega
  exact homega


/-- A countable exhaustion and compact-support restriction yield the common HCUT event. -/
theorem aux_cor_as_resolvent_hcut_supply {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc) (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D0 : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_HI : InfraredCharacterization M H),
        M.delta ≤ delta0 →
        _root_.SubdiffusiveProcess.Paper.aux_limiting_local_energy_HCUT_prop M H := by
  have : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  obtain ⟨δ, hδ, hfixed⟩ := aux_cor_as_resolvent_hcut_cube_event hd Jc Pc Xc W Cp D0 Sf Step Dbase Interp
  refine ⟨δ, hδ, ?_⟩
  intro M Rm Sreg It H HI hM s hs
  refine ⟨id, strictMono_id, ?_⟩
  let radius : ℕ → ℝ := fun n => 2 * ((n : ℝ) + 1)
  have hrad : ∀ n, 0 < radius n := fun n => by dsimp [radius]; positivity
  have hp : ∀ n, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n)),
      ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n))) u‖ := by
    intro n
    exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n))
      (isOpenBoundedConvexDomain_centeredCube (0 : SpatialCoordinates d) (hrad n))).1
  have hevents := ae_all_iff.2 fun n : ℕ => hfixed M Rm Sreg It H HI hM
    0 (radius n) (hrad n) (hp n)
  filter_upwards [hevents] with omega homega
  intro z R hR _ hP
  obtain ⟨n, hn⟩ := exists_nat_gt (R / 2 + dist z 0)
  have hQP : closure (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆
      centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n) := by
    intro x hx
    rw [aux_lem_cutoffs_geom_closure_eq] at hx
    have hx' : dist x z ≤ R / 2 := hx
    change dist x 0 < radius n / 2
    have ht := dist_triangle x z 0
    dsimp [radius]
    linarith
  have hcut := aux_cor_as_resolvent_hcut_restrict M H omega z R hR hP
    0 (radius n) (hrad n) (hp n) hQP (homega n)
  intro K O hK hO hKO hOQ
  obtain ⟨V, chi, chic, B, hV, hKV, hVO, hB, hchi⟩ := hcut K O hK hO hKO hOQ
  exact ⟨V, chi ∘ s, chic ∘ s, B, hV, hKV, hVO, hB, fun n => hchi (s n)⟩


/-- A countable exhaustion and compact-support restriction yield the common HUNIF event. -/
theorem aux_cor_as_resolvent_hunif_supply {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc) (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D0 : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
        M.delta ≤ delta0 →
        _root_.SubdiffusiveProcess.Paper.aux_limiting_local_energy_HUNIF_prop M H HI := by
  have : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  obtain ⟨δ, hδ, hfixed⟩ := aux_cor_as_resolvent_mesh_cube_event hd Jc Pc Xc W Cp D0 Sf Step Dbase Interp
  refine ⟨δ, hδ, ?_⟩
  intro M Rm Sreg It H HI hM s hs
  refine ⟨id, strictMono_id, ?_⟩
  let radius : ℕ → ℝ := fun n => 2 * ((n : ℝ) + 1)
  have hrad : ∀ n, 0 < radius n := fun n => by dsimp [radius]; positivity
  have hp : ∀ n, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n)),
      ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n))) u‖ := by
    intro n
    exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n))
      (isOpenBoundedConvexDomain_centeredCube (0 : SpatialCoordinates d) (hrad n))).1
  have hevents := ae_all_iff.2 fun n : ℕ => hfixed M Rm Sreg It H HI hM
    0 (radius n) (hrad n)
  filter_upwards [hevents] with omega homega
  intro z R hR _ hP
  obtain ⟨n, hn⟩ := exists_nat_gt (R / 2 + dist z 0)
  have hQP : closure (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆
      centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n) := by
    intro x hx
    rw [aux_lem_cutoffs_geom_closure_eq] at hx
    have hx' : dist x z ≤ R / 2 := hx
    change dist x 0 < radius n / 2
    have ht := dist_triangle x z 0
    dsimp [radius]
    linarith
  exact aux_cor_as_resolvent_hunif_fixed hd M H HI omega z R hR hP
    0 (radius n) (hrad n) (hp n) hQP (homega n) (s ∘ id)


end CutoffSupplyProofs

/-- "Pathwise convergence of
killed resolvents".

Almost surely, simultaneously for the countable triadic family of cubes `Qtri`,
every `f ∈ C(closure Q)` and every `lambda > 0`, the killed resolvents converge
along the full sequence in the uniform norm on the closed cube; the `C^{1/4}`
bounds on each fixed cube have one finite random constant for all `N` when
`lambda` ranges over a compact subset of `(0, ∞)` and `‖f‖ ≤ 1`; and inside the
VERY SAME probability-one event the canonical `Rlim` is identified
variationally with the actual unique minimizer of the killed limiting resolvent
functional.

Tick list:
- `limiting_local_energy` / `prop_as_forms` supply the actual full-sequence
  convergence of the actual killed inverses and both weak-Mosco clauses; `G` and
  `hGactual` are the concrete measurable inverse limit, never a free target.
- `prop_chaos_growth` supplies the actual cutoff speed measures, their local
  weak convergence `muFull`, the frontier-null property on every cube and finite
  mass on every closed cube; `mu n omega` is the restriction to `closure (Qn n)`.
- `speed_trace_completion` / `lem_19` supply the completed fractional traces
  `T n omega` and the pinned constants `Ktrace`, `Ctrace` through
  `MeasureTraceCharacterization` on the restricted finite speed measures.
- Poincare is the classical ordinary cube Poincare inequality `hP`, identical
  to the `hP` input of `limiting_local_energy` per cube.
- `prop_speed_resolvent` supplies the unique minimizer of the limiting
  functional; its existence, minimality and uniqueness are CONCLUDED here, no
  `ustar` is assumed.
- `prop_uniform_resolvent` (the preceding proof) is applied afresh to every
  subsequence through the compact lambda ranges and the common `C^{1/4}` bound.
- `cutoff_campanato_bound` supplies the pointwise finite-cutoff `C^{1/4}`
  estimate from the preceding proof's Campanato representative; this estimate
  is not a conclusion of `prop_uniform_resolvent`'s limit-only Holder clause.
- `lem_as_coarse` / `lem_as_regularity` / `prop_chaos_growth` supply the
  common coercivity, boundary regularity and growth bounds on the same event.
- `in_crossing` / `in_normalization` attach the actual finite-cutoff
  occupation resolvents `RN` and fix the energy and speed normalisations.
- `Rprob` is gone: no per-input a.e. equality against an arbitrary diagonal,
  no measurability or in-probability convergence input for it.
- The produced `Rlim` is identified variability-free: inside the single a.e.
  event it is `ae`-equal to the unique actual minimizer `ustar` on each cube.
- Neither a.s. convergence of resolvent errors, summability, a `C^{1/4}`
  bound, nor the conclusion is assumed.
- No proof work.

- Supplier: Jc,Pc,Xc,Sf,W,Cp,Interp,BD and the model-specific Rm,Sreg,It are the standing analytic inputs of limiting_local_energy, lem_as_coarse and lem_as_regularity, used on the common event. All full-sequence convergence and common Holder bounds remain conclusions.
-/
theorem cor_as_resolvent
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (F : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M)
        (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg), M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ N, IsMarkovKernel (KN N)) → in_crossing M H PN KN →
        aux_cutoff_lifetime_package_LocalInput M H KN →
      ∀ (Qtri : ℕ → Homogenization.TriadicCube d)
        (hr : ∀ n : ℕ, 0 < Homogenization.cubeScaleFactor (Qtri n)),
      let Qn : ℕ → Opens (SpatialCoordinates d) :=
        fun n => centeredCube (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n);
      ∀ (hP : ∀ n : ℕ, ∃ K : ℝ≥0,
          ∀ v : killedSobolevGraph (Qn n),
            ‖(v : SobolevData (Qn n)).1‖ ≤
              K * ‖subspaceGradient (killedSobolevGraph (Qn n)) v‖),
      ∀ (G : (n : ℕ) → BilateralField d →
          (DomainL2 (Qn n) →L[ℝ] DomainL2 (Qn n))),
        (∀ n : ℕ, Measurable (G n)) →
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (n : ℕ) (f : DomainL2 (Qn n)),
          Tendsto
            (fun N : ℕ =>
              (responseSolution (killedResponseSpace (Ω := Qn n) (hP n))
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (Homogenization.cubeCenter (Qtri n)) (hr n))
                  ((sobolevVolumeLoad f).comp
                    (killedResponseSpace (Ω := Qn n) (hP n)).space.subtypeL)).val.1)
            atTop (𝓝 (G n omega f))) →
      ∀ (muFull : BilateralField d → Measure (SpatialCoordinates d)),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
          (∀ n : ℕ, muFull omega (frontier (Qn n : Set (SpatialCoordinates d))) = 0) ∧
          (∀ n : ℕ, muFull omega (closure (Qn n : Set (SpatialCoordinates d))) < ⊤)) →
      let mu : ℕ → BilateralField d → Measure (SpatialCoordinates d) :=
        fun n omega =>
          (muFull omega).restrict (closure (Qn n : Set (SpatialCoordinates d)));
      ∀ (T : (n : ℕ) → (omega : BilateralField d) →
          CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n) halfFractionalOrder →
          Lp ℝ 2 (mu n omega)),
      ∀ (Ktrace Ctrace : ℕ → BilateralField d → ℝ),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ n : ℕ, 0 ≤ Ktrace n omega ∧ 0 ≤ Ctrace n omega ∧
            MeasureTraceCharacterization hd (Qtri n) (hr n) (mu n omega)
              (Ktrace n omega) (Ctrace n omega) (T n omega)) →
      ∀ (i : (n : ℕ) → (omega : BilateralField d) → (u : DomainL2 (Qn n)) →
          (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤ →
          CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n) halfFractionalOrder),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (n : ℕ) (u : DomainL2 (Qn n))
            (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
            (i n omega u hu).val 0 = u) →
      ∀ (J : (n : ℕ) → BilateralField d → DomainL2 (Qn n) →
          SpatialCoordinates d → ℝ),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (n : ℕ) (u : DomainL2 (Qn n))
            (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
            (J n omega u) =ᵐ[mu n omega]
              (T n omega (i n omega u hu) : SpatialCoordinates d → ℝ)) →
      ∀ (RN : ℕ → ℕ → BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ),
        (∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
            (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
            (x : SpatialCoordinates d),
          RN n N omega lam f x =
            ∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Set.indicator
                {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  (Qn n : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
              ∂(KN N (omega, x))) →
      let Elim : (n : ℕ) → BilateralField d → DomainL2 (Qn n) → ℝ≥0∞ :=
        fun n omega u => (limitFormEnergy (G n omega) u).toENNReal;
      let Func : (n : ℕ) → BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 (Qn n) → ℝ :=
        fun n omega lam f u =>
          (Elim n omega u).toReal +
            lam * (∫ x, J n omega u x ^ 2 ∂(mu n omega)) -
            2 * (∫ x, f x * J n omega u x ∂(mu n omega));
      ∃ Rlim : ℕ → BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ,
        (∀ (n : ℕ) (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            Measurable (fun p : BilateralField d × SpatialCoordinates d =>
              Rlim n p.1 lam f p.2)) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ContinuousOn (Rlim n omega lam f)
                (closure (Qn n : Set (SpatialCoordinates d))) ∧
              ∀ x ∈ frontier (Qn n : Set (SpatialCoordinates d)),
                Rlim n omega lam f x = 0) ∧
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ closure (Qn n : Set (SpatialCoordinates d)),
                  |RN n N omega lam f x - Rlim n omega lam f x| < delta) ∧
          (∀ (n : ℕ) (lam0 lam1 : ℝ), 0 < lam0 → lam0 ≤ lam1 →
            ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
              ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
                (∀ x ∈ closure (Qn n : Set (SpatialCoordinates d)),
                  |RN n N omega lam f x| ≤ Kom) ∧
                ∀ x ∈ closure (Qn n : Set (SpatialCoordinates d)),
                ∀ y ∈ closure (Qn n : Set (SpatialCoordinates d)),
                  |RN n N omega lam f x - RN n N omega lam f y| ≤
                    Kom * dist x y ^ (1 / 4 : ℝ)) ∧
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∀ x ∈ closure (Qn n : Set (SpatialCoordinates d)),
                |Rlim n omega lam f x| ≤ ‖f‖ / lam) ∧
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∃ ustar : DomainL2 (Qn n),
                Elim n omega ustar ≠ ⊤ ∧
                (Rlim n omega lam f)
                  =ᵐ[volume.restrict (Qn n : Set (SpatialCoordinates d))]
                    (ustar : SpatialCoordinates d → ℝ) ∧
                (∀ v : DomainL2 (Qn n), Elim n omega v ≠ ⊤ →
                  Func n omega lam f ustar ≤ Func n omega lam f v) ∧
                (∀ v : DomainL2 (Qn n), Elim n omega v ≠ ⊤ →
                  (∀ w : DomainL2 (Qn n), Elim n omega w ≠ ⊤ →
                    Func n omega lam f v ≤ Func n omega lam f w) →
                  v = ustar))) := by
  -- delta0 := min of the two restated per-cube suppliers' own thresholds (SPLIT-2
  -- ): each of `aux_cor_as_resolvent_cube_cutoff_holder` and
  -- `aux_cor_as_resolvent_cube_variational` is now itself in `∃ delta0, 0 < delta0 ∧
  -- ∀ M ..., M.delta ≤ delta0 → ...` shape (mirroring this principal and the upstream
  -- `lem_as_regularity`/`limiting_local_energy` suppliers), so `M.delta ≤ min delta0_hold
  -- delta0_var` discharges both helpers' own smallness hypotheses uniformly in `M`,
  -- exactly like the conclusion demands. Both extractions happen BEFORE `M` is
  -- introduced, since neither helper's threshold may depend on the later-quantified `M`.
  obtain ⟨delta0_hold, hpos_hold, hHold_all⟩ := aux_cor_as_resolvent_cube_cutoff_holder hd Jc Pc Xc Sf W Cp D Interp Step Dbase
  obtain ⟨delta0_var, hpos_var, hVar_all⟩ :=
    car_variational hd Jc Pc Xc Sf W Cp Interp BD BDQ D Step Dbase hcontract
  refine ⟨min delta0_hold delta0_var, lt_min hpos_hold hpos_var, ?_⟩
  intro M Rm Sreg It hMdel H hInfrared PN KN hKN hin hinput Qtri hr Qn hP G hGmeas hGtendsto muFull
    hmuFull mu T Ktrace Ctrace hT i h_i_val J hJ RN hRN_formula Elim Func
  have hMdel_hold : M.delta ≤ delta0_hold := hMdel.trans (min_le_left _ _)
  have hMdel_var : M.delta ≤ delta0_var := hMdel.trans (min_le_right _ _)
  -- Deep per-cube pieces ( "the preceding proof ... applied afresh to every
  -- subsequence"): the variational/Arzela-Ascoli construction (A, B, E) and the compact-lambda-
  -- range cutoff Holder package (C).
  have hVar := fun n => hVar_all M Rm Sreg It hMdel_var H hInfrared PN
    KN hKN hin hinput Qtri hr hP G hGmeas hGtendsto muFull hmuFull T Ktrace Ctrace hT i h_i_val J hJ
    RN hRN_formula n
  choose Rn hRnMeas hRnAE using hVar
  have hHold := fun n => hHold_all M Rm Sreg It hMdel_hold H hInfrared
    PN KN hKN hin hinput Qtri hr RN hRN_formula n
  have hall : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ n : ℕ,
      (∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ContinuousOn (Rn n omega lam f) (closure (Qn n : Set (SpatialCoordinates d))) ∧
          ∀ x ∈ frontier (Qn n : Set (SpatialCoordinates d)), Rn n omega lam f x = 0) ∧
      (∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            ∀ x ∈ closure (Qn n : Set (SpatialCoordinates d)),
              |RN n N omega lam f x - Rn n omega lam f x| < delta) ∧
      (∀ lam0 lam1 : ℝ, 0 < lam0 → lam0 ≤ lam1 →
          ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
              (∀ x ∈ closure (Qn n : Set (SpatialCoordinates d)), |RN n N omega lam f x| ≤ Kom) ∧
              ∀ x ∈ closure (Qn n : Set (SpatialCoordinates d)),
              ∀ y ∈ closure (Qn n : Set (SpatialCoordinates d)),
                |RN n N omega lam f x - RN n N omega lam f y| ≤ Kom * dist x y ^ (1 / 4 : ℝ)) ∧
      (∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x ∈ closure (Qn n : Set (SpatialCoordinates d)), |Rn n omega lam f x| ≤ ‖f‖ / lam) ∧
      (∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ ustar : DomainL2 (Qn n), Elim n omega ustar ≠ ⊤ ∧
            (Rn n omega lam f) =ᵐ[volume.restrict (Qn n : Set (SpatialCoordinates d))]
              (ustar : SpatialCoordinates d → ℝ) ∧
            (∀ v : DomainL2 (Qn n), Elim n omega v ≠ ⊤ →
              Func n omega lam f ustar ≤ Func n omega lam f v) ∧
            (∀ v : DomainL2 (Qn n), Elim n omega v ≠ ⊤ →
              (∀ w : DomainL2 (Qn n), Elim n omega w ≠ ⊤ → Func n omega lam f v ≤ Func n omega lam f w) →
              v = ustar)) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [hRnAE n, hHold n] with omega hAE hC
    refine ⟨hAE.1, hAE.2.1, hC, ?_, hAE.2.2⟩
    intro lam hlam f x hx
    have hconv : Filter.Tendsto (fun N => RN n N omega lam f x) Filter.atTop
        (nhds (Rn n omega lam f x)) := by
      rw [Metric.tendsto_atTop]
      intro eps heps
      obtain ⟨N0, hN0⟩ := hAE.2.1 lam hlam f eps heps
      exact ⟨N0, fun N hN => by rw [Real.dist_eq]; exact hN0 N hN x hx⟩
    have hbound : ∀ N, |RN n N omega lam f x| ≤ ‖f‖ / lam := by
      intro N
      have := hKN N
      rw [hRN_formula n N omega lam f x]
      exact aux_cor_as_resolvent_RN_bound (Qn n : Set (SpatialCoordinates d)) lam hlam f
        (KN N (omega, x))
    exact aux_cor_as_resolvent_Rlim_bound lam f (fun N => RN n N omega lam f) (Rn n omega lam f) x
      hbound hconv
  refine ⟨Rn, fun n lam hlam f => hRnMeas n lam hlam f, ?_⟩
  filter_upwards [hall] with omega h
  exact ⟨fun n lam hlam f => (h n).1 lam hlam f, fun n lam hlam f => (h n).2.1 lam hlam f,
    fun n lam0 lam1 h0 h01 => (h n).2.2.1 lam0 lam1 h0 h01,
    fun n lam hlam f => (h n).2.2.2.1 lam hlam f,
    fun n lam hlam f => (h n).2.2.2.2 lam hlam f⟩

end SubdiffusiveProcess.Paper
