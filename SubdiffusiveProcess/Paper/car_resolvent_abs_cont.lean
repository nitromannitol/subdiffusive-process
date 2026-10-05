module

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
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.MultiplicativeChaos.TimeMarginal
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import MarkovProcess.Killed.Minimal
public import MarkovProcess.Killed.Nested
public import MarkovProcess.Path.Exhaustion
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveContraction
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.cutoff_lifetime_package
public import SubdiffusiveProcess.Paper.car_moser_source_local_bound
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.C0CompactSupportExtension
public import Mathlib.Topology.MetricSpace.ThickenedIndicator

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal ZeroAtInfty CompactlySupported

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

/-- The finite-cutoff `(c, ρ)` pair is bounded above and below by positive constants,
*everywhere* (not just a.e.), on the closure of any bounded open set: both are continuous
and positive everywhere, so the extreme value theorem on the compact closure gives the bound. -/
theorem aux_car_resolvent_abs_cont_bounds
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    {U : Set (SpatialCoordinates d)} (hUbdd : Bornology.IsBounded U) (hUne : U.Nonempty) :
    ∃ clo chi rlo rhi : ℝ, 0 < clo ∧ 0 < rlo ∧
      (∀ x ∈ closure U, clo ≤ cutoffCoefficient M H omega N x ∧
        cutoffCoefficient M H omega N x ≤ chi) ∧
      (∀ x ∈ closure U, rlo ≤ cutoffSpeedDensity M H omega N x ∧
        cutoffSpeedDensity M H omega N x ≤ rhi) := by
  have hcC : Continuous (cutoffCoefficient M H omega N) := cutoffCoefficient_continuous M H omega N
  have hcP : ∀ x, 0 < cutoffCoefficient M H omega N x := cutoffCoefficient_pos M H omega N
  obtain ⟨hrC, hrP⟩ := aux_car_moser_source_local_bound_speed_density M H omega N
  have hcompact : IsCompact (closure U) := hUbdd.isCompact_closure
  have hne : (closure U).Nonempty := hUne.closure
  obtain ⟨xc, hxc, hxcmin⟩ := hcompact.exists_isMinOn hne hcC.continuousOn
  obtain ⟨yc, hyc, hycmax⟩ := hcompact.exists_isMaxOn hne hcC.continuousOn
  obtain ⟨xr, hxr, hxrmin⟩ := hcompact.exists_isMinOn hne hrC.continuousOn
  obtain ⟨yr, hyr, hyrmax⟩ := hcompact.exists_isMaxOn hne hrC.continuousOn
  exact ⟨cutoffCoefficient M H omega N xc, cutoffCoefficient M H omega N yc,
    cutoffSpeedDensity M H omega N xr, cutoffSpeedDensity M H omega N yr,
    hcP xc, hrP xr, fun x hx => ⟨hxcmin hx, hycmax hx⟩, fun x hx => ⟨hxrmin hx, hyrmax hx⟩⟩

/-- For a Lebesgue-null Borel set `B`, the `H¹₀` killed resolvent of `B`'s indicator vanishes
`weightedMeasure`-a.e. on any bounded open `U`: testing the weak equation against the solution
itself (`massive_l2_contraction`) forces the energy, hence the solution, to vanish since the
RHS source is a.e. zero, and the null exceptional set transports from Lebesgue to the
(absolutely continuous) weighted measure. -/
theorem aux_car_resolvent_abs_cont_killed_ae_zero
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    {L : Kernel (SpatialCoordinates d) (Path d)}
    (hL : LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) L)
    {U : Set (SpatialCoordinates d)} (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hUne : U.Nonempty) {s : ℝ} (hs : 0 < s) {B : Set (SpatialCoordinates d)}
    (hB : MeasurableSet B) (hBnull : volume B = 0) :
    ∀ᵐ x ∂(weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U,
      killedResolvent L U s (B.indicator (fun _ => (1 : ℝ))) x = 0 := by
  obtain ⟨clo, chi, rlo, rhi, hclo, hrlo, hcbdd, hrbdd⟩ :=
    aux_car_resolvent_abs_cont_bounds M H omega N hUbdd hUne
  have hrhoPos : ∀ x, 0 < cutoffSpeedDensity M H omega N x :=
    (aux_car_moser_source_local_bound_speed_density M H omega N).2
  have hUfin : volume U ≠ ⊤ := hUbdd.measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict U) := ⟨by simpa using hUfin.lt_top⟩
  have hindMemL2 : MemL2On U (fun x => s⁻¹ * B.indicator (fun _ : SpatialCoordinates d => (1 : ℝ)) x) :=
    MemLp.of_bound (((measurable_const.indicator hB).const_mul s⁻¹).aestronglyMeasurable)
      |s⁻¹| (by
      filter_upwards with x
      by_cases hx : x ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx])
  have hweightedFin : (weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    unfold weightedMeasure
    rw [withDensity_apply _ hUopen.measurableSet]
    calc ∫⁻ a in U, ENNReal.ofReal (cutoffSpeedDensity M H omega N a)
        ≤ ∫⁻ _a in U, ENNReal.ofReal rhi := by
          apply setLIntegral_mono measurable_const
          intro x hx
          exact ENNReal.ofReal_le_ofReal (hrbdd x (subset_closure hx)).2
      _ = ENNReal.ofReal rhi * volume U := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUbdd.measure_lt_top
  have hindMemLpW : MemLp (B.indicator (fun _ : SpatialCoordinates d => (1 : ℝ))) 2
      ((weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U) := by
    let : IsFiniteMeasure ((weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U) :=
      ⟨hweightedFin⟩
    exact MemLp.of_bound ((measurable_const.indicator hB).aestronglyMeasurable) 1 (by
      filter_upwards with x
      by_cases hx : x ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx])
  obtain ⟨u, hueq, hu⟩ := hL.2.2 U hUopen hUbdd s hs (B.indicator (fun _ => (1 : ℝ))) hindMemLpW
  have hcU : ∀ x ∈ U, clo ≤ cutoffCoefficient M H omega N x :=
    fun x hx => (hcbdd x (subset_closure hx)).1
  have hrhomeas : AEStronglyMeasurable (cutoffSpeedDensity M H omega N) (volume.restrict U) :=
    (aux_car_moser_source_local_bound_speed_density M H omega N).1.aestronglyMeasurable
  have hrhoU : ∀ x ∈ U, rlo ≤ cutoffSpeedDensity M H omega N x :=
    fun x hx => (hrbdd x (subset_closure hx)).1
  have hrhoAbs : ∀ᵐ x ∂(volume.restrict U), |cutoffSpeedDensity M H omega N x| ≤ rhi := by
    filter_upwards [ae_restrict_mem hUopen.measurableSet] with x hxU
    rw [abs_of_pos (hrhoPos x)]
    exact (hrbdd x (subset_closure hxU)).2
  have hf0 : (fun x : SpatialCoordinates d => cutoffSpeedDensity M H omega N x *
      (B.indicator (fun _ => (1:ℝ)) x) * (B.indicator (fun _ => (1:ℝ)) x)) =ᵐ[volume.restrict U]
      (0 : SpatialCoordinates d → ℝ) := by
    have hglobal : (fun x : SpatialCoordinates d => B.indicator (fun _ => (1:ℝ)) x)
        =ᵐ[volume] (0 : SpatialCoordinates d → ℝ) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hBnull] with x hx
      simp [Set.indicator_of_notMem hx]
    have hzero := ae_restrict_of_ae (μ := volume) (s := U) hglobal
    filter_upwards [hzero] with x hx
    simp [hx]
  have hrhof2 : ∫ x in U, cutoffSpeedDensity M H omega N x *
      (fun x => s⁻¹ * B.indicator (fun _ => (1:ℝ)) x) x *
        (fun x => s⁻¹ * B.indicator (fun _ => (1:ℝ)) x) x ∂volume = 0 := by
    have hf0' : (fun x : SpatialCoordinates d => cutoffSpeedDensity M H omega N x *
        (fun x => s⁻¹ * B.indicator (fun _ => (1:ℝ)) x) x *
          (fun x => s⁻¹ * B.indicator (fun _ => (1:ℝ)) x) x) =ᵐ[volume.restrict U]
        (0 : SpatialCoordinates d → ℝ) := by
      filter_upwards [hf0] with x hx
      simp only [Pi.zero_apply] at hx ⊢
      have hring : cutoffSpeedDensity M H omega N x * (s⁻¹ * B.indicator (fun _ => (1:ℝ)) x) *
          (s⁻¹ * B.indicator (fun _ => (1:ℝ)) x) =
          s⁻¹ * s⁻¹ * (cutoffSpeedDensity M H omega N x * B.indicator (fun _ => (1:ℝ)) x *
            B.indicator (fun _ => (1:ℝ)) x) := by ring
      rw [hring, hx, mul_zero]
    rw [integral_congr_ae hf0']; simp
  have hcontraction := massive_l2_contraction (rho := cutoffSpeedDensity M H omega N)
    hUopen.measurableSet (mu := s⁻¹) (inv_pos.mpr hs) hrlo (lam := clo) hclo hcU
    hrhomeas hrhoU hrhoAbs (u := u) (f := fun x => s⁻¹ * B.indicator (fun _ => (1:ℝ)) x)
    hindMemL2 hu
  rw [hrhof2] at hcontraction
  have hnonneg : (0:ℝ) ≤ ∫ x in U, cutoffSpeedDensity M H omega N x *
      u.toH1Function.toFun x * u.toH1Function.toFun x ∂volume :=
    setIntegral_nonneg hUopen.measurableSet fun x hx => by
      rw [mul_assoc]
      exact mul_nonneg (hrlo.le.trans (hrhoU x hx)) (mul_self_nonneg _)
  have hle0 : ∫ x in U, cutoffSpeedDensity M H omega N x *
      u.toH1Function.toFun x * u.toH1Function.toFun x ∂volume ≤ 0 := by
    have hsq : (0:ℝ) < s⁻¹ ^ 2 := by positivity
    by_contra hcon
    push Not at hcon
    exact absurd hcontraction (not_le.mpr (by nlinarith [mul_pos hsq hcon]))
  have hintzero : ∫ x in U, cutoffSpeedDensity M H omega N x *
      u.toH1Function.toFun x * u.toH1Function.toFun x ∂volume = 0 := le_antisymm hle0 hnonneg
  have hintble : IntegrableOn (fun x => cutoffSpeedDensity M H omega N x *
      u.toH1Function.toFun x * u.toH1Function.toFun x) U volume :=
    integrableOn_mass_term hrhomeas hrhoAbs u.toH1Function.memL2 u.toH1Function.memL2
  have hpointae : (fun x => cutoffSpeedDensity M H omega N x *
      u.toH1Function.toFun x * u.toH1Function.toFun x) =ᵐ[volume.restrict U]
      (0 : SpatialCoordinates d → ℝ) := by
    have hnonnegae : 0 ≤ᵐ[volume.restrict U] (fun x => cutoffSpeedDensity M H omega N x *
        u.toH1Function.toFun x * u.toH1Function.toFun x) := by
      filter_upwards [ae_restrict_mem hUopen.measurableSet] with x hx
      rw [mul_assoc]
      exact mul_nonneg (hrlo.le.trans (hrhoU x hx)) (mul_self_nonneg _)
    exact (integral_eq_zero_iff_of_nonneg_ae hnonnegae hintble).mp hintzero
  have hac : (weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U ≪ volume.restrict U := by
    have hrestrict : (weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U =
        (volume.restrict U).withDensity
          (fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x)) := by
      unfold weightedMeasure
      exact restrict_withDensity hUopen.measurableSet _
    rw [hrestrict]
    exact withDensity_absolutelyContinuous _ _
  have hpointaeW : (fun x => cutoffSpeedDensity M H omega N x *
      u.toH1Function.toFun x * u.toH1Function.toFun x) =ᵐ[
        (weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U]
      (0 : SpatialCoordinates d → ℝ) := hac.ae_eq hpointae
  have huzeroW : u.toH1Function.toFun =ᵐ[(weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U]
      (0 : SpatialCoordinates d → ℝ) := by
    filter_upwards [hpointaeW, ae_restrict_mem hUopen.measurableSet] with x hx hxU
    have hrpos : 0 < cutoffSpeedDensity M H omega N x := hrhoPos x
    rw [mul_assoc] at hx
    have hz : u.toH1Function.toFun x * u.toH1Function.toFun x = 0 := by
      rcases mul_eq_zero.mp hx with h | h
      · exact absurd h hrpos.ne'
      · exact h
    exact mul_self_eq_zero.mp hz
  filter_upwards [hueq, huzeroW] with x hx0 hx1
  rw [← hx0, hx1]
  rfl

/-- Transport a single-time killed-occupation integral from the Lifetime-path pushforward
kernel back to the honest continuous-path kernel `KN`, identifying it with the measure of a
`ContinuousPath.killedEvent`. -/
theorem aux_car_resolvent_abs_cont_killed_eq_killedEvent
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (t : ℝ) (_ht : 0 < t)
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B) (x : SpatialCoordinates d) :
    (∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w},
        (B.indicator (fun _ => (1:ℝ))) (position (Real.toNNReal t) w)
        ∂(aux_cutoff_lifetime_package_kernel KN N omega x)) =
      ((KN N (omega, x)) (ContinuousPath.killedEvent U (Real.toNNReal t) B)).toReal := by
  set S : Set (Path d) := {w | ENNReal.ofReal t < LifetimePath.exitTime U w} with hSdef
  have hSmeas : MeasurableSet S :=
    measurableSet_lt measurable_const (LifetimePath.measurable_exitTime U hU)
  have hBalive : MeasurableSet (Cemetery.alive '' B) := MeasurableSet.inl_image hB
  have hposMeas : Measurable (position (Real.toNNReal t) : Path d → SpatialCoordinates d) :=
    (Measurable.sumElim measurable_id measurable_const).comp
      (LifetimePath.measurable_coordinate (Real.toNNReal t))
  have hpreB : MeasurableSet {w : Path d | position (Real.toNNReal t) w ∈ B} := hposMeas hB
  rw [← MeasureTheory.integral_indicator hSmeas]
  have hstep : S.indicator (fun w => (B.indicator (fun _ => (1:ℝ))) (position (Real.toNNReal t) w)) =
      ({w : Path d | position (Real.toNNReal t) w ∈ B} ∩ S).indicator (fun _ => (1:ℝ)) := by
    funext w
    by_cases hwS : w ∈ S <;> by_cases hwB : position (Real.toNNReal t) w ∈ B <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hwS, hwB, Set.mem_inter_iff]
  rw [show (∫ w, S.indicator (fun w => (B.indicator (fun _ => (1:ℝ)))
        (position (Real.toNNReal t) w)) w ∂(aux_cutoff_lifetime_package_kernel KN N omega x)) =
      ∫ w, ({w : Path d | position (Real.toNNReal t) w ∈ B} ∩ S).indicator (fun _ => (1:ℝ)) w
        ∂(aux_cutoff_lifetime_package_kernel KN N omega x) from by rw [hstep]]
  have hfin := integral_indicator_one
    (μ := aux_cutoff_lifetime_package_kernel KN N omega x) (hpreB.inter hSmeas)
  rw [measureReal_def] at hfin
  rw [show (fun _ : Path d => (1:ℝ)) = (1 : Path d → ℝ) from rfl]
  rw [hfin]
  have hmap : aux_cutoff_lifetime_package_kernel KN N omega x =
      Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) :=
    (aux_cutoff_lifetime_package_spec KN N omega x).symm
  rw [hmap, Measure.map_apply LifetimePath.measurable_ofContinuousPath (hpreB.inter hSmeas)]
  congr 2
  ext path
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, hSdef,
    ContinuousPath.mem_killedEvent_iff, LifetimePath.exitTime_ofContinuousPath]
  have hposeq : position (Real.toNNReal t) (LifetimePath.ofContinuousPath path) =
      path (Real.toNNReal t) := by
    simp only [position, LifetimePath.coordinate_ofContinuousPath]
    rfl
  rw [hposeq]
  tauto

/-- One exhaustion level: the `t`-integrated killed occupation of a Lebesgue-null Borel set
vanishes `weightedMeasure`-a.e., expressed natively via the honest continuous-path kernel `KN`. -/
theorem aux_car_resolvent_abs_cont_level_ae_zero
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hL : LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
      (aux_cutoff_lifetime_package_kernel KN N omega))
    {U : Set (SpatialCoordinates d)} (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hUne : U.Nonempty) {mu : ℝ} (hmu : 0 < mu) {B : Set (SpatialCoordinates d)}
    (hB : MeasurableSet B) (hBnull : volume B = 0) :
    ∀ᵐ x ∂(weightedMeasure (cutoffSpeedDensity M H omega N)).restrict U,
      ∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
        ((KN N (omega, x)) (ContinuousPath.killedEvent U (Real.toNNReal t) B)).toReal = 0 := by
  have hs : 0 < mu⁻¹ := inv_pos.mpr hmu
  have hkilled := aux_car_resolvent_abs_cont_killed_ae_zero M H omega N hL hUopen hUbdd hUne hs hB hBnull
  filter_upwards [hkilled] with x hx
  have heq : killedResolvent (aux_cutoff_lifetime_package_kernel KN N omega) U mu⁻¹
      (B.indicator (fun _ => (1:ℝ))) x =
      mu * ∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
        ((KN N (omega, x)) (ContinuousPath.killedEvent U (Real.toNNReal t) B)).toReal := by
    unfold killedResolvent
    rw [inv_inv]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [show (-t / mu⁻¹) = -mu*t by field_simp]
    congr 1
    exact aux_car_resolvent_abs_cont_killed_eq_killedEvent KN N omega U hUopen t ht B hB x
  rw [heq] at hx
  exact (mul_eq_zero.mp hx).resolve_left hmu.ne'

/-- The full exhaustion: for a.e. `x` (globally, `weightedMeasure`-a.e.), the whole-space
`t`-integrated occupation of a Lebesgue-null Borel set vanishes, expressed natively via `KN`. -/
theorem aux_car_resolvent_abs_cont_global_ae_zero
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : IsMarkovKernel (KN N))
    (hL : LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
      (aux_cutoff_lifetime_package_kernel KN N omega))
    {mu : ℝ} (hmu : 0 < mu) {B : Set (SpatialCoordinates d)}
    (hB : MeasurableSet B) (hBnull : volume B = 0) :
    ∀ᵐ x ∂(weightedMeasure (cutoffSpeedDensity M H omega N)),
      ∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
        ((KN N (omega, x)) {path : DiffusionPath d | path (Real.toNNReal t) ∈ B}).toReal = 0 := by
  set Uexh : ℕ → Set (SpatialCoordinates d) := fun n => Metric.ball 0 ((n:ℝ)+1) with hUexhdef
  have hUopen : ∀ n, IsOpen (Uexh n) := fun _ => Metric.isOpen_ball
  have hUbdd : ∀ n, Bornology.IsBounded (Uexh n) := fun _ => Metric.isBounded_ball
  have hUne : ∀ n, (Uexh n).Nonempty := fun n =>
    ⟨0, by simp only [Uexh, Metric.mem_ball, dist_self]; positivity⟩
  have hUmono : Monotone Uexh := by
    intro m n hmn
    apply Metric.ball_subset_ball
    have : (m:ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hUcover : ⋃ n, Uexh n = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨n, hn⟩ := exists_nat_gt (dist y 0)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    simp only [Uexh, Metric.mem_ball]
    linarith
  set Bad : ℕ → Set (SpatialCoordinates d) := fun n =>
    {x | ¬ (∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
        ((KN N (omega, x)) (ContinuousPath.killedEvent (Uexh n) (Real.toNNReal t) B)).toReal = 0)}
    with hBaddef
  have hnullset : ∀ n, (weightedMeasure (cutoffSpeedDensity M H omega N)) (Bad n ∩ Uexh n) = 0 := by
    intro n
    have hlvl := aux_car_resolvent_abs_cont_level_ae_zero M H omega N KN hL
      (hUopen n) (hUbdd n) (hUne n) hmu hB hBnull (U := Uexh n)
    rwa [ae_iff, Measure.restrict_apply' (hUopen n).measurableSet] at hlvl
  have hglobalnull : (weightedMeasure (cutoffSpeedDensity M H omega N))
      (⋃ n, Bad n ∩ Uexh n) = 0 := measure_iUnion_null hnullset
  have hgoodx : ∀ᵐ x ∂(weightedMeasure (cutoffSpeedDensity M H omega N)),
      x ∉ ⋃ n, Bad n ∩ Uexh n := measure_eq_zero_iff_ae_notMem.mp hglobalnull
  filter_upwards [hgoodx] with x hxgood
  have hallgood : ∀ n, x ∈ Uexh n →
      ∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
        ((KN N (omega, x)) (ContinuousPath.killedEvent (Uexh n) (Real.toNNReal t) B)).toReal = 0 := by
    intro n hxn
    by_contra hbad
    exact hxgood (Set.mem_iUnion.mpr ⟨n, hbad, hxn⟩)
  obtain ⟨n0, hn0⟩ := Set.mem_iUnion.mp (hUcover ▸ Set.mem_univ x)
  have htail : ∀ n ≥ n0, ∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
      ((KN N (omega, x)) (ContinuousPath.killedEvent (Uexh n) (Real.toNNReal t) B)).toReal = 0 :=
    fun n hn => hallgood n (hUmono hn hn0)
  have hdom : Integrable (fun t : ℝ => Real.exp (-mu*t)) (volume.restrict (Set.Ioi (0:ℝ))) := by
    simpa only [neg_mul] using! exp_neg_integrableOn_Ioi 0 hmu
  have hev : Measurable (fun z : ℝ × DiffusionPath d => z.2 (Real.toNNReal z.1)) :=
    (continuous_eval.comp (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable
  have : IsProbabilityMeasure (KN N (omega, x)) := hKN.isProbabilityMeasure (omega, x)
  have hjointmeas : ∀ n, Measurable
      (fun z : ℝ × DiffusionPath d =>
        (ContinuousPath.killedEvent (Uexh n) (Real.toNNReal z.1) B).indicator (1 : DiffusionPath d → ℝ≥0∞) z.2) := by
    intro n
    have hexit : Measurable (fun z : ℝ × DiffusionPath d => ContinuousPath.exitTime (Uexh n) z.2) :=
      (ContinuousPath.measurable_exitTime (Uexh n) (hUopen n)).comp measurable_snd
    have htlt : MeasurableSet {z : ℝ × DiffusionPath d |
        (Real.toNNReal z.1 : ℝ≥0∞) < ContinuousPath.exitTime (Uexh n) z.2} :=
      measurableSet_lt (measurable_coe_nnreal_ennreal.comp
        (measurable_real_toNNReal.comp measurable_fst)) hexit
    have hmemB : MeasurableSet {z : ℝ × DiffusionPath d | z.2 (Real.toNNReal z.1) ∈ B} := hev hB
    have hset : MeasurableSet {z : ℝ × DiffusionPath d |
        (Real.toNNReal z.1 : ℝ≥0∞) < ContinuousPath.exitTime (Uexh n) z.2 ∧ z.2 (Real.toNNReal z.1) ∈ B} :=
      htlt.inter hmemB
    have heqfun : (fun z : ℝ × DiffusionPath d =>
        (ContinuousPath.killedEvent (Uexh n) (Real.toNNReal z.1) B).indicator
          (1 : DiffusionPath d → ℝ≥0∞) z.2) =
        Set.indicator {z : ℝ × DiffusionPath d |
          (Real.toNNReal z.1 : ℝ≥0∞) < ContinuousPath.exitTime (Uexh n) z.2 ∧
            z.2 (Real.toNNReal z.1) ∈ B} (fun _ => (1:ℝ≥0∞)) := by
      funext z
      by_cases hz : z.2 ∈ ContinuousPath.killedEvent (Uexh n) (Real.toNNReal z.1) B
      · have hz' : z ∈ {z : ℝ × DiffusionPath d |
            (Real.toNNReal z.1 : ℝ≥0∞) < ContinuousPath.exitTime (Uexh n) z.2 ∧
              z.2 (Real.toNNReal z.1) ∈ B} := (ContinuousPath.mem_killedEvent_iff _ _ _ _).mp hz
        simp [Set.indicator_of_mem hz, Set.indicator_of_mem hz']
      · have hz' : z ∉ {z : ℝ × DiffusionPath d |
            (Real.toNNReal z.1 : ℝ≥0∞) < ContinuousPath.exitTime (Uexh n) z.2 ∧
              z.2 (Real.toNNReal z.1) ∈ B} :=
          fun hcontra => hz ((ContinuousPath.mem_killedEvent_iff _ _ _ _).mpr hcontra)
        simp [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']
    rw [heqfun]
    exact measurable_const.indicator hset
  have hmeasn : ∀ n, Measurable (fun t : ℝ =>
      ((KN N (omega, x)) (ContinuousPath.killedEvent (Uexh n) (Real.toNNReal t) B))) := by
    intro n
    have hli := (hjointmeas n).lintegral_prod_right' (ν := KN N (omega, x))
    have heq2 : (fun t : ℝ => ∫⁻ path,
        (ContinuousPath.killedEvent (Uexh n) (Real.toNNReal t) B).indicator
          (1 : DiffusionPath d → ℝ≥0∞) path ∂(KN N (omega, x))) =
        (fun t : ℝ => ((KN N (omega, x)) (ContinuousPath.killedEvent (Uexh n) (Real.toNNReal t) B))) := by
      funext t
      exact lintegral_indicator_one
        (ContinuousPath.measurableSet_killedEvent (Uexh n) (hUopen n) (Real.toNNReal t) hB)
    rwa [heq2] at hli
  have htendsto : Tendsto (fun n => ∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
        ((KN N (omega, x)) (ContinuousPath.killedEvent (Uexh n) (Real.toNNReal t) B)).toReal)
      atTop (𝓝 (∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
        ((KN N (omega, x)) {path : DiffusionPath d | path (Real.toNNReal t) ∈ B}).toReal)) := by
    apply tendsto_integral_of_dominated_convergence (fun t => Real.exp (-mu*t))
    · intro n
      exact (Real.continuous_exp.measurable.comp
        (measurable_const.mul measurable_id)).aestronglyMeasurable.mul
        ((hmeasn n).ennreal_toReal).aestronglyMeasurable
    · exact hdom
    · intro n
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)]
      have hle1 : ((KN N (omega, x)) (ContinuousPath.killedEvent (Uexh n) (Real.toNNReal t) B)) ≤ 1 := by
        have hsub := measure_mono (μ := KN N (omega, x)) (Set.subset_univ
          (ContinuousPath.killedEvent (Uexh n) (Real.toNNReal t) B))
        rwa [measure_univ] at hsub
      have hb := ENNReal.toReal_mono (by norm_num) hle1
      simp only [ENNReal.toReal_one] at hb
      nlinarith [hb, Real.exp_pos (-mu*t)]
    · filter_upwards with t
      have hmonoSet : Monotone (fun n => ContinuousPath.killedEvent (Uexh n) (Real.toNNReal t) B) :=
        fun m n hmn => ContinuousPath.killedEvent_mono (hUmono hmn) _ _
      have hexh : ContinuousPath.IsOpenExhaustion Uexh := ⟨hUopen, hUmono, hUcover⟩
      have htm := tendsto_measure_iUnion_atTop (μ := (KN N (omega, x))) hmonoSet
      rw [hexh.iUnion_killedEvent] at htm
      have hne : ((KN N (omega, x)) {path : DiffusionPath d | path (Real.toNNReal t) ∈ B}) ≠ ⊤ :=
        measure_ne_top _ _
      exact Tendsto.const_mul _ ((ENNReal.tendsto_toReal hne).comp htm)
  have hconst : Tendsto (fun n => ∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
        ((KN N (omega, x)) (ContinuousPath.killedEvent (Uexh n) (Real.toNNReal t) B)).toReal)
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n0] with n hn
    exact (htail n hn).symm
  exact tendsto_nhds_unique htendsto hconst

theorem aux_car_resolvent_abs_cont_map_eval
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (omega : BilateralField d)
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (t : ℝ≥0) (x : SpatialCoordinates d) :
    (K (omega, x)).map (fun path : DiffusionPath d => path t) = P.kernel t x := by
  have hev : Measurable
      (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) ({t} : Finset ℝ≥0)) :=
    Measurable.of_eval fun s => (continuous_eval_const ((s : ℝ≥0))).measurable
  have hfdd0 :
      (K (omega, x)).map (ContinuousPath.finsetEvaluation ({t} : Finset ℝ≥0)) =
        SubMarkovKernelSemigroup.finiteSetKernel P ({t} : Finset ℝ≥0) x := by
    rw [← Kernel.map_apply K hev (omega, x)]
    exact hfdd ({t} : Finset ℝ≥0) x
  exact map_eval_eq_of_finsetEvaluation P (K (omega, x)) x t hfdd0



theorem aux_car_resolvent_abs_cont_occupation_eq_kernelIntegral
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d) (hKNmk : IsMarkovKernel (KN N))
    (hfd : ∀ I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x)
    (mu : ℝ) (hmu : 0 < mu) (f : C₀(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d) :
    (∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-mu * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x))) =
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t) *
        kernelIntegral (PN N omega (Real.toNNReal t)) f x := by
  let : IsMarkovKernel (KN N) := hKNmk
  have hev : Measurable (fun z : ℝ × DiffusionPath d => z.2 (Real.toNNReal z.1)) :=
    (continuous_eval.comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable
  have hf : Measurable f := f.continuous.measurable
  have hF : Measurable (fun z : ℝ × DiffusionPath d =>
      Real.exp (-mu * z.1) * f (z.2 (Real.toNNReal z.1))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul (hf.comp hev)
  have hbase : Integrable (fun z : ℝ × DiffusionPath d => Real.exp (-mu * z.1))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (KN N (omega, x))) := by
    simpa only [one_mul] using
      (((exp_neg_integrableOn_Ioi 0 hmu).const_mul (1 : ℝ)).comp_fst (KN N (omega, x)))
  have hbound : ∀ z : ℝ × DiffusionPath d,
      ‖Real.exp (-mu * z.1) * f (z.2 (Real.toNNReal z.1))‖ ≤ ‖f‖ * Real.exp (-mu * z.1) := by
    intro z
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (f.toBCF.norm_coe_le_norm _) (Real.exp_pos _).le
  have hswap : Integrable (fun z : ℝ × DiffusionPath d =>
      Real.exp (-mu * z.1) * f (z.2 (Real.toNNReal z.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (KN N (omega, x))) :=
    (hbase.const_mul ‖f‖).mono' hF.aestronglyMeasurable (Eventually.of_forall hbound)
  calc
    (∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-mu * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x))) =
        ∫ t in Set.Ioi (0 : ℝ), ∫ path, Real.exp (-mu * t) * f (path (Real.toNNReal t))
          ∂(KN N (omega, x)) := (integral_integral_swap hswap).symm
    _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t) *
        kernelIntegral (PN N omega (Real.toNNReal t)) f x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [integral_const_mul]
      have hmap := aux_car_resolvent_abs_cont_map_eval
        (PN N omega) (KN N) omega hfd (Real.toNNReal t) x
      have hev_path : Measurable (fun path : DiffusionPath d => path (Real.toNNReal t)) :=
        (continuous_eval_const (Real.toNNReal t)).measurable
      have hi := integral_map (μ := KN N (omega, x))
        (φ := fun path : DiffusionPath d => path (Real.toNNReal t)) (f := f)
        hev_path.aemeasurable hf.aestronglyMeasurable
      rw [hmap] at hi
      rw [kernelIntegral]
      rw [← hi]


/-- The `1/(j+1)`-thickened indicator of a compact `K`, as a real-valued continuous
compactly-supported function: `0 ≤ fj ≤ 1`, equal to `1` on `K`, and `→ K.indicator 1`
pointwise everywhere as `j → ∞`. -/
noncomputable def aux_car_resolvent_abs_cont_fj {d : ℕ} (K : Set (SpatialCoordinates d)) (j : ℕ) :
    SpatialCoordinates d → ℝ :=
  fun y => (thickenedIndicator (δ := (1:ℝ)/(j+1)) (by positivity) K y : ℝ)

theorem aux_car_resolvent_abs_cont_fj_bounds {d : ℕ} (K : Set (SpatialCoordinates d)) (j : ℕ)
    (y : SpatialCoordinates d) :
    0 ≤ aux_car_resolvent_abs_cont_fj K j y ∧ aux_car_resolvent_abs_cont_fj K j y ≤ 1 := by
  unfold aux_car_resolvent_abs_cont_fj
  refine ⟨NNReal.coe_nonneg _, ?_⟩
  have := thickenedIndicator_le_one (δ := (1:ℝ)/(j+1)) (by positivity) K y
  exact_mod_cast this

theorem aux_car_resolvent_abs_cont_fj_continuous {d : ℕ} (K : Set (SpatialCoordinates d))
    (j : ℕ) : Continuous (aux_car_resolvent_abs_cont_fj K j) :=
  continuous_induced_dom.comp
    (thickenedIndicator (δ := (1:ℝ)/(j+1)) (by positivity) K).continuous

theorem aux_car_resolvent_abs_cont_fj_eq_toNNReal {d : ℕ} (K : Set (SpatialCoordinates d))
    (j : ℕ) (y : SpatialCoordinates d) :
    aux_car_resolvent_abs_cont_fj K j y =
      ((thickenedIndicatorAux ((1:ℝ)/(j+1)) K y).toNNReal : ℝ) := by
  unfold aux_car_resolvent_abs_cont_fj
  rw [show (thickenedIndicator (δ := (1:ℝ)/(j+1)) (by positivity) K y) =
      (ENNReal.toNNReal ∘ thickenedIndicatorAux ((1:ℝ)/(j+1)) K) y from
      congrFun (thickenedIndicator.coeFn_eq_comp (by positivity) K) y]
  rfl

theorem aux_car_resolvent_abs_cont_fj_tendsto {d : ℕ} (K : Set (SpatialCoordinates d))
    (hK : IsClosed K) (y : SpatialCoordinates d) :
    Tendsto (fun j => aux_car_resolvent_abs_cont_fj K j y) atTop
      (𝓝 (K.indicator (fun _ => (1:ℝ)) y)) := by
  have hδpos : ∀ j : ℕ, (0:ℝ) < 1/(j+1) := fun j => by positivity
  have hδ : Tendsto (fun j : ℕ => (1:ℝ)/(j+1)) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have htendfun := thickenedIndicator_tendsto_indicator_closure hδpos hδ K
  rw [hK.closure_eq] at htendfun
  have htend := (tendsto_pi_nhds.mp htendfun) y
  have htendR := (continuous_induced_dom.tendsto
      (K.indicator (fun _ => (1:ℝ≥0)) y)).comp htend
  have hindeq : ((K.indicator (fun _ => (1:ℝ≥0)) y : ℝ≥0) : ℝ) = K.indicator (fun _ => (1:ℝ)) y := by
    by_cases hy : y ∈ K <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  simpa [Function.comp, aux_car_resolvent_abs_cont_fj, hindeq] using! htendR

theorem aux_car_resolvent_abs_cont_fj_zero_of_empty {d : ℕ} (j : ℕ) :
    aux_car_resolvent_abs_cont_fj (∅ : Set (SpatialCoordinates d)) j = 0 := by
  funext y
  rw [aux_car_resolvent_abs_cont_fj_eq_toNNReal]
  have hzero : thickenedIndicatorAux ((1:ℝ)/(j+1)) (∅ : Set (SpatialCoordinates d)) y = 0 := by
    unfold thickenedIndicatorAux
    rw [Metric.infEDist_empty, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    exact tsub_eq_zero_of_le le_top
  simp only [one_div] at hzero
  simp only [one_div]
  rw [hzero]
  simp

theorem aux_car_resolvent_abs_cont_fj_hasCompactSupport {d : ℕ}
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (j : ℕ) :
    HasCompactSupport (aux_car_resolvent_abs_cont_fj K j) := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe, aux_car_resolvent_abs_cont_fj_zero_of_empty]
    exact HasCompactSupport.zero
  · obtain ⟨p, hp⟩ := hKne
    obtain ⟨R, hR⟩ := hK.isBounded.subset_ball p
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall p (R+1))
    intro y hy
    simp only [Function.mem_support] at hy
    by_contra hyc
    apply hy
    have hdist : R + 1 < dist y p := by
      simpa only [Metric.mem_closedBall, not_le] using hyc
    obtain ⟨z0, hz0, hz0eq⟩ := hK.exists_infDist_eq_dist ⟨p, hp⟩ y
    have hz0p : dist z0 p ≤ R := le_of_lt (hR hz0)
    have htri : dist y p ≤ dist y z0 + dist z0 p := dist_triangle y z0 p
    have hinfdist : (1:ℝ) < Metric.infDist y K := by
      rw [hz0eq]
      linarith
    have hjbound : (1:ℝ)/(j+1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have hnotthick : y ∉ Metric.thickening ((1:ℝ)/(j+1)) K := by
      rw [Metric.mem_thickening_iff_infDist_lt ⟨p, hp⟩]
      push Not
      linarith
    have hzero := thickenedIndicatorAux_zero (δ := (1:ℝ)/(j+1)) (by positivity) K hnotthick
    rw [aux_car_resolvent_abs_cont_fj_eq_toNNReal]
    simp only [one_div] at hzero ⊢
    rw [hzero]
    simp

/-- `fj` bundled as a `C₀` function, for feeding into `D.solution`. -/
noncomputable def aux_car_resolvent_abs_cont_Fj {d : ℕ} (K : Set (SpatialCoordinates d))
    (hK : IsCompact K) (j : ℕ) : C₀(SpatialCoordinates d, ℝ) :=
  compactSupportToC0 ⟨⟨aux_car_resolvent_abs_cont_fj K j,
    aux_car_resolvent_abs_cont_fj_continuous K j⟩,
    aux_car_resolvent_abs_cont_fj_hasCompactSupport K hK j⟩

theorem aux_car_resolvent_abs_cont_Fj_apply {d : ℕ} (K : Set (SpatialCoordinates d))
    (hK : IsCompact K) (j : ℕ) (y : SpatialCoordinates d) :
    aux_car_resolvent_abs_cont_Fj K hK j y = aux_car_resolvent_abs_cont_fj K j y := by
  unfold aux_car_resolvent_abs_cont_Fj
  rw [compactSupportToC0_apply]
  rfl

/-- Inner (`t`-)convergence: for every path, the resolvent-integral applied to `Fj` converges to
the resolvent-integral applied to `K`'s indicator, dominated uniformly by `mu⁻¹`. -/
theorem aux_car_resolvent_abs_cont_inner_tendsto
    {d : ℕ} (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (mu : ℝ) (hmu : 0 < mu)
    (path : DiffusionPath d) :
    Tendsto (fun j => ∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
        aux_car_resolvent_abs_cont_fj K j (path (Real.toNNReal t)))
      atTop (𝓝 (∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
        (K.indicator (fun _ => (1:ℝ)) (path (Real.toNNReal t))))) := by
  apply tendsto_integral_of_dominated_convergence (fun t => Real.exp (-mu*t))
  · intro j
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((aux_car_resolvent_abs_cont_fj_continuous K j).comp
        (path.continuous.comp continuous_real_toNNReal))).aestronglyMeasurable
  · simpa only [neg_mul] using! exp_neg_integrableOn_Ioi 0 hmu
  · intro j
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (aux_car_resolvent_abs_cont_fj_bounds K j _).1)]
    have := (aux_car_resolvent_abs_cont_fj_bounds K j (path (Real.toNNReal t))).2
    nlinarith [Real.exp_pos (-mu*t)]
  · filter_upwards with t
    exact aux_car_resolvent_abs_cont_fj_tendsto K hK.isClosed (path (Real.toNNReal t)) |>.const_mul _

theorem aux_car_resolvent_abs_cont_inner_bound
    {d : ℕ} (K : Set (SpatialCoordinates d)) (mu : ℝ) (hmu : 0 < mu) (j : ℕ)
    (path : DiffusionPath d) :
    ‖∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
      aux_car_resolvent_abs_cont_fj K j (path (Real.toNNReal t))‖ ≤
      ∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) := by
  have hdom : Integrable (fun t : ℝ => Real.exp (-mu*t)) (volume.restrict (Set.Ioi (0:ℝ))) := by
    simpa only [neg_mul] using! exp_neg_integrableOn_Ioi 0 hmu
  have hintble : Integrable (fun t : ℝ => Real.exp (-mu*t) *
      aux_car_resolvent_abs_cont_fj K j (path (Real.toNNReal t)))
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply hdom.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((aux_car_resolvent_abs_cont_fj_continuous K j).comp
        (path.continuous.comp continuous_real_toNNReal))).aestronglyMeasurable
    filter_upwards with t
    simp only [Pi.mul_apply, Function.comp_apply, id, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (aux_car_resolvent_abs_cont_fj_bounds K j _).1)]
    nlinarith [(aux_car_resolvent_abs_cont_fj_bounds K j (path (Real.toNNReal t))).2, Real.exp_pos (-mu*t)]
  have hle : ∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
      aux_car_resolvent_abs_cont_fj K j (path (Real.toNNReal t)) ≤
      ∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) := by
    apply integral_mono_of_nonneg _ hdom
    · filter_upwards with t
      nlinarith [(aux_car_resolvent_abs_cont_fj_bounds K j (path (Real.toNNReal t))).2, Real.exp_pos (-mu*t)]
    · filter_upwards with t
      exact mul_nonneg (Real.exp_pos _).le (aux_car_resolvent_abs_cont_fj_bounds K j _).1
  have hnonneg : (0:ℝ) ≤ ∫ t in Set.Ioi (0:ℝ), Real.exp (-mu*t) *
      aux_car_resolvent_abs_cont_fj K j (path (Real.toNNReal t)) :=
    integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (aux_car_resolvent_abs_cont_fj_bounds K j _).1)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hle

/-- If a continuous function's `L∞` norm on a compact `K'` (w.r.t. a weighted measure) is bounded
by `A`, and a nonempty open `V ⊆ K'` sits where the weight is bounded below by `rlo > 0`, then the
value at any point of `V` is pointwise bounded by `A`: the exceedance set is open (continuity) and
`weightedMeasure`-null (from the `L∞` bound), hence empty since it has positive Lebesgue mass in
`V` unless it is empty. -/
theorem aux_car_resolvent_abs_cont_pointwise_of_eLpNorm_top
    {d : ℕ} {rlo : ℝ} (hrlo : 0 < rlo) (rho : SpatialCoordinates d → ℝ)
    {V K' : Set (SpatialCoordinates d)} (hVopen : IsOpen V) (hVsub : V ⊆ K')
    (hK'meas : MeasurableSet K') (hrhoV : ∀ x ∈ V, rlo ≤ rho x)
    {u : SpatialCoordinates d → ℝ} (hu : Continuous u)
    {x0 : SpatialCoordinates d} (hx0 : x0 ∈ V) {A : ℝ≥0∞}
    (hbound : eLpNorm u ⊤ ((weightedMeasure rho).restrict K') ≤ A) :
    (‖u x0‖ₑ) ≤ A := by
  by_contra hcon
  push Not at hcon
  set T : Set (SpatialCoordinates d) := V ∩ {y | A < ‖u y‖ₑ} with hTdef
  have hTopen : IsOpen T := hVopen.inter (isOpen_lt continuous_const (continuous_enorm.comp hu))
  have hTne : T.Nonempty := ⟨x0, hx0, hcon⟩
  have hTsubK : T ⊆ K' := fun y hy => hVsub hy.1
  have hae : ∀ᵐ y ∂((weightedMeasure rho).restrict K'), ‖u y‖ₑ ≤ A := by
    have h1 : eLpNormEssSup u ((weightedMeasure rho).restrict K') ≤ A := by
      rwa [← eLpNorm_exponent_top hu.aestronglyMeasurable]
    filter_upwards [ae_le_essSup (μ := (weightedMeasure rho).restrict K')
      (f := fun y => ‖u y‖ₑ)] with y hy using hy.trans h1
  have hnull : (weightedMeasure rho).restrict K' T = 0 := by
    have hTsub' : T ⊆ {y | ¬ ‖u y‖ₑ ≤ A} := fun y hy => not_le.mpr hy.2
    exact measure_mono_null hTsub' (ae_iff.mp hae)
  have hTrestr : (weightedMeasure rho).restrict K' T = weightedMeasure rho T := by
    rw [Measure.restrict_apply' hK'meas, Set.inter_eq_self_of_subset_left hTsubK]
  rw [hTrestr] at hnull
  have hvolpos : 0 < volume T := hTopen.measure_pos volume hTne
  have hbelow : ∀ y ∈ T, ENNReal.ofReal rlo ≤ ENNReal.ofReal (rho y) :=
    fun y hy => ENNReal.ofReal_le_ofReal (hrhoV y hy.1)
  have hWTpos : 0 < weightedMeasure rho T := by
    have hTmeas : MeasurableSet T := hTopen.measurableSet
    have : ENNReal.ofReal rlo * volume T ≤ weightedMeasure rho T := by
      unfold weightedMeasure
      rw [withDensity_apply _ hTmeas]
      calc ENNReal.ofReal rlo * volume T = ∫⁻ _y in T, ENNReal.ofReal rlo := by
            rw [setLIntegral_const]
        _ ≤ ∫⁻ y in T, ENNReal.ofReal (rho y) := setLIntegral_mono' hTmeas hbelow
    exact lt_of_lt_of_le (by positivity) this
  exact hWTpos.ne' hnull

/-- Bounded dominated convergence in `Lᵖ` (finite measure, uniform bound, a.e. pointwise limit
`0`): the `p`-th power lintegral tends to `0` by dominated convergence, and `eLpNorm` is that
lintegral's `p`-th root, whose continuity at `0` (for `1/p > 0`) finishes it. -/
theorem aux_car_resolvent_abs_cont_tendsto_eLpNorm_zero
    {d : ℕ} {mu_meas : Measure (SpatialCoordinates d)} [IsFiniteMeasure mu_meas]
    {p : ℝ} (hp : 0 < p) {f : ℕ → SpatialCoordinates d → ℝ}
    (hfmeas : ∀ n, Measurable (f n)) {C : ℝ} (hC0 : 0 ≤ C)
    (hbound : ∀ n, ∀ᵐ x ∂mu_meas, |f n x| ≤ C)
    (htendsto : ∀ᵐ x ∂mu_meas, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) (ENNReal.ofReal p) mu_meas) atTop (𝓝 0) := by
  have hpne0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpnetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoreal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hfin : ∫⁻ _x : SpatialCoordinates d, ENNReal.ofReal (C ^ p) ∂mu_meas ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have key : Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ^ p ∂mu_meas) atTop (𝓝 0) := by
    have hdom : Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ^ p ∂mu_meas) atTop
        (𝓝 (∫⁻ _x : SpatialCoordinates d, (0 : ℝ≥0∞) ∂mu_meas)) := by
      apply tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal (C ^ p))
        (fun n => ((hfmeas n).enorm).pow_const p)
      · intro n
        filter_upwards [hbound n] with x hx
        have h1 : ‖f n x‖ₑ ≤ ENNReal.ofReal C := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal hx
        calc ‖f n x‖ₑ ^ p ≤ (ENNReal.ofReal C) ^ p :=
              ENNReal.rpow_le_rpow h1 hp.le
          _ = ENNReal.ofReal (C ^ p) := ENNReal.ofReal_rpow_of_nonneg hC0 hp.le
      · exact hfin
      · filter_upwards [htendsto] with x hx
        have hnorm0 : Tendsto (fun n => ‖f n x‖ₑ) atTop (𝓝 (0:ℝ≥0∞)) := by
          have habs : Tendsto (fun n => |f n x|) atTop (𝓝 (0:ℝ)) := by
            simpa using hx.abs
          have h3 := (ENNReal.continuous_ofReal.tendsto (0:ℝ)).comp habs
          simp only [ENNReal.ofReal_zero] at h3
          simpa [Real.enorm_eq_ofReal_abs, Function.comp] using! h3
        have h4 := (ENNReal.continuous_rpow_const (y := p)).tendsto (0:ℝ≥0∞) |>.comp hnorm0
        rw [ENNReal.zero_rpow_of_pos hp] at h4
        exact h4
    simpa using hdom
  have heq : (fun n => eLpNorm (f n) (ENNReal.ofReal p) mu_meas) =
      fun n => (∫⁻ x, ‖f n x‖ₑ ^ (ENNReal.ofReal p).toReal ∂mu_meas) ^ (1 / (ENNReal.ofReal p).toReal) :=
    funext fun n => eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 hpnetop ((hfmeas n).aestronglyMeasurable)
  rw [heq]
  simp only [htoreal]
  have hcomp := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto (0 : ℝ≥0∞) |>.comp key
  rw [ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1 / p)] at hcomp
  exact hcomp

/-- Fubini swap connecting the two forms of the resolvent occupation quantity: the path-integral
form (matching the target theorem's statement) and the time-integral-of-kernel-measure form
(matching `aux_car_resolvent_abs_cont_global_ae_zero`'s conclusion). Valid for any measurable `B`
(not necessarily bounded), since the integrand is dominated by the integrable `exp(-mu*t)`. -/
theorem aux_car_resolvent_abs_cont_fubini_swap
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d) (hKNmk : IsMarkovKernel (KN N))
    (mu : ℝ) (hmu : 0 < mu) (x : SpatialCoordinates d)
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B) :
    (∫ path, (∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t) *
        B.indicator (fun _ => (1 : ℝ)) (path (Real.toNNReal t))) ∂(KN N (omega, x))) =
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t) *
        ((KN N (omega, x)) {path | path (Real.toNNReal t) ∈ B}).toReal := by
  let : IsMarkovKernel (KN N) := hKNmk
  have hev : Measurable (fun z : ℝ × DiffusionPath d => z.2 (Real.toNNReal z.1)) :=
    (continuous_eval.comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable
  have hind : Measurable (fun z : ℝ × DiffusionPath d =>
      B.indicator (fun _ => (1:ℝ)) (z.2 (Real.toNNReal z.1))) :=
    (measurable_const.indicator hB).comp hev
  have hbase : Integrable (fun z : ℝ × DiffusionPath d => Real.exp (-mu * z.1))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (KN N (omega, x))) := by
    simpa only [one_mul] using
      (((exp_neg_integrableOn_Ioi 0 hmu).const_mul (1 : ℝ)).comp_fst (KN N (omega, x)))
  have hF : Measurable (fun z : ℝ × DiffusionPath d =>
      Real.exp (-mu * z.1) * B.indicator (fun _ => (1:ℝ)) (z.2 (Real.toNNReal z.1))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul hind
  have hbound : ∀ z : ℝ × DiffusionPath d,
      ‖Real.exp (-mu * z.1) * B.indicator (fun _ => (1:ℝ)) (z.2 (Real.toNNReal z.1))‖ ≤
        Real.exp (-mu * z.1) := by
    intro z
    have hind1 : |B.indicator (fun _ => (1:ℝ)) (z.2 (Real.toNNReal z.1))| ≤ 1 := by
      by_cases hz : z.2 (Real.toNNReal z.1) ∈ B <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    calc Real.exp (-mu * z.1) * |B.indicator (fun _=>(1:ℝ)) (z.2 (Real.toNNReal z.1))| ≤
        Real.exp (-mu * z.1) * 1 := mul_le_mul_of_nonneg_left hind1 (Real.exp_pos _).le
      _ = Real.exp (-mu * z.1) := mul_one _
  have hswap : Integrable (fun z : ℝ × DiffusionPath d =>
      Real.exp (-mu * z.1) * B.indicator (fun _ => (1:ℝ)) (z.2 (Real.toNNReal z.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (KN N (omega, x))) :=
    hbase.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  rw [← integral_integral_swap hswap]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [integral_const_mul]
  congr 1
  have hevalt : Measurable (fun path : DiffusionPath d => path (Real.toNNReal t)) :=
    (continuous_eval_const (Real.toNNReal t)).measurable
  have hSmeas : MeasurableSet {path : DiffusionPath d | path (Real.toNNReal t) ∈ B} :=
    hevalt hB
  have hindeq : (fun path : DiffusionPath d => B.indicator (fun _ => (1:ℝ))
      (path (Real.toNNReal t))) =
      ({path : DiffusionPath d | path (Real.toNNReal t) ∈ B}).indicator (fun _ => (1:ℝ)) := by
    funext path
    by_cases hp : path (Real.toNNReal t) ∈ B <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hp]
  rw [hindeq, show (fun _ : DiffusionPath d => (1:ℝ)) = (1 : DiffusionPath d → ℝ) from rfl]
  have hfin := integral_indicator_one (μ := KN N (omega, x)) hSmeas
  rw [measureReal_def] at hfin
  rw [hfin]

/-- The `t`-integral of `Fj` against a fixed path, as a function of the path, is integrable
against `KN N (omega, x)`: Fubini on the (integrable) joint density, sliced. -/
theorem aux_car_resolvent_abs_cont_Fj_integral_prod_right
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d) (hKNmk : IsMarkovKernel (KN N))
    (mu : ℝ) (hmu : 0 < mu) (x : SpatialCoordinates d)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (j : ℕ) :
    Integrable (fun path : DiffusionPath d => ∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t) *
        aux_car_resolvent_abs_cont_Fj K hK j (path (Real.toNNReal t))) (KN N (omega, x)) := by
  let : IsMarkovKernel (KN N) := hKNmk
  have hev : Measurable (fun z : ℝ × DiffusionPath d => z.2 (Real.toNNReal z.1)) :=
    (continuous_eval.comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable
  have hFcont : Continuous (aux_car_resolvent_abs_cont_Fj K hK j) :=
    map_continuous (aux_car_resolvent_abs_cont_Fj K hK j)
  have hF : Measurable (fun z : ℝ × DiffusionPath d =>
      Real.exp (-mu * z.1) * aux_car_resolvent_abs_cont_Fj K hK j (z.2 (Real.toNNReal z.1))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
      (hFcont.measurable.comp hev)
  have hbase : Integrable (fun z : ℝ × DiffusionPath d => Real.exp (-mu * z.1))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (KN N (omega, x))) := by
    simpa only [one_mul] using
      (((exp_neg_integrableOn_Ioi 0 hmu).const_mul (1 : ℝ)).comp_fst (KN N (omega, x)))
  have hbound : ∀ z : ℝ × DiffusionPath d,
      ‖Real.exp (-mu * z.1) * aux_car_resolvent_abs_cont_Fj K hK j (z.2 (Real.toNNReal z.1))‖ ≤
        Real.exp (-mu * z.1) := by
    intro z
    rw [aux_car_resolvent_abs_cont_Fj_apply, norm_mul, Real.norm_eq_abs (Real.exp _),
      abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
      abs_of_nonneg (aux_car_resolvent_abs_cont_fj_bounds K j _).1]
    calc Real.exp (-mu * z.1) * aux_car_resolvent_abs_cont_fj K j (z.2 (Real.toNNReal z.1)) ≤
        Real.exp (-mu * z.1) * 1 := mul_le_mul_of_nonneg_left
          (aux_car_resolvent_abs_cont_fj_bounds K j _).2 (Real.exp_pos _).le
      _ = Real.exp (-mu * z.1) := mul_one _
  have hswap : Integrable (fun z : ℝ × DiffusionPath d =>
      Real.exp (-mu * z.1) * aux_car_resolvent_abs_cont_Fj K hK j (z.2 (Real.toNNReal z.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (KN N (omega, x))) :=
    hbase.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  exact hswap.integral_prod_right



theorem aux_car_resolvent_abs_cont_Fj_solution_tendsto
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d) (hKNmk : IsMarkovKernel (KN N))
    (hfd : ∀ I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x)
    (D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (SpatialCoordinates d))
    (hDsol : ∀ (m : Semigroup.PositiveShift) (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d), D.solution m f x = ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-(m : ℝ) * t) * kernelIntegral (PN N omega (Real.toNNReal t)) f x)
    (mu : ℝ) (hmu : 0 < mu) (x : SpatialCoordinates d)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K) :
    Tendsto (fun j => D.solution ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj K hK j) x) atTop
      (𝓝 (∫ path, (∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t) *
          K.indicator (fun _ => (1:ℝ)) (path (Real.toNNReal t))) ∂(KN N (omega, x)))) := by
  have hstep : ∀ j, D.solution ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj K hK j) x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t) *
          aux_car_resolvent_abs_cont_Fj K hK j (path (Real.toNNReal t))) ∂(KN N (omega, x)) := by
    intro j
    rw [hDsol ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj K hK j) x,
      aux_car_resolvent_abs_cont_occupation_eq_kernelIntegral PN KN N omega hKNmk hfd mu hmu
        (aux_car_resolvent_abs_cont_Fj K hK j) x]
  simp_rw [hstep]
  apply tendsto_integral_of_dominated_convergence
    (fun _ : DiffusionPath d => ∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t))
  · intro j
    exact (aux_car_resolvent_abs_cont_Fj_integral_prod_right KN N omega hKNmk mu hmu x K hK j)
      |>.aestronglyMeasurable
  · exact integrable_const _
  · intro j
    filter_upwards with path
    have hb := aux_car_resolvent_abs_cont_inner_bound K mu hmu j path
    simpa only [aux_car_resolvent_abs_cont_Fj_apply] using hb
  · filter_upwards with path
    have ht := aux_car_resolvent_abs_cont_inner_tendsto K hK mu hmu path
    simpa only [aux_car_resolvent_abs_cont_Fj_apply] using ht

/-- **Moser upgrade, compact case.** For a Lebesgue-null COMPACT `K` and EVERY start point `x0`
(not just a.e.), the resolvent occupation quantity vanishes: the De Giorgi–Moser local bound turns
the a.e.-`x` vanishing of `aux_car_resolvent_abs_cont_global_ae_zero` into everywhere vanishing, via
continuity of `x ↦ D.solution mu Fj x` and the essential-sup-vs-sup argument. -/
theorem aux_car_resolvent_abs_cont_compact_zero
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKNmk : IsMarkovKernel (KN N))
    (hfd : ∀ I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x)
    (hL : LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
      (aux_cutoff_lifetime_package_kernel KN N omega))
    (D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (SpatialCoordinates d))
    (hDweak : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
      (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D)
    (hDsol : ∀ (m : Semigroup.PositiveShift) (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d), D.solution m f x = ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-(m : ℝ) * t) * kernelIntegral (PN N omega (Real.toNNReal t)) f x)
    (mu : ℝ) (hmu : 0 < mu) (x0 : SpatialCoordinates d)
    (Kb : Set (SpatialCoordinates d)) (hKb : IsCompact Kb) (hKbnull : volume Kb = 0) :
    ∫ path, (∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t) *
        Kb.indicator (fun _ => (1:ℝ)) (path (Real.toNNReal t))) ∂(KN N (omega, x0)) = 0 := by
  set rho := cutoffSpeedDensity M H omega N with hrhodef
  have hr1 : (0:ℝ) < 1 := one_pos
  set Umoser : Set (SpatialCoordinates d) := (centeredCube x0 1 hr1 : Set (SpatialCoordinates d))
    with hUmoserdef
  have hUbdd : Bornology.IsBounded Umoser := centeredCube_isBounded x0 hr1
  have hUne : Umoser.Nonempty := ⟨x0, Metric.mem_ball_self (by norm_num)⟩
  obtain ⟨clo, chi, rlo, rhi, hclo, hrlo, hcbdd, hrbdd⟩ :=
    aux_car_resolvent_abs_cont_bounds M H omega N hUbdd hUne
  set V : Set (SpatialCoordinates d) := Metric.ball x0 (1/4 : ℝ) with hVdef
  set K'moser : Set (SpatialCoordinates d) := closure V with hK'def
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hVbdd : Bornology.IsBounded V := Metric.isBounded_ball
  have hK'compact : IsCompact K'moser := hVbdd.isCompact_closure
  have hVsubK' : V ⊆ K'moser := subset_closure
  have hK'subU : K'moser ⊆ Umoser := by
    have h1 : closure V ⊆ Metric.closedBall x0 (1/4 : ℝ) := Metric.closure_ball_subset_closedBall
    have h2 : Metric.closedBall x0 (1/4 : ℝ) ⊆ Metric.ball x0 (1/2 : ℝ) :=
      Metric.closedBall_subset_ball (by norm_num)
    exact h1.trans h2
  have hVclosureU : V ⊆ closure Umoser := hVsubK'.trans (hK'subU.trans subset_closure)
  have hx0V : x0 ∈ V := Metric.mem_ball_self (by norm_num)
  have hrhoV : ∀ y ∈ V, rlo ≤ rho y := fun y hy => (hrbdd y (hVclosureU hy)).1
  have hK'meas : MeasurableSet K'moser := hK'compact.isClosed.measurableSet
  set p : ℝ := (d : ℝ) / 2 + 1 with hpdef
  have hp : (d : ℝ) / 2 < p := by linarith
  obtain ⟨C, hC0, hMoser⟩ := aux_car_moser_source_local_bound_c0_resolvent hd M H omega N x0 hr1
    K'moser hK'compact hK'subU p hp D hDweak
  set uj : ℕ → SpatialCoordinates d → ℝ :=
    fun j y => D.solution ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj Kb hKb j) y with hujdef
  have hwKbzero : weightedMeasure rho Kb = 0 :=
    withDensity_absolutelyContinuous volume (fun y => ENNReal.ofReal (rho y)) hKbnull
  have hae5 : ∀ᵐ x ∂(weightedMeasure rho), Tendsto (fun j => uj j x) atTop (𝓝 0) := by
    have h5 := aux_car_resolvent_abs_cont_global_ae_zero M H omega N KN hKNmk hL hmu
      hKb.measurableSet hKbnull
    filter_upwards [h5] with x hx
    have hswapx := aux_car_resolvent_abs_cont_fubini_swap KN N omega hKNmk mu hmu x Kb
      hKb.measurableSet
    have hbridge := aux_car_resolvent_abs_cont_Fj_solution_tendsto PN KN N omega hKNmk hfd D hDsol
      mu hmu x Kb hKb
    rw [hswapx, hx] at hbridge
    exact hbridge
  have huj_ae0_U : ∀ᵐ y ∂(weightedMeasure rho).restrict Umoser,
      Tendsto (fun j => uj j y) atTop (𝓝 0) := ae_restrict_of_ae hae5
  have hFj_ae0_U : ∀ᵐ y ∂(weightedMeasure rho).restrict Umoser,
      Tendsto (fun j => aux_car_resolvent_abs_cont_Fj Kb hKb j y) atTop (𝓝 0) := by
    have hKbindic0 : Kb.indicator (fun _ => (1:ℝ)) =ᵐ[weightedMeasure rho] (0 : SpatialCoordinates d → ℝ) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hwKbzero] with y hy
      simp [Set.indicator_of_notMem hy]
    have hae0 : ∀ᵐ y ∂(weightedMeasure rho), Tendsto
        (fun j => aux_car_resolvent_abs_cont_Fj Kb hKb j y) atTop (𝓝 0) := by
      filter_upwards [hKbindic0] with y hy
      have hft := aux_car_resolvent_abs_cont_fj_tendsto Kb hKb.isClosed y
      simp only [aux_car_resolvent_abs_cont_Fj_apply]
      rwa [hy] at hft
    exact ae_restrict_of_ae hae0
  let : IsFiniteMeasure ((weightedMeasure rho).restrict Umoser) := by
    have hUfin : volume Umoser ≠ ⊤ := hUbdd.measure_lt_top.ne
    have hUopen : IsOpen Umoser := (centeredCube x0 1 hr1).2
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    unfold weightedMeasure
    rw [withDensity_apply _ hUopen.measurableSet]
    calc ∫⁻ a in Umoser, ENNReal.ofReal (rho a)
        ≤ ∫⁻ _a in Umoser, ENNReal.ofReal rhi := by
          apply setLIntegral_mono measurable_const
          intro y hy
          exact ENNReal.ofReal_le_ofReal (hrbdd y (subset_closure hy)).2
      _ = ENNReal.ofReal rhi * volume Umoser := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUbdd.measure_lt_top
  have hujcont : ∀ j, Continuous (uj j) := fun j => map_continuous (D.solution ⟨mu, hmu⟩
    (aux_car_resolvent_abs_cont_Fj Kb hKb j))
  have hFjnonneg : ∀ j y, 0 ≤ aux_car_resolvent_abs_cont_Fj Kb hKb j y := fun j y => by
    rw [aux_car_resolvent_abs_cont_Fj_apply]; exact (aux_car_resolvent_abs_cont_fj_bounds Kb j y).1
  have hFjnorm_le1 : ∀ j, ‖aux_car_resolvent_abs_cont_Fj Kb hKb j‖ ≤ 1 := by
    intro j
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le (by norm_num)).mpr (fun y => ?_)
    show |aux_car_resolvent_abs_cont_Fj Kb hKb j y| ≤ 1
    rw [abs_of_nonneg (hFjnonneg j y), aux_car_resolvent_abs_cont_Fj_apply]
    exact (aux_car_resolvent_abs_cont_fj_bounds Kb j y).2
  have huj_nonneg : ∀ j y, 0 ≤ uj j y := fun j y =>
    D.solution_nonneg ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj Kb hKb j) (hFjnonneg j) y
  have huj_le : ∀ j, ‖D.solution ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj Kb hKb j)‖ ≤ mu⁻¹ := by
    intro j
    have h1 := D.norm_solution_le ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj Kb hKb j)
    calc ‖D.solution ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj Kb hKb j)‖ ≤
        (mu⁻¹) * ‖aux_car_resolvent_abs_cont_Fj Kb hKb j‖ := h1
      _ ≤ mu⁻¹ * 1 := mul_le_mul_of_nonneg_left (hFjnorm_le1 j) (by positivity)
      _ = mu⁻¹ := mul_one _
  have huj_bound : ∀ j y, |uj j y| ≤ mu⁻¹ := fun j y => by
    rw [abs_of_nonneg (huj_nonneg j y)]
    calc uj j y = ‖(D.solution ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj Kb hKb j)).toBCF y‖ := by
          rw [Real.norm_eq_abs]
          exact (abs_of_nonneg (huj_nonneg j y)).symm
      _ ≤ ‖(D.solution ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj Kb hKb j)).toBCF‖ :=
          (D.solution ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj Kb hKb j)).toBCF.norm_coe_le_norm y
      _ = ‖D.solution ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj Kb hKb j)‖ :=
          ZeroAtInftyContinuousMap.norm_toBCF_eq_norm
      _ ≤ mu⁻¹ := huj_le j
  have hppos : 0 < p := lt_of_le_of_lt (by positivity : (0:ℝ) ≤ (d:ℝ) / 2) hp
  have hFjmeas : ∀ j, Measurable (aux_car_resolvent_abs_cont_Fj Kb hKb j) :=
    fun j => (map_continuous (aux_car_resolvent_abs_cont_Fj Kb hKb j)).measurable
  have hujmeas : ∀ j, Measurable (uj j) := fun j => (hujcont j).measurable
  have hFj_bound_ae : ∀ j, ∀ᵐ y ∂(weightedMeasure rho).restrict Umoser,
      |aux_car_resolvent_abs_cont_Fj Kb hKb j y| ≤ (1:ℝ) := fun j =>
    Filter.Eventually.of_forall (fun y => by
      rw [abs_of_nonneg (hFjnonneg j y), aux_car_resolvent_abs_cont_Fj_apply]
      exact (aux_car_resolvent_abs_cont_fj_bounds Kb j y).2)
  have huj_bound_ae : ∀ j, ∀ᵐ y ∂(weightedMeasure rho).restrict Umoser, |uj j y| ≤ mu⁻¹ :=
    fun j => Filter.Eventually.of_forall (huj_bound j)
  have hterm1' : Tendsto (fun j => eLpNorm (uj j) (ENNReal.ofReal (2:ℝ))
      ((weightedMeasure rho).restrict Umoser)) atTop (𝓝 0) :=
    aux_car_resolvent_abs_cont_tendsto_eLpNorm_zero (by norm_num : (0:ℝ) < 2) hujmeas
      (le_of_lt (inv_pos.mpr hmu)) huj_bound_ae huj_ae0_U
  have h2eq : ENNReal.ofReal (2:ℝ) = (2:ℝ≥0∞) := by norm_num
  have hterm1 : Tendsto (fun j => eLpNorm (uj j) 2 ((weightedMeasure rho).restrict Umoser))
      atTop (𝓝 0) := by simpa only [h2eq] using hterm1'
  have hterm2 : Tendsto (fun j => eLpNorm (aux_car_resolvent_abs_cont_Fj Kb hKb j)
      (ENNReal.ofReal p) ((weightedMeasure rho).restrict Umoser)) atTop (𝓝 0) :=
    aux_car_resolvent_abs_cont_tendsto_eLpNorm_zero hppos hFjmeas zero_le_one hFj_bound_ae
      hFj_ae0_U
  have hterm3' : Tendsto (fun j => eLpNorm (uj j) (ENNReal.ofReal p)
      ((weightedMeasure rho).restrict Umoser)) atTop (𝓝 0) :=
    aux_car_resolvent_abs_cont_tendsto_eLpNorm_zero hppos hujmeas
      (le_of_lt (inv_pos.mpr hmu)) huj_bound_ae huj_ae0_U
  have hterm3 : Tendsto (fun j => ENNReal.ofReal mu * eLpNorm (uj j) (ENNReal.ofReal p)
      ((weightedMeasure rho).restrict Umoser)) atTop (𝓝 0) := by
    have hcm := ENNReal.Tendsto.const_mul hterm3' (Or.inr ENNReal.ofReal_ne_top : (0:ℝ≥0∞) ≠ 0 ∨
      ENNReal.ofReal mu ≠ ⊤)
    simpa using hcm
  set RHSfun : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal C *
      (eLpNorm (uj j) 2 ((weightedMeasure rho).restrict Umoser) +
        eLpNorm (aux_car_resolvent_abs_cont_Fj Kb hKb j) (ENNReal.ofReal p)
          ((weightedMeasure rho).restrict Umoser) +
        ENNReal.ofReal mu * eLpNorm (uj j) (ENNReal.ofReal p)
          ((weightedMeasure rho).restrict Umoser)) with hRHSfundef
  have hRHStendsto : Tendsto RHSfun atTop (𝓝 0) := by
    have hsum := (hterm1.add hterm2).add hterm3
    have hcm := ENNReal.Tendsto.const_mul hsum (Or.inr ENNReal.ofReal_ne_top : (0:ℝ≥0∞) + 0 + 0 ≠ 0 ∨
      ENNReal.ofReal C ≠ ⊤)
    simpa [RHSfun] using hcm
  have hpointwise : ∀ j, (‖uj j x0‖ₑ : ℝ≥0∞) ≤ RHSfun j := fun j =>
    aux_car_resolvent_abs_cont_pointwise_of_eLpNorm_top hrlo rho hVopen hVsubK' hK'meas hrhoV
      (hujcont j) hx0V (hMoser ⟨mu, hmu⟩ (aux_car_resolvent_abs_cont_Fj Kb hKb j))
  have hsqueeze : Tendsto (fun j => (‖uj j x0‖ₑ : ℝ≥0∞)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRHStendsto
      (fun j => zero_le) hpointwise
  have hnormtendsto : Tendsto (fun j => ‖uj j x0‖) atTop (𝓝 0) := by
    have h6 := (ENNReal.tendsto_toReal (a := (0:ℝ≥0∞)) (by simp)).comp hsqueeze
    simpa [Function.comp, toReal_enorm'] using! h6
  have hujx0tendsto : Tendsto (fun j => uj j x0) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnormtendsto
  have hbridge0 := aux_car_resolvent_abs_cont_Fj_solution_tendsto PN KN N omega hKNmk hfd D hDsol
    mu hmu x0 Kb hKb
  exact tendsto_nhds_unique hbridge0 hujx0tendsto

/-- Measurability of the slice `t ↦ (KN N (omega,x)) {path | path t ∈ B}`, reused from the
`hjointmeas`/`hmeasn` pattern. -/
theorem aux_car_resolvent_abs_cont_measure_slice_measurable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d) (hKNmk : IsMarkovKernel (KN N)) (x : SpatialCoordinates d)
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B) :
    Measurable (fun t : ℝ => (KN N (omega, x)) {path : DiffusionPath d |
        path (Real.toNNReal t) ∈ B}) := by
  have : IsProbabilityMeasure (KN N (omega, x)) := hKNmk.isProbabilityMeasure (omega, x)
  have hevalt : ∀ t : ℝ, Measurable (fun path : DiffusionPath d => path (Real.toNNReal t)) :=
    fun t => (continuous_eval_const (Real.toNNReal t)).measurable
  have hjointmeas : Measurable (fun z : ℝ × DiffusionPath d =>
      ({path : DiffusionPath d | path (Real.toNNReal z.1) ∈ B}).indicator
        (1 : DiffusionPath d → ℝ≥0∞) z.2) := by
    have hev : Measurable (fun z : ℝ × DiffusionPath d => z.2 (Real.toNNReal z.1)) :=
      (continuous_eval.comp
        (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable
    have hset : MeasurableSet {z : ℝ × DiffusionPath d | z.2 (Real.toNNReal z.1) ∈ B} := hev hB
    have heqfun : (fun z : ℝ × DiffusionPath d =>
        ({path : DiffusionPath d | path (Real.toNNReal z.1) ∈ B}).indicator
          (1 : DiffusionPath d → ℝ≥0∞) z.2) =
        Set.indicator {z : ℝ × DiffusionPath d | z.2 (Real.toNNReal z.1) ∈ B}
          (fun _ => (1:ℝ≥0∞)) := by
      funext z
      by_cases hz : z.2 (Real.toNNReal z.1) ∈ B <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
    rw [heqfun]
    exact measurable_const.indicator hset
  have hli := hjointmeas.lintegral_prod_right' (ν := KN N (omega, x))
  have heq2 : (fun t : ℝ => ∫⁻ path, ({path : DiffusionPath d | path (Real.toNNReal t) ∈ B}).indicator
      (1 : DiffusionPath d → ℝ≥0∞) path ∂(KN N (omega, x))) =
      (fun t : ℝ => (KN N (omega, x)) {path : DiffusionPath d | path (Real.toNNReal t) ∈ B}) := by
    funext t
    exact lintegral_indicator_one (hevalt t hB)
  rwa [heq2] at hli

/-- The `t`-and-path occupation measure at a start point `x`: the pushforward, along path
evaluation at an exponentially-weighted random time, of the exponential-clock ⊗ path-law product
measure. A genuine (not necessarily finite) `Measure (SpatialCoordinates d)` on a Polish space, so
it is automatically inner regular for compact sets. -/
noncomputable def aux_car_resolvent_abs_cont_occMeasure
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d) (mu : ℝ) (x : SpatialCoordinates d) :
    Measure (SpatialCoordinates d) :=
  Measure.map (fun p : ℝ × DiffusionPath d => p.2 (Real.toNNReal p.1))
    (((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun t => ENNReal.ofReal (Real.exp (-mu * t)))).prod (KN N (omega, x)))



theorem aux_car_resolvent_abs_cont_occMeasure_eq
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d) (hKNmk : IsMarkovKernel (KN N))
    (mu : ℝ) (hmu : 0 < mu) (x : SpatialCoordinates d)
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B) :
    aux_car_resolvent_abs_cont_occMeasure KN N omega mu x B =
      ENNReal.ofReal (∫ path, (∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t) *
          B.indicator (fun _ => (1:ℝ)) (path (Real.toNNReal t))) ∂(KN N (omega, x))) := by
  let : IsMarkovKernel (KN N) := hKNmk
  have : IsProbabilityMeasure (KN N (omega, x)) := hKNmk.isProbabilityMeasure (omega, x)
  rw [aux_car_resolvent_abs_cont_fubini_swap KN N omega hKNmk mu hmu x B hB]
  have hev : Measurable (fun z : ℝ × DiffusionPath d => z.2 (Real.toNNReal z.1)) :=
    (continuous_eval.comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable
  unfold aux_car_resolvent_abs_cont_occMeasure
  rw [Measure.map_apply hev hB]
  have hSmeas : MeasurableSet ((fun z : ℝ × DiffusionPath d => z.2 (Real.toNNReal z.1)) ⁻¹' B) :=
    hev hB
  rw [Measure.prod_apply hSmeas]
  have heq1 : (fun t : ℝ => (KN N (omega, x))
      (Prod.mk t ⁻¹' ((fun z : ℝ × DiffusionPath d => z.2 (Real.toNNReal z.1)) ⁻¹' B))) =
      (fun t : ℝ => (KN N (omega, x)) {path : DiffusionPath d | path (Real.toNNReal t) ∈ B}) := by
    funext t; rfl
  rw [heq1, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
    (aux_car_resolvent_abs_cont_measure_slice_measurable KN N omega hKNmk x B hB)]
  have hg_ne_top : ∀ t : ℝ, (KN N (omega, x)) {path : DiffusionPath d |
      path (Real.toNNReal t) ∈ B} ≠ ⊤ := fun t => measure_ne_top _ _
  have hpointeq : (fun t : ℝ => ((fun t => ENNReal.ofReal (Real.exp (-mu * t))) *
      fun t => (KN N (omega, x)) {path : DiffusionPath d | path (Real.toNNReal t) ∈ B}) t) =
      (fun t : ℝ => ENNReal.ofReal (Real.exp (-mu * t) *
        ((KN N (omega, x)) {path : DiffusionPath d | path (Real.toNNReal t) ∈ B}).toReal)) := by
    funext t
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal (hg_ne_top t)]
  rw [hpointeq]
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] (fun t : ℝ => Real.exp (-mu * t) *
      ((KN N (omega, x)) {path : DiffusionPath d | path (Real.toNNReal t) ∈ B}).toReal) := by
    filter_upwards with t
    exact mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  have hdom : Integrable (fun t : ℝ => Real.exp (-mu * t)) (volume.restrict (Set.Ioi (0:ℝ))) := by
    simpa only [neg_mul] using! exp_neg_integrableOn_Ioi 0 hmu
  have hintble : Integrable (fun t : ℝ => Real.exp (-mu * t) *
      ((KN N (omega, x)) {path : DiffusionPath d | path (Real.toNNReal t) ∈ B}).toReal)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    have hmeas1 : AEStronglyMeasurable (fun t : ℝ => Real.exp (-mu * t))
        (volume.restrict (Set.Ioi (0:ℝ))) :=
      (Real.measurable_exp.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
    have hmeas2 : AEStronglyMeasurable (fun t : ℝ =>
        ((KN N (omega, x)) {path : DiffusionPath d | path (Real.toNNReal t) ∈ B}).toReal)
        (volume.restrict (Set.Ioi (0:ℝ))) :=
      Measurable.aestronglyMeasurable (Measurable.ennreal_toReal
        (aux_car_resolvent_abs_cont_measure_slice_measurable KN N omega hKNmk x B hB))
    apply hdom.mono' (hmeas1.mul hmeas2)
    filter_upwards with t
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)]
    have hb : ((KN N (omega, x)) {path : DiffusionPath d |
        path (Real.toNNReal t) ∈ B}).toReal ≤ 1 := by
      have hle1 : (KN N (omega, x)) {path : DiffusionPath d | path (Real.toNNReal t) ∈ B} ≤ 1 := by
        have := measure_mono (μ := KN N (omega, x)) (Set.subset_univ
          {path : DiffusionPath d | path (Real.toNNReal t) ∈ B})
        rwa [measure_univ] at this
      simpa using ENNReal.toReal_mono (by norm_num) hle1
    nlinarith [Real.exp_pos (-mu * t)]
  rw [ofReal_integral_eq_lintegral_ofReal hintble hnonneg]

/-- **Full inner-regularity upgrade.** For every `x` and every Lebesgue-null MEASURABLE `B` (not
necessarily compact), the occupation quantity vanishes: inner regularity of the occupation
measure `occMeasure` reduces `B` to its compact subsets, each null (subset of a null set) and
each handled by `aux_car_resolvent_abs_cont_compact_zero`. -/
theorem aux_car_resolvent_abs_cont_every_zero
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKNmk : IsMarkovKernel (KN N))
    (hfd : ∀ I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x)
    (hL : LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
      (aux_cutoff_lifetime_package_kernel KN N omega))
    (D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (SpatialCoordinates d))
    (hDweak : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
      (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D)
    (hDsol : ∀ (m : Semigroup.PositiveShift) (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d), D.solution m f x = ∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-(m : ℝ) * t) * kernelIntegral (PN N omega (Real.toNNReal t)) f x)
    (mu : ℝ) (hmu : 0 < mu) (x0 : SpatialCoordinates d)
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B) (hBnull : volume B = 0) :
    ∫ path, (∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t) *
        B.indicator (fun _ => (1:ℝ)) (path (Real.toNNReal t))) ∂(KN N (omega, x0)) = 0 := by
  have hoccB_ne_top : aux_car_resolvent_abs_cont_occMeasure KN N omega mu x0 B ≠ ⊤ := by
    rw [aux_car_resolvent_abs_cont_occMeasure_eq KN N omega hKNmk mu hmu x0 B hB]
    exact ENNReal.ofReal_ne_top
  have hcompactzero : ∀ K, K ⊆ B → IsCompact K →
      aux_car_resolvent_abs_cont_occMeasure KN N omega mu x0 K = 0 := by
    intro K hKB hK
    have hKnull : volume K = 0 := measure_mono_null hKB hBnull
    have htarget0 := aux_car_resolvent_abs_cont_compact_zero hd M H omega N PN KN hKNmk hfd hL D
      hDweak hDsol mu hmu x0 K hK hKnull
    rw [aux_car_resolvent_abs_cont_occMeasure_eq KN N omega hKNmk mu hmu x0 K hK.measurableSet,
      htarget0]
    simp
  have hsup := hB.measure_eq_iSup_isCompact_of_ne_top
    (μ := aux_car_resolvent_abs_cont_occMeasure KN N omega mu x0) hoccB_ne_top
  have hall0 : (⨆ (K : Set (SpatialCoordinates d)) (_ : K ⊆ B) (_ : IsCompact K),
      aux_car_resolvent_abs_cont_occMeasure KN N omega mu x0 K) = 0 := by
    refine le_antisymm ?_ (zero_le)
    refine iSup_le fun K => iSup_le fun hKB => iSup_le fun hK => ?_
    exact (hcompactzero K hKB hK).le
  rw [hall0, aux_car_resolvent_abs_cont_occMeasure_eq KN N omega hKNmk mu hmu x0 B hB] at hsup
  have hzero := (ENNReal.ofReal_eq_zero).mp hsup
  have hnonneg : 0 ≤ ∫ path, (∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t) *
      B.indicator (fun _ => (1:ℝ)) (path (Real.toNNReal t))) ∂(KN N (omega, x0)) := by
    apply integral_nonneg
    intro path
    apply integral_nonneg
    intro t
    exact mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  linarith

/-- **`car_resolvent_abs_cont`.** For a.e. sample and every cutoff `N`, the `μ`-resolvent
occupation measure of the attached path law `KN N (ω, x)` does not charge Lebesgue-null sets, for
EVERY `x`. Assembled from: `in_crossing`'s `D` existence and finset-evaluation identity (a.e.
omega), `hinput`'s `LocalDiffusion` (a.e. omega), and `aux_car_resolvent_abs_cont_every_zero` (the
Moser-upgrade + inner-regularity argument). -/
theorem car_resolvent_abs_cont
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN)
    (hinput : aux_cutoff_lifetime_package_LocalInput M H KN) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (mu : ℝ), 0 < mu →
      ∀ (x : SpatialCoordinates d) (B : Set (SpatialCoordinates d)),
        MeasurableSet B → volume B = 0 →
          ∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Real.exp (-mu * t) * B.indicator (fun _ => (1 : ℝ)) (path (Real.toNNReal t)))
            ∂(KN N (omega, x)) = 0 := by
  obtain ⟨hDex, _hCons, hfdae⟩ := hin
  filter_upwards [hDex, hfdae, hinput.localDiffusion] with omega hDomega hfdomega hLomega
  intro N mu hmu x B hB hBnull
  obtain ⟨D, _hDdense, hDweak, hDsol⟩ := hDomega N
  exact aux_car_resolvent_abs_cont_every_zero hd M H omega N PN KN (hKN N) (hfdomega N)
    (hLomega N) D hDweak hDsol mu hmu x B hB hBnull

end SubdiffusiveProcess.Paper
