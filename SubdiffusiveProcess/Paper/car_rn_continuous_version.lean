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
public import SubdiffusiveProcess.Lane3.DirichletForm
public import SubdiffusiveProcess.Lane2.KilledInverse
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationContinuity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationLaplace
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKilledSymmetry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeMeanExitLower
public import MarkovProcess.Path.ExitTimeShift
public import MarkovProcess.Killed.GluingResolventEquation
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.cutoff_lifetime_package
public import SubdiffusiveProcess.Paper.car_resolvent_abs_cont

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_car_rn_continuous_version_abel
    {F : ℝ → ℝ} {C : ℝ}
    (hF : Measurable F) (hC : 0 ≤ C)
    (hFb : ∀ t, 0 < t → |F t| ≤ C)
    (hF0 : ContinuousWithinAt F (Set.Ici (0 : ℝ)) 0) :
    Tendsto (fun mu : ℝ => mu * ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-mu * t) * F t) atTop (nhds (F 0)) := by
  have hlim : ∀ x : ℝ, 0 < x →
      Tendsto (fun mu : ℝ => Real.exp (-x) * F (x / mu)) atTop
        (nhds (Real.exp (-x) * F 0)) := by
    intro x hx
    have hdiv : Tendsto (fun mu : ℝ => x / mu) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hdiv' : Tendsto (fun mu : ℝ => x / mu) atTop (nhdsWithin 0 (Set.Ici 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hdiv, ?_⟩
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with mu hmu
      exact Set.mem_Ici.mpr (div_nonneg hx.le hmu.le)
    exact tendsto_const_nhds.mul (hF0.tendsto.comp hdiv')
  have hdom : Integrable (fun x : ℝ => C * Real.exp (-x)) (volume.restrict (Set.Ioi 0)) := by
    simpa [mul_comm] using (exp_neg_integrableOn_Ioi (0 : ℝ) zero_lt_one).const_mul C
  have heq : ∀ᶠ mu : ℝ in atTop, 0 < mu := eventually_gt_atTop 0
  have hDCT : Tendsto
      (fun mu : ℝ => ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (x / mu)) atTop
      (nhds (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => C * Real.exp (-x))
    · filter_upwards [] with mu
      have hm : Measurable (fun x : ℝ => Real.exp (-x) * F (x / mu)) :=
        (Real.continuous_exp.comp (continuous_id.neg)).measurable.mul
          (hF.comp (measurable_id.div (measurable_const : Measurable (fun _ : ℝ => mu))))
      exact hm.aestronglyMeasurable
    · filter_upwards [heq] with mu hmu
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (-x))]
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left (hFb (x / mu) (div_pos hx hmu))
          (Real.exp_pos (-x)).le)
    · exact hdom
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hlim x hx
  have hDCT' : Tendsto
      (fun mu : ℝ => ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (x / mu)) atTop
      (nhds (F 0)) := by
    have hInt : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F 0) = F 0 := by
      rw [integral_mul_const]
      have hexp : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x)) = 1 := by
        convert MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero
          zero_lt_one using 1 <;> ring
      rw [hexp]
      ring
    simpa [hInt] using hDCT
  refine hDCT'.congr' ?_
  filter_upwards [heq] with mu hmu
  have hchange := integral_comp_mul_left_Ioi
    (fun t : ℝ => Real.exp (-mu * t) * F t) 0 (inv_pos.mpr hmu)
  have hchange' : mu * ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-mu * t) * F t =
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (x / mu) := by
    calc
      mu * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-mu * t) * F t =
          (mu⁻¹)⁻¹ • ∫ t in Set.Ioi (mu⁻¹ * 0),
            (fun t : ℝ => Real.exp (-mu * t) * F t) t := by
              simp only [smul_eq_mul, inv_inv, mul_zero]
      _ = ∫ x in Set.Ioi (0 : ℝ),
            (fun t : ℝ => Real.exp (-mu * t) * F t) (mu⁻¹ * x) := by
              simpa only [smul_eq_mul, inv_inv, mul_zero] using hchange.symm
      _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * F (x / mu) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x hx
              dsimp
              rw [show -mu * (mu⁻¹ * x) = -x by field_simp]
              congr 2
              field_simp
  exact hchange'.symm

theorem aux_car_rn_continuous_version_kernel_bound
    {α : Type*} [MeasurableSpace α]
    (P : SubMarkovKernelSemigroup α) {f : α → ℝ} {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (t : ℝ≥0) (x : α) :
    |kernelIntegral (P t) f x| ≤ D := by
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  rw [← Real.norm_eq_abs]
  letI : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  calc
    ‖kernelIntegral (P t) f x‖ ≤ ∫ _y, D ∂(P t x) := by
      apply norm_integral_le_of_norm_le (integrable_const D)
      exact Eventually.of_forall hfD
    _ ≤ D := by
      rw [integral_const, smul_eq_mul]
      apply mul_le_of_le_one_left hD0
      rw [measureReal_def, ← ENNReal.toReal_one]
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
      exact (P.isSubMarkovKernel t).measure_le_one x Set.univ

theorem aux_car_rn_continuous_version_ofReal_resolvent
    {α : Type*} [MeasurableSpace α]
    (P : SubMarkovKernelSemigroup α) {lam : ℝ} (hlam : 0 < lam)
    {f : α → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D)
    (hf0 : ∀ y, 0 ≤ f y) (x : α) :
    ENNReal.ofReal (P.kernelResolventReal lam f x) =
      P.kernelResolvent lam (fun y => ENNReal.ofReal (f y)) x := by
  have houter : IntegrableOn (fun t : ℝ => Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x) (Set.Ioi 0) := by
    apply Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
    · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
        ((P.measurable_kernelIntegral hf).comp
          (measurable_real_toNNReal.prodMk measurable_const))).stronglyMeasurable
          ).aestronglyMeasurable.restrict
    · exact Eventually.of_forall (fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left
          (aux_car_rn_continuous_version_kernel_bound P hfD (Real.toNNReal t) x)
          (Real.exp_pos _).le)
  have hnonneg : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      0 ≤ Real.exp (-lam * t) * kernelIntegral (P (Real.toNNReal t)) f x := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    haveI : IsFiniteKernel (P (Real.toNNReal t)) :=
      (P.isSubMarkovKernel (Real.toNNReal t)).isFiniteKernel
    have hfint : Integrable f (P (Real.toNNReal t) x) := by
      exact Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable D
        (Eventually.of_forall hfD)
    exact mul_nonneg (Real.exp_pos _).le
      (integral_nonneg_of_ae (Filter.Eventually.of_forall (hf0)))
  unfold SubMarkovKernelSemigroup.kernelResolventReal
  unfold SubMarkovKernelSemigroup.kernelResolvent
  change ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-lam * t) * kernelIntegral (P (Real.toNNReal t)) f x) =
    ∫⁻ t, ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ y, ENNReal.ofReal (f y) ∂(P (Real.toNNReal t) x)
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))
  rw [ofReal_integral_eq_lintegral_ofReal houter hnonneg]
  apply lintegral_congr
  intro t
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  letI : IsFiniteKernel (P (Real.toNNReal t)) :=
    (P.isSubMarkovKernel (Real.toNNReal t)).isFiniteKernel
  have hfint : Integrable f (P (Real.toNNReal t) x) := by
    exact Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable D
      (Eventually.of_forall hfD)
  exact ofReal_integral_eq_lintegral_ofReal hfint
    (Filter.Eventually.of_forall hf0)

theorem aux_car_rn_continuous_version_real_resolvent_nonneg_equation
    {α : Type*} [MeasurableSpace α]
    (P : SubMarkovKernelSemigroup α) {lam mu : ℝ} (hlam : 0 < lam)
    (hlt : lam < mu) {g : α → ℝ} (hg : Measurable g)
    {D : ℝ} (hgD : ∀ y, |g y| ≤ D) (hg0 : ∀ y, 0 ≤ g y) (x : α) :
    P.kernelResolventReal lam g x =
      P.kernelResolventReal mu g x + (mu - lam) *
        P.kernelResolventReal mu (fun y => P.kernelResolventReal lam g y) x := by
  have hmu : 0 < mu := hlam.trans hlt
  have hD0 : 0 ≤ D := (abs_nonneg (g x)).trans (hgD x)
  let E : ℝ → α → ℝ≥0∞ := fun r y =>
    P.kernelResolvent r (fun z => ENNReal.ofReal (g z)) y
  have hEmeas : Measurable (E mu) := by
    exact P.measurable_kernelResolvent mu (ENNReal.measurable_ofReal.comp hg)
  have hEle : ∀ y, E mu y ≤ ENNReal.ofReal (D / mu) := by
    intro y
    calc
      E mu y ≤ P.kernelResolvent mu (fun _ : α => ENNReal.ofReal D) y := by
        apply P.kernelResolvent_mono mu
        intro z
        exact ENNReal.ofReal_le_ofReal ((le_abs_self (g z)).trans (hgD z))
      _ = ENNReal.ofReal D * P.kernelResolvent mu (fun _ : α => (1 : ℝ≥0∞)) y := by
        rw [show (fun _ : α => ENNReal.ofReal D) =
            (fun z : α => ENNReal.ofReal D * (1 : ℝ≥0∞)) by funext z; simp,
          (P.kernelResolvent_const_mul mu (ENNReal.ofReal D)
            (f := fun _ : α => (1 : ℝ≥0∞)) measurable_const y)]
      _ ≤ ENNReal.ofReal D * ENNReal.ofReal mu⁻¹ := by
        exact mul_le_mul_right (P.kernelResolvent_one_le hmu y) _
      _ = ENNReal.ofReal (D / mu) := by
        rw [← ENNReal.ofReal_mul hD0]
        congr 1
  have hEfle : ∀ y, E lam y ≤ ENNReal.ofReal (D / lam) := by
    intro y
    calc
      E lam y ≤ P.kernelResolvent lam (fun _ : α => ENNReal.ofReal D) y := by
        apply P.kernelResolvent_mono lam
        intro z
        exact ENNReal.ofReal_le_ofReal ((le_abs_self (g z)).trans (hgD z))
      _ = ENNReal.ofReal D * P.kernelResolvent lam
          (fun _ : α => (1 : ℝ≥0∞)) y := by
        rw [show (fun _ : α => ENNReal.ofReal D) =
            (fun z : α => ENNReal.ofReal D * (1 : ℝ≥0∞)) by funext z; simp,
          (P.kernelResolvent_const_mul lam (ENNReal.ofReal D)
            (f := fun _ : α => (1 : ℝ≥0∞)) measurable_const y)]
      _ ≤ ENNReal.ofReal D * ENNReal.ofReal lam⁻¹ := by
        exact mul_le_mul_right (P.kernelResolvent_one_le hlam y) _
      _ = ENNReal.ofReal (D / lam) := by
        rw [← ENNReal.ofReal_mul hD0]
        congr 1
  have hEfin : ∀ y, E mu y ≠ ∞ := by
    intro y
    exact ne_of_lt (lt_of_le_of_lt (hEle y) ENNReal.ofReal_lt_top)
  have hEfinLam : ∀ y, E lam y ≠ ∞ := by
    intro y
    exact ne_of_lt (lt_of_le_of_lt (hEfle y) ENNReal.ofReal_lt_top)
  have hRnonneg : ∀ {r : ℝ} (hr : 0 < r) (q : α → ℝ)
      (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) (y : α),
      0 ≤ P.kernelResolventReal r q y := by
    intro r hr q hq hq0 y
    unfold SubMarkovKernelSemigroup.kernelResolventReal
    apply integral_nonneg
    intro t
    exact mul_nonneg (Real.exp_pos _).le
      (integral_nonneg_of_ae (Filter.Eventually.of_forall hq0))
  have hRpoint : ∀ y, P.kernelResolventReal mu g y = (E mu y).toReal := by
    intro y
    have h := congrArg ENNReal.toReal
      (aux_car_rn_continuous_version_ofReal_resolvent P hmu hg hgD hg0 y)
    rw [ENNReal.toReal_ofReal (hRnonneg hmu g hg hg0 y)] at h
    exact h
  have he : Measurable (fun y => (E mu y).toReal) := hEmeas.ennreal_toReal
  have heD : ∀ y, |(E mu y).toReal| ≤ D / mu := by
    intro y
    rw [abs_of_nonneg (ENNReal.toReal_nonneg)]
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hD0 hmu.le) (hEle y)
  have he0 : ∀ y, 0 ≤ (E mu y).toReal := fun y => ENNReal.toReal_nonneg
  have hcomp : ∀ y, E mu y = ENNReal.ofReal (P.kernelResolventReal mu g y) := by
    intro y
    rw [hRpoint y, ENNReal.ofReal_toReal (hEfin y)]
  have hcompfin : P.kernelResolvent lam (E mu) x ≠ ∞ := by
    have hbound : P.kernelResolvent lam (E mu) x ≤
        ENNReal.ofReal ((D / mu) / lam) := by
      calc
        P.kernelResolvent lam (E mu) x ≤
            P.kernelResolvent lam (fun _ : α => ENNReal.ofReal (D / mu)) x := by
          apply P.kernelResolvent_mono lam
          intro y
          simpa using hEle y
        _ = ENNReal.ofReal (D / mu) *
            P.kernelResolvent lam (fun _ : α => (1 : ℝ≥0∞)) x := by
          rw [show (fun _ : α => ENNReal.ofReal (D / mu)) =
              (fun z : α => ENNReal.ofReal (D / mu) * (1 : ℝ≥0∞)) by funext z; simp,
            (P.kernelResolvent_const_mul lam (ENNReal.ofReal (D / mu))
              (f := fun _ : α => (1 : ℝ≥0∞)) measurable_const x)]
        _ ≤ ENNReal.ofReal (D / mu) * ENNReal.ofReal lam⁻¹ := by
          exact mul_le_mul_right (P.kernelResolvent_one_le hlam x) _
        _ = ENNReal.ofReal ((D / mu) / lam) := by
          rw [← ENNReal.ofReal_mul (div_nonneg hD0 hmu.le)]
          congr 1
    exact ne_of_lt (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)
  have hcompR := congrArg ENNReal.toReal
    (aux_car_rn_continuous_version_ofReal_resolvent P hlam he heD he0 x)
  rw [ENNReal.toReal_ofReal (hRnonneg hlam (fun y => (E mu y).toReal) he he0 x)] at hcompR
  have hErepr : (fun y => ENNReal.ofReal (E mu y).toReal) = E mu := by
    funext y
    exact ENNReal.ofReal_toReal (hEfin y)
  rw [hErepr] at hcompR
  have hElammeas : Measurable (E lam) := by
    exact P.measurable_kernelResolvent lam (ENNReal.measurable_ofReal.comp hg)
  have heLam : Measurable (fun y => (E lam y).toReal) := hElammeas.ennreal_toReal
  have heLamD : ∀ y, |(E lam y).toReal| ≤ D / lam := by
    intro y
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hD0 hlam.le) (hEfle y)
  have heLam0 : ∀ y, 0 ≤ (E lam y).toReal := fun y => ENNReal.toReal_nonneg
  have hcompfinLam : P.kernelResolvent mu (E lam) x ≠ ∞ := by
    have hbound : P.kernelResolvent mu (E lam) x ≤
        ENNReal.ofReal ((D / lam) / mu) := by
      calc
        P.kernelResolvent mu (E lam) x ≤
            P.kernelResolvent mu (fun _ : α => ENNReal.ofReal (D / lam)) x := by
          apply P.kernelResolvent_mono mu
          intro y
          simpa using hEfle y
        _ = ENNReal.ofReal (D / lam) *
            P.kernelResolvent mu (fun _ : α => (1 : ℝ≥0∞)) x := by
          rw [show (fun _ : α => ENNReal.ofReal (D / lam)) =
              (fun z : α => ENNReal.ofReal (D / lam) * (1 : ℝ≥0∞)) by funext z; simp,
            (P.kernelResolvent_const_mul mu (ENNReal.ofReal (D / lam))
              (f := fun _ : α => (1 : ℝ≥0∞)) measurable_const x)]
        _ ≤ ENNReal.ofReal (D / lam) * ENNReal.ofReal mu⁻¹ := by
          exact mul_le_mul_right (P.kernelResolvent_one_le hmu x) _
        _ = ENNReal.ofReal ((D / lam) / mu) := by
          rw [← ENNReal.ofReal_mul (div_nonneg hD0 hlam.le)]
          congr 1
    exact ne_of_lt (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top)
  have hcompRlam := congrArg ENNReal.toReal
    (aux_car_rn_continuous_version_ofReal_resolvent P hmu heLam heLamD heLam0 x)
  rw [ENNReal.toReal_ofReal (hRnonneg hmu (fun y => (E lam y).toReal)
      heLam heLam0 x)] at hcompRlam
  have hEq := P.kernelResolvent_resolventEquation hlt
    (ENNReal.measurable_ofReal.comp hg) x
  have hEqR := congrArg ENNReal.toReal hEq
  change (E lam x).toReal =
    (E mu x + ENNReal.ofReal (mu - lam) * P.kernelResolvent lam (E mu) x).toReal at hEqR
  rw [ENNReal.toReal_add (hEfin x)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcompfin),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hlt.le)] at hEqR
  have hRlam := congrArg ENNReal.toReal
    (aux_car_rn_continuous_version_ofReal_resolvent P hlam hg hgD hg0 x)
  have hRmu := congrArg ENNReal.toReal
    (aux_car_rn_continuous_version_ofReal_resolvent P hmu hg hgD hg0 x)
  rw [ENNReal.toReal_ofReal (hRnonneg hlam g hg hg0 x)] at hRlam
  rw [ENNReal.toReal_ofReal (hRnonneg hmu g hg hg0 x)] at hRmu
  rw [← hcompR, ← hRlam, ← hRmu] at hEqR
  have hcomm := congrArg ENNReal.toReal
    (P.kernelResolvent_comm lam mu (ENNReal.measurable_ofReal.comp hg) x)
  change (P.kernelResolvent lam (P.kernelResolvent mu
      (fun z => ENNReal.ofReal (g z))) x).toReal =
    (P.kernelResolvent mu (P.kernelResolvent lam
      (fun z => ENNReal.ofReal (g z))) x).toReal at hcomm
  have hcomm' :
      P.kernelResolventReal lam (fun y => (E mu y).toReal) x =
        P.kernelResolventReal mu (fun y => (E lam y).toReal) x := by
    calc
      P.kernelResolventReal lam (fun y => (E mu y).toReal) x =
          (P.kernelResolvent lam (E mu) x).toReal := hcompR
      _ = (P.kernelResolvent mu (E lam) x).toReal := by
        simpa [E] using hcomm
      _ = P.kernelResolventReal mu (fun y => (E lam y).toReal) x := by
        have hEreprLam : (fun y => ENNReal.ofReal (E lam y).toReal) = E lam := by
          funext y
          exact ENNReal.ofReal_toReal (hEfinLam y)
        calc
          (P.kernelResolvent mu (E lam) x).toReal =
              (P.kernelResolvent mu
                (fun y => ENNReal.ofReal (E lam y).toReal) x).toReal :=
            congrArg ENNReal.toReal
              (congrArg (fun k => P.kernelResolvent mu k x) hEreprLam.symm)
          _ = P.kernelResolventReal mu (fun y => (E lam y).toReal) x :=
            hcompRlam.symm
  have hfun : (fun y => (E mu y).toReal) =
      (fun y => P.kernelResolventReal mu g y) := by
    funext y
    exact (hRpoint y).symm
  rw [hfun] at hEqR
  have hRpointLam : ∀ y, P.kernelResolventReal lam g y = (E lam y).toReal := by
    intro y
    have h := congrArg ENNReal.toReal
      (aux_car_rn_continuous_version_ofReal_resolvent P hlam hg hgD hg0 y)
    rw [ENNReal.toReal_ofReal (hRnonneg hlam g hg hg0 y)] at h
    exact h
  have hfunLam : (fun y => (E lam y).toReal) =
      (fun y => P.kernelResolventReal lam g y) := by
    funext y
    exact (hRpointLam y).symm
  rw [hfun, hfunLam] at hcomm'
  rw [hcomm'] at hEqR
  exact hEqR

theorem aux_car_rn_continuous_version_real_resolvent_nonneg_measurable
    {α : Type*} [MeasurableSpace α]
    (P : SubMarkovKernelSemigroup α) {lam : ℝ} (hlam : 0 < lam)
    {g : α → ℝ} (hg : Measurable g)
    {D : ℝ} (hgD : ∀ y, |g y| ≤ D) (hg0 : ∀ y, 0 ≤ g y) :
    Measurable (P.kernelResolventReal lam g) := by
  have hRnonneg : ∀ y, 0 ≤ P.kernelResolventReal lam g y := by
    intro y
    unfold SubMarkovKernelSemigroup.kernelResolventReal
    apply integral_nonneg
    intro t
    exact mul_nonneg (Real.exp_pos _).le
      (integral_nonneg_of_ae (Filter.Eventually.of_forall hg0))
  have hpoint : ∀ y, P.kernelResolventReal lam g y =
      (P.kernelResolvent lam (fun z => ENNReal.ofReal (g z)) y).toReal := by
    intro y
    have h := congrArg ENNReal.toReal
      (aux_car_rn_continuous_version_ofReal_resolvent P hlam hg hgD hg0 y)
    rw [ENNReal.toReal_ofReal (hRnonneg y)] at h
    exact h
  have hme : Measurable
      (fun y => (P.kernelResolvent lam (fun z => ENNReal.ofReal (g z)) y).toReal) :=
    (P.measurable_kernelResolvent lam (ENNReal.measurable_ofReal.comp hg)).ennreal_toReal
  have heq : P.kernelResolventReal lam g =
      (fun y => (P.kernelResolvent lam (fun z => ENNReal.ofReal (g z)) y).toReal) := by
    funext y
    exact hpoint y
  rw [heq]
  exact hme

theorem aux_car_rn_continuous_version_real_resolvent_measurable
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (P : SubMarkovKernelSemigroup α) {lam : ℝ} (hlam : 0 < lam)
    {f : α → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    Measurable (P.kernelResolventReal lam f) := by
  let y0 : α := Classical.choice (inferInstance : Nonempty α)
  have hD0 : 0 ≤ D := (abs_nonneg (f y0)).trans (hfD y0)
  let c : α → ℝ := fun _ => D
  have hc : Measurable c := measurable_const
  have hcD : ∀ y, |c y| ≤ D := by
    intro y
    simpa [c, abs_of_nonneg hD0]
  have hc0 : ∀ y, 0 ≤ c y := fun y => hD0
  have hplus : Measurable (f + c) := hf.add hc
  have hplus0 : ∀ y, 0 ≤ (f + c) y := by
    intro y
    have hfl : -D ≤ f y := neg_le_of_abs_le (hfD y)
    change 0 ≤ f y + D
    linarith
  have hplusD : ∀ y, |(f + c) y| ≤ 2 * D := by
    intro y
    calc
      |(f + c) y| ≤ |f y| + |c y| := abs_add_le _ _
      _ ≤ D + D := add_le_add (hfD y) (hcD y)
      _ = 2 * D := by ring
  have hplusm :=
    aux_car_rn_continuous_version_real_resolvent_nonneg_measurable
      P hlam hplus hplusD hplus0
  have hcm :=
    aux_car_rn_continuous_version_real_resolvent_nonneg_measurable
      P hlam hc hcD hc0
  have hadd := P.kernelResolventReal_add hlam hf hc hfD hcD
  have heq : P.kernelResolventReal lam f =
      P.kernelResolventReal lam (f + c) - P.kernelResolventReal lam c := by
    funext y
    have hy := congrFun hadd y
    change P.kernelResolventReal lam (f + c) y =
      P.kernelResolventReal lam f y + P.kernelResolventReal lam c y at hy
    change P.kernelResolventReal lam f y =
      P.kernelResolventReal lam (f + c) y - P.kernelResolventReal lam c y
    linarith
  rw [heq]
  exact hplusm.sub hcm

theorem aux_car_rn_continuous_version_real_resolvent_equation
    {α : Type*} [MeasurableSpace α]
    (P : SubMarkovKernelSemigroup α) {lam mu : ℝ} (hlam : 0 < lam)
    (hlt : lam < mu) {f : α → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : α) :
    P.kernelResolventReal lam f x =
      P.kernelResolventReal mu f x + (mu - lam) *
        P.kernelResolventReal mu (fun y => P.kernelResolventReal lam f y) x := by
  letI : Nonempty α := ⟨x⟩
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  let c : α → ℝ := fun _ => D
  have hc : Measurable c := measurable_const
  have hcD : ∀ y, |c y| ≤ D := by
    intro y
    simpa [c, abs_of_nonneg hD0]
  have hc0 : ∀ y, 0 ≤ c y := by
    intro y
    exact hD0
  have hplus : Measurable (f + c) := hf.add hc
  have hplus0 : ∀ y, 0 ≤ (f + c) y := by
    intro y
    have hf_lower : -D ≤ f y := neg_le_of_abs_le (hfD y)
    change 0 ≤ f y + D
    linarith
  have hplusD : ∀ y, |(f + c) y| ≤ 2 * D := by
    intro y
    calc
      |(f + c) y| ≤ |f y| + |c y| := abs_add_le _ _
      _ ≤ D + D := add_le_add (hfD y) (hcD y)
      _ = 2 * D := by ring
  have hconst_meas :=
    aux_car_rn_continuous_version_real_resolvent_nonneg_measurable
      P (show 0 < mu from hlam.trans hlt) hc hcD hc0
  have hplus_meas :=
    aux_car_rn_continuous_version_real_resolvent_nonneg_measurable
      P (show 0 < mu from hlam.trans hlt) hplus hplusD hplus0
  have hinner := P.kernelResolventReal_add (show 0 < mu from hlam.trans hlt)
      hf hc hfD hcD
  have hRmf_meas : Measurable (P.kernelResolventReal mu f) := by
    have heq : P.kernelResolventReal mu f =
        P.kernelResolventReal mu (f + c) - P.kernelResolventReal mu c := by
      funext y
      have hy := congrFun hinner y
      change P.kernelResolventReal mu (f + c) y =
        P.kernelResolventReal mu f y + P.kernelResolventReal mu c y at hy
      change P.kernelResolventReal mu f y =
        P.kernelResolventReal mu (f + c) y - P.kernelResolventReal mu c y
      linarith
    rw [heq]
    exact hplus_meas.sub hconst_meas
  have hRmc_meas : Measurable (P.kernelResolventReal mu c) := hconst_meas
  have hRmfD : ∀ y, |P.kernelResolventReal mu f y| ≤ D / mu := by
    intro y
    exact P.norm_kernelResolventReal_le (show 0 < mu from hlam.trans hlt) hfD y
  have hRmcD : ∀ y, |P.kernelResolventReal mu c y| ≤ D / mu := by
    intro y
    exact P.norm_kernelResolventReal_le (show 0 < mu from hlam.trans hlt) hcD y
  have hcompadd := P.kernelResolventReal_add hlam hRmf_meas hRmc_meas hRmfD hRmcD
  have hplusEq := aux_car_rn_continuous_version_real_resolvent_nonneg_equation
    P hlam hlt hplus hplusD hplus0 x
  have hcEq := aux_car_rn_continuous_version_real_resolvent_nonneg_equation
    P hlam hlt hc hcD hc0 x
  have hplusLam := congrFun (P.kernelResolventReal_add hlam hf hc hfD hcD) x
  have hplusMu := congrFun hinner x
  have hcompPoint : P.kernelResolventReal lam
        (fun y => P.kernelResolventReal mu (f + c) y) x =
      P.kernelResolventReal lam (fun y => P.kernelResolventReal mu f y) x +
        P.kernelResolventReal lam (fun y => P.kernelResolventReal mu c y) x := by
    have hfun : (fun y => P.kernelResolventReal mu (f + c) y) =
        (P.kernelResolventReal mu f + P.kernelResolventReal mu c) := by
      funext y
      exact congrFun hinner y
    rw [hfun]
    exact congrFun hcompadd x
  have hRlf_meas : Measurable (P.kernelResolventReal lam f) :=
    aux_car_rn_continuous_version_real_resolvent_measurable P hlam hf hfD
  have hRlc_meas : Measurable (P.kernelResolventReal lam c) :=
    aux_car_rn_continuous_version_real_resolvent_measurable P hlam hc hcD
  have hRlfD : ∀ y, |P.kernelResolventReal lam f y| ≤ D / lam := by
    intro y
    exact P.norm_kernelResolventReal_le hlam hfD y
  have hRlcD : ∀ y, |P.kernelResolventReal lam c y| ≤ D / lam := by
    intro y
    exact P.norm_kernelResolventReal_le hlam hcD y
  have hcompadd' := P.kernelResolventReal_add
    (show 0 < mu from hlam.trans hlt) hRlf_meas hRlc_meas hRlfD hRlcD
  have hcompPoint' : P.kernelResolventReal mu
        (fun y => P.kernelResolventReal lam (f + c) y) x =
      P.kernelResolventReal mu (fun y => P.kernelResolventReal lam f y) x +
        P.kernelResolventReal mu (fun y => P.kernelResolventReal lam c y) x := by
    have hfun : (fun y => P.kernelResolventReal lam (f + c) y) =
        (P.kernelResolventReal lam f + P.kernelResolventReal lam c) := by
      funext y
      exact congrFun (P.kernelResolventReal_add hlam hf hc hfD hcD) y
    rw [hfun]
    exact congrFun hcompadd' x
  change P.kernelResolventReal lam (f + c) x =
    P.kernelResolventReal lam f x + P.kernelResolventReal lam c x at hplusLam
  change P.kernelResolventReal mu (f + c) x =
    P.kernelResolventReal mu f x + P.kernelResolventReal mu c x at hplusMu
  rw [hcompPoint', hplusLam, hplusMu] at hplusEq
  linear_combination hplusEq - hcEq

theorem aux_car_rn_continuous_version_path_resolvent
    {d : ℕ} (law : Kernel (SpatialCoordinates d) (MarkovProcess.LifetimePath (SpatialCoordinates d)))
    [IsMarkovKernel law] (hSM : StrongMarkov law) (Q : Set (SpatialCoordinates d))
    (hQ : IsOpen Q) (K : Measure (DiffusionPath d)) [IsProbabilityMeasure K]
    (x : SpatialCoordinates d)
    (hmap : Measure.map LifetimePath.ofContinuousPath K = law x)
    {lam : ℝ} (hlam : 0 < lam) {g : SpatialCoordinates d → ℝ}
    (hg : Measurable g) {D : ℝ} (hgD : ∀ y, |g y| ≤ D) :
    (∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
        (fun s : ℝ => Real.exp (-lam * s) * g (path (Real.toNNReal s))) t) ∂K) =
      (killedSMKS law hSM Q hQ).kernelResolventReal lam g x := by
  let P := killedSMKS law hSM Q hQ
  have hfixed : ∀ t : ℝ, 0 < t →
      kernelIntegral (P (Real.toNNReal t)) (fun y => g y) x =
        ∫ path, (if ENNReal.ofReal t < ContinuousPath.exitTime Q path then
          g (path (Real.toNNReal t)) else 0) ∂K := by
    intro t ht
    have htNN : Real.toNNReal t ≠ 0 := (Real.toNNReal_pos.mpr ht).ne'
    dsimp [P, killedSMKS]
    change kernelIntegral (killedFamily law Q hQ (Real.toNNReal t))
      (fun y => g y) x = _
    rw [killedFamily_of_ne law Q hQ htNN]
    rw [killedKernel_integral_eq_pathTest law Q hQ (fun y => g y)
      hg t x]
    have hm := measurable_killedPathTest_function Q hQ (fun y => g y)
      hg t
    have hi := integral_map (μ := K)
      (φ := LifetimePath.ofContinuousPath)
      (f := fun path : MarkovProcess.LifetimePath (SpatialCoordinates d) =>
        if ENNReal.ofReal t < LifetimePath.exitTime Q path then
          g (position (Real.toNNReal t) path) else 0)
      LifetimePath.measurable_ofContinuousPath.aemeasurable hm.aestronglyMeasurable
    rw [hmap] at hi
    simpa [killedPathTest, LifetimePath.exitTime_ofContinuousPath,
      LifetimePath.coordinate_ofContinuousPath, position] using hi
  let F : ℝ × DiffusionPath d → ℝ := fun z =>
    Real.exp (-lam * z.1) *
      (if ENNReal.ofReal z.1 < ContinuousPath.exitTime Q z.2 then
        g (z.2 (Real.toNNReal z.1)) else 0)
  have hsurv : MeasurableSet {z : ℝ × DiffusionPath d |
      ENNReal.ofReal z.1 < ContinuousPath.exitTime Q z.2} := by
    exact measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
      ((ContinuousPath.measurable_exitTime Q hQ).comp measurable_snd)
  have hev : Measurable (fun z : ℝ × DiffusionPath d =>
      z.2 (Real.toNNReal z.1)) :=
    (continuous_eval.comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable
  have hF : Measurable F := by
    exact (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
      (Measurable.ite hsurv (hg.comp hev) measurable_const)
  have hD0 : 0 ≤ D := (abs_nonneg (g 0)).trans (hgD 0)
  have hbase : Integrable (fun z : ℝ × DiffusionPath d =>
      Real.exp (-lam * z.1))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod K) := by
    simpa only [one_mul] using
      (((exp_neg_integrableOn_Ioi 0 hlam).const_mul (1 : ℝ)).comp_fst K)
  have hbound : ∀ z : ℝ × DiffusionPath d, ‖F z‖ ≤
      Real.exp (-lam * z.1) * D := by
    intro z
    dsimp [F]
    by_cases hz : ENNReal.ofReal z.1 < ContinuousPath.exitTime Q z.2
    · rw [if_pos hz, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hgD _) (Real.exp_pos _).le
    · simp only [if_neg hz, mul_zero, abs_zero]
      exact mul_nonneg (Real.exp_pos _).le hD0
  have hswap : Integrable F
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod K) := by
    have hb := hbase.mul_const D
    exact hb.mono' hF.aestronglyMeasurable (Eventually.of_forall hbound)
  unfold SubMarkovKernelSemigroup.kernelResolventReal
  change (∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
        (fun s : ℝ => Real.exp (-lam * s) * g (path (Real.toNNReal s))) t) ∂K) =
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) (fun y => g y) x
  exact calc
      (∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
            (fun s : ℝ => Real.exp (-lam * s) * g (path (Real.toNNReal s))) t) ∂K) =
          ∫ path, (∫ t in Set.Ioi (0 : ℝ), F (t, path)) ∂K := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun path => by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          simp [F, Set.indicator]
      _ = ∫ t in Set.Ioi (0 : ℝ), ∫ path, F (t, path) ∂K :=
        (MeasureTheory.integral_integral_swap hswap).symm
      _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) *
          kernelIntegral (P (Real.toNNReal t)) (fun y => g y) x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hft := hfixed t ht
        dsimp [F]
        rw [integral_const_mul]
        exact congrArg (fun r : ℝ => Real.exp (-lam * t) * r) hft.symm

theorem aux_car_rn_continuous_version_resolvent_congr_of_ae
    {d : ℕ} (law : Kernel (SpatialCoordinates d) (MarkovProcess.LifetimePath (SpatialCoordinates d)))
    [IsMarkovKernel law] (hSM : StrongMarkov law) (Q : Set (SpatialCoordinates d))
    (hQ : IsOpen Q) (K : Measure (DiffusionPath d)) [IsProbabilityMeasure K]
    (x : SpatialCoordinates d)
    (hmap : Measure.map LifetimePath.ofContinuousPath K = law x)
    {lam : ℝ} (hlam : 0 < lam) {u v : SpatialCoordinates d → ℝ}
    (hu : Measurable u) (hv : Measurable v) {Du Dv : ℝ}
    (huD : ∀ y, |u y| ≤ Du) (hvD : ∀ y, |v y| ≤ Dv)
    (hae : u =ᵐ[volume.restrict Q] v)
    (hac : ∀ B : Set (SpatialCoordinates d), MeasurableSet B → volume B = 0 →
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-lam * t) * B.indicator (fun _ => (1 : ℝ))
          (path (Real.toNNReal t))) ∂K = 0) :
    (killedSMKS law hSM Q hQ).kernelResolventReal lam u x =
      (killedSMKS law hSM Q hQ).kernelResolventReal lam v x := by
  have hDu : 0 ≤ Du := (abs_nonneg (u 0)).trans (huD 0)
  have hDv : 0 ≤ Dv := (abs_nonneg (v 0)).trans (hvD 0)
  let B : Set (SpatialCoordinates d) := Q ∩ {y | u y ≠ v y}
  have hB : MeasurableSet B := by
    have hne : MeasurableSet {y : SpatialCoordinates d | u y ≠ v y} := by
      rw [show {y : SpatialCoordinates d | u y ≠ v y} =
          {y | u y < v y} ∪ {y | v y < u y} by
            ext y
            exact ne_iff_lt_or_gt]
      exact (measurableSet_lt hu hv).union (measurableSet_lt hv hu)
    exact hQ.measurableSet.inter hne
  have hBsub : B ⊆ Q := fun y hy => hy.1
  have hBzero_restrict : (volume.restrict Q) B = 0 := by
    have hAE : ∀ᵐ y ∂(volume.restrict Q), y ∉ B := by
      filter_upwards [hae] with y hy
      intro hyB
      exact hyB.2 hy
    have hzero := (ae_iff).mp hAE
    simpa only [Set.mem_setOf_eq, not_not] using! hzero
  have hBzero : volume B = 0 := by
    have h := hBzero_restrict
    rw [Measure.restrict_apply hB] at h
    have hBQ : B ∩ Q = B := by
      ext y
      constructor
      · exact fun hy => hy.1
      · intro hy
        exact ⟨hy, hBsub hy⟩
    rw [hBQ] at h
    exact h
  let A : DiffusionPath d × ℝ → ℝ := fun z =>
    Real.exp (-lam * z.2) * B.indicator (fun _ => (1 : ℝ))
      (z.1 (Real.toNNReal z.2))
  have hA : Measurable A := by
    have hev : Measurable (fun z : DiffusionPath d × ℝ =>
        z.1 (Real.toNNReal z.2)) :=
      (continuous_eval.comp
        (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
    exact (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
      ((measurable_const.indicator hB).comp hev)
  have hAbase : Integrable (fun z : DiffusionPath d × ℝ =>
      Real.exp (-lam * z.2))
      (K.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    simpa only [one_mul] using
      (((exp_neg_integrableOn_Ioi 0 hlam).const_mul (1 : ℝ)).comp_snd K)
  have hAbound : ∀ z, ‖A z‖ ≤ Real.exp (-lam * z.2) := by
    intro z
    dsimp [A]
    by_cases hz : z.1 (Real.toNNReal z.2) ∈ B
    · simp [Set.indicator_of_mem hz, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    · simp [Set.indicator_of_notMem hz]
      positivity
  have hAint : Integrable A (K.prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
    hAbase.mono' hA.aestronglyMeasurable (Eventually.of_forall hAbound)
  have hAnonneg : 0 ≤ᵐ[K.prod (volume.restrict (Set.Ioi (0 : ℝ)))] A := by
    filter_upwards [] with z
    dsimp [A]
    exact mul_nonneg (Real.exp_pos _).le (by
      by_cases hz : z.1 (Real.toNNReal z.2) ∈ B <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz])
  have hAfull : (∫ z, A z ∂(K.prod (volume.restrict (Set.Ioi (0 : ℝ))))) = 0 := by
    rw [MeasureTheory.integral_prod A hAint]
    exact hac B hB hBzero
  have hAae : A =ᵐ[K.prod (volume.restrict (Set.Ioi (0 : ℝ)))] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hAnonneg hAint).mp hAfull
  let Fu : DiffusionPath d × ℝ → ℝ := fun z =>
    if ENNReal.ofReal z.2 < ContinuousPath.exitTime Q z.1 then
      Real.exp (-lam * z.2) * u (z.1 (Real.toNNReal z.2)) else 0
  let Fv : DiffusionPath d × ℝ → ℝ := fun z =>
    if ENNReal.ofReal z.2 < ContinuousPath.exitTime Q z.1 then
      Real.exp (-lam * z.2) * v (z.1 (Real.toNNReal z.2)) else 0
  have hsurv : MeasurableSet {z : DiffusionPath d × ℝ |
      ENNReal.ofReal z.2 < ContinuousPath.exitTime Q z.1} := by
    exact measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
      ((ContinuousPath.measurable_exitTime Q hQ).comp measurable_fst)
  have hev : Measurable (fun z : DiffusionPath d × ℝ =>
      z.1 (Real.toNNReal z.2)) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hFum : Measurable Fu := by
    exact Measurable.ite hsurv
      ((Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
        (hu.comp hev)) measurable_const
  have hFvm : Measurable Fv := by
    exact Measurable.ite hsurv
      ((Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
        (hv.comp hev)) measurable_const
  have hFub : ∀ z, ‖Fu z‖ ≤ Real.exp (-lam * z.2) * Du := by
    intro z
    by_cases hz : ENNReal.ofReal z.2 < ContinuousPath.exitTime Q z.1
    · dsimp [Fu]
      rw [if_pos hz, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (huD _) (Real.exp_pos _).le
    · simp [Fu, hz]
      exact mul_nonneg (Real.exp_pos _).le hDu
  have hFvb : ∀ z, ‖Fv z‖ ≤ Real.exp (-lam * z.2) * Dv := by
    intro z
    by_cases hz : ENNReal.ofReal z.2 < ContinuousPath.exitTime Q z.1
    · dsimp [Fv]
      rw [if_pos hz, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hvD _) (Real.exp_pos _).le
    · simp [Fv, hz]
      exact mul_nonneg (Real.exp_pos _).le hDv
  have hFuint : Integrable Fu (K.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    exact (hAbase.mul_const Du).mono' hFum.aestronglyMeasurable
      (Eventually.of_forall hFub)
  have hFvint : Integrable Fv (K.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    exact (hAbase.mul_const Dv).mono' hFvm.aestronglyMeasurable
      (Eventually.of_forall hFvb)
  let Hdiff : DiffusionPath d × ℝ → ℝ := fun z => Fu z - Fv z
  have hHdiff_ae : Hdiff =ᵐ[K.prod (volume.restrict (Set.Ioi (0 : ℝ)))] 0 := by
    filter_upwards [hAae] with z hz
    by_cases hs : ENNReal.ofReal z.2 < ContinuousPath.exitTime Q z.1
    · have hmem : z.1 (Real.toNNReal z.2) ∈ Q := by
        apply ContinuousPath.mem_of_lt_exitTime Q z.1 (Real.toNNReal z.2)
        simpa only [show ((Real.toNNReal z.2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal z.2 from rfl]
          using hs
      have hnotB : z.1 (Real.toNNReal z.2) ∉ B := by
        intro hzB
        have hzA : Real.exp (-lam * z.2) = 0 := by
          have := hz
          dsimp [A] at this
          rw [Set.indicator_of_mem hzB] at this
          simpa using this
        exact (ne_of_gt (Real.exp_pos _)) hzA
      have huv : u (z.1 (Real.toNNReal z.2)) =
          v (z.1 (Real.toNNReal z.2)) := by
        by_contra hne
        exact hnotB ⟨hmem, hne⟩
      simp [Hdiff, Fu, Fv, hs, huv]
    · simp [Hdiff, Fu, Fv, hs]
  have hHbound : ∀ z, ‖Hdiff z‖ ≤
      Real.exp (-lam * z.2) * (Du + Dv) := by
    intro z
    exact (norm_sub_le _ _).trans ((add_le_add (hFub z) (hFvb z)).trans (by rw [mul_add]))
  have hHint : Integrable Hdiff (K.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    exact (hAbase.mul_const (Du + Dv)).mono' ((hFum.sub hFvm).aestronglyMeasurable)
      (Eventually.of_forall hHbound)
  have hHfull : ∫ z, Hdiff z ∂(K.prod (volume.restrict (Set.Ioi (0 : ℝ)))) = 0 :=
    integral_eq_zero_of_ae hHdiff_ae
  have hFuFv : (∫ path, (∫ t in Set.Ioi (0 : ℝ), Fu (path, t)) ∂K) =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ), Fv (path, t)) ∂K := by
    rw [← MeasureTheory.integral_prod Fu hFuint,
      ← MeasureTheory.integral_prod Fv hFvint]
    have hsub := integral_sub hFuint hFvint
    have hz : (∫ z, Fu z ∂(K.prod (volume.restrict (Set.Ioi (0 : ℝ)))) -
        ∫ z, Fv z ∂(K.prod (volume.restrict (Set.Ioi (0 : ℝ))))) = 0 := by
      rw [← hsub]
      simpa [Hdiff] using hHfull
    linarith
  have hbridgeu := aux_car_rn_continuous_version_path_resolvent
    law hSM Q hQ K x hmap hlam hu huD
  have hbridgev := aux_car_rn_continuous_version_path_resolvent
    law hSM Q hQ K x hmap hlam hv hvD
  calc
    (killedSMKS law hSM Q hQ).kernelResolventReal lam u x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
            (fun s => Real.exp (-lam * s) * u (path (Real.toNNReal s))) t) ∂K := hbridgeu.symm
    _ = ∫ path, (∫ t in Set.Ioi (0 : ℝ), Fu (path, t)) ∂K := by
      apply integral_congr_ae
      exact Eventually.of_forall fun path => by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp [Fu, Set.indicator]
    _ = ∫ path, (∫ t in Set.Ioi (0 : ℝ), Fv (path, t)) ∂K := hFuFv
    _ = ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
            (fun s => Real.exp (-lam * s) * v (path (Real.toNNReal s))) t) ∂K := by
      apply integral_congr_ae
      exact Eventually.of_forall fun path => by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simp [Fv, Set.indicator]
    _ = (killedSMKS law hSM Q hQ).kernelResolventReal lam v x := hbridgev

/-- **(RPT) Pointwise identification of the killed resolvent with its continuous version.**
Given (RAC), the pathwise killed resolvent `RN` of any bounded continuous `f` agrees at EVERY interior
point of the cube with any function `U` continuous on the closed cube that agrees with it a.e. on the cube.
Truth: the killed resolvent equation `R^Q_λ f = R^Q_{λ+μ} f + μ R^Q_{λ+μ} (R^Q_λ f)` (Markov property at
fixed times, `LocalInput`'s `StrongMarkov`, `τ ∘ θ_t = τ - t` on `{t < τ}`); (RAC) (killed ≤ unkilled
occupation) lets `R^Q_λ f` be replaced by `U` inside `R^Q_{λ+μ}`; then `|R^Q_{λ+μ} f| ≤ ‖f‖/(λ+μ) → 0` and
`μ R^Q_{λ+μ} U (x) → U x` as `μ → ∞` (paths start at `x ∈ Q` open and are continuous, `U` is continuous and
bounded on the compact closure). The frontier is separate (`RN = 0` there by `exitTime = 0`). -/
theorem car_rn_continuous_version
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN)
    (hinput : aux_cutoff_lifetime_package_LocalInput M H KN)
    (hac : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (mu : ℝ), 0 < mu →
      ∀ (x : SpatialCoordinates d) (B : Set (SpatialCoordinates d)),
        MeasurableSet B → volume B = 0 →
          ∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Real.exp (-mu * t) * B.indicator (fun _ => (1 : ℝ)) (path (Real.toNNReal t)))
            ∂(KN N (omega, x)) = 0)
    (Qtri : ℕ → Homogenization.TriadicCube d)
    (hr : ∀ n : ℕ, 0 < Homogenization.cubeScaleFactor (Qtri n))
    (RN : ℕ → ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (Homogenization.cubeCenter (Qtri n))
                (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (n N : ℕ) (lam : ℝ), 0 < lam →
      ∀ (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (U : SpatialCoordinates d → ℝ),
        ContinuousOn U (closure (centeredCube (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d))) →
        (RN n N omega lam f =ᵐ[volume.restrict (centeredCube (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d))] U) →
        ∀ x ∈ (centeredCube (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)),
          RN n N omega lam f x = U x := by
  obtain ⟨L, hL, hLlocal, hLstrong⟩ :=
    aux_cutoff_lifetime_package_local M H KN hinput
  filter_upwards [hLstrong, hac] with omega hSMall hacω
  intro n N lam hlam f U hU hae x hx
  let Q : Set (SpatialCoordinates d) :=
    centeredCube (Homogenization.cubeCenter (Qtri n))
      (Homogenization.cubeScaleFactor (Qtri n)) (hr n)
  have hQ : IsOpen Q := by
    exact (centeredCube (Homogenization.cubeCenter (Qtri n))
      (Homogenization.cubeScaleFactor (Qtri n)) (hr n)).isOpen
  have hUQ : ContinuousOn U (closure Q) := by
    simpa [Q] using hU
  have hQsub : closure Q ⊆ Metric.closedBall
      (Homogenization.cubeCenter (Qtri n))
      (Homogenization.cubeScaleFactor (Qtri n) / 2) := by
    apply closure_minimal
    · simpa [Q, centeredCube] using
        (Metric.ball_subset_closedBall : Metric.ball
          (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n) / 2) ⊆ _)
    · exact Metric.isClosed_closedBall
  have hQcompact : IsCompact (closure Q) := by
    exact (isCompact_closedBall (Homogenization.cubeCenter (Qtri n))
      (Homogenization.cubeScaleFactor (Qtri n) / 2)).of_isClosed_subset
        isClosed_closure hQsub
  letI : CompactSpace (closure Q) := isCompact_iff_compactSpace.mp hQcompact
  let uC : C(closure Q, ℝ) :=
    ⟨fun z => U z, continuousOn_iff_continuous_restrict.mp hUQ⟩
  let uB : BoundedContinuousFunction (closure Q) ℝ :=
    BoundedContinuousFunction.mkOfCompact uC
  obtain ⟨g, hgrest⟩ :=
    uB.exists_norm_eq_restrict_eq_of_closed isClosed_closure
  have hgU : ∀ y ∈ closure Q, g y = U y := by
    intro y hy
    have hz := congrArg (fun v : BoundedContinuousFunction (closure Q) ℝ => v ⟨y, hy⟩)
      hgrest.2
    exact hz
  have hKprob : IsProbabilityMeasure (KN N (omega, x)) := by
    infer_instance
  letI : IsMarkovKernel (L N omega) := ⟨fun y => ⟨(hSMall N).1 y⟩⟩
  have hRN_eq : ∀ y : SpatialCoordinates d,
      RN n N omega lam f y =
        (killedSMKS (L N omega) (hSMall N) Q hQ).kernelResolventReal lam
          (fun z => f z) y := by
    intro y
    rw [hRN_formula n N omega lam f y]
    exact aux_car_rn_continuous_version_path_resolvent
      (L N omega) (hSMall N) Q hQ (KN N (omega, y)) y
      (hL N omega y) hlam f.continuous.measurable
      (fun z => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm z)
  have hAEg :
      (fun y => (killedSMKS (L N omega) (hSMall N) Q hQ).kernelResolventReal lam
        (fun z => f z) y) =ᵐ[volume.restrict Q] g := by
    filter_upwards [hae, self_mem_ae_restrict hQ.measurableSet] with y hy hyQ
    rw [← hRN_eq y]
    exact hy.trans (hgU y (subset_closure hyQ)).symm
  let P := killedSMKS (L N omega) (hSMall N) Q hQ
  have hfD : ∀ y, |f y| ≤ ‖f‖ := by
    intro y
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm y
  have hgD : ∀ y, |g y| ≤ ‖g‖ := by
    intro y
    simpa [Real.norm_eq_abs] using g.norm_coe_le_norm y
  have hRlammeas : Measurable (P.kernelResolventReal lam (fun z => f z)) := by
    exact aux_car_rn_continuous_version_real_resolvent_measurable
      P hlam f.continuous.measurable hfD
  have hreplace : ∀ mu : ℝ, lam < mu →
      P.kernelResolventReal mu (fun y => P.kernelResolventReal lam (fun z => f z) y) x =
        P.kernelResolventReal mu (fun y => g y) x := by
    intro mu hlt
    have hmu : 0 < mu := hlam.trans hlt
    have hRlamD : ∀ y, |P.kernelResolventReal lam (fun z => f z) y| ≤
        ‖f‖ / lam := by
      intro y
      exact P.norm_kernelResolventReal_le hlam hfD y
    have hRlamG : Measurable (fun y => P.kernelResolventReal lam (fun z => f z) y) :=
      hRlammeas
    have hKNprob : IsProbabilityMeasure (KN N (omega, x)) := hKprob
    exact aux_car_rn_continuous_version_resolvent_congr_of_ae
      (L N omega) (hSMall N) Q hQ (KN N (omega, x)) x (hL N omega x)
      hmu hRlamG g.measurable hRlamD hgD hAEg
      (fun B hB hBzero => hacω N mu hmu x B hB hBzero)
  have heq : ∀ mu : ℝ, lam < mu →
      P.kernelResolventReal lam (fun z => f z) x =
        P.kernelResolventReal mu (fun z => f z) x + (mu - lam) *
          P.kernelResolventReal mu
            (fun y => P.kernelResolventReal lam (fun z => f z) y) x := by
    intro mu hlt
    simpa [P] using
      (aux_car_rn_continuous_version_real_resolvent_equation
        P hlam hlt f.continuous.measurable hfD x)
  have hfirst : Tendsto
      (fun mu : ℝ => P.kernelResolventReal mu (fun z => f z) x)
      atTop (nhds 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with mu hmu
      simpa [Real.norm_eq_abs] using P.norm_kernelResolventReal_le hmu hfD x
    · exact tendsto_const_nhds.div_atTop tendsto_id
  let F : ℝ → ℝ := fun t =>
    kernelIntegral (P (Real.toNNReal t)) (fun y => g y) x
  have hFmeas : Measurable F := by
    exact (P.measurable_kernelIntegral g.measurable).comp
      (measurable_real_toNNReal.prodMk measurable_const)
  have hFD : ∀ t, 0 < t → |F t| ≤ ‖g‖ := by
    intro t ht
    exact aux_car_rn_continuous_version_kernel_bound P hgD (Real.toNNReal t) x
  have hFzero : F 0 = g x := by
    change kernelIntegral (P (Real.toNNReal 0)) (fun y => g y) x = g x
    dsimp [P, killedSMKS]
    rw [Real.toNNReal_zero, killedFamily_zero]
    unfold kernelIntegral
    rw [Kernel.id_apply]
    simp
  have hF0 : ContinuousWithinAt F (Set.Ici (0 : ℝ)) 0 := by
    have hKzero : kernelIntegral
        (killedKernel (L N omega) Q hQ 0) g x = g x :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.goodCube_killedKernel_integral_zero_of_start
        (L N omega) (hSMall N) Q hQ g g.continuous.measurable hx
    have hcont := continuousWithinAt_killedKernel_integral
      (L N omega) Q hQ g x 0
    change Tendsto (fun r : ℝ => kernelIntegral
        (killedKernel (L N omega) Q hQ (Real.toNNReal r)) g x)
        (nhdsWithin (0 : ℝ) (Set.Ici 0))
        (nhds (kernelIntegral (killedKernel (L N omega) Q hQ (Real.toNNReal 0)) g x)) at hcont
    rw [Real.toNNReal_zero, hKzero] at hcont
    have hcont' : Tendsto
        (fun r : ℝ => kernelIntegral
          (killedKernel (L N omega) Q hQ (Real.toNNReal r)) g x)
        (nhdsWithin (0 : ℝ) (Set.Ici 0)) (nhds (g x)) := by
      exact hcont
    have heq : (fun r : ℝ => F r) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)]
        (fun r : ℝ => kernelIntegral
          (killedKernel (L N omega) Q hQ (Real.toNNReal r)) g x) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : 0 ≤ r := hr
      rcases eq_or_lt_of_le hr0 with rfl | hr
      · have hKzero' :
            kernelIntegral (killedKernel (L N omega) Q hQ (Real.toNNReal 0)) g x = g x := by
          simpa only [Real.toNNReal_zero] using hKzero
        exact hFzero.trans hKzero'.symm
      · have hrnn : Real.toNNReal r ≠ 0 := (Real.toNNReal_pos.mpr hr).ne'
        change kernelIntegral (P (Real.toNNReal r)) (fun y => g y) x = _
        dsimp [P, killedSMKS]
        rw [killedFamily_of_ne (L N omega) Q hQ hrnn]
    change Tendsto F (nhdsWithin (0 : ℝ) (Set.Ici 0)) (nhds (F 0))
    rw [hFzero]
    exact hcont'.congr' heq.symm
  have habel := aux_car_rn_continuous_version_abel hFmeas
    (norm_nonneg g) hFD hF0
  have hmuR : Tendsto
      (fun mu : ℝ => mu * P.kernelResolventReal mu (fun y => g y) x)
      atTop (nhds (g x)) := by
    simpa [F, hFzero, SubMarkovKernelSemigroup.kernelResolventReal] using habel
  have hfactor : Tendsto (fun mu : ℝ => (mu - lam) / mu)
      atTop (nhds (1 : ℝ)) := by
    have hdiv : Tendsto (fun mu : ℝ => lam / mu) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hsub : Tendsto (fun mu : ℝ => (1 : ℝ) - lam / mu)
        atTop (nhds ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hdiv
    have heq : (fun mu : ℝ => (mu - lam) / mu) =ᶠ[atTop]
        (fun mu : ℝ => 1 - lam / mu) := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with mu hmu
      field_simp
    simpa only [sub_zero] using hsub.congr' heq.symm
  have hsecond : Tendsto
      (fun mu : ℝ => (mu - lam) * P.kernelResolventReal mu
        (fun y => g y) x) atTop (nhds (g x)) := by
    have hprod := hfactor.mul hmuR
    have heq : (fun mu : ℝ => (mu - lam) * P.kernelResolventReal mu
        (fun y => g y) x) =ᶠ[atTop]
        (fun mu : ℝ => ((mu - lam) / mu) *
          (mu * P.kernelResolventReal mu (fun y => g y) x)) := by
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with mu hmu
      field_simp
    simpa only [one_mul] using hprod.congr' heq.symm
  have hRlim : P.kernelResolventReal lam (fun z => f z) x = g x := by
    have hsum : Tendsto
        (fun mu : ℝ => P.kernelResolventReal mu (fun z => f z) x +
          (mu - lam) * P.kernelResolventReal mu
            (fun y => P.kernelResolventReal lam (fun z => f z) y) x)
        atTop (nhds (g x)) := by
      have hcomp : Tendsto
          (fun mu : ℝ => (mu - lam) * P.kernelResolventReal mu
            (fun y => P.kernelResolventReal lam (fun z => f z) y) x)
          atTop (nhds (g x)) := by
        refine hsecond.congr' ?_
        filter_upwards [eventually_gt_atTop lam] with mu hmu
        rw [hreplace mu hmu]
      simpa only [zero_add] using hfirst.add hcomp
    have hconst : Tendsto
        (fun _ : ℝ => P.kernelResolventReal lam (fun z => f z) x)
        atTop (nhds (P.kernelResolventReal lam (fun z => f z) x)) :=
      tendsto_const_nhds
    have heq' : (fun mu : ℝ => P.kernelResolventReal mu (fun z => f z) x +
          (mu - lam) * P.kernelResolventReal mu
            (fun y => P.kernelResolventReal lam (fun z => f z) y) x) =ᶠ[atTop]
        (fun _ : ℝ => P.kernelResolventReal lam (fun z => f z) x) := by
      filter_upwards [eventually_gt_atTop lam] with mu hmu
      exact (heq mu hmu).symm
    have hconst' := hconst.congr' heq'.symm
    exact tendsto_nhds_unique hconst' hsum
  rw [hRN_eq x, hRlim, hgU x (subset_closure hx)]

end Paper
