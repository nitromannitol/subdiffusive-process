module

public import Mathlib
public import SubdiffusiveProcess.Paper.lim_thm_measure
public import SubdiffusiveProcess.Section10.KilledSobolev
public import SubdiffusiveProcess.Paper.tight_subharmonic
public import SubdiffusiveProcess.Section10.KilledSobolevMomentEnergy
public import SubdiffusiveProcess.Paper.tight_static
public import SubdiffusiveProcess.Paper.lfsgs_response_bank
public import SubdiffusiveProcess.Paper.inputs_J_witness
public import SubdiffusiveProcess.Paper.inputs_poincare_witness
public import SubdiffusiveProcess.Paper.inputs_Sf_witness
public import SubdiffusiveProcess.Assumptions.CoefficientRegularity
public import SubdiffusiveProcess.Processes.CutoffResolventUniqueness
public import SubdiffusiveProcess.Section10.TransitionPassage
public import SubdiffusiveProcess.Section10.TorsionExitPointwise
public import SubdiffusiveProcess.Section10.TransitionFinalPassage
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
public import SubdiffusiveProcess.Model.LifetimeProcess
public import SubdiffusiveProcess.Paper.classical_weighted_nash_ultracontractivity
public import SubdiffusiveProcess.Section10.ClassicalNashConsumer
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastScalarBridge
public import SubdiffusiveProcess.Section10.TransitionMetric
public import SubdiffusiveProcess.Section10.GaussianLawApplicationsProjections
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierGrowth

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Paper

/-- Convergence of the quenched path laws `K_{N,x}^ω → K_x^ω` locally uniformly in `x`, almost surely
(Theorem A(i), `eq:mfd-main-as`), for the rescaled cutoff path kernels `KN` attached to `in_crossing`.
`K` is the limit kernel of Theorem A (the process `Z`). -/
def aux_lim_thm_nongaussian_QuenchedConv {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) : Prop :=
  ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
    ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
        pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K hK omega x) < epsilon


section KilledSobolevApplication


/-! First actual application of B1, on a fixed unit cube inside the side-four
reference cube. General-p trace and padded coercivity are discharged by their
existing exports. This is an internal deterministic application, with no
process, environment or new source assumption. -/

open MeasureTheory Set Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open scoped ENNReal


lemma aux_lim_thm_nongaussian_killed_sobolev_trace_supplier {d : ℕ} (hd : 2 ≤ d)
    {r0 : ℝ} (hr0 : 0 < r0) :
    ∃ C : ℝ, 0 < C ∧ KilledTraceBound d r0 C := by
  obtain ⟨C, hC, htrace⟩ := aux_tight_subharmonic_aux_trace_Lp d (1 / 2) (3 / 4)
    (killedSobolevExponent d) r0 (killedSobolevExponent_ge_two hd)
    (by norm_num) hr0 (killedSobolev_trace_margin hd)
  refine ⟨C, hC, ?_⟩
  intro V ν Km hKm hfin hV hac hsupp hgrowth f hfm hfL
  simpa only [killedFractionalEnergy, show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num] using
    htrace V ν Km hKm hfin hV hac hsupp hgrowth f hfm hfL

/-- All-H10 deterministic B1 on arbitrary measurable domains inside an open
padded domain. The trace constant is fixed before the measure and coefficients;
the general-p trace premise is discharged by its actual proved supplier. -/
theorem aux_lim_thm_nongaussian_killed_sobolev_of_padded_coercivity {d : ℕ} (hd : 2 ≤ d)
    {r0 : ℝ} (hr0 : 0 < r0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U V : Set (SpatialCoordinates d)),
      MeasurableSet U → IsOpen V → U ⊆ V →
      ∀ (μ : Measure (SpatialCoordinates d)), μ ≪ volume →
      ∀ [IsFiniteMeasure (μ.restrict U)] (Km Kc : ℝ), 0 < Km → 0 ≤ Kc →
      (μ.restrict U) {x | ¬ Metric.closedBall x r0 ⊆ V} = 0 →
      (∀ y ∈ V, ∀ r : ℝ, 0 < r → r ≤ r0 →
        (μ.restrict U) (Metric.ball y r) ≤ ENNReal.ofReal (Km * r ^ ((d : ℝ) - 1 / 2))) →
      ∀ A : SpatialCoordinates d → ℝ,
      (∀ w : H10Function V,
        killedFractionalEnergy V w.toFun + ∫⁻ x in V, ENNReal.ofReal (w.toFun x ^ 2) ≤
          ENNReal.ofReal Kc * killedCoefficientEnergy A w.toH1Function) →
      ∀ v : H10Function U,
        eLpNorm v.toFun (ENNReal.ofReal (killedSobolevExponent d)) (μ.restrict U) ^ 2 ≤
          ENNReal.ofReal (killedSobolevConstant d r0 C Km ((μ.restrict U) univ).toReal Kc) *
            killedCoefficientEnergy A v.toH1Function := by
  obtain ⟨C, hC, htrace⟩ := aux_lim_thm_nongaussian_killed_sobolev_trace_supplier hd hr0
  refine ⟨C, hC, ?_⟩
  intro U V hU hV hUV μ hμ inst Km Kc hKm hKc hsupp hgrowth A hcoer v
  exact killed_sobolev_all_h10 hd hU hV hUV μ hμ hr0 hC.le hKm hKc
    htrace hsupp hgrowth A hcoer v



end KilledSobolevApplication

section TransitionSobolevExhaustionDeterministic


/-! The existing padded-domain Sobolev supplier on arbitrary exhaustion
balls. A finite cover controls total mass using the supplied small-ball bound. -/

open MeasureTheory Set Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal


theorem aux_lim_thm_nongaussian_transition_sobolev_exhaustion_deterministic {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b A : SpatialCoordinates d → ℝ) (K : ℝ), 1 ≤ K →
      (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (2 * ((n : ℝ) + 2)),
        ∀ r : ℝ, 0 < r → r ≤ 1 →
          weightedMeasure b (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2))) →
      (∀ w : H10Function (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 2)),
        killedFractionalEnergy (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 2)) w.toFun +
          ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 2),
            ENNReal.ofReal (w.toFun x ^ 2) ≤
        ENNReal.ofReal (K * (2 : ℝ) ^ (5 : ℝ)) * killedCoefficientEnergy A w.toH1Function) →
      CoefficientOn (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) A →
      KilledSobolevBound (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) b A
        (D * K ^ 2) := by
  classical
  obtain ⟨C, hC, hSob⟩ := aux_lim_thm_nongaussian_killed_sobolev_of_padded_coercivity hd
    (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨centers, hcsub, hcfin, hcover⟩ :=
    (isCompact_closedBall (0 : SpatialCoordinates d) ((n : ℝ) + 1)).finite_cover_balls
      (by norm_num : (0 : ℝ) < 1)
  let F := hcfin.toFinset
  let a : ℝ := F.card + 1
  have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) F.card]
  let D : ℝ := (C * (1 + (1 / 4 : ℝ) ^ (-((d : ℝ) / 2)))) ^ 2 *
    (2 : ℝ) ^ (5 : ℝ) * a ^ 2 + 1
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro b A K hK hmass hcoer hA
  let μ := weightedMeasure b
  let U : Set (SpatialCoordinates d) := Metric.ball 0 ((n : ℝ) + 1)
  let V : Set (SpatialCoordinates d) := Metric.ball 0 ((n : ℝ) + 2)
  have hKm : 1 ≤ a * K := hK.trans (le_mul_of_one_le_left (zero_le_one.trans hK) ha)
  have hmassLe : μ U ≤ ENNReal.ofReal (a * K) := by
    have hcov : U ⊆ ⋃ x ∈ F, Metric.ball x (1 : ℝ) := by
      simpa only [U, F, Set.Finite.mem_toFinset] using Metric.ball_subset_closedBall.trans hcover
    calc
      μ U ≤ μ (⋃ x ∈ F, Metric.ball x (1 : ℝ)) := measure_mono hcov
      _ ≤ ∑ x ∈ F, μ (Metric.ball x (1 : ℝ)) := measure_biUnion_finset_le _ _
      _ ≤ ∑ x ∈ F, ENNReal.ofReal K := by
        apply Finset.sum_le_sum
        intro x hx
        have hxC : x ∈ Metric.closedBall (0 : SpatialCoordinates d) ((n : ℝ) + 1) :=
          hcsub (hcfin.mem_toFinset.mp hx)
        have hxR : x ∈ Metric.ball (0 : SpatialCoordinates d) (2 * ((n : ℝ) + 2)) := by
          change dist x 0 < _
          have hh : dist x 0 ≤ (n : ℝ) + 1 := hxC
          linarith [Nat.cast_nonneg (α := ℝ) n]
        simpa only [Real.one_rpow, mul_one] using hmass x hxR 1 zero_lt_one le_rfl
      _ = ENNReal.ofReal ((F.card : ℝ) * K) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp
      _ ≤ ENNReal.ofReal (a * K) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by dsimp [a]; linarith) (zero_le_one.trans hK))
  letI : IsFiniteMeasure (μ.restrict U) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hmassLe.trans_lt ENNReal.ofReal_lt_top⟩
  have hm : ((μ.restrict U) univ).toReal ≤ a * K := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmassLe
    simpa only [Measure.restrict_apply_univ, ENNReal.toReal_ofReal (zero_le_one.trans hKm)] using hh
  have hsupp : (μ.restrict U) {x | ¬ Metric.closedBall x (1 / 4) ⊆ V} = 0 := by
    apply measure_mono_null (t := Uᶜ)
    · intro x hx hxU
      apply hx
      intro y hy
      have hx0 : dist x (0 : SpatialCoordinates d) < (n : ℝ) + 1 := hxU
      have hyx : dist y x ≤ 1 / 4 := hy
      change dist y 0 < (n : ℝ) + 2
      linarith [dist_triangle y x (0 : SpatialCoordinates d)]
    · rw [Measure.restrict_apply measurableSet_ball.compl, compl_inter_self, measure_empty]
  have hgrowth : ∀ y ∈ V, ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      (μ.restrict U) (Metric.ball y r) ≤ ENNReal.ofReal (a * K * r ^ ((d : ℝ) - 1 / 2)) := by
    intro y hy r hr hr0
    have hyR : y ∈ Metric.ball (0 : SpatialCoordinates d) (2 * ((n : ℝ) + 2)) := by
      apply Metric.ball_subset_ball _ hy
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (Measure.restrict_le_self (μ := μ) (s := U) _).trans ((hmass y hyR r hr (by linarith)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left (zero_le_one.trans hK) ha) (Real.rpow_nonneg hr.le _))))
  have hcoer' : ∀ w : H10Function V,
      killedFractionalEnergy V w.toFun + ∫⁻ x in V, ENNReal.ofReal (w.toFun x ^ 2) ≤
        ENNReal.ofReal (a * K * (2 : ℝ) ^ (5 : ℝ)) * killedCoefficientEnergy A w.toH1Function := by
    intro w
    exact (hcoer w).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (zero_le_one.trans hK) ha)
        (by positivity))) _)
  apply killedSobolevBound_of_lower hA (by dsimp [D]; positivity)
  intro v
  have hb := hSob U V measurableSet_ball Metric.isOpen_ball
    (Metric.ball_subset_ball (by linarith)) μ (withDensity_absolutelyContinuous _ _)
    (a * K) (a * K * (2 : ℝ) ^ (5 : ℝ)) (lt_of_lt_of_le zero_lt_one hKm)
    (by positivity) hsupp hgrowth A hcoer' v
  have hconst := killedSobolevConstant_le_sq hd (by norm_num : (0 : ℝ) < 1 / 4)
    hC.le hKm ENNReal.toReal_nonneg hm (by positivity : 0 ≤ (2 : ℝ) ^ (5 : ℝ))
  have he : killedSobolevConstant d (1 / 4) C (a * K) ((μ.restrict U) univ).toReal
      (a * K * (2 : ℝ) ^ (5 : ℝ)) ≤ D * K ^ 2 := by
    refine hconst.trans ?_
    dsimp [D]
    nlinarith [sq_nonneg K]
  exact hb.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal he) _)


end TransitionSobolevExhaustionDeterministic

section TransitionSobolevExhaustionBank


/-! Actual all-cutoff Sobolev bank on a countable spatial exhaustion.
The disorder threshold precedes every exhaustion radius. -/

open MeasureTheory Set Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal


theorem aux_lim_thm_nongaussian_transition_sobolev_exhaustion_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ δ →
      ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
      ∃ Ks : ℕ → ℕ → BilateralField d → ℝ,
        (∀ n N, Measurable (Ks n N)) ∧ (∀ n N w, 1 ≤ Ks n N w) ∧
        (∀ n, ∃ C : ℝ, 0 < C ∧ ∀ N,
          (∫⁻ w, ENNReal.ofReal (Ks n N w) ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal C) ∧
        ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ (n N : ℕ),
          KilledSobolevBound (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1))
            (cutoffSpeedDensity M H w N) (cutoffCoefficient M H w N) (Ks n N w) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  let Jc := Classical.choice (inputs_J_witness d hd)
  let Pc := Classical.choice (inputs_poincare_witness d hd Jc)
  let Sf := Classical.choice (inputs_Sf_witness d hd)
  obtain ⟨δup, hδup, hupper⟩ := aux_tight_static_upper hd 2 (by norm_num)
  obtain ⟨δcoer, hδcoer, hcoercivity⟩ := tight_static_coer hd Jc Pc Sf 2 (by norm_num)
  obtain ⟨Cresp, _, hresponses⟩ := lfsgs_response_bank hd
  refine ⟨min δup δcoer, lt_min hδup hδcoer, ?_⟩
  intro M hM H hH
  obtain ⟨Rm, _⟩ := hresponses M
  have hbank : ∀ n : ℕ, ∃ Ks : ℕ → BilateralField d → ℝ,
      (∀ N, Measurable (Ks N)) ∧ (∀ N w, 1 ≤ Ks N w) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ N,
        (∫⁻ w, ENNReal.ofReal (Ks N w) ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal C) ∧
      ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ N,
        KilledSobolevBound (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1))
          (cutoffSpeedDensity M H w N) (cutoffCoefficient M H w N) (Ks N w) := by
    intro n
    let R : ℝ := 4 * ((n : ℝ) + 2)
    have hR : 1 ≤ R := by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨D, hD, hdet⟩ := aux_lim_thm_nongaussian_transition_sobolev_exhaustion_deterministic hd n
    obtain ⟨Cup, hCup, hupperM⟩ := hupper M (hM.trans (min_le_left _ _)) R hR
    obtain ⟨Ccoer, hCcoer, hcoerM⟩ := hcoercivity M Rm
      (hM.trans (min_le_right _ _)) R hR
    obtain ⟨Kup, hKup, hKupone, hKupmoment, hKupmass⟩ := hupperM H hH
    have hN : ∀ N : ℕ, ∃ Ks : BilateralField d → ℝ,
        Measurable Ks ∧ (∀ w, 1 ≤ Ks w) ∧
        (∫⁻ w, ENNReal.ofReal (Ks w) ∂(chaosSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (1 + D * (Cup + Ccoer)) ∧
        ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          KilledSobolevBound (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1))
            (cutoffSpeedDensity M H w N) (cutoffCoefficient M H w N) (Ks w) := by
      intro N
      obtain ⟨Kcoer, hKcoer, hKcoerone, hKcoermoment, hKcoerbound⟩ := hcoerM H hH N
      let Kstatic : BilateralField d → ℝ := fun w => max (Kup w) (Kcoer w)
      have hKstatic : Measurable Kstatic := hKup.max hKcoer
      have hKstaticone : ∀ w, 1 ≤ Kstatic w :=
        fun w => (hKupone w).trans (le_max_left _ _)
      have hmoment : (∫⁻ w, ENNReal.ofReal (Kstatic w ^ killedSobolevMomentOrder 1)
          ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal (Cup + Ccoer) := by
        have hh := lintegral_max_rpow_le (chaosSampleLaw M).toMeasure hKup
          (fun w => zero_le_one.trans (hKupone w)) (fun w => zero_le_one.trans (hKcoerone w))
          (by norm_num : (0 : ℝ) ≤ 2) hCup.le hCcoer.le hKupmoment hKcoermoment
        simpa only [Kstatic, killedSobolevMomentOrder, show max (1 : ℝ) (2 * 1) = 2 by norm_num] using hh
      have hA : ∀ w, CoefficientOn (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1))
          (cutoffCoefficient M H w N) := fun w =>
        SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
          (continuous_cutoffCoefficient M H w N) (cutoffCoefficient_pos' M H w N) Metric.isBounded_ball
      have hbound : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          KilledSobolevBound (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1))
            (cutoffSpeedDensity M H w N) (cutoffCoefficient M H w N) (D * Kstatic w ^ 2) := by
        filter_upwards [hKupmass, hKcoerbound] with w hmass hcoer
        apply hdet _ _ (Kstatic w) (hKstaticone w)
        · intro x hx r hr hr1
          have hx' : x ∈ Metric.ball (0 : SpatialCoordinates d) (R / 2) := by
            have hr : R / 2 = 2 * ((n : ℝ) + 2) := by dsimp [R]; ring
            rw [hr]
            exact hx
          exact (hmass N x r hr hr1 hx').trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _)))
        · intro v
          have hc := (hcoer (1 / 2) (by norm_num) (by norm_num)).2
          have hrad : R * ((1 / 2 : ℚ) : ℝ) / 2 = (n : ℝ) + 2 := by dsimp [R]; norm_num; ring
          have hden : ((1 / 2 : ℚ).den : ℝ) = 2 := by norm_num
          rw [hrad, hden] at hc
          exact (hc v).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by norm_num) _))) _)
        · exact hA w
      obtain ⟨Ks, hKs, hKsone, hKsmoment, _, hKsbound⟩ :=
        killedSobolev_moment_bank_of_bound (chaosSampleLaw M).toMeasure _
          (fun w => cutoffSpeedDensity M H w N) (fun w => cutoffCoefficient M H w N)
          Kstatic D (Cup + Ccoer) 1 hKstatic hKstaticone hD.le (by positivity)
          hmoment hA hbound
      exact ⟨Ks, hKs, hKsone, by simpa using hKsmoment, hKsbound⟩
    choose Ks hKs hKsone hmom hbound using hN
    exact ⟨Ks, hKs, hKsone, ⟨1 + D * (Cup + Ccoer), by positivity, hmom⟩,
      ae_all_iff.2 hbound⟩
  choose Ks hKs hKsone hmom hbound using hbank
  exact ⟨Ks, hKs, hKsone, hmom, ae_all_iff.2 hbound⟩


end TransitionSobolevExhaustionBank

section TransitionActualContinuity


/-! Weak continuity of the actual supplied cutoff path kernels, derived
from their proved local diffusion attachment and fixed-cutoff tightness. -/

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal


theorem aux_lim_thm_nongaussian_actual_cutoff_path_continuity {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN) :
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ N,
      Continuous (fun x => jointPathProbabilityMeasure (KN N) (hKN N) w x) := by
  let L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d) := fun N w =>
    ((KN N).comap (Prod.mk w) measurable_prodMk_left).map LifetimePath.ofContinuousPath
  have hL : ∀ N w x, (KN N (w, x)).map LifetimePath.ofContinuousPath = L N w x := by
    intro N w x
    dsimp only [L]
    rw [Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath, Kernel.comap_apply]
  have hLloc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ N,
      LocalDiffusion (cutoffCoefficient M H w N) (cutoffSpeedDensity M H w N) (L N w) :=
    aux_lim_thm_measure_actual_cutoff_localDiffusion_supplier hd M H hH PN KN hKN hin
  exact in_cutoff_start_continuity hd M H hH PN KN hKN hin
    (tight_fixed_cutoff hd M H hH PN KN hKN hin L hL hLloc)


end TransitionActualContinuity

section TransitionStartPromotion


/-! Every-start positive killed-test bounds from weak continuity and full
support. No killed density or exceptional-start identification is assumed. -/

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal CompactlySupported


/-- Positive killed-test integration is LSC in a weakly continuous family. -/
theorem aux_lim_thm_nongaussian_transition_killed_test_lowerSemicontinuous
    {d : ℕ} (P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (hP : Continuous P) (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : C(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    LowerSemicontinuous (fun x => ∫⁻ w, ENNReal.ofReal
      (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
        ∂(P x : Measure (DiffusionPath d))) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro B
  apply IsSeqClosed.isClosed
  intro xs x hxs hx
  exact (aux_lim_transition_domination_portmanteau_lsc
    (P x : Measure (DiffusionPath d)) (fun n => (P (xs n) : Measure (DiffusionPath d)))
    (fun w => if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
    (aux_lim_transition_domination_killed_test_lsc U hU t f hf)
    (fun w => by
      split_ifs
      · exact hf (w t)
      · exact le_rfl)
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      ((hP.tendsto x).comp hx) hG)).trans
    (liminf_le_of_frequently_le' (Eventually.of_forall hxs).frequently)

/-- Full support upgrades an AE-start killed-test bound on an open domain. -/
theorem aux_lim_thm_nongaussian_transition_killed_test_le_of_ae
    {d : ℕ} (P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (hP : Continuous P) (rho : SpatialCoordinates d → ℝ)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (hrho : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.CoefficientOn U rho)
    (t : ℝ≥0) (f : C(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (B : ℝ≥0∞)
    (hb : ∀ᵐ x ∂(weightedMeasure rho).restrict U,
      (∫⁻ w, ENNReal.ofReal
        (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
          ∂(P x : Measure (DiffusionPath d))) ≤ B) :
    ∀ x ∈ U, (∫⁻ w, ENNReal.ofReal
      (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
        ∂(P x : Measure (DiffusionPath d))) ≤ B := by
  have hv := volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU.measurableSet hrho
  exact SubdiffusiveProcess.Section10.lowerSemicontinuousOn_le_of_ae_restrict volume hU
    ((aux_lim_thm_nongaussian_transition_killed_test_lowerSemicontinuous P hP U hU t f hf).lowerSemicontinuousOn U)
    (hv.ae_le hb)


end TransitionStartPromotion

section TransitionKilledPathBridge


/-! Literal continuous-path and lifetime-path killed marginals agree. The
Nash essential supremum can therefore be promoted for positive spatial tests. -/

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
open scoped ENNReal NNReal CompactlySupported


theorem aux_lim_thm_nongaussian_transition_killedKernel_ofContinuousPath {d : ℕ}
    (κ : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (t : ℝ≥0) (x : SpatialCoordinates d) :
    killedKernel (κ.map LifetimePath.ofContinuousPath) U hU t x =
      ((κ x).restrict {w | (t : ℝ≥0∞) < ContinuousPath.exitTime U w}).map
        (fun w : DiffusionPath d => w t) := by
  apply Measure.ext
  intro B hB
  have hExit : Measurable (LifetimePath.exitTime U : Path d → ℝ≥0∞) := by
    simpa only using! (LifetimePath.isStoppingTime_exitTime U hU).measurable'
  have hE : MeasurableSet ((position t) ⁻¹' B ∩
      {w : Path d | (t : ℝ≥0∞) < LifetimePath.exitTime U w}) :=
    ((position_fixed_measurable t) hB).inter
      (measurableSet_lt measurable_const hExit)
  rw [killedKernel, map_restrict_apply _ _ _ _ (position_fixed_measurable t) x B hB,
    Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath,
    Measure.map_apply LifetimePath.measurable_ofContinuousPath hE,
    Measure.map_apply (continuous_eval_const t).measurable hB,
    Measure.restrict_apply ((continuous_eval_const t).measurable hB)]
  congr 1
  ext w
  simp only [mem_preimage, mem_inter_iff, mem_setOf_eq,
    SubdiffusiveProcess.Model.LifetimeProcess.position_ofContinuousPath, LifetimePath.exitTime_ofContinuousPath]

theorem aux_lim_thm_nongaussian_transition_killed_test_eq_ofReal_integral {d : ℕ}
    (κ : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel κ]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : C_c(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 ≤ f x) (x : SpatialCoordinates d) :
    (∫⁻ w, ENNReal.ofReal
      (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0) ∂κ x) =
      ENNReal.ofReal (kernelIntegral
        (killedKernel (κ.map LifetimePath.ofContinuousPath) U hU t) f x) := by
  letI : IsMarkovKernel (κ.map LifetimePath.ofContinuousPath) :=
    Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
  letI : IsFiniteMeasure (killedKernel (κ.map LifetimePath.ofContinuousPath) U hU t x) :=
    ⟨((killedKernel_subMarkov _ U hU t).measure_le_one x univ).trans_lt ENNReal.one_lt_top⟩
  have h := aux_lim_transition_domination_killed_integral (κ x) U hU t f.toContinuousMap
  change (∫⁻ y, ENNReal.ofReal (f y) ∂((κ x).restrict
    {w | (t : ℝ≥0∞) < ContinuousPath.exitTime U w}).map (fun w : DiffusionPath d => w t)) =
    (∫⁻ w, ENNReal.ofReal
      (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0) ∂κ x) at h
  rw [← h, ← aux_lim_thm_nongaussian_transition_killedKernel_ofContinuousPath κ U hU t x]
  exact (ofReal_integral_eq_lintegral_ofReal f.integrable (Eventually.of_forall hf)).symm

/-- Every-start positive test bound from a native killed L-infinity estimate. -/
theorem aux_lim_thm_nongaussian_transition_killed_test_of_esssup {d : ℕ}
    (κ : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel κ]
    (P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (hP : ∀ x, (P x : Measure (DiffusionPath d)) = κ x) (hc : Continuous P)
    (rho : SpatialCoordinates d → ℝ) (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (hrho : CoefficientOn U rho) (t : ℝ≥0)
    (f : C_c(SpatialCoordinates d, ℝ)) (hf : ∀ x, 0 ≤ f x) (B : ℝ≥0∞)
    (hb : eLpNorm (kernelIntegral (killedKernel (κ.map LifetimePath.ofContinuousPath) U hU t) f)
      ∞ ((weightedMeasure rho).restrict U) ≤ B * eLpNorm f 1 ((weightedMeasure rho).restrict U)) :
    ∀ x ∈ U, (∫⁻ w, ENNReal.ofReal
      (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0) ∂κ x) ≤
      B * (∫⁻ y, ENNReal.ofReal (f y) ∂weightedMeasure rho) := by
  have htest : ∀ᵐ x ∂(weightedMeasure rho).restrict U,
      (∫⁻ w, ENNReal.ofReal
        (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
        ∂(P x : Measure (DiffusionPath d))) ≤
        B * (∫⁻ y, ENNReal.ofReal (f y) ∂weightedMeasure rho) := by
    filter_upwards [enorm_ae_le_eLpNormEssSup
      (kernelIntegral (killedKernel (κ.map LifetimePath.ofContinuousPath) U hU t) f)
      ((weightedMeasure rho).restrict U)] with x hx
    rw [hP x, aux_lim_thm_nongaussian_transition_killed_test_eq_ofReal_integral κ U hU t f hf x]
    refine (Real.ofReal_le_enorm _).trans (hx.trans ?_)
    have hKernelAES : AEStronglyMeasurable
        (kernelIntegral (killedKernel (κ.map LifetimePath.ofContinuousPath) U hU t) f)
        ((weightedMeasure rho).restrict U) := by
      simpa only [kernelIntegral] using!
        (f.continuous.measurable.stronglyMeasurable.integral_kernel
          (κ := killedKernel (κ.map LifetimePath.ofContinuousPath) U hU t)).aestronglyMeasurable
    rw [eLpNorm_exponent_top hKernelAES] at hb
    refine hb.trans (mul_le_mul_right ?_ B)
    have hfAES : AEStronglyMeasurable (fun x => f x) ((weightedMeasure rho).restrict U) := by
      simpa only using! f.continuous.measurable.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hfAES]
    simp_rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf _)]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have h := aux_lim_thm_nongaussian_transition_killed_test_le_of_ae P hc rho U hU hrho t f.toContinuousMap hf
    (B * (∫⁻ y, ENNReal.ofReal (f y) ∂weightedMeasure rho)) htest
  simpa only [hP] using! h


end TransitionKilledPathBridge

section TransitionNashCutoffConsumer


/-! The proved P2 Nash theorem applied to the actual cutoff laws and actual
Sobolev bank. Full support and weak path continuity give every starting point. -/

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Section10 SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped ENNReal NNReal CompactlySupported


lemma aux_lim_thm_nongaussian_transition_nash_coefficient (d : ℕ) (Cd K : ℝ) (hCd : 0 ≤ Cd) (hK : 0 ≤ K)
    (t : ℝ≥0) (ht : 0 < t) :
    ENNReal.ofReal Cd * (ENNReal.ofReal K / (t : ℝ≥0∞)) ^ d =
      ENNReal.ofReal (Cd * K ^ d * (t : ℝ) ^ (-(d : ℝ))) := by
  have htR : (0 : ℝ) < t := ht
  rw [Real.rpow_neg t.coe_nonneg, Real.rpow_natCast,
    ENNReal.ofReal_mul (mul_nonneg hCd (pow_nonneg hK _)), ENNReal.ofReal_mul hCd,
    ENNReal.ofReal_inv_of_pos (pow_pos htR _), ENNReal.ofReal_pow hK,
    ENNReal.ofReal_pow t.coe_nonneg, ENNReal.ofReal_coe_nnreal, div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow, mul_assoc]

theorem aux_lim_thm_nongaussian_actual_cutoff_killed_test_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ Cd : ℝ, 0 < Cd ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ δ →
      ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (_hKN : ∀ N, IsMarkovKernel (KN N)), in_crossing M H PN KN →
      ∃ Ks : ℕ → ℕ → BilateralField d → ℝ,
        (∀ n N, Measurable (Ks n N)) ∧ (∀ n N w, 1 ≤ Ks n N w) ∧
        (∀ n, ∃ C : ℝ, 0 < C ∧ ∀ N,
          (∫⁻ w, ENNReal.ofReal (Ks n N w) ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal C) ∧
        ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ (n N : ℕ),
          ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1),
          ∀ t : ℝ≥0, 0 < t → ∀ f : C_c(SpatialCoordinates d, ℝ), (∀ y, 0 ≤ f y) →
            (∫⁻ path, ENNReal.ofReal
              (if (t : ℝ≥0∞) < ContinuousPath.exitTime
                (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) path
                then f (path t) else 0) ∂KN N (w, x)) ≤
              ENNReal.ofReal (Cd * (Ks n N w) ^ d * (t : ℝ) ^ (-(d : ℝ)) *
                ∫ y, f y ∂cutoffSpeedMeasure M H w N) := by
  classical
  obtain ⟨δ, hδ, hbank⟩ := aux_lim_thm_nongaussian_transition_sobolev_exhaustion_bank hd
  obtain ⟨Cd, hCd, hNash⟩ := classical_weighted_nash_ultracontractivity d hd
  refine ⟨δ, hδ, Cd, hCd, ?_⟩
  intro M hM H hH PN KN hKN hin
  obtain ⟨Ks, hKs, hKsone, hmoment, hSob⟩ := hbank M hM H hH
  have hlocal := aux_lim_thm_measure_actual_cutoff_localDiffusion_supplier hd M H hH PN KN hKN hin
  have hcont := aux_lim_thm_nongaussian_actual_cutoff_path_continuity hd M H hH PN KN hKN hin
  refine ⟨Ks, hKs, hKsone, hmoment, ?_⟩
  filter_upwards [hSob, hlocal, hcont] with w hs hD hc
  intro n N x hx t ht f hf
  let U : Set (SpatialCoordinates d) := Metric.ball 0 ((n : ℝ) + 1)
  let κ := (KN N).comap (Prod.mk w) measurable_prodMk_left
  letI : IsMarkovKernel (KN N) := hKN N
  letI : IsMarkovKernel κ := by dsimp [κ]; infer_instance
  letI : IsMarkovKernel (κ.map LifetimePath.ofContinuousPath) :=
    Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
  have hU : IsOpen U := Metric.isOpen_ball
  have hUb : Bornology.IsBounded U := Metric.isBounded_ball
  have hccont := continuous_cutoffCoefficient M H w N
  have hrcont := continuous_cutoffSpeedDensity M H w N
  have hrho := SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
    hrcont (fun y => Real.exp_pos _) hUb
  letI : IsLocallyFiniteMeasure (weightedMeasure (cutoffSpeedDensity M H w N)) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hrcont
  letI : IsFiniteMeasure ((weightedMeasure (cutoffSpeedDensity M H w N)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      hUb.measure_lt_top (μ := weightedMeasure (cutoffSpeedDensity M H w N))⟩
  let C : Set (SpatialCoordinates d) := insert 0 (closure U)
  have hC : IsCompact C := hUb.isCompact_closure.insert 0
  obtain ⟨y, _, hy⟩ := hC.exists_isMinOn (Set.insert_nonempty 0 (closure U)) hccont.continuousOn
  obtain ⟨z, _, hz⟩ := hC.exists_isMaxOn (Set.insert_nonempty 0 (closure U)) hccont.continuousOn
  have hell := isEllipticFieldOn_scalarCoeffField_of_continuousOn hU.measurableSet hccont.continuousOn
      (cutoffCoefficient_pos' M H w N y)
      (fun a ha => ⟨hy (Set.mem_insert_of_mem _ (subset_closure ha)),
        hz (Set.mem_insert_of_mem _ (subset_closure ha))⟩)
  have hlp := killed_ultracontractive_consumer (hD N) hU hUb hell Cd (Ks n N w)
    (lt_of_lt_of_le zero_lt_one (hKsone n N w)) (fun u => (hs n N u).2.1)
    (hNash (SpatialCoordinates d) ((weightedMeasure (cutoffSpeedDensity M H w N)).restrict U))
    t ht (f : SpatialCoordinates d → ℝ) f.integrable
  rw [killedFamily_of_ne _ _ _ ht.ne'] at hlp
  have htest := aux_lim_thm_nongaussian_transition_killed_test_of_esssup κ
    (fun a => jointPathProbabilityMeasure (KN N) (hKN N) w a) (fun _ => rfl)
    (hc N) (cutoffSpeedDensity M H w N) U hU hrho t f hf
    (ENNReal.ofReal Cd * (ENNReal.ofReal (Ks n N w) / (t : ℝ≥0∞)) ^ d) hlp x hx
  rw [aux_lim_thm_nongaussian_transition_nash_coefficient d Cd (Ks n N w) hCd.le
    (zero_le_one.trans (hKsone n N w)) t ht,
    ← ofReal_integral_eq_lintegral_ofReal
      (f.integrable (μ := weightedMeasure (cutoffSpeedDensity M H w N))) (Eventually.of_forall hf),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCd.le (pow_nonneg (zero_le_one.trans (hKsone n N w)) _))
      (Real.rpow_nonneg t.coe_nonneg _))] at htest
  exact htest


end TransitionNashCutoffConsumer

section TransitionQuantitativePassage


/-! Quantitative killed-law transport along the same vague limit.
The coefficient is retained, rather than discarded after obtaining AC. -/

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal CompactlySupported


theorem aux_lim_thm_nongaussian_transition_measure_le_of_positive_tests
    {d : ℕ} (mu nu : Measure (SpatialCoordinates d))
    [IsFiniteMeasure mu] [IsLocallyFiniteMeasure nu]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hsupp : mu.restrict U = mu)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x) → tsupport f ⊆ U →
      (∫⁻ x, ENNReal.ofReal (f x) ∂mu) ≤ ENNReal.ofReal (C * ∫ x, f x ∂nu)) :
    mu ≤ ENNReal.ofReal C • nu.restrict U := by
  haveI : IsFiniteMeasureOnCompacts nu := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  haveI : nu.OuterRegular := inferInstance
  haveI : mu.InnerRegular := inferInstance
  haveI : ((ENNReal.ofReal C) • nu).OuterRegular :=
    Measure.OuterRegular.smul nu ENNReal.ofReal_ne_top
  have hle : mu.restrict U ≤ ENNReal.ofReal C • nu := by
    apply aux_lim_transition_domination_restrict_le_of_tests mu (ENNReal.ofReal C • nu) U hU
    intro f hf hfs
    rw [lintegral_smul_measure, ← ofReal_integral_eq_lintegral_ofReal
      (f.integrable (μ := nu)) (Eventually.of_forall hf), smul_eq_mul, ← ENNReal.ofReal_mul hC]
    exact h f hf hfs
  have hr := Measure.restrict_mono (Subset.refl U) hle
  simpa only [Measure.restrict_smul, hsupp] using hr

/-- Weak path convergence and vague speed convergence preserve a fixed
subsequence bound for every Borel set, with its exact multiplicative constant. -/
theorem aux_lim_thm_nongaussian_transition_killed_le_of_subsequence
    {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (t : ℝ≥0)
    (P : ProbabilityMeasure (DiffusionPath d))
    (PN : ℕ → ProbabilityMeasure (DiffusionPath d)) (hp : Tendsto PN atTop (𝓝 P))
    (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d))
    [IsLocallyFiniteMeasure mu] (hmu : MeasuresConvergeLocally muN mu)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x) → tsupport f ⊆ U →
      ∀ n, (∫⁻ w, ENNReal.ofReal
        (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
        ∂(PN (phi n) : Measure (DiffusionPath d))) ≤
          ENNReal.ofReal (C * ∫ x, f x ∂muN (phi n))) :
    ((P : Measure (DiffusionPath d)).restrict
      {w | (t : ℝ≥0∞) < ContinuousPath.exitTime U w}).map
      (fun w : DiffusionPath d => w t) ≤ ENNReal.ofReal C • mu.restrict U := by
  apply aux_lim_thm_nongaussian_transition_measure_le_of_positive_tests _ mu U hU
    (aux_lim_transition_domination_killed_supported _ U hU t) C hC
  intro f hf hfs
  exact (aux_lim_transition_domination_killed_integral (P : Measure (DiffusionPath d))
    U hU t f.toContinuousMap).trans_le
      (aux_lim_transition_domination_vague_killed_passage U hU t f hf P PN hp
        muN mu hmu phi hphi C (hb f hf hfs))

/-- Domination on an exhaustion ball restricts to every smaller open domain. -/
theorem aux_lim_thm_nongaussian_transition_killed_bound_mono_domain
    {d : ℕ} (P : Measure (DiffusionPath d)) (mu : Measure (SpatialCoordinates d))
    {U V : Set (SpatialCoordinates d)} (hU : IsOpen U) (hUV : U ⊆ V)
    (t : ℝ≥0) (C : ℝ≥0∞)
    (h : (P.restrict {w | (t : ℝ≥0∞) < ContinuousPath.exitTime V w}).map
      (fun w : DiffusionPath d => w t) ≤ C • mu.restrict V) :
    (P.restrict {w | (t : ℝ≥0∞) < ContinuousPath.exitTime U w}).map
      (fun w : DiffusionPath d => w t) ≤ C • mu.restrict U := by
  have hs : {w : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U w} ⊆
      {w | (t : ℝ≥0∞) < ContinuousPath.exitTime V w} := by
    intro w hw
    exact hw.trans_le (ContinuousPath.exitTime_mono hUV w)
  have hl : (P.restrict {w | (t : ℝ≥0∞) < ContinuousPath.exitTime U w}).map
      (fun w : DiffusionPath d => w t) ≤ C • mu.restrict V :=
    (Measure.map_mono (Measure.restrict_mono_set P hs)
      (continuous_eval_const t).measurable).trans h
  have hr := Measure.restrict_mono (Subset.refl U) hl
  rw [aux_lim_transition_domination_killed_supported P U hU t,
    Measure.restrict_smul, Measure.restrict_restrict hU.measurableSet,
    Set.inter_eq_left.mpr hUV] at hr
  exact hr


end TransitionQuantitativePassage

section TransitionLimitBounds


/-! The environment-wise quantitative killed bound and full marginal AC.
Each exhaustion ball has one subsequence, chosen before starts, times and tests. -/

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal CompactlySupported


/-- Local uniform path-metric convergence supplies every fixed-start weak limit. -/
theorem aux_lim_thm_nongaussian_transition_path_tendsto_of_locally_uniform {d : ℕ}
    (P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (PN : ℕ → SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (hc : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B, pathLevyProkhorovDist (PN N x) (P x) < eps) :
    ∀ x, Tendsto (fun N => PN N x) atTop (𝓝 (P x)) := by
  intro x
  apply aux_lim_transition_domination_path_metric_tendsto
  apply Metric.tendsto_atTop.2
  intro eps heps
  obtain ⟨N0, hN0⟩ := hc {x} isCompact_singleton eps heps
  refine ⟨N0, fun N hN => ?_⟩
  have hn : 0 ≤ pathLevyProkhorovDist (PN N x) (P x) := by
    dsimp only [pathLevyProkhorovDist, levyProkhorovDist]
    exact ENNReal.toReal_nonneg
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hn] using hN0 N hN x (mem_singleton x)

/-- Quantitative ball bounds along a single bounded Sobolev subsequence per ball. -/
theorem aux_lim_thm_nongaussian_transition_limit_exhaustion_bounds {d : ℕ}
    (P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (PN : ℕ → SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (hp : ∀ x, Tendsto (fun N => PN N x) atTop (𝓝 (P x)))
    (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d))
    [IsLocallyFiniteMeasure mu] (hc : MeasuresConvergeLocally muN mu)
    (Ks : ℕ → ℕ → ℝ) (hKs : ∀ n N, 1 ≤ Ks n N) (Cd : ℝ) (hCd : 0 < Cd)
    (hf : ∀ n, liminf (fun N => ENNReal.ofReal (Ks n N)) atTop < ⊤)
    (hb : ∀ (n N : ℕ), ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1),
      ∀ t : ℝ≥0, 0 < t → ∀ f : C_c(SpatialCoordinates d, ℝ), (∀ y, 0 ≤ f y) →
        (∫⁻ path, ENNReal.ofReal
          (if (t : ℝ≥0∞) < ContinuousPath.exitTime
            (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) path
            then f (path t) else 0) ∂(PN N x : Measure (DiffusionPath d))) ≤
          ENNReal.ofReal (Cd * (Ks n N) ^ d * (t : ℝ) ^ (-(d : ℝ)) * ∫ y, f y ∂muN N)) :
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1),
      ∀ t : ℝ≥0, 0 < t →
        ((P x : Measure (DiffusionPath d)).restrict {w | (t : ℝ≥0∞) <
          ContinuousPath.exitTime (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) w}).map
          (fun w : DiffusionPath d => w t) ≤
          ENNReal.ofReal (C * (t : ℝ) ^ (-(d : ℝ))) •
            mu.restrict (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) := by
  intro n
  obtain ⟨c, phi, hphi, hbound⟩ := aux_lim_transition_domination_bounded_subsequence _ (hf n)
  let C : ℝ := Cd * ((c : ℝ) + 1) ^ d
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x hx t ht
  apply aux_lim_thm_nongaussian_transition_killed_le_of_subsequence _ Metric.isOpen_ball t
    (P x) (fun N => PN N x) (hp x) muN mu hc phi hphi
    (C * (t : ℝ) ^ (-(d : ℝ))) (mul_nonneg hC.le (Real.rpow_nonneg t.coe_nonneg _))
  intro f hf0 _ m
  have hK : Ks n (phi m) ≤ (c : ℝ) + 1 := by
    have hle := ENNReal.toReal_mono (by simp : (c : ℝ≥0∞) ≠ ⊤) (hbound m)
    have hnonneg := zero_le_one.trans (hKs n (phi m))
    rw [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_natCast] at hle
    linarith
  have hpow := pow_le_pow_left₀ (zero_le_one.trans (hKs n (phi m))) hK d
  exact (hb n (phi m) x hx t ht f hf0).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCd.le)
        (Real.rpow_nonneg t.coe_nonneg _)) (integral_nonneg hf0)))

/-- An exhaustion-ball estimate supplies the literal estimate on every bounded
open set, including the empty set. -/
theorem aux_lim_thm_nongaussian_transition_bounded_domain_bound {d : ℕ}
    (P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (mu : Measure (SpatialCoordinates d))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1),
      ∀ t : ℝ≥0, 0 < t →
        ((P x : Measure (DiffusionPath d)).restrict {w | (t : ℝ≥0∞) <
          ContinuousPath.exitTime (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) w}).map
          (fun w : DiffusionPath d => w t) ≤
          ENNReal.ofReal (C * (t : ℝ) ^ (-(d : ℝ))) •
            mu.restrict (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1))) :
    ∀ U : Set (SpatialCoordinates d), IsOpen U → Bornology.IsBounded U →
      ∃ CU : ℝ, 0 < CU ∧ ∀ x ∈ U, ∀ t : ℝ≥0, 0 < t →
        ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
          (P x : Measure (DiffusionPath d)) {w | w t ∈ A ∧
            (t : ℝ≥0∞) < ContinuousPath.exitTime U w} ≤
            ENNReal.ofReal (CU * (t : ℝ) ^ (-(d : ℝ))) * mu.restrict U A := by
  intro U hU hUb
  obtain ⟨r, hr⟩ := hUb.subset_ball (0 : SpatialCoordinates d)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hUV : U ⊆ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1) :=
    hr.trans (Metric.ball_subset_ball (by linarith))
  obtain ⟨C, hC, hball⟩ := hb n
  refine ⟨C, hC, ?_⟩
  intro x hx t ht A hA
  have h := aux_lim_thm_nongaussian_transition_killed_bound_mono_domain (P x : Measure (DiffusionPath d)) mu hU hUV t
    (ENNReal.ofReal (C * (t : ℝ) ^ (-(d : ℝ)))) (hball x (hUV hx) t ht) A
  rw [Measure.map_apply (continuous_eval_const t).measurable hA,
    Measure.restrict_apply ((continuous_eval_const t).measurable hA),
    Measure.smul_apply, smul_eq_mul] at h
  exact h

/-- Every positive-time full marginal is AC, by a tail of the same exhaustion. -/
theorem aux_lim_thm_nongaussian_transition_full_marginal_ac {d : ℕ}
    (P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d))
    (mu : Measure (SpatialCoordinates d))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1),
      ∀ t : ℝ≥0, 0 < t →
        ((P x : Measure (DiffusionPath d)).restrict {w | (t : ℝ≥0∞) <
          ContinuousPath.exitTime (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) w}).map
          (fun w : DiffusionPath d => w t) ≤
          ENNReal.ofReal (C * (t : ℝ) ^ (-(d : ℝ))) •
            mu.restrict (Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1))) :
    ∀ x (t : ℝ≥0), 0 < t → (P x : Measure (DiffusionPath d)).map
      (fun w : DiffusionPath d => w t) ≪ mu := by
  intro x t ht
  obtain ⟨N0, hN0⟩ := exists_nat_gt (dist x (0 : SpatialCoordinates d))
  apply aux_lim_transition_domination_ac_of_killed_tail (P x : Measure (DiffusionPath d)) mu t N0
  intro n hn
  obtain ⟨C, _, hball⟩ := hb n
  have hxn : x ∈ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1) := by
    change dist x 0 < _
    have hnR : (N0 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact (Measure.absolutelyContinuous_of_le_smul (hball x hxn t ht)).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)


end TransitionLimitBounds

section TransitionActualLimitConsumer


/-! Actual same-limit transition domination. All analytic and pointwise
suppliers are discharged; only the constructed vague-limit data are supplied. -/

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal CompactlySupported


/-- One environment event supports every start, positive time, bounded open
set and Borel evaluation. The measure is the supplied actual cutoff limit. -/
theorem aux_lim_thm_nongaussian_actual_limit_transition_bounds {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ δ →
      ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N)), in_crossing M H PN KN →
      ∀ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hK : IsMarkovKernel K), aux_lim_thm_nongaussian_QuenchedConv M KN hKN K hK →
      ∀ mu : BilateralField d → Measure (SpatialCoordinates d),
        (∀ w, IsLocallyFiniteMeasure (mu w)) →
        (∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H w N) (mu w)) →
        ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          (∀ x : SpatialCoordinates d, ∀ t : ℝ≥0, 0 < t →
            (K (w, x)).map (fun path : DiffusionPath d => path t) ≪ mu w) ∧
          ∀ U : Set (SpatialCoordinates d), IsOpen U → Bornology.IsBounded U →
            ∃ CU : ℝ, 0 < CU ∧ ∀ x ∈ U, ∀ t : ℝ≥0, 0 < t →
              ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
                K (w, x) {path | path t ∈ A ∧ (t : ℝ≥0∞) < ContinuousPath.exitTime U path} ≤
                  ENNReal.ofReal (CU * (t : ℝ) ^ (-(d : ℝ))) * (mu w).restrict U A := by
  obtain ⟨δ, hδ, Cd, hCd, hbank⟩ := aux_lim_thm_nongaussian_actual_cutoff_killed_test_bank hd
  refine ⟨δ, hδ, ?_⟩
  intro M hM H hH PN KN hKN hin K hK hconv mu hl hc
  obtain ⟨Ks, hKs, hKsone, hmoment, hbound⟩ := hbank M hM H hH PN KN hKN hin
  have hfatou : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      ∀ n : ℕ, liminf (fun N => ENNReal.ofReal (Ks n N w)) atTop < ⊤ := by
    apply ae_all_iff.2
    intro n
    obtain ⟨C, _, hC⟩ := hmoment n
    exact aux_lim_transition_domination_fatou_finite (chaosSampleLaw M).toMeasure
      (fun N w => ENNReal.ofReal (Ks n N w))
      (fun N => ENNReal.measurable_ofReal.comp (hKs n N))
      (ENNReal.ofReal C) ENNReal.ofReal_ne_top hC
  filter_upwards [hbound, hfatou, hconv, hc] with w hb hf hw hcw
  letI := hl w
  let P : SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d) :=
    fun x => jointPathProbabilityMeasure K hK w x
  let Q : ℕ → SpatialCoordinates d → ProbabilityMeasure (DiffusionPath d) :=
    fun N x => jointPathProbabilityMeasure (KN N) (hKN N) w x
  have hp : ∀ x, Tendsto (fun N => Q N x) atTop (𝓝 (P x)) :=
    aux_lim_thm_nongaussian_transition_path_tendsto_of_locally_uniform P Q hw
  have hball := aux_lim_thm_nongaussian_transition_limit_exhaustion_bounds P Q hp
    (fun N => cutoffSpeedMeasure M H w N) (mu w) hcw
    (fun n N => Ks n N w) (fun n N => hKsone n N w) Cd hCd hf hb
  exact ⟨aux_lim_thm_nongaussian_transition_full_marginal_ac P (mu w) hball,
    aux_lim_thm_nongaussian_transition_bounded_domain_bound P (mu w) hball⟩


end TransitionActualLimitConsumer

section NongaussianGaussianProcessAdapter


/-! Source-law comparison with arbitrary continuous Gaussian process laws.
A one-point finite-dimensional distribution gives the evaluation marginal. -/

open MeasureTheory ProbabilityTheory SubdiffusiveProcess MarkovProcess
open SubdiffusiveProcess.Section10
open scoped NNReal


theorem aux_lim_thm_nongaussian_continuous_gaussian_process_eval {d : ℕ} (s t : ℝ≥0)
    (Q : Measure C(Set.Icc s t, SpatialCoordinates d))
    (hQ : ∀ (n : ℕ) (times : Fin n → Set.Icc s t),
      IsGaussian (Q.map (fun w => fun i => w (times i))))
    (r : Set.Icc s t) : IsGaussian (Q.map (fun w => w r)) := by
  let times : Fin 1 → Set.Icc s t := fun _ => r
  let e : (Fin 1 → SpatialCoordinates d) →L[ℝ] SpatialCoordinates d := ContinuousLinearMap.proj 0
  letI : IsGaussian (Q.map (fun w => fun i => w (times i))) := hQ 1 times
  have h : IsGaussian ((Q.map (fun w => fun i => w (times i))).map e) := inferInstance
  rw [Measure.map_map e.continuous.measurable
    (Measurable.of_eval (fun i => (continuous_eval_const (times i)).measurable))] at h
  exact h


end NongaussianGaussianProcessAdapter

/-- Theorem `lim:thm-nongaussian` = `lim:lem-transition-domination` (Quenched transition laws),
paper lines 11085–11098 (one result carrying both labels).

Let `K` be the limit kernel of the quenched path laws (Theorem A(i)) and `μ^ω` the limit of the
reversible measures `μ_N` (`cutoffSpeedMeasure`).  Almost surely, simultaneously for every `x` and
every `t > 0`: the transition law `P_t^ω(x, ·)` (the law of `Z_t` under `K_x^ω`) is absolutely
continuous with respect to `μ^ω`, singular with respect to Lebesgue measure and with respect to
every Gaussian law (degenerate or not, `IsGaussian`); for every bounded open `U` there is a finite
`C_U` (depending on the environment and `U`) with
`𝐏_x^ω(Z_t ∈ A, t < τ_U) ≤ C_U t^{-d} μ^ω|_U(A)` for all `x ∈ U`, `t > 0` and measurable `A`; the
quenched joint law at any nonempty finite family of positive times is mutually singular with every
Gaussian law on `(ℝ^d)^n`; and the quenched path law on any interval `[s,t]`, `0 ≤ s < t`
(restriction to `C([s,t], ℝ^d)`), is mutually singular with the law of every continuous Gaussian
process on that interval (a probability measure on `C([s,t], ℝ^d)` all of whose finite-dimensional
distributions are Gaussian). -/
theorem lim_thm_nongaussian
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N)), in_crossing M H PN KN →
      ∀ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hK : IsMarkovKernel K), aux_lim_thm_nongaussian_QuenchedConv M KN hKN K hK →
      ∃ mu : BilateralField d → Measure (SpatialCoordinates d), Measurable mu ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (mu omega) ∧
          (∀ x : SpatialCoordinates d, ∀ t : ℝ≥0, 0 < t →
            (K (omega, x)).map (fun w : DiffusionPath d => w t) ≪ mu omega ∧
            (K (omega, x)).map (fun w : DiffusionPath d => w t) ⟂ₘ
              (volume : Measure (SpatialCoordinates d)) ∧
            ∀ gamma : Measure (SpatialCoordinates d), IsGaussian gamma →
              (K (omega, x)).map (fun w : DiffusionPath d => w t) ⟂ₘ gamma) ∧
          (∀ U : Set (SpatialCoordinates d), IsOpen U → Bornology.IsBounded U →
            ∃ CU : ℝ, 0 < CU ∧ ∀ x ∈ U, ∀ t : ℝ≥0, 0 < t →
              ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
                K (omega, x) {w | w t ∈ A ∧ (t : ℝ≥0∞) < ContinuousPath.exitTime U w} ≤
                  ENNReal.ofReal (CU * (t : ℝ) ^ (-(d : ℝ))) * (mu omega).restrict U A) ∧
          (∀ (x : SpatialCoordinates d) (n : ℕ), 0 < n →
            ∀ times : Fin n → ℝ≥0, (∀ i, 0 < times i) →
            ∀ gamma : Measure (Fin n → SpatialCoordinates d), IsGaussian gamma →
              (K (omega, x)).map (fun w : DiffusionPath d => fun i => w (times i)) ⟂ₘ gamma) ∧
          ∀ (x : SpatialCoordinates d) (s t : ℝ≥0), s < t →
            letI : MeasurableSpace C(Set.Icc s t, SpatialCoordinates d) :=
              borel C(Set.Icc s t, SpatialCoordinates d)
            ∀ Q : Measure C(Set.Icc s t, SpatialCoordinates d),
              (IsProbabilityMeasure Q ∧ ∀ (n : ℕ) (times : Fin n → Set.Icc s t),
                IsGaussian (Q.map (fun w => fun i => w (times i)))) →
              (K (omega, x)).map (fun w : DiffusionPath d => w.restrict (Set.Icc s t)) ⟂ₘ Q := by
  obtain ⟨δm, hδm, hdata⟩ := aux_lim_thm_measure_exists_same_limit_measure_root_data hd 1 (by norm_num)
  obtain ⟨δt, hδt, htrans⟩ := aux_lim_thm_nongaussian_actual_limit_transition_bounds hd
  refine ⟨min δm δt, lt_min hδm hδt, ?_⟩
  intro M hM H hH PN KN hKN hin K hK hconv
  obtain ⟨mu0, _, _, hwm, hwl, hdensity, _, _, hgrowth, _⟩ :=
    hdata M (hM.trans (min_le_left _ _)) H hH
  have hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H w N)
        (SubdiffusiveProcess.Section10.infraredWeightedLimit H mu0 w) := by
    filter_upwards [hdensity] with w hw
    exact measuresConvergeLocally_congr _ _ _
      (fun N => (cutoffSpeedMeasure_eq_weightedChaosCutoff M H w N).symm) hw.1.2.2.2.2.1
  have hdom := htrans M (hM.trans (min_le_right _ _)) H hH PN KN hKN hin K hK hconv
    (SubdiffusiveProcess.Section10.infraredWeightedLimit H mu0) hwl hc
  refine ⟨SubdiffusiveProcess.Section10.infraredWeightedLimit H mu0, hwm, ?_⟩
  filter_upwards [hdensity, hgrowth, hc, hdom] with w hm hg hw hp
  letI : NullSingletonClass (SubdiffusiveProcess.Section10.infraredWeightedLimit H mu0 w) := by
    simpa only using! hm.2.2.2.2.2.1
  have hsing : SubdiffusiveProcess.Section10.infraredWeightedLimit H mu0 w ⟂ₘ volume := hm.1.2.2.2.2.2.1
  have hballs : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1),
        ∀ r : ℝ, 0 < r → r ≤ 1 →
          SubdiffusiveProcess.Section10.infraredWeightedLimit H mu0 w (Metric.ball x r) ≤
            ENNReal.ofReal (C * r ^ ((d : ℝ) - 1 / 2)) := by
    intro n
    obtain ⟨C, hC, hb⟩ := hg (n + 1)
    refine ⟨C, hC, ?_⟩
    intro x hx r hr hr1
    have hx' : x ∈ Metric.closedBall (0 : SpatialCoordinates d) ((n + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Metric.ball_subset_closedBall hx
    exact (hb x hx' r hr hr1).2
  have hplanes := aux_lim_nongaussian_hyperplanes_of_local_growth hd
    (SubdiffusiveProcess.Section10.infraredWeightedLimit H mu0 w) hballs
  refine ⟨hw, ?_, hp.2, ?_, ?_⟩
  · intro x t ht
    exact ⟨hp.1 x t ht, SubdiffusiveProcess.Section10.dominated_measure_gaussian_singular _ _
      hsing hplanes (hp.1 x t ht)⟩
  · intro x n hn times htimes gamma hgamma
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    letI : IsGaussian gamma := hgamma
    exact SubdiffusiveProcess.Section10.finite_time_law_mutuallySingular_gaussian_of_domination
      _ (K (w, x)) hsing hplanes (hp.1 x) times htimes gamma
  · intro x s t hst Q hQ
    exact SubdiffusiveProcess.Section10.interval_law_mutuallySingular_gaussian_of_domination
      _ (K (w, x)) hsing hplanes (hp.1 x) s t hst Q
      (aux_lim_thm_nongaussian_continuous_gaussian_process_eval s t Q hQ.2)

end Paper
