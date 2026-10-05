module

public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.resolvent_datum
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.MultiplicativeChaos.TimeMarginal
public import MarkovProcess.Trajectory.StartingPointContinuity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeLaplaceUniqueness

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_in_cutoff_fdd_start_continuity_kernelIntegral_continuous
    {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [SecondCountableTopology alpha]
    (P : SubMarkovKernelSemigroup alpha)
    (K : alpha → Measure (ContinuousPath alpha))
    (hKfinite : ∀ x, IsFiniteMeasure (K x))
    (hmap : ∀ (t : ℝ≥0) (x : alpha),
      Measure.map (ContinuousPath.eval t) (K x) = P t x)
    (g : ZeroAtInftyContinuousMap alpha ℝ) (x : alpha) :
    Continuous (fun s : ℝ =>
      kernelIntegral (P (Real.toNNReal s)) g x) := by
  let : IsFiniteMeasure (K x) := hKfinite x
  have hcont : Continuous (fun t : ℝ≥0 =>
      ∫ path, g (path t) ∂(K x)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    refine tendsto_integral_filter_of_norm_le_const (μ := K x)
      (F := fun s : ℝ≥0 => fun path => g (path s))
      (f := fun path => g (path t)) ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun s =>
        (g.toBCF.continuous.comp (ContinuousPath.continuous_eval s)).aestronglyMeasurable
    · refine ⟨‖g.toBCF‖, Filter.Eventually.of_forall fun s =>
        Filter.Eventually.of_forall fun path => ?_⟩
      exact g.toBCF.norm_coe_le_norm (path s)
    · exact Filter.Eventually.of_forall fun path =>
        (g.toBCF.continuous.comp (ContinuousMap.continuous path)).tendsto t
  have hcont' : Continuous (fun t : ℝ≥0 => kernelIntegral (P t) g x) := by
    apply hcont.congr
    intro t
    change (∫ path, g (path t) ∂K x) = ∫ y, g y ∂P t x
    rw [← hmap t x]
    simpa only [Function.comp_def, ZeroAtInftyContinuousMap.toBCF, ContinuousPath.eval] using! (integral_map (μ := K x)
      (ContinuousPath.continuous_eval t).measurable.aemeasurable
      g.toBCF.continuous.measurable.aestronglyMeasurable).symm
  exact hcont'.comp continuous_real_toNNReal

theorem aux_in_cutoff_fdd_start_continuity_kernel_eq_of_laplace
    {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
    [MeasurableSpace alpha] [BorelSpace alpha]
    [SecondCountableTopology alpha] [LocallyCompactSpace alpha]
    (P Q : SubMarkovKernelSemigroup alpha)
    (hQ : Q.IsFellerKernelSemigroup)
    (K : alpha → Measure (ContinuousPath alpha))
    (hKfinite : ∀ x, IsFiniteMeasure (K x))
    (hmap : ∀ (t : ℝ≥0) (x : alpha),
      Measure.map (ContinuousPath.eval t) (K x) = P t x)
    (hlap : ∀ (mu : Semigroup.PositiveShift)
      (g : ZeroAtInftyContinuousMap alpha ℝ) (x : alpha),
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
          kernelIntegral (P (Real.toNNReal t)) g x) =
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
          kernelIntegral (Q (Real.toNNReal t)) g x) :
    P = Q := by
  apply SubMarkovKernelSemigroup.ext
  intro t
  apply Kernel.ext
  intro x
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  let : IsFiniteMeasure (P t x) := IsFiniteKernel.isFiniteMeasure x
  let : IsFiniteKernel (Q t) := (Q.isSubMarkovKernel t).isFiniteKernel
  let : IsFiniteMeasure (Q t x) := IsFiniteKernel.isFiniteMeasure x
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let g : ZeroAtInftyContinuousMap alpha ℝ :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  have hgf : ∀ y, g y = f y := by
    intro y
    exact PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply f y
  have hPcont : Continuous (fun s : ℝ =>
      kernelIntegral (P (Real.toNNReal s)) g x) :=
    aux_in_cutoff_fdd_start_continuity_kernelIntegral_continuous
      P K hKfinite hmap g x
  have hQcontNN : Continuous (fun s : ℝ≥0 =>
      kernelIntegral (Q s) g x) := by
    have hpair : Continuous
        (fun f : BoundedContinuousFunction alpha ℝ => (f, x)) :=
      (continuous_id.prodMk
        (continuous_const : Continuous (fun _ : BoundedContinuousFunction alpha ℝ => x)))
    have hEvalBCF : Continuous (fun f : BoundedContinuousFunction alpha ℝ => f x) :=
      by simpa only [Function.comp_def] using!
        (continuous_apply x).comp BoundedContinuousFunction.continuous_coe
    have hEval : Continuous
        (fun f : ZeroAtInftyContinuousMap alpha ℝ => f x) :=
      hEvalBCF.comp ZeroAtInftyContinuousMap.isometry_toBCF.continuous
    change Continuous (fun s : ℝ≥0 => hQ.c0Semigroup s g x)
    exact hEval.comp (hQ.c0Semigroup.continuous g)
  have hQcont : Continuous (fun s : ℝ =>
      kernelIntegral (Q (Real.toNNReal s)) g x) :=
    hQcontNN.comp continuous_real_toNNReal
  have hnormP : ∀ s : ℝ,
      |kernelIntegral (P (Real.toNNReal s)) g x| ≤ ‖g.toBCF‖ := by
    intro s
    let : IsFiniteKernel (P (Real.toNNReal s)) :=
      (P.isSubMarkovKernel (Real.toNNReal s)).isFiniteKernel
    let : IsFiniteMeasure (P (Real.toNNReal s) x) :=
      IsFiniteKernel.isFiniteMeasure x
    have hbound : ∀ᵐ y ∂(P (Real.toNNReal s) x),
        ‖g y‖ ≤ ‖g.toBCF‖ := Filter.Eventually.of_forall fun y =>
      g.toBCF.norm_coe_le_norm y
    have hnorm := norm_integral_le_of_norm_le_const hbound
    have hmass := (P.isSubMarkovKernel (Real.toNNReal s) x)
    rw [Real.norm_eq_abs] at hnorm
    change ‖∫ y, g y ∂P (Real.toNNReal s) x‖ ≤ ‖g.toBCF‖ *
      (P (Real.toNNReal s) x).real Set.univ at hnorm
    have hreal : (P (Real.toNNReal s) x).real Set.univ ≤ 1 := by
      rw [Measure.real_def]
      exact ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top |>.2
        hmass
    calc
      |kernelIntegral (P (Real.toNNReal s)) g x| ≤
          ‖g.toBCF‖ * (P (Real.toNNReal s) x).real Set.univ := hnorm
      _ ≤ ‖g.toBCF‖ * 1 := mul_le_mul_of_nonneg_left hreal (norm_nonneg _)
      _ = ‖g.toBCF‖ := mul_one _
  have hnormQ : ∀ s : ℝ,
      |kernelIntegral (Q (Real.toNNReal s)) g x| ≤ ‖g.toBCF‖ := by
    intro s
    let : IsFiniteKernel (Q (Real.toNNReal s)) :=
      (Q.isSubMarkovKernel (Real.toNNReal s)).isFiniteKernel
    let : IsFiniteMeasure (Q (Real.toNNReal s) x) :=
      IsFiniteKernel.isFiniteMeasure x
    have hbound : ∀ᵐ y ∂(Q (Real.toNNReal s) x),
        ‖g y‖ ≤ ‖g.toBCF‖ := Filter.Eventually.of_forall fun y =>
      g.toBCF.norm_coe_le_norm y
    have hnorm := norm_integral_le_of_norm_le_const hbound
    have hmass := (Q.isSubMarkovKernel (Real.toNNReal s) x)
    rw [Real.norm_eq_abs] at hnorm
    change ‖∫ y, g y ∂Q (Real.toNNReal s) x‖ ≤ ‖g.toBCF‖ *
      (Q (Real.toNNReal s) x).real Set.univ at hnorm
    have hreal : (Q (Real.toNNReal s) x).real Set.univ ≤ 1 := by
      rw [Measure.real_def]
      exact ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top |>.2
        hmass
    calc
      |kernelIntegral (Q (Real.toNNReal s)) g x| ≤
          ‖g.toBCF‖ * (Q (Real.toNNReal s) x).real Set.univ := hnorm
      _ ≤ ‖g.toBCF‖ * 1 := mul_le_mul_of_nonneg_left hreal (norm_nonneg _)
      _ = ‖g.toBCF‖ := mul_one _
  have hscalar : ∀ s : ℝ, 0 ≤ s →
      kernelIntegral (P (Real.toNNReal s)) g x =
        kernelIntegral (Q (Real.toNNReal s)) g x := by
    intro s hs
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.eq_of_forall_integral_exp_neg_mul_eq
      hPcont hQcont hnormP hnormQ (fun mu hmu => by
        have hcoe : ((⟨mu, hmu⟩ : Semigroup.PositiveShift) : ℝ) = mu := rfl
        simpa only [hcoe, neg_mul] using hlap ⟨mu, hmu⟩ g x) s hs
  calc
    ∫ y, f y ∂P t x = ∫ y, g y ∂P t x := by simp only [hgf]
    _ = ∫ y, g y ∂Q t x := by
      change kernelIntegral (P t) g x = kernelIntegral (Q t) g x
      simpa using hscalar (t : ℝ) (NNReal.coe_nonneg t)
    _ = ∫ y, f y ∂Q t x := by simp only [hgf]



theorem in_cutoff_fdd_start_continuity
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hin : in_crossing M H PN KN) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ I : Finset ℝ≥0,
        ∀ f : BoundedContinuousFunction (I → SpatialCoordinates d) ℝ,
          Continuous (fun x : SpatialCoordinates d =>
            ∫ y, f y ∂((KN N).map (ContinuousPath.finsetEvaluation I)
              (omega, x))) := by
  rcases hin with ⟨hres, hcons, hfdd⟩
  filter_upwards [hres, hfdd] with omega hres hfdd
  intro N I f
  obtain ⟨D, hDdense, hDweak, hDlap⟩ := hres N
  let Q : SubMarkovKernelSemigroup (SpatialCoordinates d) :=
    D.fellerKernelSemigroup hDdense
  have hQfeller : Q.IsFellerKernelSemigroup := by
    exact D.isFellerKernelSemigroup_fellerKernelSemigroup hDdense
  have hmap : ∀ (t : ℝ≥0) (x : SpatialCoordinates d),
      Measure.map (ContinuousPath.eval t) (KN N (omega, x)) =
        (PN N omega) t x := by
    intro t x
    simpa only [Kernel.map_apply, ContinuousPath.eval] using!
      (SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation
        (PN N omega) (KN N (omega, x)) x t
        (by
          have h := hfdd N ({t} : Finset ℝ≥0) x
          rw [Kernel.map_apply (KN N)
            (ContinuousPath.measurable_finsetEvaluation ({t} : Finset ℝ≥0))] at h
          exact h))
  have hKfinite : ∀ x, IsFiniteMeasure (KN N (omega, x)) := by
    intro x
    have hmass : (KN N (omega, x)) Set.univ = 1 := by
      calc
        (KN N (omega, x)) Set.univ =
            Measure.map (ContinuousPath.eval (0 : ℝ≥0))
              (KN N (omega, x)) Set.univ := by
                rw [Measure.map_apply (ContinuousPath.continuous_eval 0).measurable
                  MeasurableSet.univ, Set.preimage_univ]
        _ = (PN N omega) 0 x Set.univ := by rw [hmap 0 x]
        _ = 1 := by
          let : IsMarkovKernel ((PN N omega) 0) :=
            (hcons N omega).isMarkovKernel 0
          exact IsProbabilityMeasure.measure_univ
    exact ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  have hEq : PN N omega = Q := by
    apply aux_in_cutoff_fdd_start_continuity_kernel_eq_of_laplace
      (PN N omega) Q hQfeller (fun x => KN N (omega, x)) hKfinite hmap
    intro mu g x
    calc
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
          kernelIntegral ((PN N omega) (Real.toNNReal t)) g x) =
          D.solution mu g x := (hDlap mu g x).symm
      _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
          kernelIntegral (Q (Real.toNNReal t)) g x := by
            simpa only [Q] using D.solution_eq_laplace hDdense mu g x
  have hQcons : Q.IsConservative := by
    rw [← hEq]
    exact hcons N omega
  have hcont :=
    hQfeller.continuous_integral_boundedContinuous_finiteSetKernel hQcons I f
  refine hcont.congr ?_
  intro x
  rw [hfdd N I x, hEq]

end SubdiffusiveProcess.Paper
