module

public import SubdiffusiveProcess.Paper.physical_rescaling_kernel_conjugacy
public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.MultiplicativeChaos.RescaledPath
public import SubdiffusiveProcess.Main.PhysicalTimeFactor
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Paper.physical_generator_reindexing
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.physical_rescaling_finite_dimensional
public import MarkovProcess.Trajectory.Equivariance
public import SubdiffusiveProcess.Processes.FiniteEvaluationMeasureDetermination

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_physical_rescaling_ordered_marginal
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (μ : Measure (DiffusionPath d)) (x : SpatialCoordinates d)
    (hμ : ∀ I : Finset NNReal,
      μ.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel P I x)
    {n : ℕ} (times : FiniteOrderedTimes n) :
    μ.map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) =
      SubMarkovKernelSemigroup.finiteTimeKernel P times x := by
  classical
  let I : Finset NNReal :=
    Finset.image (fun j ↦ times j) (Finset.univ : Finset (Fin n))
  have hmem : ∀ i : Fin n,
      times i ∈ Finset.image (fun j ↦ times j) (Finset.univ : Finset (Fin n)) :=
    fun i ↦ Finset.mem_image_of_mem _ (Finset.mem_univ i)
  let phi : Fin n ↪o I :=
    OrderEmbedding.ofStrictMono (fun i ↦ (⟨times i, hmem i⟩ : I))
      (fun _ _ hij ↦ times.strictMono hij)
  let emb : Fin n ↪o Fin I.card :=
    phi.trans (I.orderIsoOfFin rfl).symm.toOrderEmbedding
  have hphi : ∀ i : Fin n, ((phi i : I) : NNReal) = times i :=
    fun _ ↦ rfl
  have hsel : Measurable (fun w : I → SpatialCoordinates d =>
      w ∘ (phi : Fin n → I)) := by
    exact measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (phi i)
  have hfinset : Measurable
      (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) I) :=
    ContinuousPath.measurable_finsetEvaluation I
  have hcomp : ContinuousPath.finiteEvaluation (α := SpatialCoordinates d)
      (fun i ↦ times i) =
      (fun w : I → SpatialCoordinates d => w ∘ (phi : Fin n → I)) ∘
        ContinuousPath.finsetEvaluation I := by
    funext path i
    rfl
  have hrestrict :
      (fun w : I → SpatialCoordinates d => w ∘ (phi : Fin n → I)) ∘
          SubMarkovKernelSemigroup.orderedPathToFiniteSet I =
        FiniteOrderedTimes.restrictPath emb := by
    rfl
  have htimes : (SubMarkovKernelSemigroup.finiteSetTimes I).restrict emb = times := by
    apply DFunLike.ext _ _
    intro i
    show SubMarkovKernelSemigroup.finiteSetTimes I
        ((I.orderIsoOfFin rfl).symm (phi i)) = times i
    rw [SubMarkovKernelSemigroup.finiteSetTimes_orderIsoOfFin_symm_apply, hphi i]
  have hset : SubMarkovKernelSemigroup.finiteSetKernel P I x =
      (SubMarkovKernelSemigroup.finiteTimeKernel P
        (SubMarkovKernelSemigroup.finiteSetTimes I) x).map
          (SubMarkovKernelSemigroup.orderedPathToFiniteSet I) := by
    rw [← Kernel.map_apply _
      (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)]
    exact congrArg (fun K : Kernel (SpatialCoordinates d) (I → SpatialCoordinates d) => K x)
      (SubMarkovKernelSemigroup.finiteSetKernel_eq_map P I)
  calc
    μ.map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) =
        (μ.map (ContinuousPath.finsetEvaluation I)).map
          (fun w : I → SpatialCoordinates d => w ∘ (phi : Fin n → I)) := by
      rw [hcomp, ← Measure.map_map hsel hfinset]
    _ = (SubMarkovKernelSemigroup.finiteSetKernel P I x).map
          (fun w : I → SpatialCoordinates d => w ∘ (phi : Fin n → I)) := by
      rw [hμ I]
    _ = ((SubMarkovKernelSemigroup.finiteTimeKernel P
        (SubMarkovKernelSemigroup.finiteSetTimes I) x).map
          (SubMarkovKernelSemigroup.orderedPathToFiniteSet I)).map
            (fun w : I → SpatialCoordinates d => w ∘ (phi : Fin n → I)) := by
      rw [hset]
    _ = (SubMarkovKernelSemigroup.finiteTimeKernel P
        (SubMarkovKernelSemigroup.finiteSetTimes I) x).map
          (FiniteOrderedTimes.restrictPath emb) := by
      rw [Measure.map_map hsel
        (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I), hrestrict]
    _ = SubMarkovKernelSemigroup.finiteTimeKernel P
        ((SubMarkovKernelSemigroup.finiteSetTimes I).restrict emb) x := by
      rw [← Kernel.map_apply _ (FiniteOrderedTimes.measurable_restrictPath emb)]
      exact congrArg (fun K : Kernel (SpatialCoordinates d) (Fin n → SpatialCoordinates d) => K x)
        (hP.finiteTimeKernel_map_restrictPath P
          (SubMarkovKernelSemigroup.finiteSetTimes I) emb)
    _ = SubMarkovKernelSemigroup.finiteTimeKernel P times x := by rw [htimes]

theorem aux_physical_rescaling_path_measure
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P P' : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : P.IsConservative)
    (K K' : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hKmarg : ∀ I : Finset NNReal, ∀ x : SpatialCoordinates d,
      (K x).map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (hK'marg : ∀ I : Finset NNReal, ∀ x : SpatialCoordinates d,
      (K' x).map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel P' I x)
    {e : SpatialCoordinates d ≃ₜ SpatialCoordinates d} {c : NNReal}
    (hc : 0 < c)
    (hconj : SubMarkovKernelSemigroup.IsRescaledConjugate P P' e c) :
    ∀ x : SpatialCoordinates d,
      Measure.map (ContinuousPath.rescale e c) (K (e.symm x)) = K' x := by
  classical
  let : IsMarkovKernel K := hK
  intro x
  apply SubdiffusiveProcess.path_measure_eq_of_finiteEvaluation_map_eq
    (Measure.map (ContinuousPath.rescale e c) (K (e.symm x))) (K' x)
  intro I
  let hmapPath : Measurable
      ((FiniteOrderedTimes.mapPath e : (I → SpatialCoordinates d) → I → SpatialCoordinates d) ∘
        SubMarkovKernelSemigroup.orderedPathToFiniteSet I) :=
    (FiniteOrderedTimes.measurable_mapPath e.measurable).comp
      (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)
  let hfinite : Measurable (ContinuousPath.finiteEvaluation
      (α := SpatialCoordinates d)
      (fun i ↦ ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc) i)) :=
    ContinuousPath.measurable_finiteEvaluation _
  have hcomp : ContinuousPath.finsetEvaluation I ∘
        ContinuousPath.rescale e c =
      ((FiniteOrderedTimes.mapPath e : (I → SpatialCoordinates d) → I → SpatialCoordinates d) ∘
        SubMarkovKernelSemigroup.orderedPathToFiniteSet I) ∘
        ContinuousPath.finiteEvaluation
          (fun i ↦ ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc) i) := by
    funext path t
    show e (path (c * (t : NNReal))) =
      e (path (c * SubMarkovKernelSemigroup.finiteSetTimes I
        ((I.orderIsoOfFin rfl).symm t)))
    rw [SubMarkovKernelSemigroup.finiteSetTimes_orderIsoOfFin_symm_apply]
  have hordered := aux_physical_rescaling_ordered_marginal P hP (K (e.symm x)) (e.symm x)
    (fun J ↦ hKmarg J (e.symm x))
    ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc)
  have hfinite' := hconj.finiteSetKernel_eq hc hP I
  have hfinite'x := congrArg
    (fun Q : Kernel (SpatialCoordinates d) (I → SpatialCoordinates d) => Q x) hfinite'
  change SubMarkovKernelSemigroup.finiteSetKernel P' I x =
      ((Kernel.comap
          (SubMarkovKernelSemigroup.finiteTimeKernel P
            ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc))
          e.symm e.symm.measurable).map
        ((FiniteOrderedTimes.mapPath e : (I → SpatialCoordinates d) → I → SpatialCoordinates d) ∘
          SubMarkovKernelSemigroup.orderedPathToFiniteSet I)) x at hfinite'x
  rw [Kernel.map_apply _ hmapPath, Kernel.comap_apply] at hfinite'x
  calc
    (Measure.map (ContinuousPath.rescale e c) (K (e.symm x))).map
        (ContinuousPath.finsetEvaluation I) =
        (K (e.symm x)).map (ContinuousPath.finsetEvaluation I ∘
          ContinuousPath.rescale e c) := by
      rw [Measure.map_map (ContinuousPath.measurable_finsetEvaluation I)
        (ContinuousPath.measurable_rescale e c)]
    _ = (K (e.symm x)).map (
          ((FiniteOrderedTimes.mapPath e : (I → SpatialCoordinates d) → I → SpatialCoordinates d) ∘
            SubMarkovKernelSemigroup.orderedPathToFiniteSet I) ∘
            ContinuousPath.finiteEvaluation
              (fun i ↦ ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc) i)) := by
      rw [hcomp]
    _ = ((K (e.symm x)).map (ContinuousPath.finiteEvaluation
          (fun i ↦ ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc) i))).map
            ((FiniteOrderedTimes.mapPath e : (I → SpatialCoordinates d) → I → SpatialCoordinates d) ∘
              SubMarkovKernelSemigroup.orderedPathToFiniteSet I) := by
      rw [Measure.map_map hmapPath hfinite]
    _ = ((SubMarkovKernelSemigroup.finiteTimeKernel P
          ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc) (e.symm x)).map
            ((FiniteOrderedTimes.mapPath e : (I → SpatialCoordinates d) → I → SpatialCoordinates d) ∘
              SubMarkovKernelSemigroup.orderedPathToFiniteSet I)) := by
      rw [hordered]
    _ = SubMarkovKernelSemigroup.finiteSetKernel P' I x := hfinite'x.symm
    _ = (K' x).map (ContinuousPath.finsetEvaluation I) := (hK'marg I x).symm




theorem physical_rescaling
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (sigma : ℕ → BilateralField d → BilateralField d)
    (hsigmadef : ∀ N omega (j : ℤ) (x : SpatialCoordinates d),
      sigma N omega j x = omega (j + (N : ℤ)) (((3 : ℝ) ^ N) • x)) :
    (∀ N : ℕ, MeasurePreserving (sigma N) (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure) ∧
    (∀ N : ℕ, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ x : SpatialCoordinates d,
        Measure.map (physicalRescaledPath M N)
            (KN 0 (omega, (3 : ℝ) ^ N • x))
          = KN N (sigma N omega, x)) ∧
    ∀ (N : ℕ) (x : SpatialCoordinates d)
        (F : BoundedContinuousFunction (DiffusionPath d) ℝ),
      ∫ omega, (∫ path, F (physicalRescaledPath M N path)
            ∂(KN 0 (omega, (3 : ℝ) ^ N • x)))
          ∂(chaosSampleLaw M).toMeasure
        = ∫ omega, (∫ path, F path ∂(KN N (omega, x)))
          ∂(chaosSampleLaw M).toMeasure := by
  have hconjAE := physical_rescaling_kernel_conjugacy
    hd M H hH PN KN hKN hin sigma hsigmadef
  have hmp : ∀ N : ℕ, MeasurePreserving (sigma N)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
    intro N
    exact aux_physical_generator_reindexing_sigma_measurePreserving
      M sigma hsigmadef N
  have hpathAE : ∀ N : ℕ, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ x : SpatialCoordinates d,
        Measure.map (physicalRescaledPath M N)
            (KN 0 (omega, (3 : ℝ) ^ N • x)) = KN N (sigma N omega, x) := by
    intro N
    have hfdSigmaAE :=
      (aux_physical_generator_reindexing_sigma_measurePreserving M sigma hsigmadef N).quasiMeasurePreserving.ae
        hin.2.2
    filter_upwards [hconjAE N, hin.2.2, hfdSigmaAE] with omega hconj hfd hfdSigma
    intro x
    let r : ℝ := ((3 : ℝ)⁻¹ ^ N)
    have hr : r ≠ 0 := by
      dsimp [r]
      positivity
    let e : SpatialCoordinates d ≃ₜ SpatialCoordinates d :=
      Homeomorph.smulOfNeZero r hr
    have he : ∀ y : SpatialCoordinates d, e y = r • y := by
      intro y
      rfl
    have hes : ∀ y : SpatialCoordinates d, e.symm y = ((3 : ℝ) ^ N) • y := by
      intro y
      rw [Homeomorph.smulOfNeZero_symm_apply hr]
      simp [r]
    have hc : 0 < physicalTimeFactor M N := by
      change (0 : ℝ) <
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * (3 : ℝ) ^ (2 * N) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
      exact div_pos
        (mul_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0)
          (pow_pos (by norm_num) _))
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
    have hpath : physicalRescaledPath M N =
        ContinuousPath.rescale e (physicalTimeFactor M N) := by
      funext path
      ext t
      simp only [physicalRescaledPath, ContinuousPath.rescale,
        ContinuousPath.timeScaling_apply, ContinuousMap.smul_apply,
        ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      exact congrArg (fun z : SpatialCoordinates d => z _) (he _).symm
    have hconj' :
        SubMarkovKernelSemigroup.IsRescaledConjugate (PN 0 omega)
          (PN N (sigma N omega)) e (physicalTimeFactor M N) := by
      intro t y
      calc
        PN N (sigma N omega) t y =
            Measure.map (fun z => r • z)
              (PN 0 omega (physicalTimeFactor M N * t) (((3 : ℝ) ^ N) • y)) :=
          hconj t y
        _ = Measure.map (e : SpatialCoordinates d → SpatialCoordinates d)
              (PN 0 omega (physicalTimeFactor M N * t) (e.symm y)) := by
          rw [hes y, show (fun z : SpatialCoordinates d => r • z) = e from funext he]
    let K0 : Kernel (SpatialCoordinates d) (DiffusionPath d) :=
      Kernel.comap (KN 0) (fun y => (omega, y))
        (measurable_const.prodMk measurable_id)
    let K1 : Kernel (SpatialCoordinates d) (DiffusionPath d) :=
      Kernel.comap (KN N) (fun y => (sigma N omega, y))
        (measurable_const.prodMk measurable_id)
    let : IsMarkovKernel (KN 0) := hKN 0
    let : IsMarkovKernel (KN N) := hKN N
    have hK0 : IsMarkovKernel K0 := by
      dsimp [K0]
      infer_instance
    have hK0marg : ∀ I : Finset NNReal, ∀ y : SpatialCoordinates d,
        (K0 y).map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel (PN 0 omega) I y := by
      intro I y
      simpa only [K0, Kernel.comap_apply,
        Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)] using hfd 0 I y
    have hK1marg : ∀ I : Finset NNReal, ∀ y : SpatialCoordinates d,
        (K1 y).map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel (PN N (sigma N omega)) I y := by
      intro I y
      simpa only [K1, Kernel.comap_apply,
        Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)] using hfdSigma N I y
    have htransport := aux_physical_rescaling_path_measure
      (PN 0 omega) (PN N (sigma N omega)) (hin.2.1 0 omega)
      K0 K1 hK0 hK0marg hK1marg hc hconj'
    have hx := htransport x
    simpa only [K0, K1, Kernel.comap_apply, hes, hpath] using hx

  refine ⟨hmp, hpathAE, ?_⟩
  intro N x F
  let : IsMarkovKernel (KN N) := hKN N
  let G : BilateralField d → ℝ := fun omega ↦
    ∫ path, F path ∂(KN N (omega, x))
  have hGsm : StronglyMeasurable G := by
    let Kx : Kernel (BilateralField d) (DiffusionPath d) :=
      Kernel.comap (KN N) (fun omega => (omega, x))
        (measurable_id.prodMk measurable_const)
    have h := (F.continuous.stronglyMeasurable).integral_kernel (κ := Kx)
    simpa only [G, Kx, Kernel.comap_apply] using h
  have hGbound : ∀ omega : BilateralField d, ‖G omega‖ ≤ ‖F‖ := by
    intro omega
    dsimp [G]
    have hb := norm_integral_le_of_norm_le_const
      (μ := KN N (omega, x)) (f := fun path => F path) (C := ‖F‖) (by
        filter_upwards [] with path
        exact F.norm_coe_le_norm path)
    simpa using hb
  have hGint : Integrable G (chaosSampleLaw M).toMeasure := by
    exact Integrable.of_bound hGsm.aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall hGbound)
  have hpoint : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (∫ path, F (physicalRescaledPath M N path)
          ∂(KN 0 (omega, (3 : ℝ) ^ N • x))) = G (sigma N omega) := by
    filter_upwards [hpathAE N] with omega hω
    have hωx := hω x
    have hi := congrArg
      (fun μ : Measure (DiffusionPath d) => ∫ path, F path ∂μ) hωx
    change (∫ path, F path ∂(Measure.map (physicalRescaledPath M N)
        (KN 0 (omega, (3 : ℝ) ^ N • x)))) =
      ∫ path, F path ∂(KN N (sigma N omega, x)) at hi
    rw [MeasureTheory.integral_map_of_stronglyMeasurable
      (measurable_physicalRescaledPath M N) F.continuous.stronglyMeasurable] at hi
    simpa only [G] using hi
  have hchange :
      (∫ omega, G (sigma N omega) ∂(chaosSampleLaw M).toMeasure) =
        ∫ omega, G omega ∂(chaosSampleLaw M).toMeasure := by
    have hi := MeasureTheory.integral_map_of_stronglyMeasurable
      (μ := (chaosSampleLaw M).toMeasure) (hmp N).measurable hGsm
    rw [(hmp N).map_eq] at hi
    exact hi.symm
  calc
    ∫ omega, (∫ path, F (physicalRescaledPath M N path)
          ∂(KN 0 (omega, (3 : ℝ) ^ N • x)))
        ∂(chaosSampleLaw M).toMeasure =
      ∫ omega, G (sigma N omega) ∂(chaosSampleLaw M).toMeasure :=
        integral_congr_ae hpoint
    _ = ∫ omega, G omega ∂(chaosSampleLaw M).toMeasure := hchange

end SubdiffusiveProcess.Paper

