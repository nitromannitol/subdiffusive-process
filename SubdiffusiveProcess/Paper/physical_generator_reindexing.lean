module

public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.in_common_scale_coupling
public import SubdiffusiveProcess.Paper.relabelled_layer_law
public import SubdiffusiveProcess.Paper.potential_gauge_invariance
public import SubdiffusiveProcess.Paper.coefficient_physical_identity
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffPotential
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.Lane1.RescaledPath
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

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
open scoped BigOperators

namespace Paper

theorem aux_physical_generator_reindexing_sigma_measurePreserving
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (sigma : ℕ → BilateralField d → BilateralField d)
    (hsigmadef : ∀ N omega (j : ℤ) (x : SpatialCoordinates d),
      sigma N omega j x = omega (j + (N : ℤ)) (((3 : ℝ) ^ N) • x))
    (N : ℕ) :
    MeasurePreserving (sigma N) (chaosSampleLaw M).toMeasure
      (chaosSampleLaw M).toMeasure := by
  let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) := chaosRootFieldLaw M
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  have hcoord : ∀ j : ℤ, Measurable (fun omega : BilateralField d => sigma N omega j) := by
    intro j
    have hbase : Measurable (fun omega : BilateralField d =>
        SubdiffusiveProcess.layerScaling d (-(N : ℤ)) (omega (j + (N : ℤ)))) :=
      (SubdiffusiveProcess.layerScaling d (-(N : ℤ))).continuous.measurable.comp
        (measurable_pi_apply (j + (N : ℤ)))
    have heq : (fun omega : BilateralField d => sigma N omega j) =
        (fun omega : BilateralField d =>
          SubdiffusiveProcess.layerScaling d (-(N : ℤ))
            (omega (j + (N : ℤ)))) := by
      funext omega
      apply ContinuousMap.ext
      intro x
      rw [hsigmadef]
      simp only [SubdiffusiveProcess.layerScaling,
        ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
        Function.comp_apply, ContinuousMap.coe_mk]
      congr 2
      rw [zpow_neg]
      simp
    rw [heq]
    exact hbase
  have hmeas : Measurable (sigma N) := measurable_pi_iff.mpr (fun j => hcoord j)
  have hshift :
      Measure.map (fun omega : BilateralField d => fun j : ℤ =>
          omega (j + (N : ℤ))) (Measure.infinitePi laws) =
        Measure.infinitePi (fun j : ℤ => laws (j + (N : ℤ))) := by
    let e : ℤ ≃ ℤ := Equiv.subRight (N : ℤ)
    have h := Measure.infinitePi_map_piCongrLeft
      (μ := fun j : ℤ => laws (j + (N : ℤ))) e
    have heq :
        (fun z : (j : ℤ) → C(SpatialCoordinates d, ℝ) =>
            (MeasurableEquiv.piCongrLeft
              (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) e) z) =
          (fun z : (j : ℤ) → C(SpatialCoordinates d, ℝ) =>
            fun j => z (j + (N : ℤ))) := by
      funext z j
      simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    rw [← heq]
    convert h using 1 <;> simp [e]
  have hscaled : ∀ j : ℤ,
      Measure.map (SubdiffusiveProcess.layerScaling d (-(N : ℤ)))
          (laws (j + (N : ℤ))) = laws j := by
    intro j
    change Measure.map (SubdiffusiveProcess.layerScaling d (-(N : ℤ)))
        (Measure.map (SubdiffusiveProcess.layerScaling d (j + (N : ℤ)))
          ν.toMeasure) = Measure.map (SubdiffusiveProcess.layerScaling d j) ν.toMeasure
    calc
      Measure.map (SubdiffusiveProcess.layerScaling d (-(N : ℤ)))
          (Measure.map (SubdiffusiveProcess.layerScaling d (j + (N : ℤ)))
            ν.toMeasure) =
          Measure.map
            (SubdiffusiveProcess.layerScaling d (-(N : ℤ)) ∘
              SubdiffusiveProcess.layerScaling d (j + (N : ℤ))) ν.toMeasure :=
        Measure.map_map
          (SubdiffusiveProcess.layerScaling d (-(N : ℤ))).continuous.measurable
          (SubdiffusiveProcess.layerScaling d (j + (N : ℤ))).continuous.measurable
      _ = Measure.map (SubdiffusiveProcess.layerScaling d j) ν.toMeasure := by
        congr 1
        funext f
        apply ContinuousMap.ext
        intro x
        simp only [SubdiffusiveProcess.layerScaling,
          ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
          Function.comp_apply, ContinuousMap.coe_mk]
        rw [smul_smul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        congr 2
        ring_nf
  have hscale :
      Measure.map (fun z : (j : ℤ) → C(SpatialCoordinates d, ℝ) =>
          fun j : ℤ =>
            SubdiffusiveProcess.layerScaling d (-(N : ℤ)) (z j))
        (Measure.infinitePi (fun j : ℤ => laws (j + (N : ℤ)))) =
      Measure.infinitePi (fun j : ℤ => laws j) := by
    rw [Measure.infinitePi_map_pi
      (μ := fun j : ℤ => laws (j + (N : ℤ)))
      (f := fun _ : ℤ => SubdiffusiveProcess.layerScaling d (-(N : ℤ)))
      (fun _ => (SubdiffusiveProcess.layerScaling d (-(N : ℤ))).continuous.measurable)]
    congr 1
    funext j
    exact hscaled j
  have hmap :
      Measure.map (fun omega : BilateralField d =>
          fun j : ℤ =>
            SubdiffusiveProcess.layerScaling d (-(N : ℤ))
              (omega (j + (N : ℤ)))) (Measure.infinitePi laws) =
        Measure.infinitePi laws := by
    let shift : BilateralField d → BilateralField d := fun omega j =>
      omega (j + (N : ℤ))
    let scale : BilateralField d → BilateralField d := fun z j =>
      SubdiffusiveProcess.layerScaling d (-(N : ℤ)) (z j)
    have hshiftMeas : Measurable shift := measurable_pi_iff.mpr (fun j =>
      measurable_pi_apply (j + (N : ℤ)))
    have hscaleMeas : Measurable scale := measurable_pi_iff.mpr (fun j =>
      (SubdiffusiveProcess.layerScaling d (-(N : ℤ))).continuous.measurable.comp
        (measurable_pi_apply j))
    have hshift' : Measure.map shift (Measure.infinitePi laws) =
        Measure.infinitePi (fun j : ℤ => laws (j + (N : ℤ))) := by
      simpa only [shift] using hshift
    have hscale' : Measure.map scale
        (Measure.infinitePi (fun j : ℤ => laws (j + (N : ℤ)))) =
        Measure.infinitePi laws := by
      simpa only [scale] using hscale
    have hcomp : scale ∘ shift =
        (fun omega : BilateralField d => fun j : ℤ =>
          SubdiffusiveProcess.layerScaling d (-(N : ℤ))
            (omega (j + (N : ℤ)))) := by
      rfl
    calc
      Measure.map (fun omega : BilateralField d => fun j : ℤ =>
          SubdiffusiveProcess.layerScaling d (-(N : ℤ))
            (omega (j + (N : ℤ)))) (Measure.infinitePi laws) =
          Measure.map (scale ∘ shift) (Measure.infinitePi laws) := by rw [hcomp]
      _ = Measure.map scale (Measure.map shift (Measure.infinitePi laws)) := by
        rw [Measure.map_map hscaleMeas hshiftMeas]
      _ = Measure.map scale
          (Measure.infinitePi (fun j : ℤ => laws (j + (N : ℤ)))) := by rw [hshift']
      _ = Measure.infinitePi laws := hscale'
  refine ⟨hmeas, ?_⟩
  have heq : sigma N =
      (fun omega : BilateralField d => fun j : ℤ =>
        SubdiffusiveProcess.layerScaling d (-(N : ℤ))
          (omega (j + (N : ℤ)))) := by
    funext omega j
    apply ContinuousMap.ext
    intro x
    rw [hsigmadef]
    simp only [SubdiffusiveProcess.layerScaling,
      ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
      Function.comp_apply, ContinuousMap.coe_mk]
    congr 2
    rw [zpow_neg]
    simp
  rw [heq]
  simpa only [chaosSampleLaw, commonScaleLaw, ν, laws] using! hmap

theorem aux_physical_generator_reindexing_finite_sum
    (N : ℕ) (A B : ℝ) (q : ℕ → ℝ)
    (hrel : A = B + ∑ i ∈ Finset.range N, q (i + 1)) :
    A + q 0 = B + ∑ i ∈ Finset.range (N + 1), q i := by
  rw [hrel, Finset.sum_range_succ' q N]
  ring

theorem aux_physical_generator_reindexing_potential_identity
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (sigma : ℕ → BilateralField d → BilateralField d)
    (hsigmadef : ∀ N omega (j : ℤ) (x : SpatialCoordinates d),
      sigma N omega j x = omega (j + (N : ℤ)) (((3 : ℝ) ^ N) • x))
    (μ : Measure (BilateralField d))
    (hseries : ∀ᵐ omega ∂μ,
      ∀ x : SpatialCoordinates d, HasSum
        (fun n : ℕ => omega (Int.ofNat (n + 1)) x - omega (Int.ofNat (n + 1)) 0)
        (H omega x))
    (hmp : ∀ N, MeasurePreserving (sigma N) μ μ) :
    ∀ N, ∀ᵐ omega ∂μ, ∀ x : SpatialCoordinates d,
      cutoffPotential H omega 0 (((3 : ℝ) ^ N) • x) - omega 0 0 =
        cutoffPotential H (sigma N omega) N x -
          ∑ i ∈ Finset.range (N + 1), (sigma N omega) (-(i : Int)) 0 := by
  intro N
  have hsigma := (hmp N).quasiMeasurePreserving.ae hseries
  filter_upwards [hseries, hsigma] with omega hω hσω
  intro x
  let y : SpatialCoordinates d := ((3 : ℝ) ^ N) • x
  let q : ℕ → ℝ := fun k =>
    omega (Int.ofNat k) y - omega (Int.ofNat k) 0
  have hfull : HasSum (fun n : ℕ => q (n + 1)) (H omega y) := by
    simpa only [q] using hω y
  have htail : HasSum
      (fun n : ℕ => (sigma N omega) (Int.ofNat (n + 1)) x -
        (sigma N omega) (Int.ofNat (n + 1)) 0) (H (sigma N omega) x) :=
    hσω x
  have htail' : HasSum (fun n : ℕ => q (n + N + 1)) (H (sigma N omega) x) := by
    convert htail using 1
    funext n
    dsimp [q, y]
    rw [hsigmadef, hsigmadef]
    simp only [smul_zero]
    congr 1 <;> ring
  have htailSum : HasSum (fun n : ℕ => q (n + 1))
      (H (sigma N omega) x + ∑ i ∈ Finset.range N, q (i + 1)) := by
    exact (hasSum_nat_add_iff N).1 htail'
  have hrel : H omega y =
      H (sigma N omega) x + ∑ i ∈ Finset.range N, q (i + 1) :=
    hfull.unique htailSum
  have hsum_rev :
      (∑ i ∈ Finset.range (N + 1), q (N - i)) =
        ∑ i ∈ Finset.range (N + 1), q i := by
    have h := Finset.sum_range_reflect q (N + 1)
    convert h using 1 <;> simp [Nat.add_sub_assoc]
  have hsum_sigma :
      (Finset.range (N + 1)).sum (fun i =>
          (sigma N omega) (-(i : Int)) x -
          (sigma N omega) (-(i : Int)) 0) =
        (Finset.range (N + 1)).sum (fun i => q (N - i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsigmadef, hsigmadef]
    dsimp [q, y]
    simp only [smul_zero]
    have hi' : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.1 hi)
    rw [Int.ofNat_sub hi']
    congr 1 <;> ring
  unfold cutoffPotential
  simp only [Nat.zero_add]
  have hleft : (Finset.range 1).sum (fun j =>
      omega (-Int.ofNat j) y) = omega 0 y := by
    simp
  rw [hleft]
  have hsum_sigma_sep :
      (Finset.range (N + 1)).sum (fun i =>
          (sigma N omega) (-(i : Int)) x) -
        (Finset.range (N + 1)).sum (fun i =>
          (sigma N omega) (-(i : Int)) 0) =
      (Finset.range (N + 1)).sum (fun i => q (N - i)) := by
    rw [← Finset.sum_sub_distrib]
    exact hsum_sigma
  have hsum_final :
      (Finset.range (N + 1)).sum (fun i =>
          (sigma N omega) (-Int.ofNat i) x) -
        (Finset.range (N + 1)).sum (fun i =>
          (sigma N omega) (-(i : Int)) 0) =
      (Finset.range (N + 1)).sum (fun i => q i) := by
    calc
      (Finset.range (N + 1)).sum (fun i =>
          (sigma N omega) (-Int.ofNat i) x) -
          (Finset.range (N + 1)).sum (fun i =>
            (sigma N omega) (-(i : Int)) 0) =
        (Finset.range (N + 1)).sum (fun i => q (N - i)) := by
          simpa only [Int.ofNat_eq_coe] using hsum_sigma_sep
      _ = (Finset.range (N + 1)).sum (fun i => q i) := hsum_rev
  have hfinite := aux_physical_generator_reindexing_finite_sum
    N (H omega y) (H (sigma N omega) x) q hrel
  nth_rewrite 2 [add_sub_assoc]
  rw [hsum_final]
  change H omega y + omega 0 y - omega 0 0 =
    H (sigma N omega) x + (Finset.range (N + 1)).sum (fun i => q i)
  calc
    H omega y + omega 0 y - omega 0 0 = H omega y + q 0 := by
      simp only [q, Int.ofNat_zero]
      ring
    _ = H (sigma N omega) x + (Finset.range (N + 1)).sum (fun i => q i) := hfinite



theorem physical_generator_reindexing
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (sigma : ℕ → BilateralField d → BilateralField d)
    (hsigmadef : ∀ N omega (j : ℤ) (x : SpatialCoordinates d),
      sigma N omega j x = omega (j + (N : ℤ)) (((3 : ℝ) ^ N) • x))
    (htransport : ∀ N omega (x : SpatialCoordinates d),
      Measure.map (physicalRescaledPath M N)
        (KN 0 (omega, (3 : ℝ) ^ N • x)) =
          KN N (sigma N omega, x)) :
    let V : BilateralField d → SpatialCoordinates d → ℝ :=
      fun omega y ↦ cutoffPotential H omega 0 y - omega 0 0
    let T : ℕ → ℝ :=
      fun N ↦ (3 : ℝ) ^ (2 * N) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
    let rawPath : DiffusionPath d → DiffusionPath d := fun path ↦
      path.comp
        ⟨fun t ↦ Real.toNNReal (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0) * t,
          continuous_const.mul continuous_id⟩
    let rawRescale : ℕ → DiffusionPath d → DiffusionPath d := fun N path ↦
      ((3 : ℝ)⁻¹ ^ N) • path.comp
        ⟨fun t ↦ Real.toNNReal (T N) * t, continuous_const.mul continuous_id⟩
    (∀ N : ℕ, MeasurePreserving (sigma N)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure) ∧
    (∀ N : ℕ, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ x : SpatialCoordinates d,
        V omega ((3 : ℝ) ^ N • x)
          = cutoffPotential H (sigma N omega) N x
            - ∑ i ∈ Finset.range (N + 1), (sigma N omega) (-(i : Int)) 0) ∧
    (∀ N : ℕ, T N * (3 : ℝ) ^ (-(2 * (N : ℝ))) = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹) ∧
    (∀ N : ℕ, ∀ omega (x : SpatialCoordinates d),
      Measure.map (rawRescale N) (Measure.map rawPath (KN 0 (omega, (3 : ℝ) ^ N • x)))
        = Measure.map (physicalRescaledPath M N) (KN 0 (omega, (3 : ℝ) ^ N • x))) ∧
    (∀ N : ℕ, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∃ Pres : SubMarkovKernelSemigroup (SpatialCoordinates d),
        (∀ (I : Finset NNReal) (x : SpatialCoordinates d),
          (Measure.map (physicalRescaledPath M N)
              (KN 0 (omega, (3 : ℝ) ^ N • x))).map
              (ContinuousPath.finsetEvaluation I)
            = SubMarkovKernelSemigroup.finiteSetKernel Pres I x) ∧
        ∃ D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
            (SpatialCoordinates d),
          (∀ mu, DenseRange (D.operator mu)) ∧
          SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
            (cutoffCoefficient M H (sigma N omega) N)
            (cutoffSpeedDensity M H (sigma N omega) N) D ∧
          ∀ (mu : Semigroup.PositiveShift)
            (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
            (x : SpatialCoordinates d),
            D.solution mu f x =
              ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
                kernelIntegral (Pres (Real.toNNReal t)) f x) := by
  dsimp only
  let g : ℕ → BilateralField d → ℕ → SpatialCoordinates d → ℝ :=
    fun N omega i y =>
      omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)
  let a : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
    fun N omega y => Real.exp (∑ i ∈ Finset.range (N + 1),
      (g N omega i y - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
  have hg : ∀ N omega i y, g N omega i y =
      omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y) := by
    intro N omega i y
    rfl
  have ha : ∀ N omega y, a N omega y = Real.exp (∑ i ∈ Finset.range (N + 1),
      (g N omega i y - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
    intro N omega y
    rfl
  obtain ⟨hcoeff, hseriesCoeff⟩ :=
    coefficient_physical_identity M H hH g hg a ha
  have hseries : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ x : SpatialCoordinates d, HasSum
        (fun n : ℕ => omega (Int.ofNat (n + 1)) x -
          omega (Int.ofNat (n + 1)) 0) (H omega x) := by
    filter_upwards [hseriesCoeff] with omega hω
    intro x
    convert hω 0 x using 1
    funext n
    dsimp [g]
    norm_num
    congr 1 <;> ring
  have hmp : ∀ N, MeasurePreserving (sigma N)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
    intro N
    exact aux_physical_generator_reindexing_sigma_measurePreserving
      M sigma hsigmadef N
  have hV := aux_physical_generator_reindexing_potential_identity
    H sigma hsigmadef (chaosSampleLaw M).toMeasure hseries hmp
  have hclock : ∀ N : ℕ,
      (3 : ℝ) ^ (2 * N) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          (3 : ℝ) ^ (-(2 * (N : ℝ))) =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ := by
    intro N
    have hpos : 0 < (3 : ℝ) := by norm_num
    have hpow : (3 : ℝ) ^ (-(2 * (N : ℝ))) =
        ((3 : ℝ) ^ (2 * N))⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hpos)]
      have hexp : 2 * (N : ℝ) = ((2 * N : ℕ) : ℝ) := by
        norm_num [Nat.cast_mul]
      rw [hexp, Real.rpow_natCast]
    rw [hpow]
    field_simp [ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)]
  have hraw : ∀ N : ℕ, ∀ path : DiffusionPath d,
      ((3 : ℝ)⁻¹ ^ N) •
          (path.comp
            ⟨fun t ↦ Real.toNNReal (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0) * t,
              continuous_const.mul continuous_id⟩).comp
            ⟨fun t ↦ Real.toNNReal
                ((3 : ℝ) ^ (2 * N) /
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * t,
              continuous_const.mul continuous_id⟩ =
        physicalRescaledPath M N path := by
    intro N path
    apply ContinuousMap.ext
    intro t
    simp only [physicalRescaledPath, ContinuousMap.smul_apply,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk]
    have hpos0 : 0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 :=
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0).le
    have hposN : 0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).le
    have hratio : 0 ≤ (3 : ℝ) ^ (2 * N) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := by positivity
    rw [Real.toNNReal_of_nonneg hratio]
    simp only [physicalTimeFactor]
    congr 2
    apply NNReal.eq
    simp! only [NNReal.coe_mul, NNReal.coe_mk,
      Real.coe_toNNReal _ hpos0]
    erw [NNReal.coe_mul, NNReal.coe_mk]
    change SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 *
      ((3 : ℝ) ^ (2 * N) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * (t : ℝ)) =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * (3 : ℝ) ^ (2 * N) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * (t : ℝ)
    ring
  refine ⟨hmp, hV, hclock, ?_, ?_⟩
  · intro N omega x
    let rawPath : DiffusionPath d → DiffusionPath d := fun path ↦
      path.comp
        ⟨fun t ↦ Real.toNNReal (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0) * t,
          continuous_const.mul continuous_id⟩
    let rawRescale : DiffusionPath d → DiffusionPath d := fun path ↦
      ((3 : ℝ)⁻¹ ^ N) • path.comp
        ⟨fun t ↦ Real.toNNReal
            ((3 : ℝ) ^ (2 * N) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * t,
          continuous_const.mul continuous_id⟩
    have hraw' : rawRescale ∘ rawPath = physicalRescaledPath M N := by
      funext path
      exact hraw N path
    have hrawMeas : Measurable rawPath := by
      dsimp [rawPath]
      fun_prop
    have hrawRescaleMeas : Measurable rawRescale := by
      dsimp [rawRescale]
      fun_prop
    calc
      Measure.map rawRescale (Measure.map rawPath
          (KN 0 (omega, (3 : ℝ) ^ N • x))) =
          Measure.map (rawRescale ∘ rawPath)
            (KN 0 (omega, (3 : ℝ) ^ N • x)) :=
        Measure.map_map hrawRescaleMeas hrawMeas
      _ = Measure.map (physicalRescaledPath M N)
          (KN 0 (omega, (3 : ℝ) ^ N • x)) := by rw [hraw']
  · intro N
    have hres' := (hmp N).quasiMeasurePreserving.ae hin.1
    have hmap' := (hmp N).quasiMeasurePreserving.ae hin.2.2
    filter_upwards [hres', hmap'] with omega hresN hmapN
    refine ⟨PN N (sigma N omega), ?_, ?_⟩
    · intro I x
      rw [htransport N omega x]
      have heval : Measurable (ContinuousPath.finsetEvaluation
          (alpha := SpatialCoordinates d) I) := by
        rw [measurable_pi_iff]
        intro t
        exact ContinuousPath.measurable_coordinateProcess
          (alpha := SpatialCoordinates d) (t : NNReal)
      rw [← Kernel.map_apply _ heval]
      exact hmapN N I x
    · exact hresN N

end Paper
