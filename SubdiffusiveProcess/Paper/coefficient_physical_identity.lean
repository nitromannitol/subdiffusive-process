module

public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.MultiplicativeChaos.SpeedBasic
public import SubdiffusiveProcess.Probability.AbsoluteSeries

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory SubdiffusiveProcess Topology TopologicalSpace
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper

/--
- The cutoff coefficient and the relabelling definitions are supplied by in_normalization.
- hH is the infrared limit characterization supplied by lem_infrared; it is used only to identify the infinite tail.
- g and a are pinned by their displayed definitions, not free coefficient families.
- Both equalities of the physical-coefficient identity are conclusions, including convergence of the infrared series.
- The coefficient identity is pointwise; the infrared identity is simultaneous in N and x on the full-measure event.
-/
theorem coefficient_physical_identity
    {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (g : Nat → BilateralField d → Nat → SpatialCoordinates d → ℝ)
    (hg : ∀ N omega i y,
      g N omega i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (a : Nat → BilateralField d → SpatialCoordinates d → ℝ)
    (ha : ∀ N omega y,
      a N omega y = Real.exp (∑ i ∈ Finset.range (N + 1),
        (g N omega i y - _root_.SubdiffusiveProcess.Model.tauSq M.P))) :
    (∀ omega N x,
      cutoffCoefficient M H omega N x =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
          a N omega ((3 : ℝ) ^ N • x) * Real.exp (H omega x)) ∧
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N x,
      HasSum (fun n : Nat =>
        g N omega (N + 1 + n) ((3 : ℝ) ^ N • x) -
          g N omega (N + 1 + n) 0) (H omega x)) := by
  constructor
  · intro omega N x
    have hcoeff := SubdiffusiveProcess.cutoffCoefficient_eq_smul_cutoffSpeedDensity
      M H omega N x
    have hsum : (∑ i ∈ Finset.range (N + 1),
        (g N omega i ((3 : ℝ) ^ N • x) - _root_.SubdiffusiveProcess.Model.tauSq M.P)) =
        (∑ j ∈ Finset.range (N + 1),
          omega (-(j : ℤ)) x) - (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P := by
      simp_rw [hg]
      simp
      rw [← Finset.sum_range_reflect (fun j : ℕ => (omega (-(j : ℤ))) x) (N + 1)]
      apply Finset.sum_congr rfl
      intro i hi
      have hi'' : i < N + 1 := Finset.mem_range.mp hi
      have hi' : i ≤ N := by omega
      congr 2
      omega
    rw [hcoeff]
    unfold SubdiffusiveProcess.cutoffSpeedDensity
      SubdiffusiveProcess.cutoffPotential
    rw [ha]
    have hexp :
        Real.exp ((H omega) x +
          ∑ j ∈ Finset.range (N + 1), (omega (-(j : ℤ))) x -
            (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
        Real.exp (∑ i ∈ Finset.range (N + 1),
          (g N omega i ((3 : ℝ) ^ N • x) - _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
          Real.exp ((H omega) x) := by
      calc
        Real.exp ((H omega) x +
            ∑ j ∈ Finset.range (N + 1), (omega (-(j : ℤ))) x -
              (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
            Real.exp ((H omega) x +
              ((∑ j ∈ Finset.range (N + 1), (omega (-(j : ℤ))) x) -
                (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
              congr 2
              ring
        _ = Real.exp ((H omega) x +
              ∑ i ∈ Finset.range (N + 1),
                (g N omega i ((3 : ℝ) ^ N • x) -
                  _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
              rw [hsum]
        _ = Real.exp (∑ i ∈ Finset.range (N + 1),
              (g N omega i ((3 : ℝ) ^ N • x) -
                _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
              Real.exp ((H omega) x) := by
              rw [Real.exp_add]
              ring
    calc
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
          Real.exp ((H omega) x +
            ∑ j ∈ Finset.range (N + 1), (omega (-Int.ofNat j)) x -
              (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
            (Real.exp (∑ i ∈ Finset.range (N + 1),
              (g N omega i ((3 : ℝ) ^ N • x) -
                _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
              Real.exp ((H omega) x)) := by
                congr 2
      _ = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
          Real.exp (∑ i ∈ Finset.range (N + 1),
            (g N omega i ((3 : ℝ) ^ N • x) -
              _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
          Real.exp ((H omega) x) := by ring
  · classical
    change Measurable H ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        Tendsto (fun L => infraredPartialSum omega L) atTop (nhds (H omega))) at hH
    let K : ℕ → Compacts (SpatialCoordinates d) := fun R =>
      ⟨Metric.closedBall (0 : SpatialCoordinates d) R, isCompact_closedBall _ _⟩
    let (R : ℕ) : MeasurableSpace C(K R, ℝ) := borel _
    let (R : ℕ) : BorelSpace C(K R, ℝ) := ⟨rfl⟩
    let F (R n : ℕ) (beta : BilateralField d) : C(K R, ℝ) :=
      (beta (Int.ofNat (n + 1))).restrict (K R : Set (SpatialCoordinates d)) -
        ContinuousMap.const (K R) ((beta (Int.ofNat (n + 1))) 0)
    have hFcont : ∀ R n, Continuous (F R n) := by
      intro R n
      dsimp [F]
      exact ((ContinuousMap.continuous_restrict (K R : Set (SpatialCoordinates d))).comp
        (continuous_apply (Int.ofNat (n + 1)))).sub
        (ContinuousMap.continuous_const'.comp
          ((continuous_eval_const (0 : SpatialCoordinates d)).comp
            (continuous_apply (Int.ofNat (n + 1)))))
    have hFmeas : ∀ R n, Measurable (F R n) := by
      intro R n
      exact (hFcont R n).measurable
    have hpartial : ∀ L, Measurable (fun beta : BilateralField d =>
        infraredPartialSum beta L) := by
      intro L
      unfold infraredPartialSum
      apply Continuous.measurable
      apply continuous_finsetSum
      intro n hn
      exact (continuous_apply (Int.ofNat (n + 1))).sub
        (ContinuousMap.continuous_const'.comp
          ((continuous_eval_const (0 : SpatialCoordinates d)).comp
            (continuous_apply (Int.ofNat (n + 1)))))
    have hsumset : ∀ R, MeasurableSet {beta : BilateralField d |
        Summable (fun n => ‖F R n beta‖)} := by
      intro R
      exact measurableSet_summable_norm (hFmeas R)
    have hTset : MeasurableSet {beta : BilateralField d |
        Tendsto (fun L => infraredPartialSum beta L) atTop (nhds (H beta))} := by
      exact MeasureTheory.measurableSet_tendsto_fun hpartial hH.1
    let Good : Set (BilateralField d) :=
      {beta | (∀ R, Summable (fun n => ‖F R n beta‖)) ∧
        Tendsto (fun L => infraredPartialSum beta L) atTop (nhds (H beta))}
    have hGood : MeasurableSet Good := by
      rw [show Good = (⋂ R : ℕ, {beta : BilateralField d |
          Summable (fun n => ‖F R n beta‖)}) ∩
          {beta : BilateralField d |
            Tendsto (fun L => infraredPartialSum beta L) atTop (nhds (H beta))} by
        ext beta
        change ((∀ R, Summable (fun n => ‖F R n beta‖)) ∧
          Tendsto (fun L => infraredPartialSum beta L) atTop (nhds (H beta))) ↔ _
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]]
      exact (MeasurableSet.iInter hsumset).inter hTset
    let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
        C(SpatialCoordinates d, ℝ)) :=
      ⟨fun q => q.1.1, continuous_subtype_val.fst⟩
    let π : NativeBilateralPotentialSample d → BilateralField d :=
      fun omega j => layerScaling d j (forget (omega j))
    have hπ : ∀ omega n,
        forget (positiveScaledNativeLayer omega n) = π omega (Int.ofNat (n + 1)) := by
      intro omega n
      ext y
      change omega (n + 1) ((3 : ℝ) ^ (-(n + 1 : ℤ)) • y) =
        omega (Int.ofNat (n + 1)) ((3 : ℝ) ^ (-Int.ofNat (n + 1)) • y)
      congr 1
    have hπmeas : Measurable π := by
      apply Measurable.of_eval
      intro j
      exact (layerScaling d j).continuous.measurable.comp
        (forget.continuous.measurable.comp (measurable_pi_apply j))
    let μ : Measure (NativeBilateralPotentialSample d) :=
      Measure.infinitePi (fun _ : ℤ =>
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
    have hπmeasure : Measure.map π μ = (chaosSampleLaw M).toMeasure := by
      simpa only [chaosSampleLaw, chaosRootFieldLaw, μ, π, Function.comp_apply] using
        (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
    have hπMP : MeasurePreserving π μ (chaosSampleLaw M).toMeasure :=
      ⟨hπmeas, hπmeasure⟩
    have hHβ : ∀ᵐ omega ∂μ,
        Tendsto (fun L => infraredPartialSum (π omega) L) atTop
          (nhds (H (π omega))) := by
      exact hπMP.quasiMeasurePreserving.ae hH.2
    have hShell : ∀ᵐ omega ∂μ,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellC11Summable
          (positiveScaledNativeLayer omega) := by
      simpa [μ] using ae_positiveScaledNativeLayer_shellC11Summable M
    have hGoodSource : ∀ᵐ omega ∂μ, π omega ∈ Good := by
      filter_upwards [hShell, hHβ] with omega hs hconv
      refine ⟨?_, hconv⟩
      intro R
      obtain ⟨hc1, _⟩ :=
        shellC11Summable_compact_observables
          (positiveScaledNativeLayer omega) hs (K R)
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hc1
      intro n
      have heq : F R n (π omega) =
          (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
            (positiveScaledNativeLayer omega n)).1.1.restrict
              (K R : Set (SpatialCoordinates d)) := by
        ext y
        change (π omega (Int.ofNat (n + 1))) y.1 -
            (π omega (Int.ofNat (n + 1))) 0 =
          (positiveScaledNativeLayer omega n) y.1 -
            (positiveScaledNativeLayer omega n) 0
        rw [← hπ omega n]
        rfl
      rw [heq]
      unfold compactPotentialC1Norm
      exact le_add_of_nonneg_right
        (norm_nonneg
          ((_root_.SubdiffusiveProcess.Model.PotentialField.deriv
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer omega n))).restrict
                (K R : Set (SpatialCoordinates d))))
    have hGoodAE : ∀ᵐ beta ∂(chaosSampleLaw M).toMeasure, beta ∈ Good := by
      rw [← hπmeasure]
      exact (MeasureTheory.ae_map_iff hπmeas.aemeasurable hGood).2 hGoodSource
    filter_upwards [hGoodAE] with omega hGoodOmega
    intro N x
    obtain ⟨R, hR⟩ := exists_nat_gt ‖x‖
    have hxK : x ∈ K R := by
      change x ∈ Metric.closedBall (0 : SpatialCoordinates d) (R : ℝ)
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hR
    have hnormsum : Summable (fun n =>
        ‖omega (Int.ofNat (n + 1)) x - omega (Int.ofNat (n + 1)) 0‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
        (hGoodOmega.1 R)
      intro n
      have heval := ContinuousMap.norm_coe_le_norm (F R n omega) ⟨x, hxK⟩
      change ‖F R n omega ⟨x, hxK⟩‖ ≤ ‖F R n omega‖
      exact heval
    have ht : Tendsto (fun L =>
        ∑ n ∈ Finset.range L,
          (omega (Int.ofNat (n + 1)) x - omega (Int.ofNat (n + 1)) 0)) atTop
          (nhds (H omega x)) := by
      have heval := (continuous_eval_const x).tendsto (H omega)
      have hcomp := heval.comp (hGoodOmega.2)
      change Tendsto (fun L => (infraredPartialSum omega L) x) atTop
        (nhds (H omega x)) at hcomp
      simpa [infraredPartialSum] using hcomp
    have hhas : HasSum (fun n =>
        omega (Int.ofNat (n + 1)) x - omega (Int.ofNat (n + 1)) 0) (H omega x) :=
      ((hnormsum.of_norm).hasSum_iff_tendsto_nat).2 ht
    have hterm : ∀ n : ℕ,
        g N omega (N + 1 + n) ((3 : ℝ) ^ N • x) -
            g N omega (N + 1 + n) 0 =
          omega (Int.ofNat (n + 1)) x - omega (Int.ofNat (n + 1)) 0 := by
      intro n
      rw [hg, hg]
      simp
      have hi : (N : ℤ) + 1 + (n : ℤ) - (N : ℤ) = (n : ℤ) + 1 := by omega
      rw [hi]
    simpa only [hterm] using hhas

end SubdiffusiveProcess.Paper
