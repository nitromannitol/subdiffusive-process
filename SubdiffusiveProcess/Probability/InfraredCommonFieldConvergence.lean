import SubdiffusiveProcess.Main.NativeBilateralPotentialSample
import SubdiffusiveProcess.Main.PositiveScaledNativeLayer
import SubdiffusiveProcess.Main.PositiveScaledNativeLayer_apply
import SubdiffusiveProcess.Main.PositiveAnchoredInfraredTruncation
import SubdiffusiveProcess.Main.CompactPotentialC1Norm
import SubdiffusiveProcess.Main.LayerScaling
import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

theorem infraredPartialSum_tendsto_of_native_infrared_limit
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : NativeBilateralPotentialSample d → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (hHconv :
      ∀ᵐ omega ∂(Measure.infinitePi (fun _ : ℤ =>
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) :
            Measure (NativeBilateralPotentialSample d)),
        (∀ x : SpatialCoordinates d,
          H omega x = ∑' n : ℕ,
            (positiveScaledNativeLayer omega n x -
              positiveScaledNativeLayer omega n 0)) ∧
        (∀ K : Compacts (SpatialCoordinates d),
          Tendsto
            (fun L => compactPotentialC1Norm K
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
                (positiveAnchoredInfraredTruncation omega L)
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega))))
            atTop (nhds 0))) :
    ∀ᵐ beta ∂(chaosSampleLaw M).toMeasure,
      ∃ y : C(SpatialCoordinates d, ℝ),
        Tendsto (fun L => infraredPartialSum beta L) atTop (nhds y) := by
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let π : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j))
  have hπ : ∀ omega n,
      forget (positiveScaledNativeLayer omega n) = π omega (Int.ofNat (n + 1)) := by
    intro omega n
    ext x
    change omega (n + 1) ((3 : ℝ) ^ (-(n + 1 : ℤ)) • x) =
      omega (Int.ofNat (n + 1)) ((3 : ℝ) ^ (-Int.ofNat (n + 1)) • x)
    congr 1
  have hsum : ∀ omega L,
      infraredPartialSum (π omega) L =
        forget (positiveAnchoredInfraredTruncation omega L) := by
    intro omega L
    induction L with
    | zero =>
        simp [infraredPartialSum, positiveAnchoredInfraredTruncation, forget,
          zeroNativePotentialField]
    | succ L ih =>
        unfold infraredPartialSum
        rw [Finset.sum_range_succ]
        change infraredPartialSum (π omega) L +
            (π omega (Int.ofNat (L + 1)) -
              ContinuousMap.const _ ((π omega (Int.ofNat (L + 1))) 0)) = _
        rw [ih, ← hπ omega L]
        ext x
        change (forget (positiveAnchoredInfraredTruncation omega L)) x +
            ((forget (positiveScaledNativeLayer omega L)) x -
              (forget (positiveScaledNativeLayer omega L)) 0) =
          (forget (positiveAnchoredInfraredTruncation omega L)) x +
            ((forget (positiveScaledNativeLayer omega L)) x -
              (forget (positiveScaledNativeLayer omega L)) 0)
        rfl
  have hfield_tendsto : ∀ omega,
      (∀ K : Compacts (SpatialCoordinates d),
        Tendsto
          (fun L => compactPotentialC1Norm K
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
              (positiveAnchoredInfraredTruncation omega L)
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega))))
          atTop (nhds 0)) →
      Tendsto (fun L => forget (positiveAnchoredInfraredTruncation omega L))
        atTop (nhds (forget (H omega))) := by
    intro omega homega
    apply (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn).2
    intro S hS
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hK := homega (⟨S, hS⟩ : Compacts (SpatialCoordinates d))
    filter_upwards [hK (Metric.ball_mem_nhds 0 hε)] with L hL
    intro x hx
    have hq : ‖(forget (positiveAnchoredInfraredTruncation omega L)) x -
          (forget (H omega)) x‖ ≤
        compactPotentialC1Norm (⟨S, hS⟩ : Compacts (SpatialCoordinates d))
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega))) := by
      let q := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
        (positiveAnchoredInfraredTruncation omega L)
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega))
      change ‖(forget (positiveAnchoredInfraredTruncation omega L)) x -
          (forget (H omega)) x‖ ≤
        ‖(⟨fun z : (⟨S, hS⟩ : Compacts (SpatialCoordinates d)) => q z.1,
          q.1.1.continuous.comp continuous_subtype_val⟩ :
            C((⟨S, hS⟩ : Compacts (SpatialCoordinates d)), ℝ))‖ +
          ‖(⟨fun z : (⟨S, hS⟩ : Compacts (SpatialCoordinates d)) =>
              SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv q z.1,
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv q).continuous.comp
              continuous_subtype_val⟩ :
            C((⟨S, hS⟩ : Compacts (SpatialCoordinates d)),
              SpatialCoordinates d →L[ℝ] ℝ))‖
      have heval := ContinuousMap.norm_coe_le_norm
        (⟨fun z : (⟨S, hS⟩ : Compacts (SpatialCoordinates d)) =>
            q z.1, q.1.1.continuous.comp
            continuous_subtype_val⟩ : C((⟨S, hS⟩ : Compacts (SpatialCoordinates d)), ℝ))
        ⟨x, hx⟩
      rw [show (forget (positiveAnchoredInfraredTruncation omega L)) x -
          (forget (H omega)) x = q x by
        change (positiveAnchoredInfraredTruncation omega L) x - (H omega) x = q x
        dsimp [q]
        ring]
      calc
        ‖q x‖ ≤ ‖(⟨fun z : (⟨S, hS⟩ : Compacts (SpatialCoordinates d)) => q z.1,
            q.1.1.continuous.comp continuous_subtype_val⟩ :
              C((⟨S, hS⟩ : Compacts (SpatialCoordinates d)), ℝ))‖ := heval
        _ ≤ _ + ‖(⟨fun z : (⟨S, hS⟩ : Compacts (SpatialCoordinates d)) =>
              SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv q z.1,
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv q).continuous.comp
              continuous_subtype_val⟩ :
              C((⟨S, hS⟩ : Compacts (SpatialCoordinates d)),
                SpatialCoordinates d →L[ℝ] ℝ))‖ :=
          le_add_of_nonneg_right (by positivity)
    change dist ((forget (H omega)) x)
        ((forget (positiveAnchoredInfraredTruncation omega L)) x) < ε
    rw [dist_eq_norm']
    have hc : 0 ≤ compactPotentialC1Norm (⟨S, hS⟩ : Compacts (SpatialCoordinates d))
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega))) := by
      unfold compactPotentialC1Norm
      positivity
    have hL' : compactPotentialC1Norm (⟨S, hS⟩ : Compacts (SpatialCoordinates d))
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega))) < ε := by
      have hL'' : dist (compactPotentialC1Norm (⟨S, hS⟩ : Compacts (SpatialCoordinates d))
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega)))) 0 < ε := hL
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hc] using hL''
    exact hq.trans_lt hL'
  have hnative : ∀ᵐ omega ∂(Measure.infinitePi (fun _ : ℤ =>
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) :
        Measure (NativeBilateralPotentialSample d)),
      ∃ y : C(SpatialCoordinates d, ℝ),
        Tendsto (fun L => infraredPartialSum (π omega) L) atTop (nhds y) := by
    filter_upwards [hHconv] with omega homega
    refine ⟨forget (H omega), ?_⟩
    rw [show (fun L => infraredPartialSum (π omega) L) =
      (fun L => forget (positiveAnchoredInfraredTruncation omega L)) by
        funext L; exact hsum omega L]
    exact hfield_tendsto omega homega.2
  let μ : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)
  have hmp := measurePreserving_nativeCopies_commonScaleLaw M
  have hπmeas : Measurable π := by
    apply measurable_pi_lambda
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hmeas : ∀ L, Measurable (fun beta : BilateralField d =>
      infraredPartialSum beta L) := by
    intro L
    unfold infraredPartialSum
    apply Continuous.measurable
    apply continuous_finset_sum
    intro n hn
    have hcoord : Continuous (fun beta : BilateralField d =>
        beta (Int.ofNat (n + 1))) := continuous_apply (Int.ofNat (n + 1))
    have heval0 : Continuous (fun f : C(SpatialCoordinates d, ℝ) => f 0) :=
      continuous_eval_const 0
    have hc : Continuous (fun beta : BilateralField d =>
        ContinuousMap.const (SpatialCoordinates d) ((beta (Int.ofNat (n + 1))) 0)) := by
      simpa [ContinuousMap.constPi, Function.comp_def] using
        ((ContinuousMap.continuous_const' (X := SpatialCoordinates d) (Y := ℝ)).comp
          (heval0.comp hcoord))
    exact (continuous_apply (Int.ofNat (n + 1))).sub hc
  have hset : MeasurableSet {beta : BilateralField d |
      ∃ y : C(SpatialCoordinates d, ℝ),
        Tendsto (fun L => infraredPartialSum beta L) atTop (nhds y)} := by
    apply MeasureTheory.measurableSet_exists_tendsto
    intro L
    exact hmeas L
  have hπmeasure : Measure.map π μ = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, μ, π, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  rw [← hπmeasure]
  apply (MeasureTheory.ae_map_iff hπmeas.aemeasurable hset).2
  simpa only [Function.comp_apply] using hnative

end SubdiffusiveProcess
