module

public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.NativeInfraredLimit
public import SubdiffusiveProcess.Main.NativeBilateralPotentialSample
public import SubdiffusiveProcess.Main.PositiveScaledNativeLayer
public import SubdiffusiveProcess.Main.PositiveScaledNativeLayer_apply
public import SubdiffusiveProcess.Main.PositiveAnchoredInfraredTruncation
public import SubdiffusiveProcess.Main.CompactPotentialC1Norm
public import SubdiffusiveProcess.Main.LayerScaling
public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

theorem exists_compactExponentialMoment_of_infraredCharacterization
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (K : Compacts (SpatialCoordinates d)) (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    Integrable (fun omega => Real.exp
      (lambda * ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖))
      (chaosSampleLaw M).toMeasure := by
  classical
  obtain ⟨_Cconst, _hCnonneg, hCM⟩ := exists_native_infrared_limit hd
  obtain ⟨Hn, hHnmeas, _hHnCont, hHnLimAE, _hLpLayer, _hLpH, hExpMoment⟩ := hCM M
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let π : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j))
  let μ : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
  -- identity chase reused from InfraredCommonFieldConvergence.lean, not reproving the estimates
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
        ext x
        rfl
    | succ L ih =>
        unfold infraredPartialSum
        rw [Finset.sum_range_succ]
        change infraredPartialSum (π omega) L +
            (π omega (Int.ofNat (L + 1)) -
              ContinuousMap.const _ ((π omega (Int.ofNat (L + 1))) 0)) = _
        rw [ih, ← hπ omega L]
        ext x
        rfl
  have hπmeas : Measurable π := by
    apply Measurable.of_eval
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hmp := measurePreserving_nativeCopies_commonScaleLaw M
  have hπmeasure : Measure.map π μ = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, μ, π, Function.comp_apply] using
      hmp.map_eq
  have hπMP : MeasurePreserving π μ (chaosSampleLaw M).toMeasure := ⟨hπmeas, hπmeasure⟩
  -- pull the given tendsto-to-H back through the measure-preserving map, no predicate
  -- measurability needed (QuasiMeasurePreserving pullback of an ae property)
  have hHβ : ∀ᵐ omega ∂μ,
      Tendsto (fun L => infraredPartialSum (π omega) L) atTop (nhds (H (π omega))) :=
    hπMP.quasiMeasurePreserving.ae hH.2
  have hvalDom : ∀ (g : _root_.SubdiffusiveProcess.Model.PotentialField d),
      ‖g.1.1.restrict (K : Set (SpatialCoordinates d))‖ ≤ compactPotentialC1Norm K g := by
    intro g
    have heq : g.1.1.restrict (K : Set (SpatialCoordinates d)) =
        (⟨fun x : K => g x.1, g.1.1.continuous.comp continuous_subtype_val⟩ : C(K, ℝ)) := by
      ext x; rfl
    unfold compactPotentialC1Norm
    rw [heq]
    exact le_add_of_nonneg_right (by positivity)
  have hkey : ∀ (g h : _root_.SubdiffusiveProcess.Model.PotentialField d),
      g.1.1.restrict (K : Set (SpatialCoordinates d)) -
        h.1.1.restrict (K : Set (SpatialCoordinates d)) =
        (_root_.SubdiffusiveProcess.Model.PotentialField.add g
          (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) h)).1.1.restrict
          (K : Set (SpatialCoordinates d)) := by
    intro g h
    ext x
    rw [ContinuousMap.sub_apply, ContinuousMap.restrict_apply, ContinuousMap.restrict_apply,
      ContinuousMap.restrict_apply, _root_.SubdiffusiveProcess.Model.PotentialField.add_apply,
      _root_.SubdiffusiveProcess.Model.PotentialField.scale_apply]
    ring
  have hnativeConv : ∀ᵐ omega ∂μ,
      Tendsto (fun L => ‖(forget (positiveAnchoredInfraredTruncation omega L)).restrict
        (K : Set (SpatialCoordinates d)) -
          (forget (Hn omega)).restrict (K : Set (SpatialCoordinates d))‖) atTop (nhds 0) := by
    filter_upwards [hHnLimAE] with omega ho
    have h0 := ho.2.1 K
    have hb : ∀ L, ‖(forget (positiveAnchoredInfraredTruncation omega L)).restrict
        (K : Set (SpatialCoordinates d)) -
          (forget (Hn omega)).restrict (K : Set (SpatialCoordinates d))‖ ≤
        compactPotentialC1Norm K
          (_root_.SubdiffusiveProcess.Model.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (Hn omega))) := by
      intro L
      change ‖(positiveAnchoredInfraredTruncation omega L).1.1.restrict
        (K : Set (SpatialCoordinates d)) - (Hn omega).1.1.restrict
        (K : Set (SpatialCoordinates d))‖ ≤ _
      rw [hkey]
      exact hvalDom _
    exact squeeze_zero (fun L => norm_nonneg _) hb h0
  have hnativeTendsto : ∀ᵐ omega ∂μ,
      Tendsto (fun L => (forget (positiveAnchoredInfraredTruncation omega L)).restrict
        (K : Set (SpatialCoordinates d))) atTop
        (nhds ((forget (Hn omega)).restrict (K : Set (SpatialCoordinates d)))) := by
    filter_upwards [hnativeConv] with omega ho
    rwa [tendsto_iff_norm_sub_tendsto_zero]
  have hEqAE : ∀ᵐ omega ∂μ,
      (H (π omega)).restrict (K : Set (SpatialCoordinates d)) =
        (forget (Hn omega)).restrict (K : Set (SpatialCoordinates d)) := by
    filter_upwards [hHβ, hnativeTendsto] with omega h1 h2
    have hL1 := ((ContinuousMap.continuous_restrict
        (K : Set (SpatialCoordinates d))).tendsto (H (π omega))).comp h1
    have hL2 : Tendsto (fun L => (infraredPartialSum (π omega) L).restrict
        (K : Set (SpatialCoordinates d))) atTop
        (nhds ((forget (Hn omega)).restrict (K : Set (SpatialCoordinates d)))) := by
      simpa only [hsum omega] using h2
    exact tendsto_nhds_unique hL1 hL2
  have hφ : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
      Real.exp (lambda * ‖f.restrict (K : Set (SpatialCoordinates d))‖)) :=
    Real.continuous_exp.comp (continuous_const.mul
      (continuous_norm.comp (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d)))))
  have hNativeInt := (hExpMoment K lambda hlambda).1
  have hf'meas : Measurable (fun omega => Real.exp
      (lambda * ‖(forget (Hn omega)).restrict (K : Set (SpatialCoordinates d))‖)) :=
    hφ.measurable.comp (forget.continuous.measurable.comp hHnmeas)
  have hf'Int : Integrable (fun omega => Real.exp
      (lambda * ‖(forget (Hn omega)).restrict (K : Set (SpatialCoordinates d))‖)) μ := by
    apply hNativeInt.mono' hf'meas.aestronglyMeasurable
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left (hvalDom (Hn omega)) hlambda
  have hgπEq : (fun omega => Real.exp
      (lambda * ‖(H (π omega)).restrict (K : Set (SpatialCoordinates d))‖)) =ᵐ[μ]
      (fun omega => Real.exp
        (lambda * ‖(forget (Hn omega)).restrict (K : Set (SpatialCoordinates d))‖)) := by
    filter_upwards [hEqAE] with omega ho
    rw [ho]
  have hDomInt : Integrable (fun omega => Real.exp
      (lambda * ‖(H (π omega)).restrict (K : Set (SpatialCoordinates d))‖)) μ :=
    hf'Int.congr hgπEq.symm
  have hgAESM : AEStronglyMeasurable (fun beta => Real.exp
      (lambda * ‖(H beta).restrict (K : Set (SpatialCoordinates d))‖))
      (chaosSampleLaw M).toMeasure :=
    (hφ.measurable.comp hH.1).aestronglyMeasurable
  exact (hπMP.integrable_comp hgAESM).1 hDomInt

end SubdiffusiveProcess
