module

public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.NativeInfraredLimit
public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.LayerScaling
public import SubdiffusiveProcess.Main.PositiveAnchoredInfraredTruncation
public import SubdiffusiveProcess.Main.CompactPotentialC1Norm
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Analysis.ELpNormTsum
public import Mathlib.Topology.Metrizable.ContinuousMap

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ}

/-- The value-part restriction of a `PotentialField` to a compact `K`, matching
`compactPotentialC1Norm`'s first summand's underlying `ContinuousMap`. -/
def restrictForget (K : Compacts (SpatialCoordinates d))
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : C(K, ℝ) :=
  ⟨fun x : K => g x.1, g.1.1.continuous.comp continuous_subtype_val⟩

theorem restrictForget_add (K : Compacts (SpatialCoordinates d))
    (g h : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    restrictForget K (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add g h) =
      restrictForget K g + restrictForget K h := by
  ext x
  simp [restrictForget, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add_apply]

theorem norm_restrictForget_le (K : Compacts (SpatialCoordinates d))
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    ‖restrictForget K g‖ ≤ compactPotentialC1Norm K g := by
  unfold compactPotentialC1Norm
  have hrfl : (⟨fun x : K => g x.1, g.1.1.continuous.comp continuous_subtype_val⟩ : C(K, ℝ)) =
      restrictForget K g := rfl
  rw [hrfl]
  refine le_add_of_nonneg_right ?_
  exact norm_nonneg (⟨fun x : K => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x.1,
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g).continuous.comp continuous_subtype_val⟩ :
    C(K, SpatialCoordinates d →L[ℝ] ℝ))

theorem restrictForget_scale (K : Compacts (SpatialCoordinates d)) (c : ℝ)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    restrictForget K (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale c g) =
      c • restrictForget K g := by
  ext x
  simp [restrictForget, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale_apply]

theorem restrictForget_continuous (K : Compacts (SpatialCoordinates d)) :
    Continuous (restrictForget K : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → C(K, ℝ)) :=
  (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).comp
    continuous_subtype_val.fst

theorem restrictForget_anchor (K : Compacts (SpatialCoordinates d))
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    restrictForget K (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor g) =
      restrictForget K g - ContinuousMap.const K (g 0) := by
  ext x
  simp [restrictForget, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor_apply]

theorem restrictForget_zero (K : Compacts (SpatialCoordinates d)) :
    restrictForget K (zeroNativePotentialField d) = 0 := by
  ext x; simp [restrictForget, zeroNativePotentialField]

theorem restrictForget_truncation_eq_sum (K : Compacts (SpatialCoordinates d))
    (omega : NativeBilateralPotentialSample d) (L : ℕ) :
    restrictForget K (positiveAnchoredInfraredTruncation omega L) =
      ∑ i ∈ Finset.range L, restrictForget K
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (positiveScaledNativeLayer omega i)) := by
  induction L with
  | zero => simp [positiveAnchoredInfraredTruncation, restrictForget_zero]
  | succ L ih =>
      show restrictForget K (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
          (positiveAnchoredInfraredTruncation omega L)
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (positiveScaledNativeLayer omega L))) = _
      rw [restrictForget_add, ih, Finset.sum_range_succ]

/-- Squeeze: the native qualitative `compactPotentialC1Norm`-convergence of the truncations to `H`
transfers to `restrictForget`-norm convergence (dropping the gradient half). -/
theorem tendsto_restrictForget_truncation (K : Compacts (SpatialCoordinates d))
    (H : NativeBilateralPotentialSample d → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (omega : NativeBilateralPotentialSample d)
    (homega : Tendsto (fun L => compactPotentialC1Norm K
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
          (positiveAnchoredInfraredTruncation omega L)
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega))))
      atTop (𝓝 0)) :
    Tendsto (fun L => restrictForget K (positiveAnchoredInfraredTruncation omega L)) atTop
      (𝓝 (restrictForget K (H omega))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hsq : ∀ L, dist (restrictForget K (positiveAnchoredInfraredTruncation omega L))
      (restrictForget K (H omega)) ≤
      compactPotentialC1Norm K (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
        (positiveAnchoredInfraredTruncation omega L)
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega))) := by
    intro L
    rw [dist_eq_norm]
    have hne : restrictForget K (positiveAnchoredInfraredTruncation omega L) -
        restrictForget K (H omega) =
        restrictForget K (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
          (positiveAnchoredInfraredTruncation omega L)
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega))) := by
      rw [restrictForget_add, restrictForget_scale]
      module
    rw [hne]
    exact norm_restrictForget_le K _
  have hzero : Tendsto (fun L => dist (restrictForget K
      (positiveAnchoredInfraredTruncation omega L)) (restrictForget K (H omega))) atTop (𝓝 0) := by
    apply squeeze_zero (fun L => dist_nonneg) hsq homega
  exact hzero

theorem restrictForget_truncation_shift_eq_sum (K : Compacts (SpatialCoordinates d))
    (omega : NativeBilateralPotentialSample d) (L : ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range n, restrictForget K
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (positiveScaledNativeLayer omega (L + i))) =
      restrictForget K (positiveAnchoredInfraredTruncation omega (L + n)) -
        restrictForget K (positiveAnchoredInfraredTruncation omega L) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hrec : positiveAnchoredInfraredTruncation omega (L + n + 1) =
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
            (positiveAnchoredInfraredTruncation omega (L + n))
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (positiveScaledNativeLayer omega (L + n))) :=
        rfl
      rw [show L + (n + 1) = L + n + 1 from rfl, hrec, restrictForget_add]
      abel

/-- Tail-sum convergence: the partial sums of the layers from depth `L` onward tend to the
truncation tail `H(omega) − truncation(omega, L)` (`restrictForget`-restricted). -/
theorem tendsto_restrictForget_truncation_tail (K : Compacts (SpatialCoordinates d))
    (H : NativeBilateralPotentialSample d → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (omega : NativeBilateralPotentialSample d) (L : ℕ)
    (homega : Tendsto (fun N => compactPotentialC1Norm K
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
          (positiveAnchoredInfraredTruncation omega N)
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega))))
      atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, restrictForget K
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (positiveScaledNativeLayer omega (L + i))))
      atTop (𝓝 (restrictForget K (H omega) -
        restrictForget K (positiveAnchoredInfraredTruncation omega L))) := by
  have hfull := tendsto_restrictForget_truncation K H omega homega
  have hLadd : Tendsto (fun n : ℕ => L + n) atTop atTop := by
    simpa [add_comm] using tendsto_add_atTop_nat L
  have hshift : Tendsto (fun n => restrictForget K
      (positiveAnchoredInfraredTruncation omega (L + n))) atTop (𝓝 (restrictForget K (H omega))) :=
    hfull.comp hLadd
  simpa [restrictForget_truncation_shift_eq_sum] using hshift.sub_const
    (restrictForget K (positiveAnchoredInfraredTruncation omega L))

theorem continuous_restrictForget_anchor (K : Compacts (SpatialCoordinates d)) :
    Continuous (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
      restrictForget K (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor g)) := by
  simp_rw [restrictForget_anchor]
  exact (restrictForget_continuous K).sub
    (ContinuousMap.continuous_const'.comp (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.continuous_eval 0))

theorem continuous_restrictForget_anchor_layer (K : Compacts (SpatialCoordinates d)) (n : ℕ) :
    Continuous (fun omega : NativeBilateralPotentialSample d =>
      restrictForget K (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor
        (positiveScaledNativeLayer omega n))) :=
  (continuous_restrictForget_anchor K).comp
    ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.continuous_spatialScale
      ((3 : ℝ) ^ (-(n + 1 : ℤ)))).comp (continuous_apply ((n + 1 : ℕ) : ℤ)))

/-- `Measurable`, not `Continuous`, version of `continuous_restrictForget_anchor_layer`: avoids
needing `OpensMeasurableSpace (NativeBilateralPotentialSample d)` for the (Pi-type) domain by
routing the outer projection through `measurable_pi_apply` instead of a continuity argument. -/
theorem measurable_restrictForget_anchor_layer (K : Compacts (SpatialCoordinates d))
    [MeasurableSpace C(K, ℝ)] [BorelSpace C(K, ℝ)] (n : ℕ) :
    Measurable (fun omega : NativeBilateralPotentialSample d =>
      restrictForget K (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor
        (positiveScaledNativeLayer omega n))) :=
  (continuous_restrictForget_anchor K).measurable.comp
    (((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.continuous_spatialScale
      ((3 : ℝ) ^ (-(n + 1 : ℤ)))).measurable).comp (measurable_pi_apply ((n + 1 : ℕ) : ℤ)))

/-- Geometric series bookkeeping: `∑'_{i} c·3^{-(L+i+1)} = (c/2)·3^{-L}` for `c ≥ 0`. -/
theorem tsum_geom_shift (c : ℝ) (L : ℕ) :
    ∑' i : ℕ, c * (3 : ℝ) ^ (-((L : ℤ) + (i : ℤ) + 1)) = (c / 2) * (3 : ℝ) ^ (-(L : ℤ)) := by
  have hpow : ∀ i : ℕ, (3 : ℝ) ^ (-((L : ℤ) + (i : ℤ) + 1)) =
      ((3 : ℝ) ^ (L + 1))⁻¹ * (1 / 3 : ℝ) ^ i := by
    intro i
    rw [show -((L : ℤ) + (i : ℤ) + 1) = -((L + 1 : ℕ) : ℤ) + (-(i : ℤ)) by push_cast; ring,
      zpow_add₀ (by norm_num : (3:ℝ) ≠ 0), zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
      one_div, inv_pow]
  have hrw : ∀ i : ℕ, c * (3 : ℝ) ^ (-((L : ℤ) + (i : ℤ) + 1)) =
      (c * ((3 : ℝ) ^ (L + 1))⁻¹) * (1 / 3 : ℝ) ^ i := by
    intro i; rw [hpow]; ring
  simp_rw [hrw]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  have hzpow : (3 : ℝ) ^ (-(L : ℤ)) = ((3 : ℝ) ^ L)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hzpow, pow_succ]
  ring

/-- Native geometric truncation-tail `Lp` bound: `H`'s own value (restricted to a compact `K`)
lies within a `C(K)·δ·√p·3^{-L}`-`Lp`-ball of its finite truncation, for every cutoff `L`. Built
from `exists_native_infrared_limit`'s per-layer bound + `eLpNorm_tsum_le_tsum_eLpNorm`. -/
theorem native_truncation_tail_geometric_eLpNorm_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C : Compacts (SpatialCoordinates d) → ℝ, (∀ K, 0 ≤ C K) ∧
    ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∃ Hn : NativeBilateralPotentialSample d → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        Measurable Hn ∧
        (∀ᵐ omega ∂(Measure.infinitePi (fun _ : ℤ =>
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)),
          ∀ K : Compacts (SpatialCoordinates d),
            Tendsto (fun L => compactPotentialC1Norm K
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
                (positiveAnchoredInfraredTruncation omega L)
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (Hn omega))))
              atTop (𝓝 0)) ∧
        ∀ K : Compacts (SpatialCoordinates d), ∀ p : ℝ≥0∞, 2 ≤ p → p ≠ ∞ → ∀ L : ℕ,
          eLpNorm (fun omega => restrictForget K (Hn omega) -
              restrictForget K (positiveAnchoredInfraredTruncation omega L)) p
            (Measure.infinitePi (fun _ : ℤ =>
              (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) ≤
            ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal * (3 : ℝ) ^ (-(L : ℤ))) := by
  obtain ⟨C, hCnonneg, hCM⟩ := exists_native_infrared_limit hd
  refine ⟨fun K => C K / 2, fun K => by have := hCnonneg K; positivity, ?_⟩
  intro M
  obtain ⟨Hn, hHnmeas, _hHnCont, hHnLimAE, hLpLayer, _hLpAll⟩ := hCM M
  set μ : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ => (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)
    with hμdef
  refine ⟨Hn, hHnmeas, hHnLimAE.mono (fun omega h K => h.2.1 K), ?_⟩
  intro K p hp2 hptop L
  letI : MeasurableSpace C(K, ℝ) := borel _
  haveI : BorelSpace C(K, ℝ) := ⟨rfl⟩
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_trans (by norm_num) hp2
  have hae_tendsto : ∀ᵐ omega ∂μ, Tendsto (fun n => ∑ i ∈ Finset.range n, restrictForget K
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (positiveScaledNativeLayer omega (L + i))))
      atTop (𝓝 (restrictForget K (Hn omega) -
        restrictForget K (positiveAnchoredInfraredTruncation omega L))) := by
    filter_upwards [hHnLimAE] with omega h
    exact tendsto_restrictForget_truncation_tail K Hn omega L (h.2.1 K)
  have hmeasf : ∀ n, AEStronglyMeasurable (fun omega => restrictForget K
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor
        (positiveScaledNativeLayer omega (L + n)))) μ :=
    fun n => (measurable_restrictForget_anchor_layer K (L + n)).aestronglyMeasurable
  have hstep3 := eLpNorm_tsum_le_tsum_eLpNorm hp1 hmeasf hae_tendsto
  have hterm_le : ∀ n : ℕ, eLpNorm (fun omega => restrictForget K
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (positiveScaledNativeLayer omega (L + n))))
      p μ ≤ ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal *
        (3 : ℝ) ^ (-((L : ℤ) + (n : ℤ) + 1))) := by
    intro n
    have hcast : (3 : ℝ) ^ (-((L : ℤ) + (n : ℤ) + 1)) = (3 : ℝ) ^ (-(((L + n : ℕ) : ℤ) + 1)) := by
      push_cast; ring_nf
    rw [hcast]
    refine le_trans ?_ (hLpLayer K p hp2 hptop (L + n))
    apply eLpNorm_mono (hmeasf n)
    intro omega
    have hle := norm_restrictForget_le K
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (positiveScaledNativeLayer omega (L + n)))
    have hnn : (0:ℝ) ≤ compactPotentialC1Norm K
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (positiveScaledNativeLayer omega (L + n))) :=
      le_trans (norm_nonneg _) hle
    rwa [Real.norm_eq_abs, abs_of_nonneg hnn]
  have htsum_le : ∑' n : ℕ, eLpNorm (fun omega => restrictForget K
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (positiveScaledNativeLayer omega (L + n))))
      p μ ≤ ∑' n : ℕ, ENNReal.ofReal
        (C K * M.delta * Real.sqrt p.toReal * (3 : ℝ) ^ (-((L : ℤ) + (n : ℤ) + 1))) :=
    ENNReal.tsum_le_tsum hterm_le
  have hnonneg : ∀ n : ℕ, 0 ≤ C K * M.delta * Real.sqrt p.toReal *
      (3 : ℝ) ^ (-((L : ℤ) + (n : ℤ) + 1)) := by
    intro n
    have h1 : (0:ℝ) ≤ (3:ℝ) ^ (-((L:ℤ) + (n:ℤ) + 1)) := (zpow_pos (by norm_num) _).le
    have h2 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
    have h3 : 0 ≤ C K := hCnonneg K
    positivity
  have hsummable : Summable (fun n : ℕ => C K * M.delta * Real.sqrt p.toReal *
      (3 : ℝ) ^ (-((L : ℤ) + (n : ℤ) + 1))) := by
    have hpow : ∀ n : ℕ, (3 : ℝ) ^ (-((L : ℤ) + (n : ℤ) + 1)) =
        ((3 : ℝ) ^ (L + 1))⁻¹ * (1 / 3 : ℝ) ^ n := by
      intro n
      rw [show -((L : ℤ) + (n : ℤ) + 1) = -((L + 1 : ℕ) : ℤ) + (-(n : ℤ)) by push_cast; ring,
        zpow_add₀ (by norm_num : (3:ℝ) ≠ 0), zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
        one_div, inv_pow]
    simp_rw [hpow]
    apply Summable.mul_left
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hofReal_tsum : ∑' n : ℕ, ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal *
        (3 : ℝ) ^ (-((L : ℤ) + (n : ℤ) + 1))) =
      ENNReal.ofReal (∑' n : ℕ, C K * M.delta * Real.sqrt p.toReal *
        (3 : ℝ) ^ (-((L : ℤ) + (n : ℤ) + 1))) :=
    (ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable).symm
  have hgeomsum : ∑' n : ℕ, C K * M.delta * Real.sqrt p.toReal *
      (3 : ℝ) ^ (-((L : ℤ) + (n : ℤ) + 1)) =
      ((C K * M.delta * Real.sqrt p.toReal) / 2) * (3 : ℝ) ^ (-(L : ℤ)) :=
    tsum_geom_shift (C K * M.delta * Real.sqrt p.toReal) L
  calc eLpNorm (fun omega => restrictForget K (Hn omega) -
      restrictForget K (positiveAnchoredInfraredTruncation omega L)) p μ
      ≤ ∑' n : ℕ, eLpNorm (fun omega => restrictForget K
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor
            (positiveScaledNativeLayer omega (L + n)))) p μ := hstep3
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal *
          (3 : ℝ) ^ (-((L : ℤ) + (n : ℤ) + 1))) := htsum_le
    _ = ENNReal.ofReal (((C K * M.delta * Real.sqrt p.toReal) / 2) * (3 : ℝ) ^ (-(L : ℤ))) := by
          rw [hofReal_tsum, hgeomsum]
    _ = ENNReal.ofReal (C K / 2 * M.delta * Real.sqrt p.toReal * (3 : ℝ) ^ (-(L : ℤ))) := by
          ring_nf




/-- Restriction of a plain `C(SpatialCoordinates d, ℝ)` to a compact `K`. -/
def restrictC (K : Compacts (SpatialCoordinates d)) (g : C(SpatialCoordinates d, ℝ)) :
    C(K, ℝ) :=
  ⟨fun x : K => g x.1, g.continuous.comp continuous_subtype_val⟩

theorem restrictC_continuous (K : Compacts (SpatialCoordinates d)) :
    Continuous (restrictC K : C(SpatialCoordinates d, ℝ) → C(K, ℝ)) :=
  ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))

theorem restrictC_val_eq_restrictForget (K : Compacts (SpatialCoordinates d))
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    restrictC K g.1.1 = restrictForget K g := rfl

/-- The measure-preserving native-copies-to-`BilateralField` map, specialized from
`measurePreserving_nativeCopies_commonScaleLaw`. -/
def piNative (omega : NativeBilateralPotentialSample d) : BilateralField d :=
  fun j => layerScaling d j (omega j).1.1

theorem piNative_measurePreserving (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    MeasurePreserving (piNative (d := d))
      (Measure.infinitePi (fun _ : ℤ => (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure))
      (chaosSampleLaw M).toMeasure := by
  have h := measurePreserving_nativeCopies_commonScaleLaw M
  simpa only [chaosSampleLaw, chaosRootFieldLaw, piNative, Function.comp_apply] using! h

theorem infraredPartialSum_piNative_eq (omega : NativeBilateralPotentialSample d) (L : ℕ) :
    infraredPartialSum (piNative omega) L =
      (positiveAnchoredInfraredTruncation omega L).1.1 := by
  induction L with
  | zero => simp [infraredPartialSum, positiveAnchoredInfraredTruncation, zeroNativePotentialField]
  | succ L ih =>
      unfold infraredPartialSum
      rw [Finset.sum_range_succ]
      show infraredPartialSum (piNative omega) L +
          (piNative omega (Int.ofNat (L + 1)) -
            ContinuousMap.const _ ((piNative omega (Int.ofNat (L + 1))) 0)) = _
      rw [ih]
      have hshow : positiveAnchoredInfraredTruncation omega (L + 1) =
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
            (positiveAnchoredInfraredTruncation omega L)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor (positiveScaledNativeLayer omega L)) :=
        rfl
      rw [hshow]
      ext x
      show _ + (piNative omega (Int.ofNat (L+1)) x - piNative omega (Int.ofNat (L+1)) 0) =
        _ + (positiveScaledNativeLayer omega L x - positiveScaledNativeLayer omega L 0)
      have hpi : piNative omega (Int.ofNat (L + 1)) = (positiveScaledNativeLayer omega L).1.1 := by
        show layerScaling d (Int.ofNat (L + 1)) (omega (Int.ofNat (L + 1))).1.1 = _
        rfl
      rw [hpi]

/-- For `H` satisfying `InfraredCharacterization M H`, the restricted value at any native-copy
image `piNative omega` agrees with the restricted native limit `Hn omega`, a.e. `omega`. Both are
limits (in `C(K,ℝ)`) of the SAME sequence `restrictC K (infraredPartialSum (piNative omega) ·)
= restrictForget K (positiveAnchoredInfraredTruncation omega ·)`, so agree by uniqueness of
limits. -/
theorem restrictC_H_piNative_eq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (Hn : NativeBilateralPotentialSample d → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (K : Compacts (SpatialCoordinates d))
    (homega : ∀ᵐ omega ∂(Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)),
      Tendsto (fun L => compactPotentialC1Norm K
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
          (positiveAnchoredInfraredTruncation omega L)
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (Hn omega))))
        atTop (𝓝 0)) :
    ∀ᵐ omega ∂(Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)),
      restrictC K (H (piNative omega)) = restrictForget K (Hn omega) := by
  have hpm := piNative_measurePreserving (d := d) M
  have hHae : ∀ᵐ beta ∂(chaosSampleLaw M).toMeasure,
      Tendsto (fun L => infraredPartialSum beta L) atTop (𝓝 (H beta)) := hH.2
  have hHae' : ∀ᵐ omega ∂(Measure.infinitePi (fun _ : ℤ =>
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)),
      Tendsto (fun L => infraredPartialSum (piNative omega) L) atTop
        (𝓝 (H (piNative omega))) :=
    hpm.quasiMeasurePreserving.ae hHae
  filter_upwards [hHae', homega] with omega hL hcomp
  have h1 : Tendsto (fun L => restrictC K (infraredPartialSum (piNative omega) L)) atTop
      (𝓝 (restrictC K (H (piNative omega)))) := (restrictC_continuous K).continuousAt.tendsto.comp hL
  have h2 : Tendsto (fun L => restrictC K (infraredPartialSum (piNative omega) L)) atTop
      (𝓝 (restrictForget K (Hn omega))) := by
    have heq : ∀ L, restrictC K (infraredPartialSum (piNative omega) L) =
        restrictForget K (positiveAnchoredInfraredTruncation omega L) := by
      intro L
      rw [infraredPartialSum_piNative_eq, restrictC_val_eq_restrictForget]
    simp_rw [heq]
    exact tendsto_restrictForget_truncation K Hn omega hcomp
  exact tendsto_nhds_unique h1 h2

theorem continuous_infraredPartialSum (L : ℕ) :
    Continuous (fun beta : BilateralField d => infraredPartialSum beta L) := by
  unfold infraredPartialSum
  apply continuous_finset_sum
  intro n _
  have hcoord : Continuous (fun beta : BilateralField d => beta (Int.ofNat (n + 1))) :=
    continuous_apply (Int.ofNat (n + 1))
  have heval0 : Continuous (fun f : C(SpatialCoordinates d, ℝ) => f 0) := continuous_eval_const 0
  have hc : Continuous (fun beta : BilateralField d =>
      ContinuousMap.const (SpatialCoordinates d) ((beta (Int.ofNat (n + 1))) 0)) := by
    simpa [ContinuousMap.constPi, Function.comp_def] using
      ((ContinuousMap.continuous_const' (X := SpatialCoordinates d) (Y := ℝ)).comp
        (heval0.comp hcoord))
  exact hcoord.sub hc



theorem infraredCharacterization_truncation_tail_geometric_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C : Compacts (SpatialCoordinates d) → ℝ, (∀ K, 0 ≤ C K) ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ K : Compacts (SpatialCoordinates d), ∀ p : ℝ≥0∞, 2 ≤ p → p ≠ ∞ → ∀ L : ℕ,
        eLpNorm (fun beta => restrictC K (H beta) - restrictC K (infraredPartialSum beta L)) p
          (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal * (3 : ℝ) ^ (-(L : ℤ))) := by
  obtain ⟨C, hCnonneg, hCM⟩ := native_truncation_tail_geometric_eLpNorm_bound hd
  refine ⟨C, hCnonneg, ?_⟩
  intro M H hH K p hp2 hptop L
  obtain ⟨Hn, _hHnmeas, hcomp, hbound⟩ := hCM M
  letI : MeasurableSpace C(K, ℝ) := borel _
  haveI : BorelSpace C(K, ℝ) := ⟨rfl⟩
  have heqAE := restrictC_H_piNative_eq M H hH Hn K (hcomp.mono fun omega h => h K)
  have hpm := piNative_measurePreserving (d := d) M
  have hgmeas : AEStronglyMeasurable (fun beta => restrictC K (H beta) -
      restrictC K (infraredPartialSum beta L)) (chaosSampleLaw M).toMeasure := by
    have h1 : Measurable (fun beta => restrictC K (H beta)) :=
      (restrictC_continuous K).measurable.comp hH.1
    have h2 : Measurable (fun beta => restrictC K (infraredPartialSum beta L)) :=
      (restrictC_continuous K).measurable.comp (continuous_infraredPartialSum L).measurable
    exact (h1.sub h2).aestronglyMeasurable
  have hstep : eLpNorm (fun beta => restrictC K (H beta) -
      restrictC K (infraredPartialSum beta L)) p (chaosSampleLaw M).toMeasure =
      eLpNorm (fun omega => restrictForget K (Hn omega) -
        restrictForget K (positiveAnchoredInfraredTruncation omega L)) p
        (Measure.infinitePi (fun _ : ℤ =>
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) := by
    rw [← eLpNorm_comp_measurePreserving hgmeas hpm]
    apply eLpNorm_congr_ae
    filter_upwards [heqAE] with omega heq
    show restrictC K (H (piNative omega)) - restrictC K (infraredPartialSum (piNative omega) L) =
      restrictForget K (Hn omega) - restrictForget K (positiveAnchoredInfraredTruncation omega L)
    rw [heq, infraredPartialSum_piNative_eq, restrictC_val_eq_restrictForget]
  rw [hstep]
  exact hbound K p hp2 hptop L

end SubdiffusiveProcess
