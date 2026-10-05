module

public import SubdiffusiveProcess.Analysis.CompactShellSummability
public import SubdiffusiveProcess.Analysis.NativeInfraredEnvelope
public import SubdiffusiveProcess.Analysis.MeasurableNativeInfrared
public import SubdiffusiveProcess.Analysis.NativeInfraredSeries
public import SubdiffusiveProcess.Probability.NativeScalarSeries
public import SubdiffusiveProcess.Probability.NativeShellSummability
public import SubdiffusiveProcess.Probability.OrliczLpNorm
public import SubdiffusiveProcess.Probability.OrliczExponentialMoment
public import SubdiffusiveProcess.Main.CompactPotentialC1Norm
public import SubdiffusiveProcess.Main.CompactGradientLipschitzObservable
public import SubdiffusiveProcess.Main.PositiveAnchoredInfraredTruncation
public import SubdiffusiveProcess.Main.PositiveScaledNativeLayer_apply
public import SubdiffusiveProcess.Main.PositiveScaledNativeLayer_deriv
public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

private theorem native_infrared_orlicz_dom
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (lambda A C delta : ℝ) (hA : 0 < A) (hdelta : 0 < delta)
    (Z : ℕ → Ω → ℝ) (hZ0 : ∀ j omega, 0 ≤ Z j omega)
    (hSeries : (∫⁻ omega, ENNReal.ofReal (Real.exp
      (((∑' j : ℕ, Z j omega) / (A * delta / 2)) ^ (2 : ℕ))) ∂μ) ≤ 2)
    (V : Ω → ℝ) (hV : Measurable V) (hV0 : ∀ omega, 0 ≤ V omega)
    (hle : ∀ᵐ omega ∂μ, V omega ≤ ∑' j : ℕ, Z j omega)
    (hC : A ^ 2 ≤ C) (hlambda : 0 ≤ lambda) :
    Integrable (fun omega => Real.exp (lambda * V omega)) μ ∧
      (∫ omega, Real.exp (lambda * V omega) ∂μ) ≤
        2 * Real.exp (C * lambda ^ 2 * delta ^ 2) := by
  have hAδ2 : 0 < A * delta / 2 := div_pos (mul_pos hA hdelta) (by norm_num)
  have hExp : (∫⁻ omega, ENNReal.ofReal (Real.exp
      ((V omega / (A * delta / 2)) ^ (2 : ℕ))) ∂μ) ≤ 2 := by
    apply (lintegral_mono_ae ?_).trans hSeries
    filter_upwards [hle] with omega he
    have hnum : 0 ≤ ∑' j : ℕ, Z j omega :=
      tsum_nonneg (fun j => hZ0 j omega)
    have hq : V omega / (A * delta / 2) ≤
        (∑' j : ℕ, Z j omega) / (A * delta / 2) :=
      div_le_div_of_nonneg_right he hAδ2.le
    exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr
      ((sq_le_sq₀ (div_nonneg (hV0 omega) hAδ2.le)
        (div_nonneg hnum hAδ2.le)).2 hq))
  obtain ⟨hInt, hIntle⟩ :=
    orlicz_exp_linear_integrable_integral_le μ V (A * delta / 2)
      lambda hV hV0 hAδ2 hlambda hExp
  have hcoeff : (A * delta / 2) ^ 2 * lambda ^ 2 / 4 ≤
      C * lambda ^ 2 * delta ^ 2 := by
    calc
      (A * delta / 2) ^ 2 * lambda ^ 2 / 4 =
          A ^ 2 * (lambda ^ 2 * delta ^ 2) / 16 := by ring
      _ ≤ C * lambda ^ 2 * delta ^ 2 := by
        have hmul : A ^ 2 * (lambda ^ 2 * delta ^ 2) ≤
            C * (lambda ^ 2 * delta ^ 2) :=
            mul_le_mul_of_nonneg_right hC
              (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        have hCterm : 0 ≤ C * (lambda ^ 2 * delta ^ 2) := by
          exact le_trans (mul_nonneg (sq_nonneg _) (mul_nonneg
            (sq_nonneg _) (sq_nonneg _))) hmul
        nlinarith
  refine ⟨hInt, hIntle.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcoeff) (by norm_num))⟩

theorem exists_native_infrared_limit
    {d : ℕ} (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
  ∃ C : Compacts (SpatialCoordinates d) → ℝ,
    (∀ K, 0 ≤ C K) ∧
    ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      let μ : Measure (NativeBilateralPotentialSample d) :=
        Measure.infinitePi (fun _ : ℤ =>
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
      ∃ H : NativeBilateralPotentialSample d →
          _root_.SubdiffusiveProcess.Model.PotentialField d,
        Measurable H ∧
        (∀ K : Compacts (SpatialCoordinates d),
          Measurable (fun omega => compactPotentialC1Norm K (H omega)) ∧
          Measurable (fun omega => compactGradientLipschitzObservable K (H omega))) ∧
        (∀ᵐ omega ∂μ,
          (∀ x : SpatialCoordinates d,
            H omega x = ∑' n : ℕ,
              (positiveScaledNativeLayer omega n x -
                positiveScaledNativeLayer omega n 0)) ∧
          (∀ K : Compacts (SpatialCoordinates d),
            Tendsto
              (fun L => compactPotentialC1Norm K
                (_root_.SubdiffusiveProcess.Model.PotentialField.add
                  (positiveAnchoredInfraredTruncation omega L)
                  (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H omega))))
              atTop (nhds 0)) ∧
          (∀ K : Compacts (SpatialCoordinates d),
            LipschitzOnWith
              (Real.toNNReal (compactGradientLipschitzObservable K (H omega)))
              (fun x => _root_.SubdiffusiveProcess.Model.PotentialField.deriv (H omega) x)
              (K : Set (SpatialCoordinates d)))) ∧
        (∀ K : Compacts (SpatialCoordinates d), ∀ p : ℝ≥0∞,
          2 ≤ p → p ≠ ∞ → ∀ n : ℕ,
            eLpNorm (fun omega => compactPotentialC1Norm K
              (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                (positiveScaledNativeLayer omega n))) p μ ≤
              ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal *
                (3 : ℝ) ^ (-(n + 1 : ℤ)))) ∧
        (∀ K : Compacts (SpatialCoordinates d), ∀ p : ℝ≥0∞,
          2 ≤ p → p ≠ ∞ →
          eLpNorm (fun omega => compactPotentialC1Norm K (H omega)) p μ ≤
            ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal) ∧
          eLpNorm (fun omega => compactGradientLipschitzObservable K (H omega)) p μ ≤
            ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal) ∧
          ∀ L : ℕ,
            eLpNorm (fun omega => compactPotentialC1Norm K
                (positiveAnchoredInfraredTruncation omega L)) p μ ≤
              ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal) ∧
            eLpNorm (fun omega => compactGradientLipschitzObservable K
                (positiveAnchoredInfraredTruncation omega L)) p μ ≤
              ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal)) ∧
        (∀ K : Compacts (SpatialCoordinates d), ∀ lambda : ℝ, 0 ≤ lambda →
          Integrable (fun omega => Real.exp
            (lambda * compactPotentialC1Norm K (H omega))) μ ∧
          (∫ omega, Real.exp (lambda * compactPotentialC1Norm K (H omega)) ∂μ) ≤
            2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2) ∧
          Integrable (fun omega => Real.exp
            (lambda * compactGradientLipschitzObservable K (H omega))) μ ∧
          (∫ omega, Real.exp
              (lambda * compactGradientLipschitzObservable K (H omega)) ∂μ) ≤
            2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2) ∧
          ∀ L : ℕ,
            Integrable (fun omega => Real.exp (lambda * compactPotentialC1Norm K
              (positiveAnchoredInfraredTruncation omega L))) μ ∧
            (∫ omega, Real.exp (lambda * compactPotentialC1Norm K
                (positiveAnchoredInfraredTruncation omega L)) ∂μ) ≤
              2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2) ∧
            Integrable (fun omega => Real.exp
              (lambda * compactGradientLipschitzObservable K
                (positiveAnchoredInfraredTruncation omega L))) μ ∧
            (∫ omega, Real.exp (lambda * compactGradientLipschitzObservable K
                (positiveAnchoredInfraredTruncation omega L)) ∂μ) ≤
              2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2))
:= by
  classical
  obtain ⟨B, hB, hBbound⟩ := exists_universal_orlicz_eLpNorm_constant
  let R₀ : Compacts (SpatialCoordinates d) → ℝ := fun K =>
    Classical.choose (K.isCompact.isBounded.subset_closedBall (0 : SpatialCoordinates d))
  have hR₀ : ∀ K : Compacts (SpatialCoordinates d), ∀ x ∈ (K : Set (SpatialCoordinates d)), ‖x‖ ≤ R₀ K := by
    intro K x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (Classical.choose_spec
        (K.isCompact.isBounded.subset_closedBall (0 : SpatialCoordinates d))) hx
  let R : Compacts (SpatialCoordinates d) → ℝ := fun K => max 1 (R₀ K)
  have hR : ∀ K : Compacts (SpatialCoordinates d), 0 < R K := by
    intro K
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hKR : ∀ K : Compacts (SpatialCoordinates d), ∀ x ∈ (K : Set (SpatialCoordinates d)), ‖x‖ ≤ R K := by
    intro K x hx
    exact (hR₀ K x hx).trans (le_max_right _ _)
  let Alayer : Compacts (SpatialCoordinates d) → ℝ := fun K =>
    Classical.choose
      (exists_native_layer_joint_exp_square_bound (d := d) (R K) (hR K))
  have hAlayer : ∀ K : Compacts (SpatialCoordinates d), 0 < Alayer K := by
    intro K
    exact (Classical.choose_spec
      (exists_native_layer_joint_exp_square_bound (d := d) (R K) (hR K))).1
  let Aseries : Compacts (SpatialCoordinates d) → ℝ := fun K =>
    Classical.choose
      (exists_native_joint_scalar_series_exp_square_bound (d := d) (R K) (hR K))
  have hAseries : ∀ K : Compacts (SpatialCoordinates d), 0 < Aseries K := by
    intro K
    exact (Classical.choose_spec
      (exists_native_joint_scalar_series_exp_square_bound (d := d) (R K) (hR K))).1
  let A : Compacts (SpatialCoordinates d) → ℝ := fun K =>
    max (Alayer K) (Aseries K)
  have hA : ∀ K : Compacts (SpatialCoordinates d), 0 < A K := by
    intro K
    exact (hAlayer K).trans_le (le_max_left _ _)
  let C : Compacts (SpatialCoordinates d) → ℝ := fun K =>
    max (B * A K) ((A K) ^ 2)
  refine ⟨C, ?_, ?_⟩
  · intro K
    exact (mul_nonneg hB.le (hA K).le).trans (le_max_left _ _)
  · intro M
    let μ : Measure (NativeBilateralPotentialSample d) :=
      Measure.infinitePi (fun _ : ℤ =>
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
    let f : NativeBilateralPotentialSample d →
        _root_.SubdiffusiveProcess.Model.PotentialSample d := positiveScaledNativeLayer
    have hf : Measurable f := measurable_positiveScaledNativeLayer
    have hShell : ∀ᵐ ω ∂μ,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellC11Summable (f ω) := by
      simpa [μ, f] using ae_positiveScaledNativeLayer_shellC11Summable M
    obtain ⟨H, hHmeas, hHlim⟩ :=
      exists_measurable_anchoredC11Limit μ f hf hShell
    have hAdd : Measurable
        (fun q : _root_.SubdiffusiveProcess.Model.PotentialField d ×
            _root_.SubdiffusiveProcess.Model.PotentialField d =>
          _root_.SubdiffusiveProcess.Model.PotentialField.add q.1 q.2) := by
      let hInd : Topology.IsInducing (Subtype.val :
          _root_.SubdiffusiveProcess.Model.PotentialField d →
            C(SpatialCoordinates d, ℝ) ×
              C(SpatialCoordinates d, SpatialCoordinates d →L[ℝ] ℝ)) := ⟨rfl⟩
      let : SecondCountableTopology
          (_root_.SubdiffusiveProcess.Model.PotentialField d) :=
        hInd.secondCountableTopology
      apply Continuous.measurable
      apply Continuous.subtype_mk
      exact
        (((continuous_subtype_val.comp continuous_fst).fst.add
            (continuous_subtype_val.comp continuous_snd).fst).prodMk
          ((continuous_subtype_val.comp continuous_fst).snd.add
            (continuous_subtype_val.comp continuous_snd).snd))
    have hAnchorMeas : ∀ j : ℕ, Measurable
        (fun omega : NativeBilateralPotentialSample d =>
          _root_.SubdiffusiveProcess.Model.PotentialField.anchor
            (positiveScaledNativeLayer omega j)) := by
      intro j
      have hj : Measurable
          (fun omega : NativeBilateralPotentialSample d =>
            positiveScaledNativeLayer omega j) := by
        exact (measurable_pi_apply j).comp measurable_positiveScaledNativeLayer
      have hanchor : Continuous
          (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
            _root_.SubdiffusiveProcess.Model.PotentialField.anchor g) := by
        apply Continuous.subtype_mk
        let hval : Continuous
            (fun g : C(SpatialCoordinates d, ℝ) =>
              g - ContinuousMap.const (SpatialCoordinates d) (g 0)) :=
          continuous_id.sub
            ((ContinuousMap.continuous_const' (X := SpatialCoordinates d)
              (Y := ℝ)).comp (continuous_eval_const (0 : SpatialCoordinates d)))
        exact (hval.comp continuous_subtype_val.fst).prodMk
          continuous_subtype_val.snd
      exact hanchor.measurable.comp hj
    have hTrMeas : ∀ L : ℕ, Measurable
        (fun omega : NativeBilateralPotentialSample d =>
          positiveAnchoredInfraredTruncation omega L) := by
      intro L
      induction L with
      | zero => exact measurable_const
      | succ L ih =>
          simpa only [positiveAnchoredInfraredTruncation] using!
            hAdd.comp (ih.prodMk (hAnchorMeas L))
    have hC1nonneg : ∀ (K : Compacts (SpatialCoordinates d))
        (g : _root_.SubdiffusiveProcess.Model.PotentialField d),
        0 ≤ compactPotentialC1Norm K g := by
      intro K g
      unfold compactPotentialC1Norm
      positivity
    have hLipnonneg : ∀ (K : Compacts (SpatialCoordinates d))
        (g : _root_.SubdiffusiveProcess.Model.PotentialField d),
        0 ≤ compactGradientLipschitzObservable K g := by
      intro K g
      unfold compactGradientLipschitzObservable
      apply Real.sSup_nonneg
      rintro q ⟨x, y, hxy, rfl⟩
      exact div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hHobsMeas : ∀ K : Compacts (SpatialCoordinates d), Measurable
        (fun omega : NativeBilateralPotentialSample d =>
          compactPotentialC1Norm K (H omega)) := by
      intro K
      exact compactPotentialC1Norm_measurable_comp K hHmeas
    have hHLipMeas : ∀ K : Compacts (SpatialCoordinates d), Measurable
        (fun omega : NativeBilateralPotentialSample d =>
          compactGradientLipschitzObservable K (H omega)) := by
      intro K
      exact (compactGradientLipschitzObservable_measurable K).comp hHmeas
    refine ⟨H, hHmeas, ?_, ?_, ?_, ?_, ?_⟩
    · intro K
      constructor
      · exact compactPotentialC1Norm_measurable_comp K hHmeas
      · exact (compactGradientLipschitzObservable_measurable K).comp hHmeas
    · filter_upwards [hShell, hHlim] with ω hs hh
      have huniq : H ω =
          SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.anchoredLimitField hs :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.isAnchoredC11Limit_unique hh
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.isAnchoredC11Limit_anchoredLimitField hs)
      constructor
      · intro x
        rw [huniq]
        simp only [SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.anchoredLimitField_apply,
          SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.shellAnchoredValue]
        simp [f]
      · constructor
        · intro K
          have htrunc_apply : ∀ n : ℕ, ∀ x : SpatialCoordinates d,
              positiveAnchoredInfraredTruncation ω (n + 1) x =
                _root_.SubdiffusiveProcess.Model.anchoredPartialSumField
                  (positiveScaledNativeLayer ω) n x := by
            intro n x
            induction n with
            | zero =>
                change (zeroNativePotentialField d) x +
                    (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                      (positiveScaledNativeLayer ω 0)) x =
                  (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                    (positiveScaledNativeLayer ω 0)) x
                simp [zeroNativePotentialField]
            | succ n ih =>
                change (positiveAnchoredInfraredTruncation ω (n + 1)) x +
                    (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                      (positiveScaledNativeLayer ω (n + 1))) x =
                  (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField
                    (positiveScaledNativeLayer ω) n) x +
                    (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                      (positiveScaledNativeLayer ω (n + 1))) x
                rw [ih]
          have htrunc_deriv : ∀ n : ℕ, ∀ x : SpatialCoordinates d,
              _root_.SubdiffusiveProcess.Model.PotentialField.deriv
                  (positiveAnchoredInfraredTruncation ω (n + 1)) x =
                _root_.SubdiffusiveProcess.Model.PotentialField.deriv
                  (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField
                    (positiveScaledNativeLayer ω) n) x := by
            intro n x
            induction n with
            | zero =>
                change (zeroNativePotentialField d).deriv x +
                    (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                      (positiveScaledNativeLayer ω 0)).deriv x =
                  (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                    (positiveScaledNativeLayer ω 0)).deriv x
                have hz : (zeroNativePotentialField d).deriv x = 0 := by rfl
                rw [hz, zero_add]
            | succ n ih =>
                change (positiveAnchoredInfraredTruncation ω (n + 1)).deriv x +
                    (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                      (positiveScaledNativeLayer ω (n + 1))).deriv x =
                  (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField
                    (positiveScaledNativeLayer ω) n).deriv x +
                    (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                      (positiveScaledNativeLayer ω (n + 1))).deriv x
                rw [ih]
          have hval := hh.value_tendsto (K : Set (SpatialCoordinates d)) K.isCompact
          have hderiv := hh.deriv_tendsto (K : Set (SpatialCoordinates d)) K.isCompact
          have hvalnorm : Tendsto (fun L =>
              ‖(_root_.SubdiffusiveProcess.Model.PotentialField.add
                (positiveAnchoredInfraredTruncation ω L)
                (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H ω))).1.1.restrict
                  (K : Set (SpatialCoordinates d))‖) atTop (nhds 0) := by
            rw [Metric.tendsto_atTop]
            intro ε hε
            obtain ⟨N, hN⟩ := eventually_atTop.1
              ((Metric.tendstoUniformlyOn_iff.1 hval) ε hε)
            refine ⟨N + 1, fun L hL => ?_⟩
            obtain ⟨L', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
            have hNL : N ≤ L' := by omega
            have hx := hN L' hNL
            have hnorm : 0 ≤ ‖(_root_.SubdiffusiveProcess.Model.PotentialField.add
                (positiveAnchoredInfraredTruncation ω (L' + 1))
                (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H ω))).1.1.restrict
                  (K : Set (SpatialCoordinates d))‖ := by positivity
            rw [Real.dist_eq, sub_zero, abs_of_nonneg hnorm]
            apply (ContinuousMap.norm_lt_iff _ hε).2
            intro x
            simp only [_root_.SubdiffusiveProcess.Model.PotentialField.add_apply,
              _root_.SubdiffusiveProcess.Model.PotentialField.scale_apply,
              ContinuousMap.restrict_apply]
            rw [htrunc_apply L' x]
            simpa [f, _root_.SubdiffusiveProcess.Model.anchoredPartialSumField_apply,
              neg_one_mul, dist_eq_norm, norm_sub_rev] using! hx x x.property
          have hderivnorm : Tendsto (fun L =>
              ‖(_root_.SubdiffusiveProcess.Model.PotentialField.deriv
                (_root_.SubdiffusiveProcess.Model.PotentialField.add
                (positiveAnchoredInfraredTruncation ω L)
                  (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H ω)))).restrict
                (K : Set (SpatialCoordinates d))‖) atTop (nhds 0) := by
            rw [Metric.tendsto_atTop]
            intro ε hε
            obtain ⟨N, hN⟩ := eventually_atTop.1
              ((Metric.tendstoUniformlyOn_iff.1 hderiv) ε hε)
            refine ⟨N + 1, fun L hL => ?_⟩
            obtain ⟨L', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
            have hNL : N ≤ L' := by omega
            have hx := hN L' hNL
            have hscale (z : SpatialCoordinates d) :
                _root_.SubdiffusiveProcess.Model.PotentialField.deriv
                    (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H ω)) z =
                  -_root_.SubdiffusiveProcess.Model.PotentialField.deriv (H ω) z := by
              change ((-1 : ℝ) • ContinuousLinearMap.id ℝ
                (SpatialCoordinates d →L[ℝ] ℝ))
                  (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (H ω) z) = _
              simpa only using! (neg_one_smul ℝ (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (H ω) z))
            have hnorm : 0 ≤ ‖(_root_.SubdiffusiveProcess.Model.PotentialField.deriv
                (_root_.SubdiffusiveProcess.Model.PotentialField.add
                  (positiveAnchoredInfraredTruncation ω (L' + 1))
                  (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H ω)))).restrict
                (K : Set (SpatialCoordinates d))‖ := by positivity
            rw [Real.dist_eq, sub_zero, abs_of_nonneg hnorm]
            apply (ContinuousMap.norm_lt_iff _ hε).2
            intro x
            change ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv
                (positiveAnchoredInfraredTruncation ω (L' + 1)) x +
              _root_.SubdiffusiveProcess.Model.PotentialField.deriv
                (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H ω)) x‖ < ε
            rw [htrunc_deriv L' x, hscale x]
            rw [← sub_eq_add_neg, norm_sub_rev]
            simpa [f, SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.deriv_anchoredPartialSumField,
              neg_one_smul, dist_eq_norm] using hx x x.property
          change Tendsto (fun L =>
              ‖(_root_.SubdiffusiveProcess.Model.PotentialField.add
                (positiveAnchoredInfraredTruncation ω L)
                (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H ω))).1.1.restrict
                  (K : Set (SpatialCoordinates d))‖ +
              ‖(_root_.SubdiffusiveProcess.Model.PotentialField.deriv
                (_root_.SubdiffusiveProcess.Model.PotentialField.add
                  (positiveAnchoredInfraredTruncation ω L)
                  (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H ω)))).restrict
                (K : Set (SpatialCoordinates d))‖) atTop (nhds 0)
          simpa only [add_zero] using hvalnorm.add hderivnorm
        · intro K
          exact deriv_lipschitzOnWith_compactGradientLipschitzObservable K (H ω)
    · intro K p hp2 hp_top n
      have hδ : 0 < M.delta := M.shellPrefix.delta_pos
      let c : ℝ := (3 : ℝ) ^ (-(n + 1 : ℤ))
      let X : NativeBilateralPotentialSample d → ℝ := fun omega =>
        compactPotentialC1Norm K
          (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
            (positiveScaledNativeLayer omega n))
      let Y : NativeBilateralPotentialSample d → ℝ := fun omega =>
        compactGradientLipschitzObservable K
          (positiveScaledNativeLayer omega n)
      have hlayer : Measurable
          (fun omega : NativeBilateralPotentialSample d =>
            positiveScaledNativeLayer omega n) := by
        exact (measurable_pi_apply n).comp measurable_positiveScaledNativeLayer
      have hXmeas : Measurable X := by
        have hanchor : Continuous
            (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
              _root_.SubdiffusiveProcess.Model.PotentialField.anchor g) := by
          apply Continuous.subtype_mk
          let hval : Continuous
              (fun g : C(SpatialCoordinates d, ℝ) =>
                g - ContinuousMap.const (SpatialCoordinates d) (g 0)) :=
            continuous_id.sub
              ((ContinuousMap.continuous_const' (X := SpatialCoordinates d)
                (Y := ℝ)).comp (continuous_eval_const (0 : SpatialCoordinates d)))
          exact (hval.comp continuous_subtype_val.fst).prodMk
            continuous_subtype_val.snd
        apply compactPotentialC1Norm_measurable_comp K
        exact hanchor.measurable.comp hlayer
      have hX0 : ∀ omega, 0 ≤ X omega := by
        intro omega
        exact (by dsimp [X, compactPotentialC1Norm]; positivity)
      have hY0 : ∀ omega, 0 ≤ Y omega := by
        intro omega
        dsimp [Y]
        unfold compactGradientLipschitzObservable
        apply Real.sSup_nonneg
        rintro q ⟨x, y, hxy, rfl⟩
        exact div_nonneg (norm_nonneg _) (norm_nonneg _)
      have hanchor : Continuous
          (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
            _root_.SubdiffusiveProcess.Model.PotentialField.anchor g) := by
        apply Continuous.subtype_mk
        let hval : Continuous
            (fun g : C(SpatialCoordinates d, ℝ) =>
              g - ContinuousMap.const (SpatialCoordinates d) (g 0)) :=
          continuous_id.sub
            ((ContinuousMap.continuous_const' (X := SpatialCoordinates d)
              (Y := ℝ)).comp (continuous_eval_const (0 : SpatialCoordinates d)))
        exact (hval.comp continuous_subtype_val.fst).prodMk
          continuous_subtype_val.snd
      have hZmeas : ∀ j : ℕ, Measurable (fun omega =>
          max
            (compactPotentialC1Norm K
              (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                (positiveScaledNativeLayer omega j)))
            (compactGradientLipschitzObservable K
              (positiveScaledNativeLayer omega j))) := by
        intro j
        have hj : Measurable
            (fun omega : NativeBilateralPotentialSample d =>
              positiveScaledNativeLayer omega j) := by
          exact (measurable_pi_apply j).comp measurable_positiveScaledNativeLayer
        have hxj : Measurable (fun omega =>
            compactPotentialC1Norm K
              (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                (positiveScaledNativeLayer omega j))) :=
          compactPotentialC1Norm_measurable_comp K
            (hanchor.measurable.comp hj)
        have hyj : Measurable (fun omega =>
            compactGradientLipschitzObservable K
              (positiveScaledNativeLayer omega j)) :=
          (compactGradientLipschitzObservable_measurable K).comp hj
        exact hxj.max hyj
      have hC1nonneg : ∀ j omega, 0 ≤
          compactPotentialC1Norm K
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer omega j)) := by
        intro j omega
        dsimp [compactPotentialC1Norm]
        positivity
      have hLipnonneg : ∀ j omega, 0 ≤
          compactGradientLipschitzObservable K
            (positiveScaledNativeLayer omega j) := by
        intro j omega
        unfold compactGradientLipschitzObservable
        apply Real.sSup_nonneg
        rintro q ⟨x, y, hxy, rfl⟩
        exact div_nonneg (norm_nonneg _) (norm_nonneg _)
      have hZsum : ∀ᵐ omega ∂μ, Summable (fun j =>
          max
            (compactPotentialC1Norm K
              (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                (positiveScaledNativeLayer omega j)))
            (compactGradientLipschitzObservable K
              (positiveScaledNativeLayer omega j))) := by
        filter_upwards [hShell] with omega hω
        obtain ⟨hC1sum, hLipsum⟩ :=
          shellC11Summable_compact_observables (f omega) hω K
        apply Summable.of_nonneg_of_le
          (fun j => le_max_of_le_left (hC1nonneg j omega))
          (fun j => max_le
            (le_add_of_nonneg_right (hLipnonneg j omega))
            (le_add_of_nonneg_left (hC1nonneg j omega)))
          (hC1sum.add hLipsum)
      have hLayerNative :=
        (Classical.choose_spec
          (exists_native_layer_joint_exp_square_bound
            (d := d) (R K) (hR K))).2 M K (hKR K) n
      dsimp [X, Y, c] at hLayerNative ⊢
      have hAlayerA : Alayer K ≤ A K := by
        exact le_max_left _ _
      have hc : 0 < c := by
        dsimp [c]
        positivity
      have hscale : ∀ {x y q B : ℝ}, 0 < q → q ≤ 1 → 0 < B →
          0 ≤ x → 0 ≤ y →
          max x y / (B * q) ≤ max (x / q) (y / q ^ 2) / B := by
        intro x y q B hq hq1 hB hx hy
        have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
        have hyq : y / q ≤ y / q ^ 2 := by
          apply (div_le_div_iff₀ hq hq2).2
          nlinarith [mul_nonneg hy (sub_nonneg.mpr hq1)]
        have hmax : max x y / q ≤ max (x / q) (y / q ^ 2) := by
          apply (div_le_iff₀ hq).2
          apply max_le
          · calc
              x = (x / q) * q := by field_simp
              _ ≤ max (x / q) (y / q ^ 2) * q :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) hq.le
          · calc
              y = (y / q) * q := by field_simp
              _ ≤ (y / q ^ 2) * q :=
                mul_le_mul_of_nonneg_right hyq hq.le
              _ ≤ max (x / q) (y / q ^ 2) * q :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) hq.le
        calc
          max x y / (B * q) = (max x y / q) / B := by field_simp
          _ ≤ max (x / q) (y / q ^ 2) / B :=
            div_le_div_of_nonneg_right hmax hB.le
      have hpoint : ∀ omega,
          X omega / (A K * M.delta * c) ≤
            max (X omega / c) (Y omega / c ^ 2) / (A K * M.delta) := by
        intro omega
        have hc : 0 < c := by
          dsimp [c]
          positivity
        calc
          X omega / (A K * M.delta * c) ≤
              max (X omega) (Y omega) / (A K * M.delta * c) := by
            exact div_le_div_of_nonneg_right (le_max_left _ _)
              (mul_pos (mul_pos (hA K) hδ) hc).le
          _ ≤ max (X omega / c) (Y omega / c ^ 2) / (A K * M.delta) :=
            hscale (q := c) (B := A K * M.delta) hc (by
          apply zpow_le_one_of_nonpos₀ (by norm_num)
          omega) (mul_pos (hA K) hδ) (hX0 omega) (hY0 omega)
      have hExp : (∫⁻ omega, ENNReal.ofReal (Real.exp
          ((X omega / (A K * M.delta * c)) ^ (2 : ℕ))) ∂μ) ≤ 2 := by
        apply (lintegral_mono (fun omega => ?_)).trans hLayerNative.1
        have hleft : 0 ≤ X omega / (A K * M.delta * c) := by
          exact div_nonneg (hX0 omega)
            (mul_pos (mul_pos (hA K) hδ) (zpow_pos (by norm_num) _)).le
        have hright : 0 ≤
            max (X omega / c) (Y omega / c ^ 2) / (A K * M.delta) := by
          apply div_nonneg
          · exact le_max_of_le_left
              (div_nonneg (hX0 omega) (zpow_pos (by norm_num) _).le)
          · exact (mul_pos (hA K) hδ).le
        have hden' : 0 ≤
            max (X omega / c) (Y omega / c ^ 2) / (Alayer K * M.delta) := by
          apply div_nonneg
          · exact le_max_of_le_left
              (div_nonneg (hX0 omega) (zpow_pos (by norm_num) _).le)
          · exact (mul_pos (hAlayer K) hδ).le
        have htransport :
            max (X omega / c) (Y omega / c ^ 2) / (A K * M.delta) ≤
              max (X omega / c) (Y omega / c ^ 2) / (Alayer K * M.delta) := by
          exact div_le_div_of_nonneg_left
            (le_max_of_le_left
              (div_nonneg (hX0 omega) (zpow_pos (by norm_num) _).le))
            (mul_pos (hAlayer K) hδ)
            (mul_le_mul_of_nonneg_right hAlayerA hδ.le)
        exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr
          ((sq_le_sq₀ hleft hden').2 (hpoint omega |>.trans htransport)))
      have hLp := hBbound μ X (A K * M.delta * c)
        hXmeas hX0 (mul_pos (mul_pos (hA K) hδ) hc) hExp p hp_top hp2
      apply hLp.trans
      apply ENNReal.ofReal_mono
      calc
        B * (A K * M.delta * c) * Real.sqrt p.toReal =
            (B * A K) * M.delta * Real.sqrt p.toReal * c := by ring
        _ ≤ C K * M.delta * Real.sqrt p.toReal * c := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le)
              (Real.sqrt_nonneg _))
            hc.le
        _ = C K * M.delta * Real.sqrt p.toReal *
            (3 : ℝ) ^ (-(n + 1 : ℤ)) := by rfl
    · intro K p hp2 hp_top
      let Z : ℕ → NativeBilateralPotentialSample d → ℝ := fun j omega =>
        max
          (compactPotentialC1Norm K
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer omega j)))
          (compactGradientLipschitzObservable K
            (positiveScaledNativeLayer omega j))
      have hδ : 0 < M.delta := M.shellPrefix.delta_pos
      have hZ0 : ∀ j omega, 0 ≤ Z j omega := by
        intro j omega
        exact le_max_of_le_left (by
          change 0 ≤ compactPotentialC1Norm K
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer omega j))
          unfold compactPotentialC1Norm
          positivity)
      have hZm : ∀ j, Measurable (Z j) := by
        intro j
        have hj : Measurable
            (fun omega : NativeBilateralPotentialSample d =>
              positiveScaledNativeLayer omega j) := by
          exact (measurable_pi_apply j).comp measurable_positiveScaledNativeLayer
        have hanchor : Continuous
            (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
              _root_.SubdiffusiveProcess.Model.PotentialField.anchor g) := by
          apply Continuous.subtype_mk
          let hval : Continuous
              (fun g : C(SpatialCoordinates d, ℝ) =>
                g - ContinuousMap.const (SpatialCoordinates d) (g 0)) :=
            continuous_id.sub
              ((ContinuousMap.continuous_const' (X := SpatialCoordinates d)
                (Y := ℝ)).comp (continuous_eval_const (0 : SpatialCoordinates d)))
          exact (hval.comp continuous_subtype_val.fst).prodMk
            continuous_subtype_val.snd
        have hxj : Measurable (fun omega =>
            compactPotentialC1Norm K
              (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                (positiveScaledNativeLayer omega j))) :=
          compactPotentialC1Norm_measurable_comp K
            (hanchor.measurable.comp hj)
        have hyj : Measurable (fun omega =>
            compactGradientLipschitzObservable K
              (positiveScaledNativeLayer omega j)) :=
          (compactGradientLipschitzObservable_measurable K).comp hj
        simpa [Z] using hxj.max hyj
      have hZs : ∀ᵐ omega ∂μ, Summable (fun j => Z j omega) := by
        filter_upwards [hShell] with omega hs
        obtain ⟨hc1, hlip⟩ := shellC11Summable_compact_observables
          (f omega) hs K
        exact Summable.of_nonneg_of_le
          (fun j => hZ0 j omega)
          (fun j => max_le
            (le_add_of_nonneg_right (by
              unfold compactGradientLipschitzObservable
              apply Real.sSup_nonneg
              rintro q ⟨x, y, hxy, rfl⟩
              exact div_nonneg (norm_nonneg _) (norm_nonneg _)))
            (le_add_of_nonneg_left (by
              unfold compactPotentialC1Norm
              positivity)))
          (hc1.add hlip)
      have hSeriesNative :=
        (Classical.choose_spec
          (exists_native_joint_scalar_series_exp_square_bound
            (d := d) (R K) (hR K))).2 M K (hKR K) hZm hZs
      have hSeries :
          (∫⁻ omega, ENNReal.ofReal (Real.exp
            (((∑' j : ℕ, Z j omega) / (A K * M.delta / 2)) ^ (2 : ℕ))) ∂μ) ≤ 2 ∧
          ∀ L : ℕ,
            (∫⁻ omega, ENNReal.ofReal (Real.exp
              (((∑ j ∈ Finset.range L, Z j omega) /
                (A K * M.delta / 2)) ^ (2 : ℕ))) ∂μ) ≤ 2 := by
        have hAseriesA : Aseries K ≤ A K := le_max_right _ _
        have hδ2 : 0 < M.delta / 2 := div_pos hδ (by norm_num)
        have hdenA : 0 < A K * M.delta / 2 :=
          div_pos (mul_pos (hA K) hδ) (by norm_num)
        have hdenS : 0 < Aseries K * M.delta / 2 :=
          div_pos (mul_pos (hAseries K) hδ) (by norm_num)
        have hdenle : Aseries K * M.delta / 2 ≤ A K * M.delta / 2 := by
          gcongr
        rcases hSeriesNative with ⟨hTotal, hFin⟩
        have htotal :
            (∫⁻ omega, ENNReal.ofReal (Real.exp
              (((∑' j : ℕ, Z j omega) / (A K * M.delta / 2)) ^ (2 : ℕ))) ∂μ) ≤ 2 := by
          apply (lintegral_mono (fun omega => ?_)).trans hTotal
          have hnum : 0 ≤ ∑' j : ℕ, Z j omega :=
            tsum_nonneg (fun j => hZ0 j omega)
          have hq :
              (∑' j : ℕ, Z j omega) / (A K * M.delta / 2) ≤
                (∑' j : ℕ, Z j omega) / (Aseries K * M.delta / 2) :=
            div_le_div_of_nonneg_left hnum hdenS hdenle
          have hleft : 0 ≤
              (∑' j : ℕ, Z j omega) / (A K * M.delta / 2) :=
            div_nonneg hnum hdenA.le
          have hright : 0 ≤
              (∑' j : ℕ, Z j omega) / (Aseries K * M.delta / 2) :=
            div_nonneg hnum hdenS.le
          exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr
            ((sq_le_sq₀ hleft hright).2 hq))
        refine ⟨htotal, ?_⟩
        intro L
        apply (lintegral_mono (fun omega => ?_)).trans (hFin L)
        have hnum : 0 ≤ ∑ j ∈ Finset.range L, Z j omega := by
          exact Finset.sum_nonneg (fun j hj =>
            hZ0 j omega)
        have hq :
            (∑ j ∈ Finset.range L, Z j omega) / (A K * M.delta / 2) ≤
              (∑ j ∈ Finset.range L, Z j omega) /
                (Aseries K * M.delta / 2) :=
          div_le_div_of_nonneg_left hnum hdenS hdenle
        have hleft : 0 ≤
            (∑ j ∈ Finset.range L, Z j omega) / (A K * M.delta / 2) :=
          div_nonneg hnum hdenA.le
        have hright : 0 ≤
            (∑ j ∈ Finset.range L, Z j omega) / (Aseries K * M.delta / 2) :=
          div_nonneg hnum hdenS.le
        exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr
          ((sq_le_sq₀ hleft hright).2 hq))
      have hHobs : Measurable
          (fun omega => compactPotentialC1Norm K (H omega)) :=
        compactPotentialC1Norm_measurable_comp K hHmeas
      have hHlip : Measurable
          (fun omega => compactGradientLipschitzObservable K (H omega)) :=
        (compactGradientLipschitzObservable_measurable K).comp hHmeas
      have hHobs0 : ∀ omega, 0 ≤ compactPotentialC1Norm K (H omega) := by
        intro omega
        unfold compactPotentialC1Norm
        positivity
      have hHlip0 : ∀ omega,
          0 ≤ compactGradientLipschitzObservable K (H omega) := by
        intro omega
        unfold compactGradientLipschitzObservable
        apply Real.sSup_nonneg
        rintro q ⟨x, y, hxy, rfl⟩
        exact div_nonneg (norm_nonneg _) (norm_nonneg _)
      have hEnv : ∀ᵐ omega ∂μ,
          compactPotentialC1Norm K (H omega) ≤ ∑' j : ℕ, Z j omega ∧
          compactGradientLipschitzObservable K (H omega) ≤ ∑' j : ℕ, Z j omega ∧
          ∀ L : ℕ,
            compactPotentialC1Norm K (positiveAnchoredInfraredTruncation omega L) ≤
              ∑' j : ℕ, Z j omega ∧
            compactGradientLipschitzObservable K
                (positiveAnchoredInfraredTruncation omega L) ≤ ∑' j : ℕ, Z j omega := by
        filter_upwards [hShell, hHlim, hZs] with omega hs hh hω
        obtain ⟨hc1, hlip⟩ := shellC11Summable_compact_observables
          (f omega) hs K
        have hc1' : Summable (fun j =>
            compactPotentialC1Norm K
              (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                (positiveScaledNativeLayer omega j))) :=
          Summable.of_nonneg_of_le
            (fun j => by
              unfold compactPotentialC1Norm
              positivity)
            (fun j => le_max_left _ _) hω
        have hlip' : Summable (fun j =>
            compactGradientLipschitzObservable K
              (positiveScaledNativeLayer omega j)) :=
          Summable.of_nonneg_of_le
            (fun j => by
              unfold compactGradientLipschitzObservable
              apply Real.sSup_nonneg
              rintro q ⟨x, y, hxy, rfl⟩
              exact div_nonneg (norm_nonneg _) (norm_nonneg _))
            (fun j => le_max_right _ _) hω
        have he := native_infrared_compact_observable_envelope omega (H omega)
          hh K hc1' hlip'
        refine ⟨?_, ?_, ?_⟩
        · exact he.1.trans (Summable.tsum_le_tsum
            (fun j => le_max_left _ _) hc1' hω)
        · exact he.2.1.trans (Summable.tsum_le_tsum
            (fun j => le_max_right _ _) hlip' hω)
        · intro L
          exact ⟨he.2.2 L |>.1.trans (Summable.tsum_le_tsum
              (fun j => le_max_left _ _) hc1' hω),
            he.2.2 L |>.2.trans (Summable.tsum_le_tsum
              (fun j => le_max_right _ _) hlip' hω)⟩
      have hExpH :
          (∫⁻ omega, ENNReal.ofReal (Real.exp
            ((compactPotentialC1Norm K (H omega) /
              (A K * M.delta)) ^ (2 : ℕ))) ∂μ) ≤ 2 := by
        apply (lintegral_mono_ae ?_).trans hSeries.1
        filter_upwards [hEnv] with omega he
        have hnum : 0 ≤ ∑' j : ℕ, Z j omega := by
          exact tsum_nonneg (fun j => hZ0 j omega)
        have hq : compactPotentialC1Norm K (H omega) / (A K * M.delta) ≤
            (∑' j : ℕ, Z j omega) / (A K * M.delta / 2) := by
          calc
            _ ≤ (∑' j : ℕ, Z j omega) / (A K * M.delta) :=
              div_le_div_of_nonneg_right he.1 (mul_pos (hA K) hδ).le
            _ ≤ _ := by
              apply div_le_div_of_nonneg_left hnum
              · exact div_pos (mul_pos (hA K) hδ) (by norm_num)
              · nlinarith [mul_pos (hA K) hδ]
        exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr
          ((sq_le_sq₀ (div_nonneg (hHobs0 omega) (mul_pos (hA K) hδ).le)
            (div_nonneg hnum
              (div_pos (mul_pos (hA K) hδ) (by norm_num)).le)).2 hq))
      have hLpH := hBbound μ (fun omega => compactPotentialC1Norm K (H omega))
        (A K * M.delta) hHobs hHobs0 (mul_pos (hA K) hδ) hExpH p hp_top hp2
      have hLpH' : eLpNorm (fun omega => compactPotentialC1Norm K (H omega)) p μ ≤
          ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal) := by
        apply hLpH.trans
        apply ENNReal.ofReal_mono
        calc
          B * (A K * M.delta) * Real.sqrt p.toReal =
              (B * A K) * M.delta * Real.sqrt p.toReal := by ring
          _ ≤ C K * M.delta * Real.sqrt p.toReal := by
            gcongr
            exact le_max_left _ _
      have hExpLip :
          (∫⁻ omega, ENNReal.ofReal (Real.exp
            ((compactGradientLipschitzObservable K (H omega) /
              (A K * M.delta)) ^ (2 : ℕ))) ∂μ) ≤ 2 := by
        apply (lintegral_mono_ae ?_).trans hSeries.1
        filter_upwards [hEnv] with omega he
        have hnum : 0 ≤ ∑' j : ℕ, Z j omega := by
          exact tsum_nonneg (fun j => hZ0 j omega)
        have hq : compactGradientLipschitzObservable K (H omega) /
              (A K * M.delta) ≤
            (∑' j : ℕ, Z j omega) / (A K * M.delta / 2) := by
          calc
            _ ≤ (∑' j : ℕ, Z j omega) / (A K * M.delta) :=
              div_le_div_of_nonneg_right he.2.1 (mul_pos (hA K) hδ).le
            _ ≤ _ := by
              apply div_le_div_of_nonneg_left hnum
              · exact div_pos (mul_pos (hA K) hδ) (by norm_num)
              · nlinarith [mul_pos (hA K) hδ]
        exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr
          ((sq_le_sq₀ (div_nonneg (hHlip0 omega) (mul_pos (hA K) hδ).le)
            (div_nonneg hnum
              (div_pos (mul_pos (hA K) hδ) (by norm_num)).le)).2 hq))
      have hLpLip := hBbound μ (fun omega => compactGradientLipschitzObservable K (H omega))
        (A K * M.delta) hHlip hHlip0 (mul_pos (hA K) hδ) hExpLip p hp_top hp2
      have hLpLip' : eLpNorm (fun omega => compactGradientLipschitzObservable K (H omega)) p μ ≤
          ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal) := by
        apply hLpLip.trans
        apply ENNReal.ofReal_mono
        calc
          B * (A K * M.delta) * Real.sqrt p.toReal =
              (B * A K) * M.delta * Real.sqrt p.toReal := by ring
          _ ≤ C K * M.delta * Real.sqrt p.toReal := by
            gcongr
            exact le_max_left _ _
      refine ⟨hLpH', hLpLip', ?_⟩
      intro L
      have hTrC1Meas : Measurable (fun omega =>
          compactPotentialC1Norm K
            (positiveAnchoredInfraredTruncation omega L)) :=
        compactPotentialC1Norm_measurable_comp K (hTrMeas L)
      have hTrLipMeas : Measurable (fun omega =>
          compactGradientLipschitzObservable K
            (positiveAnchoredInfraredTruncation omega L)) :=
        (compactGradientLipschitzObservable_measurable K).comp (hTrMeas L)
      have hTrC10 : ∀ omega, 0 ≤ compactPotentialC1Norm K
          (positiveAnchoredInfraredTruncation omega L) := by
        intro omega
        unfold compactPotentialC1Norm
        positivity
      have hTrLip0 : ∀ omega, 0 ≤ compactGradientLipschitzObservable K
          (positiveAnchoredInfraredTruncation omega L) := by
        intro omega
        unfold compactGradientLipschitzObservable
        apply Real.sSup_nonneg
        rintro q ⟨x, y, hxy, rfl⟩
        exact div_nonneg (norm_nonneg _) (norm_nonneg _)
      have hExpTrC :
          (∫⁻ omega, ENNReal.ofReal (Real.exp
            ((compactPotentialC1Norm K
              (positiveAnchoredInfraredTruncation omega L) /
                (A K * M.delta)) ^ (2 : ℕ))) ∂μ) ≤ 2 := by
        apply (lintegral_mono_ae ?_).trans hSeries.1
        filter_upwards [hEnv] with omega he
        have hnum : 0 ≤ ∑' j : ℕ, Z j omega :=
          tsum_nonneg (fun j => hZ0 j omega)
        have hq : compactPotentialC1Norm K
              (positiveAnchoredInfraredTruncation omega L) /
                (A K * M.delta) ≤
            (∑' j : ℕ, Z j omega) /
              (A K * M.delta / 2) := by
          calc
            _ ≤ (∑' j : ℕ, Z j omega) /
                (A K * M.delta) :=
              div_le_div_of_nonneg_right (he.2.2 L).1
                (mul_pos (hA K) hδ).le
            _ ≤ _ := by
              apply div_le_div_of_nonneg_left hnum
              · exact div_pos (mul_pos (hA K) hδ) (by norm_num)
              · nlinarith [mul_pos (hA K) hδ]
        exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr
          ((sq_le_sq₀ (div_nonneg (hTrC10 omega)
              (mul_pos (hA K) hδ).le)
            (div_nonneg hnum
              (div_pos (mul_pos (hA K) hδ) (by norm_num)).le)).2 hq))
      have hExpTrLip :
          (∫⁻ omega, ENNReal.ofReal (Real.exp
            ((compactGradientLipschitzObservable K
              (positiveAnchoredInfraredTruncation omega L) /
                (A K * M.delta)) ^ (2 : ℕ))) ∂μ) ≤ 2 := by
        apply (lintegral_mono_ae ?_).trans hSeries.1
        filter_upwards [hEnv] with omega he
        have hnum : 0 ≤ ∑' j : ℕ, Z j omega :=
          tsum_nonneg (fun j => hZ0 j omega)
        have hq : compactGradientLipschitzObservable K
              (positiveAnchoredInfraredTruncation omega L) /
                (A K * M.delta) ≤
            (∑' j : ℕ, Z j omega) /
              (A K * M.delta / 2) := by
          calc
            _ ≤ (∑' j : ℕ, Z j omega) /
                (A K * M.delta) :=
              div_le_div_of_nonneg_right (he.2.2 L).2
                (mul_pos (hA K) hδ).le
            _ ≤ _ := by
              apply div_le_div_of_nonneg_left hnum
              · exact div_pos (mul_pos (hA K) hδ) (by norm_num)
              · nlinarith [mul_pos (hA K) hδ]
        exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr
          ((sq_le_sq₀ (div_nonneg (hTrLip0 omega)
              (mul_pos (hA K) hδ).le)
            (div_nonneg hnum
              (div_pos (mul_pos (hA K) hδ) (by norm_num)).le)).2 hq))
      have hTrLpC := hBbound μ
        (fun omega => compactPotentialC1Norm K
          (positiveAnchoredInfraredTruncation omega L))
        (A K * M.delta) hTrC1Meas hTrC10 (mul_pos (hA K) hδ) hExpTrC p hp_top hp2
      have hTrLpLip := hBbound μ
        (fun omega => compactGradientLipschitzObservable K
          (positiveAnchoredInfraredTruncation omega L))
        (A K * M.delta) hTrLipMeas hTrLip0 (mul_pos (hA K) hδ) hExpTrLip p hp_top hp2
      constructor
      · apply hTrLpC.trans
        apply ENNReal.ofReal_mono
        calc
          B * (A K * M.delta) * Real.sqrt p.toReal =
              (B * A K) * M.delta * Real.sqrt p.toReal := by ring
          _ ≤ C K * M.delta * Real.sqrt p.toReal := by
            gcongr
            exact le_max_left _ _
      · apply hTrLpLip.trans
        apply ENNReal.ofReal_mono
        calc
          B * (A K * M.delta) * Real.sqrt p.toReal =
              (B * A K) * M.delta * Real.sqrt p.toReal := by ring
          _ ≤ C K * M.delta * Real.sqrt p.toReal := by
            gcongr
            exact le_max_left _ _
    · intro K lambda hlambda
      let Z : ℕ → NativeBilateralPotentialSample d → ℝ := fun j omega =>
        max
          (compactPotentialC1Norm K
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer omega j)))
          (compactGradientLipschitzObservable K
            (positiveScaledNativeLayer omega j))
      have hδ : 0 < M.delta := M.shellPrefix.delta_pos
      have hZ0 : ∀ j omega, 0 ≤ Z j omega := by
        intro j omega
        exact le_max_of_le_left (by
          change 0 ≤ compactPotentialC1Norm K
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer omega j))
          unfold compactPotentialC1Norm
          positivity)
      have hZm : ∀ j : ℕ, Measurable (Z j) := by
        intro j
        have hj : Measurable
            (fun omega : NativeBilateralPotentialSample d =>
              positiveScaledNativeLayer omega j) := by
          exact (measurable_pi_apply j).comp measurable_positiveScaledNativeLayer
        have hanchor : Continuous
            (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
              _root_.SubdiffusiveProcess.Model.PotentialField.anchor g) := by
          apply Continuous.subtype_mk
          let hval : Continuous
              (fun g : C(SpatialCoordinates d, ℝ) =>
                g - ContinuousMap.const (SpatialCoordinates d) (g 0)) :=
            continuous_id.sub
              ((ContinuousMap.continuous_const' (X := SpatialCoordinates d)
                (Y := ℝ)).comp (continuous_eval_const (0 : SpatialCoordinates d)))
          exact (hval.comp continuous_subtype_val.fst).prodMk
            continuous_subtype_val.snd
        have hxj : Measurable (fun omega =>
            compactPotentialC1Norm K
              (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                (positiveScaledNativeLayer omega j))) :=
          compactPotentialC1Norm_measurable_comp K
            (hanchor.measurable.comp hj)
        have hyj : Measurable (fun omega =>
            compactGradientLipschitzObservable K
              (positiveScaledNativeLayer omega j)) :=
          (compactGradientLipschitzObservable_measurable K).comp hj
        simpa [Z] using hxj.max hyj
      have hZs : ∀ᵐ omega ∂μ, Summable (fun j => Z j omega) := by
        filter_upwards [hShell] with omega hs
        obtain ⟨hc1, hlip⟩ := shellC11Summable_compact_observables
          (f omega) hs K
        exact Summable.of_nonneg_of_le
          (fun j => hZ0 j omega)
          (fun j => max_le
            (le_add_of_nonneg_right (by
              unfold compactGradientLipschitzObservable
              apply Real.sSup_nonneg
              rintro q ⟨x, y, hxy, rfl⟩
              exact div_nonneg (norm_nonneg _) (norm_nonneg _)))
            (le_add_of_nonneg_left (by
              unfold compactPotentialC1Norm
              positivity)))
          (hc1.add hlip)
      have hSeriesNative :=
        (Classical.choose_spec
          (exists_native_joint_scalar_series_exp_square_bound
            (d := d) (R K) (hR K))).2 M K (hKR K) hZm hZs
      have hSeries :
          (∫⁻ omega, ENNReal.ofReal (Real.exp
            (((∑' j : ℕ, Z j omega) / (A K * M.delta / 2)) ^ (2 : ℕ))) ∂μ) ≤ 2 := by
        rcases hSeriesNative with ⟨hTotal, hFin⟩
        have hdenA : 0 < A K * M.delta / 2 :=
          div_pos (mul_pos (hA K) hδ) (by norm_num)
        have hdenS : 0 < Aseries K * M.delta / 2 :=
          div_pos (mul_pos (hAseries K) hδ) (by norm_num)
        have hdenle : Aseries K * M.delta / 2 ≤ A K * M.delta / 2 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le)
            (by norm_num)
        apply (lintegral_mono (fun omega => ?_)).trans hTotal
        have hnum : 0 ≤ ∑' j : ℕ, Z j omega :=
          tsum_nonneg (fun j => hZ0 j omega)
        have hq :
            (∑' j : ℕ, Z j omega) / (A K * M.delta / 2) ≤
              (∑' j : ℕ, Z j omega) / (Aseries K * M.delta / 2) :=
          div_le_div_of_nonneg_left hnum hdenS hdenle
        exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr
          ((sq_le_sq₀ (div_nonneg hnum hdenA.le)
            (div_nonneg hnum hdenS.le)).2 hq))
      have hEnv : ∀ᵐ omega ∂μ,
          compactPotentialC1Norm K (H omega) ≤ ∑' j : ℕ, Z j omega ∧
          compactGradientLipschitzObservable K (H omega) ≤ ∑' j : ℕ, Z j omega ∧
          ∀ L : ℕ,
            compactPotentialC1Norm K (positiveAnchoredInfraredTruncation omega L) ≤
              ∑' j : ℕ, Z j omega ∧
            compactGradientLipschitzObservable K
                (positiveAnchoredInfraredTruncation omega L) ≤ ∑' j : ℕ, Z j omega := by
        filter_upwards [hShell, hHlim, hZs] with omega hs hh hω
        obtain ⟨hc1, hlip⟩ := shellC11Summable_compact_observables
          (f omega) hs K
        have hc1' : Summable (fun j =>
            compactPotentialC1Norm K
              (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                (positiveScaledNativeLayer omega j))) :=
          Summable.of_nonneg_of_le
            (fun j => hC1nonneg K
              (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                (positiveScaledNativeLayer omega j)))
            (fun j => le_max_left _ _) hω
        have hlip' : Summable (fun j =>
            compactGradientLipschitzObservable K
              (positiveScaledNativeLayer omega j)) :=
          Summable.of_nonneg_of_le
            (fun j => hLipnonneg K (positiveScaledNativeLayer omega j))
            (fun j => le_max_right _ _) hω
        have he := native_infrared_compact_observable_envelope omega (H omega)
          hh K hc1' hlip'
        refine ⟨?_, ?_, ?_⟩
        · exact he.1.trans (Summable.tsum_le_tsum
            (fun j => le_max_left _ _) hc1' hω)
        · exact he.2.1.trans (Summable.tsum_le_tsum
            (fun j => le_max_right _ _) hlip' hω)
        · intro L
          exact ⟨he.2.2 L |>.1.trans (Summable.tsum_le_tsum
              (fun j => le_max_left _ _) hc1' hω),
            he.2.2 L |>.2.trans (Summable.tsum_le_tsum
              (fun j => le_max_right _ _) hlip' hω)⟩
      have hHobs : Measurable (fun omega => compactPotentialC1Norm K (H omega)) :=
        hHobsMeas K
      have hHlip : Measurable
          (fun omega => compactGradientLipschitzObservable K (H omega)) :=
        hHLipMeas K
      have hH0 : ∀ omega, 0 ≤ compactPotentialC1Norm K (H omega) := by
        intro omega
        exact hC1nonneg K (H omega)
      have hHL0 : ∀ omega, 0 ≤ compactGradientLipschitzObservable K (H omega) := by
        intro omega
        exact hLipnonneg K (H omega)
      have hDom (V : NativeBilateralPotentialSample d → ℝ)
          (hV : Measurable V) (hV0 : ∀ omega, 0 ≤ V omega)
          (hle : ∀ᵐ omega ∂μ, V omega ≤ ∑' j : ℕ, Z j omega) :=
        native_infrared_orlicz_dom μ lambda (A K) (C K) M.delta
          (hA K) hδ Z hZ0 hSeries V hV hV0 hle (le_max_right _ _) hlambda
      have hleH : ∀ᵐ omega ∂μ,
          compactPotentialC1Norm K (H omega) ≤ ∑' j : ℕ, Z j omega :=
        hEnv.mono fun omega he => he.1
      obtain ⟨hIH, hIHle⟩ := hDom
        (fun omega => compactPotentialC1Norm K (H omega)) hHobs hH0
        hleH
      have hleHL : ∀ᵐ omega ∂μ,
          compactGradientLipschitzObservable K (H omega) ≤ ∑' j : ℕ, Z j omega :=
        hEnv.mono fun omega he => he.2.1
      obtain ⟨hIL, hILle⟩ := hDom
        (fun omega => compactGradientLipschitzObservable K (H omega)) hHlip hHL0
        hleHL
      refine ⟨hIH, hIHle, hIL, hILle, ?_⟩
      intro L
      have hTC : Measurable (fun omega =>
          compactPotentialC1Norm K (positiveAnchoredInfraredTruncation omega L)) :=
        compactPotentialC1Norm_measurable_comp K (hTrMeas L)
      have hTL : Measurable (fun omega =>
          compactGradientLipschitzObservable K (positiveAnchoredInfraredTruncation omega L)) :=
        (compactGradientLipschitzObservable_measurable K).comp (hTrMeas L)
      have hTC0 : ∀ omega, 0 ≤ compactPotentialC1Norm K
          (positiveAnchoredInfraredTruncation omega L) := by
        intro omega
        exact hC1nonneg K (positiveAnchoredInfraredTruncation omega L)
      have hTL0 : ∀ omega, 0 ≤ compactGradientLipschitzObservable K
          (positiveAnchoredInfraredTruncation omega L) := by
        intro omega
        exact hLipnonneg K (positiveAnchoredInfraredTruncation omega L)
      have hTC' := hDom
        (fun omega => compactPotentialC1Norm K
          (positiveAnchoredInfraredTruncation omega L)) hTC hTC0
        (hEnv.mono fun omega he => he.2.2 L |>.1)
      have hTL' := hDom
        (fun omega => compactGradientLipschitzObservable K
          (positiveAnchoredInfraredTruncation omega L)) hTL hTL0
        (hEnv.mono fun omega he => he.2.2 L |>.2)
      exact ⟨hTC'.1, hTC'.2, hTL'.1, hTL'.2⟩


end SubdiffusiveProcess
