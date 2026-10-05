module

public import SubdiffusiveProcess.Probability.NativeLayerOrlicz
public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.infrared_characterization_local_lipschitz_majorant
public import SubdiffusiveProcess.Paper.infrared_admissible_lipschitz_majorant
public import SubdiffusiveProcess.Paper.finite_negative_layer_log_lipschitz_majorant
public import SubdiffusiveProcess.Paper.finite_cutoff_log_abs_majorant
public import SubdiffusiveProcess.Main.InfraredAdmissible


@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_lem_extremes_additive_lip_scale (d Q0 N j : ℕ) (hj : j ≤ N) :
    5 * (1 + Real.log (2 *
        ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).card : ℝ))) ≤
      (5 * (1 + Real.log 2 + 3 * (d : ℝ) * Real.log 3)) * (N : ℝ) + (5 * (1 + Real.log 2 + (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3)) := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcard := aux_finite_cutoff_log_abs_majorant_card_log d ((j : ℤ) + (Q0 : ℤ))
  have htoNat : (((j : ℤ) + (Q0 : ℤ) + 1).toNat : ℝ) = (j : ℝ) + (Q0 : ℝ) + 1 := by
    have : ((j : ℤ) + (Q0 : ℤ) + 1).toNat = j + Q0 + 1 := by omega
    rw [this]; push_cast; ring
  rw [htoNat] at hcard
  have hjN : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hQ0 : (0 : ℝ) ≤ (Q0 : ℝ) := Nat.cast_nonneg Q0
  have hstep := mul_le_mul_of_nonneg_left hjN
    (mul_nonneg hd0 hlog3.le)
  have hextra := mul_nonneg hN0 (show 0 ≤ 1 + Real.log 2 +
    2 * (d : ℝ) * Real.log 3 by positivity)
  nlinarith [hcard]

theorem aux_lem_extremes_additive_osc_integral {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N Q0 : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    Integrable (fun w : NativeBilateralPotentialSample d => Real.exp (lam *
        ∑ j ∈ Finset.range (N + 1), ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ))))))))
      (Measure.infinitePi (fun _ : ℤ =>
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)) ∧
      (∫ w, Real.exp (lam *
        ∑ j ∈ Finset.range (N + 1), ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ)))))))
        ∂(Measure.infinitePi (fun _ : ℤ =>
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure))) ≤
        2 * Real.exp (((3 / 2) * (M.delta * Real.sqrt
          ((5 * (1 + Real.log 2 + 3 * (d : ℝ) * Real.log 3)) * (N : ℝ) + (5 * (1 + Real.log 2 + (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3))))) ^ 2 * lam ^ 2 / 4) := by
  classical
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  set E0 : ℝ := 5 * (1 + Real.log 2 + (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3) with hE0
  have hE0pos : 0 < E0 := by
    rw [hE0]
    have : (0 : ℝ) ≤ (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3 := by positivity
    linarith
  set Ed : ℝ := 5 * (1 + Real.log 2 + 3 * (d : ℝ) * Real.log 3) with hEd
  have hEdnn : 0 ≤ Ed := by rw [hEd]; positivity
  set A : ℝ := M.delta * Real.sqrt (Ed * (N : ℝ) + E0) with hA
  have hApos : 0 < A := by
    rw [hA]
    have : 0 < Real.sqrt (Ed * (N : ℝ) + E0) := Real.sqrt_pos.mpr (by positivity)
    positivity
  set W : ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun j g =>
    (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
      (fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g)) with hW
  have hWmeas : ∀ j, Measurable (W j) := by
    intro j
    have h0 : Measurable ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
        (fun a g => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g))) :=
      Finset.measurable_sup' _ (fun a _ =>
        _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable.comp
          (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate _))
    have h1 : ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
        (fun a g => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g))) = W j := by
      funext g
      exact Finset.sup'_apply _ _ g
    rwa [h1] at h0
  have hWnn : ∀ j g, 0 ≤ W j g := by
    intro j g
    obtain ⟨a, ha⟩ := SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ))
    exact le_trans (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _)
      (Finset.le_sup' (f := fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g)) ha)
  set f : ℕ → NativeBilateralPotentialSample d → ℝ := fun j w => W j (w (-(j : ℤ))) with hf
  have hfmeas : ∀ j, Measurable (f j) := fun j => (hWmeas j).comp (measurable_pi_apply _)
  have hfnn : ∀ j w, 0 ≤ f j w := fun j w => hWnn j _
  set wt : ℕ → ℝ := fun j => (3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ)) with hwt
  have hwtpos : ∀ j, 0 < wt j := by intro j; rw [hwt]; positivity
  have hOG : ∀ j ∈ Finset.range (N + 1),
      SubdiffusiveProcess.OGammaLE (Measure.infinitePi (fun _ : ℤ =>
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)) 2 A (f j) := by
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hbase := aux_finite_cutoff_log_abs_majorant_lip_ogamma M ((j : ℤ) + (Q0 : ℤ))
    have hmap : Measure.map
        (fun w : NativeBilateralPotentialSample d => w (-(j : ℤ)))
        (Measure.infinitePi (fun _ : ℤ =>
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)) =
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure :=
      Measure.infinitePi_map_eval _ (-(j : ℤ))
    have htrans := aux_finite_cutoff_log_abs_majorant_ogamma_map
      (T := fun w : NativeBilateralPotentialSample d => w (-(j : ℤ)))
      (measurable_pi_apply _) hmap (hWmeas j) hbase
    refine SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_mono_scale ?_ ?_ (by norm_num)
      (hfmeas j).aemeasurable htrans
    · have hcard : (1 : ℝ) ≤ ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d
          ((j : ℤ) + (Q0 : ℤ))).card : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ))))
      have hlog : 0 ≤ Real.log (2 * ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d
          ((j : ℤ) + (Q0 : ℤ))).card : ℝ)) := Real.log_nonneg (by linarith)
      have : 0 < Real.sqrt (5 * (1 + Real.log (2 * ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d
          ((j : ℤ) + (Q0 : ℤ))).card : ℝ)))) := Real.sqrt_pos.mpr (by linarith)
      positivity
    · rw [hA]
      refine mul_le_mul_of_nonneg_left ?_ hdelta.le
      exact Real.sqrt_le_sqrt
        (aux_lem_extremes_additive_lip_scale d Q0 N j hjN)
  have hAtot : (∑ j ∈ Finset.range (N + 1), wt j) * A ≤ (3 / 2) * A := by
    have hsum := aux_finite_cutoff_log_abs_majorant_weight_sum N
    exact mul_le_mul_of_nonneg_right hsum hApos.le
  have horl := aux_finite_cutoff_log_abs_majorant_weighted_sum_orlicz
    (Measure.infinitePi (fun _ : ℤ =>
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)) N f A hApos wt hwtpos
    hfmeas hfnn hOG ((3 / 2) * A) hAtot
  have hXmeas : Measurable (fun w : NativeBilateralPotentialSample d =>
      ∑ j ∈ Finset.range (N + 1), wt j * f j w) :=
    Finset.measurable_sum _ (fun j _ => measurable_const.mul (hfmeas j))
  have hXnn : ∀ w, 0 ≤ ∑ j ∈ Finset.range (N + 1), wt j * f j w := by
    intro w
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hwtpos j).le (hfnn j w))
  exact SubdiffusiveProcess.orlicz_exp_linear_integrable_integral_le _ _ ((3 / 2) * A) lam
    hXmeas hXnn (by positivity) hlam horl

theorem aux_lem_extremes_additive_moment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K : Compacts (SpatialCoordinates d)) (Bnd : ℝ)
    (hKnorm : ∀ x : K, ‖(x : SpatialCoordinates d)‖ ≤ Bnd)
    (Q0 Q1 : ℕ) (hQ0 : Bnd ≤ (3 : ℝ) ^ Q0 / 4)
    (Vr : C(SpatialCoordinates d, ℝ) → ℝ) (_hVr0 : ∀ f, 0 ≤ Vr f)
    (hVrle : ∀ (f : C(SpatialCoordinates d, ℝ)) (L : ℝ), 0 ≤ L →
      (∀ x y : K, x ≠ y →
        |f (x : SpatialCoordinates d) - f (y : SpatialCoordinates d)| /
          dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤ L) → Vr f ≤ L)
    (CH : ℝ) (hCH0 : 0 ≤ CH)
    (hCHb : ∀ lambda : ℝ, 0 ≤ lambda →
      Integrable (fun om => Real.exp
          (lambda * ‖(H om).restrict (K : Set (SpatialCoordinates d))‖))
        (chaosSampleLaw M).toMeasure ∧
      (∫ om, Real.exp (lambda * ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
        ∂(chaosSampleLaw M).toMeasure) ≤ 2 * Real.exp (CH * lambda ^ 2 * M.delta ^ 2))
    (Cval E0 Ed u0 u1 t : ℝ)
    (hCvaldef : Cval = 6 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹))
    (hE0def : E0 = 5 * (1 + Real.log 2 + (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3))
    (hEddef : Ed = 5 * (1 + Real.log 2 + 3 * (d : ℝ) * Real.log 3))
    (hu1nn : 0 ≤ u1)
    (hu0a : Real.log 2 + CH / 4 ≤ u0)
    (hu0b : Real.log 2 + (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 + Cval ^ 2 / 4 ≤ u0)
    (hu1b : (d : ℝ) * Real.log 3 + Cval ^ 2 / 4 ≤ u1)
    (hu0c : Real.log 2 + (9 / 16) * E0 ≤ u0)
    (hu1c : (9 / 16) * Ed ≤ u1)
    (ht : t = 1 / (4 * M.delta))
    (Ah : BilateralField d → ℝ)
    (hAhdef : ∀ om, Ah om = ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
    (hAhmeas : Measurable Ah)
    (Amax : ℕ → BilateralField d → ℝ)
    (hAmaxdef : ∀ N om, Amax N om =
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
        (fun q => |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j))
          ((3 : ℝ) ^ (-(N : ℤ)) • SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q)|))
    (hAmaxmeas : ∀ N, Measurable (Amax N))
    (Aosc : ℕ → BilateralField d → ℝ)
    (hAoscdef : ∀ N om, Aosc N om =
      (3 : ℝ) ^ (-(N : ℤ)) * ∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j))))
    (hAoscmeas : ∀ N, Measurable (Aosc N))
    (N : ℕ) :
    Integrable (fun om => Real.exp (t *
        (2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
          Ah om + Amax N om + Aosc N om))) (chaosSampleLaw M).toMeasure ∧
      (∫ om, Real.exp (t *
        (2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
          Ah om + Amax N om + Aosc N om)) ∂(chaosSampleLaw M).toMeasure) ≤
        Real.exp (t * (2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
          4 * M.delta * (Real.log 3 + u0 + u1 * (N : ℝ)))) := by
  classical
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdhalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hE0pos : 0 < E0 := by
    rw [hE0def]
    have h : (0 : ℝ) ≤ (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3 := by positivity
    linarith
  have hEdnn : 0 ≤ Ed := by rw [hEddef]; positivity
  have h4dt : 4 * M.delta * t = 1 := by rw [ht]; field_simp
  have htpos : 0 < t := by rw [ht]; positivity
  have ht2 : (0 : ℝ) ≤ 2 * t := by linarith
  have ht4 : (0 : ℝ) ≤ 4 * t := by linarith
  set mu0 : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) with hmu0
  set forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩ with hforget
  set pz : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j)) with hpz
  have hpzmeas : Measurable pz := by
    apply Measurable.of_eval
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hpzmap : Measure.map pz mu0 = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, hmu0, hpz, hforget, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  have hpzapp : ∀ (w : NativeBilateralPotentialSample d) (j : ℕ) (y : SpatialCoordinates d),
      (pz w) (-(Int.ofNat j)) y = (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • y) := by
    intro w j y
    show (layerScaling d (-(Int.ofNat j)) (forget (w (-(Int.ofNat j))))) y = _
    simp [layerScaling, ContinuousMap.compRightContinuousMap, hforget]
    rfl
  set gpt : ℕ → (Fin d → ℤ) → SpatialCoordinates d := fun N q =>
    (3 : ℝ) ^ (-(N : ℤ)) • SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q with hgpt
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hu1N : 0 ≤ u1 * (N : ℝ) := mul_nonneg hu1nn hNnn
  have hCvalsq : (0 : ℝ) ≤ Cval ^ 2 / 4 := by positivity
  have hE0nn : (0 : ℝ) ≤ (9 / 16) * E0 := by linarith
  have hdQ1 : (0 : ℝ) ≤ (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 := by positivity
  have hCHK : 0 ≤ CH := hCH0
  -- the infrared part
  obtain ⟨hIHint0, hIHbd0⟩ := hCHb (2 * t) ht2
  obtain ⟨hHiff, hHeq⟩ := aux_finite_cutoff_log_abs_majorant_transfer hpzmeas hpzmap
    (fun om => Real.exp ((2 * t) * Ah om)) ((measurable_const.mul hAhmeas).exp)
  have hAhfun : (fun om : BilateralField d => Real.exp ((2 * t) * Ah om)) =
      (fun om : BilateralField d => Real.exp ((2 * t) *
        ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)) := by
    funext om
    rw [hAhdef]
  have hA0 : Integrable (fun w => Real.exp ((2 * t) * Ah (pz w))) mu0 := by
    refine hHiff.mpr ?_
    rw [hAhfun]
    exact hIHint0
  have hA1 : (∫ w, Real.exp ((2 * t) * Ah (pz w)) ∂mu0) ≤
      Real.exp (u0 + u1 * (N : ℝ)) := by
    rw [← hHeq, hAhfun]
    refine le_trans hIHbd0 ?_
    have hcalc : CH * (2 * t) ^ 2 * M.delta ^ 2 = CH / 4 := by
      rw [ht]; field_simp; ring
    rw [hcalc, show (2 : ℝ) * Real.exp (CH / 4) =
      Real.exp (Real.log 2 + CH / 4) by
        rw [Real.exp_add, Real.exp_log (by norm_num)]]
    apply Real.exp_le_exp.mpr
    linarith
  -- the grid maximum
  have hAmaxcomp : ∀ w : NativeBilateralPotentialSample d,
      Amax N (pz w) =
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
          (fun q => |∑ j ∈ Finset.range (N + 1),
            (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • gpt N q)|) := by
    intro w
    have hfun : (fun q : Fin d → ℤ => |∑ j ∈ Finset.range (N + 1),
          (pz w) (-(Int.ofNat j)) (gpt N q)|) =
        (fun q : Fin d → ℤ => |∑ j ∈ Finset.range (N + 1),
          (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • gpt N q)|) := by
      funext q
      congr 1
      exact Finset.sum_congr rfl (fun j _ => hpzapp w j (gpt N q))
    rw [hAmaxdef]
    rw [hfun]
  obtain ⟨hIMint0, hIMbd0⟩ := aux_finite_cutoff_log_abs_majorant_max_integral M N
    ((N : ℤ) + (Q1 : ℤ)) (fun q => gpt N q) (4 * t) ht4
  rw [← hCvaldef] at hIMbd0
  have hMrw : (fun w : NativeBilateralPotentialSample d =>
      Real.exp ((4 * t) * Amax N (pz w))) =
      (fun w : NativeBilateralPotentialSample d => Real.exp ((4 * t) *
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
          (fun q => |∑ j ∈ Finset.range (N + 1),
            (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • gpt N q)|))) := by
    funext w
    rw [hAmaxcomp w]
  have hM0 : Integrable (fun w => Real.exp ((4 * t) * Amax N (pz w))) mu0 := by
    rw [hMrw]; exact hIMint0
  have hM1 : (∫ w, Real.exp ((4 * t) * Amax N (pz w)) ∂mu0) ≤
      Real.exp (u0 + u1 * (N : ℝ)) := by
    rw [hMrw]
    refine le_trans hIMbd0 ?_
    have hsq : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    have htt : 4 * t = 1 / M.delta := by rw [ht]; field_simp
    have hexp : ((Cval * (M.delta * Real.sqrt ((N : ℝ) + 1))) ^ 2) * (4 * t) ^ 2 / 4 =
        Cval ^ 2 * ((N : ℝ) + 1) / 4 :=
      aux_finite_cutoff_log_abs_majorant_sq_scale Cval M.delta t
        (Real.sqrt ((N : ℝ) + 1)) ((N : ℝ) + 1) (ne_of_gt hdelta) htt hsq
    rw [hexp]
    have hcard1 : (1 : ℝ) ≤ ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d
        ((N : ℤ) + (Q1 : ℤ))).card : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ))))
    have hprod : (((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d
          ((N : ℤ) + (Q1 : ℤ))).card : ℝ)) *
        (2 * Real.exp (Cval ^ 2 * ((N : ℝ) + 1) / 4)) =
        Real.exp (Real.log (2 * ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d
          ((N : ℤ) + (Q1 : ℤ))).card : ℝ)) + Cval ^ 2 * ((N : ℝ) + 1) / 4) := by
      rw [Real.exp_add, Real.exp_log (by linarith)]
      ring
    rw [hprod]
    apply Real.exp_le_exp.mpr
    have hlogcard := aux_finite_cutoff_log_abs_majorant_card_log d ((N : ℤ) + (Q1 : ℤ))
    have htoNat : ((((N : ℤ) + (Q1 : ℤ)) + 1).toNat : ℝ) = (N : ℝ) + (Q1 : ℝ) + 1 := by
      have h : (((N : ℤ) + (Q1 : ℤ)) + 1).toNat = N + Q1 + 1 := by omega
      rw [h]; push_cast; ring
    rw [htoNat] at hlogcard
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hexp2 : (d : ℝ) * ((N : ℝ) + (Q1 : ℝ) + 1 + 1) * Real.log 3
        = (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 + ((d : ℝ) * Real.log 3) * (N : ℝ) := by
      ring
    rw [hexp2] at hlogcard
    have hexpand : Cval ^ 2 * ((N : ℝ) + 1) / 4 =
        Cval ^ 2 / 4 + (Cval ^ 2 / 4) * (N : ℝ) := by ring
    have hprod : ((d : ℝ) * Real.log 3 + Cval ^ 2 / 4) * (N : ℝ) ≤ u1 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hu1b hNnn
    have hprod2 : ((d : ℝ) * Real.log 3 + Cval ^ 2 / 4) * (N : ℝ) =
        ((d : ℝ) * Real.log 3) * (N : ℝ) + (Cval ^ 2 / 4) * (N : ℝ) := by ring
    rw [hprod2] at hprod
    rw [hexpand]
    linarith
  -- the oscillation
  have hOle : ∀ w : NativeBilateralPotentialSample d,
      Aosc N (pz w) ≤ ∑ j ∈ Finset.range (N + 1),
        ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ)))))) := by
    intro w
    have hterm : ∀ j ∈ Finset.range (N + 1),
        Vr ((pz w) (-(Int.ofNat j))) ≤ (3 : ℝ) ^ (j : ℤ) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ)))))) := by
      intro j _
      have hc : (0 : ℝ) ≤ (3 : ℝ) ^ (j : ℤ) := by positivity
      have hq : (3 : ℝ) ^ (j : ℤ) * Bnd ≤ (3 : ℝ) ^ (j + Q0) / 4 := by
        have h1 : (3 : ℝ) ^ (j : ℤ) * Bnd ≤ (3 : ℝ) ^ (j : ℤ) * ((3 : ℝ) ^ Q0 / 4) :=
          mul_le_mul_of_nonneg_left hQ0 hc
        have h2 : (3 : ℝ) ^ (j : ℤ) * ((3 : ℝ) ^ Q0 / 4) = (3 : ℝ) ^ (j + Q0) / 4 := by
          rw [pow_add, zpow_natCast]
          ring
        linarith
      have hratio := aux_finite_cutoff_log_abs_majorant_ratio_bound K Bnd hKnorm
        ((3 : ℝ) ^ (j : ℤ)) hc (j + Q0) hq (w (-(j : ℤ)))
      have hidx : ((j + Q0 : ℕ) : ℤ) = (j : ℤ) + (Q0 : ℤ) := by push_cast; ring
      rw [hidx] at hratio
      refine hVrle ((pz w) (-(Int.ofNat j))) _ ?_ ?_
      · refine mul_nonneg hc ?_
        obtain ⟨a, ha⟩ :=
          SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ))
        exact le_trans (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _)
          (Finset.le_sup' (f := fun a =>
            _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ))))) ha)
      · intro x y hxy
        have hval : ∀ u : SpatialCoordinates d,
            (pz w) (-(Int.ofNat j)) u = (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • u) :=
          fun u => hpzapp w j u
        rw [hval, hval]
        exact hratio x y hxy
    have hsum : (∑ j ∈ Finset.range (N + 1), Vr ((pz w) (-(Int.ofNat j)))) ≤
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (j : ℤ) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ)))))) :=
      Finset.sum_le_sum hterm
    rw [hAoscdef]
    have hstep : (3 : ℝ) ^ (-(N : ℤ)) *
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (j : ℤ) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ)))))) =
        ∑ j ∈ Finset.range (N + 1), ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ)))))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← mul_assoc, mul_comm ((3 : ℝ) ^ (-(N : ℤ)))]
    rw [← hstep]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  obtain ⟨hIOint0, hIObd0⟩ := aux_lem_extremes_additive_osc_integral M N Q0
    (4 * t) ht4
  rw [← hE0def, ← hEddef] at hIObd0
  have hOptw : ∀ w : NativeBilateralPotentialSample d,
      Real.exp ((4 * t) * Aosc N (pz w)) ≤ Real.exp ((4 * t) *
        ∑ j ∈ Finset.range (N + 1), ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ))))))) := by
    intro w
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hOle w) ht4)
  have hOmeas : Measurable (fun w : NativeBilateralPotentialSample d =>
      Real.exp ((4 * t) * Aosc N (pz w))) :=
    (measurable_const.mul ((hAoscmeas N).comp hpzmeas)).exp
  have hO0 : Integrable (fun w => Real.exp ((4 * t) * Aosc N (pz w))) mu0 := by
    refine hIOint0.mono' hOmeas.aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hOptw w
  have hO1 : (∫ w, Real.exp ((4 * t) * Aosc N (pz w)) ∂mu0) ≤
      Real.exp (u0 + u1 * (N : ℝ)) := by
    refine le_trans (integral_mono hO0 hIOint0 hOptw) ?_
    refine le_trans hIObd0 ?_
    have hsq : Real.sqrt (Ed * (N : ℝ) + E0) ^ 2 = Ed * (N : ℝ) + E0 :=
      Real.sq_sqrt (by positivity)
    have htt : 4 * t = 1 / M.delta := by rw [ht]; field_simp
    have hexp0 := aux_finite_cutoff_log_abs_majorant_sq_scale (3 / 2) M.delta t
        (Real.sqrt (Ed * (N : ℝ) + E0)) (Ed * (N : ℝ) + E0) (ne_of_gt hdelta) htt hsq
    have hexp : ((3 / 2) * (M.delta * Real.sqrt (Ed * (N : ℝ) + E0))) ^ 2 *
        (4 * t) ^ 2 / 4 = (9 / 16) * (Ed * (N : ℝ) + E0) := by
      rw [hexp0]; ring
    rw [hexp, show (2 : ℝ) * Real.exp ((9 / 16) * (Ed * (N : ℝ) + E0)) =
      Real.exp (Real.log 2 + (9 / 16) * (Ed * (N : ℝ) + E0)) by
        rw [Real.exp_add, Real.exp_log (by norm_num)]]
    apply Real.exp_le_exp.mpr
    have hexpand : (9 / 16) * (Ed * (N : ℝ) + E0) =
        (9 / 16) * E0 + ((9 / 16) * Ed) * (N : ℝ) := by ring
    have hprod : ((9 / 16) * Ed) * (N : ℝ) ≤ u1 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hu1c hNnn
    rw [hexpand]
    linarith
  -- assemble
  obtain ⟨hint3, hbd3⟩ := aux_finite_cutoff_log_abs_majorant_amgm3 mu0 t
    (fun w => Ah (pz w)) (fun w => Amax N (pz w)) (fun w => Aosc N (pz w))
    (hAhmeas.comp hpzmeas) ((hAmaxmeas N).comp hpzmeas) ((hAoscmeas N).comp hpzmeas)
    hA0 hM0 hO0 _ _ _ hA1 hM1 hO1
  have hVVm : Measurable (fun om : BilateralField d =>
      2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P + Ah om + Amax N om + Aosc N om) :=
    ((measurable_const.add hAhmeas).add (hAmaxmeas N)).add (hAoscmeas N)
  obtain ⟨hViff, hVeq⟩ := aux_finite_cutoff_log_abs_majorant_transfer hpzmeas hpzmap
    (fun om => Real.exp (t * (2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
      Ah om + Amax N om + Aosc N om))) ((measurable_const.mul hVVm).exp)
  have hVVsplit : (fun w : NativeBilateralPotentialSample d =>
      Real.exp (t * (2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
        Ah (pz w) + Amax N (pz w) + Aosc N (pz w)))) =
      (fun w : NativeBilateralPotentialSample d =>
        Real.exp (t * (2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
          Real.exp (t * (Ah (pz w) + Amax N (pz w) + Aosc N (pz w)))) := by
    funext w
    rw [← Real.exp_add]
    congr 1
    ring
  have hfinal : Real.exp (t * (2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
      (Real.exp (u0 + u1 * (N : ℝ)) + Real.exp (u0 + u1 * (N : ℝ)) +
        Real.exp (u0 + u1 * (N : ℝ))) =
      Real.exp (t * (2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
        4 * M.delta * (Real.log 3 + u0 + u1 * (N : ℝ)))) := by
    have harg : t * (2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
          4 * M.delta * (Real.log 3 + u0 + u1 * (N : ℝ))) =
        t * (2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
          (Real.log 3 + u0 + u1 * (N : ℝ)) := by
      have hx : t * (4 * M.delta * (Real.log 3 + u0 + u1 * (N : ℝ))) =
          (4 * M.delta * t) * (Real.log 3 + u0 + u1 * (N : ℝ)) := by ring
      rw [mul_add, hx, h4dt, one_mul]
    have e1 : Real.exp (t * (2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
          (Real.log 3 + u0 + u1 * (N : ℝ))) =
        Real.exp (t * (2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
          Real.exp (Real.log 3 + u0 + u1 * (N : ℝ)) := Real.exp_add _ _
    have e2 : Real.exp (Real.log 3 + u0 + u1 * (N : ℝ)) =
        3 * Real.exp (u0 + u1 * (N : ℝ)) := by
      rw [show Real.log 3 + u0 + u1 * (N : ℝ) = Real.log 3 + (u0 + u1 * (N : ℝ)) from by ring,
        Real.exp_add (Real.log 3) (u0 + u1 * (N : ℝ)), Real.exp_log (by norm_num)]
    rw [harg, e1, e2]
    ring
  constructor
  · refine hViff.mp ?_
    rw [hVVsplit]
    exact hint3.const_mul _
  · rw [hVeq, hVVsplit, integral_const_mul, ← hfinal]
    exact mul_le_mul_of_nonneg_left hbd3 (Real.exp_pos _).le

theorem aux_lem_extremes_fine_fixed_threshold :
  ∀ (d : ℕ), 2 ≤ d →
  ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
  ∀ (p : ℝ), 1 ≤ p →
  ∃ C : ℝ, 0 < C ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
      M.delta ≤ 1 / p →
      ∃ U : ℕ → BilateralField d → ℝ,
        (∀ N om, 0 ≤ U N om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ N x y,
            x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
            y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
            |(∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
                ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) y| ≤
              U N om * (3 : ℝ) ^ N * dist x y) ∧
        (∀ N, MemLp (U N) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure) ∧
        (∀ N, eLpNorm (U N) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C * M.delta * Real.sqrt (1 + (N : ℝ)))) := by
  intro d hd _ _ z r hr p hp
  obtain ⟨C₀, hC₀, hC₀mom⟩ := layer_regularity_moments hd
  obtain ⟨Q₀, hQ₀⟩ :=
    pow_unbounded_of_one_lt (4 * (‖z‖ + r / 2))
      (by norm_num : (1 : ℝ) < 3)
  let C₁ : ℝ := C₀ + 1 + 6 * (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
        Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * Real.sqrt (Q₀ + 1)
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    have hgamma := Homogenization.IndependentSums.gammaMomentConst_pos
      (show (0 : ℝ) < 2 by norm_num)
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK := SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst_pos
    positivity
  let Dglobal : ℝ :=
    Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
      Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)
  have hCdom : 2 * Dglobal * Real.sqrt (Q₀ + 1) ≤ C₁ := by
    dsimp [C₁, Dglobal]
    have hD : 0 ≤
        Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Homogenization.IndependentSums.gammaMomentConst_pos
              (show (0 : ℝ) < 2 by norm_num)).le (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by
          have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
          linarith) _)
    have hq : 0 ≤ Real.sqrt (Q₀ + 1) := Real.sqrt_nonneg _
    have hprod : 0 ≤ (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * Real.sqrt (Q₀ + 1) :=
      mul_nonneg hD hq
    nlinarith [hC₀, hprod]
  refine ⟨C₁, hC₁, ?_⟩
  intro M hM
  let K : Compacts (SpatialCoordinates d) := closedCube z r hr
  obtain ⟨V, hVmeas, hV0, hVdom, hVle, hPmeas⟩ :=
    aux_finite_negative_layer_log_lipschitz_majorant_continuous_ratio K
  let F : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
    fun N om x => ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x
  let U : ℕ → BilateralField d → ℝ := fun N om =>
    (3 : ℝ) ^ (-(N : ℤ)) *
      ∑ j ∈ Finset.range (N + 1), V (om (-(Int.ofNat j)))
  let μ₀ : Measure (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
  let forget₀ : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let π₀ : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) → BilateralField d :=
    fun omega j => layerScaling d j (forget₀ (omega j))
  have hπ₀meas : Measurable π₀ := by
    apply Measurable.of_eval
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget₀.continuous.measurable.comp (measurable_pi_apply j))
  have hπ₀measure : Measure.map π₀ μ₀ = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, μ₀, π₀, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  let H : ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun q g =>
    (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).sup' (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ))
      (fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable (_root_.SubdiffusiveProcess.Model.PotentialField.translate (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g))
  have hHmeas : ∀ q, Measurable (H q) := by
    intro q
    dsimp [H]
    convert (Finset.measurable_sup' (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ))
      (fun a _ => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable.comp (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a)))) using 1
    funext g
    simp only [Finset.sup'_apply, Function.comp_apply]
  have hHnonneg : ∀ q g, 0 ≤ H q g := by
    intro q g
    obtain ⟨a, ha⟩ :=
      SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ)
    exact (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _).trans
      (Finset.le_sup' (f := fun a =>
        _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable (_root_.SubdiffusiveProcess.Model.PotentialField.translate (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g)) ha)
  let Wj₀ : ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun j g =>
    H (Q₀ + j + 1) g
  have hscaled₀ : ∀ omega : ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d,
      ∀ j, ∀ x y : K, x ≠ y →
        |(π₀ omega (-(Int.ofNat j))) x.1 -
            (π₀ omega (-(Int.ofNat j))) y.1| / dist x.1 y.1 ≤
          (3 : ℝ) ^ j * (Wj₀ j (omega (-(Int.ofNat j))) : ℝ) := by
    intro omega j x y hxy
    let Rj : ℝ := (3 : ℝ) ^ j * (‖z‖ + r / 2)
    let qj : ℕ := Q₀ + j + 1
    have hRj : Rj ≤ (3 : ℝ) ^ qj / 4 := by
      dsimp [Rj, qj]
      have hpow : (3 : ℝ) ^ (Q₀ + j + 1) =
          (3 : ℝ) ^ Q₀ * (3 : ℝ) ^ j * 3 := by
        rw [pow_add, pow_add]
        ring
      rw [hpow]
      have h3j : 0 < (3 : ℝ) ^ j := by positivity
      have hbase : ‖z‖ + r / 2 < (3 : ℝ) ^ Q₀ / 4 := by
        nlinarith [hQ₀]
      calc
        (3 : ℝ) ^ j * (‖z‖ + r / 2) ≤
            (3 : ℝ) ^ j * ((3 : ℝ) ^ Q₀ / 4) :=
          (mul_lt_mul_of_pos_left hbase h3j).le
        _ ≤ (3 : ℝ) ^ Q₀ * (3 : ℝ) ^ j * 3 / 4 := by
          calc
            (3 : ℝ) ^ j * ((3 : ℝ) ^ Q₀ / 4) =
                (3 : ℝ) ^ Q₀ * (3 : ℝ) ^ j / 4 := by ring
            _ ≤ (3 : ℝ) ^ Q₀ * (3 : ℝ) ^ j * 3 / 4 := by
              have hnonneg : 0 ≤ (3 : ℝ) ^ Q₀ * (3 : ℝ) ^ j := by positivity
              nlinarith
    have hroot :=
      aux_finite_negative_layer_log_lipschitz_majorant_grid_cover
        (q := qj) hRj (omega (-(Int.ofNat j)))
    have hs : 0 ≤ (3 : ℝ) ^ j := by positivity
    have hfield (w : K) :
        (π₀ omega (-(Int.ofNat j))) w.1 =
          (omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • w.1) := by
      simp [π₀, layerScaling, ContinuousMap.compRightContinuousMap_apply,
        zpow_natCast]
      rfl
    have hxnorm : ‖x.1‖ ≤ ‖z‖ + r / 2 := by
      have hxprop := x.property
      change dist x.1 z ≤ r / 2 at hxprop
      calc
        ‖x.1‖ = ‖(x.1 - z) + z‖ := by congr 1 ; abel
        _ ≤ ‖x.1 - z‖ + ‖z‖ := norm_add_le _ _
        _ = dist x.1 z + ‖z‖ := by rw [dist_eq_norm]
        _ ≤ r / 2 + ‖z‖ := add_le_add hxprop le_rfl
        _ = ‖z‖ + r / 2 := by ring
    have hynorm : ‖y.1‖ ≤ ‖z‖ + r / 2 := by
      have hyprop := y.property
      change dist y.1 z ≤ r / 2 at hyprop
      calc
        ‖y.1‖ = ‖(y.1 - z) + z‖ := by congr 1 ; abel
        _ ≤ ‖y.1 - z‖ + ‖z‖ := norm_add_le _ _
        _ = dist y.1 z + ‖z‖ := by rw [dist_eq_norm]
        _ ≤ r / 2 + ‖z‖ := add_le_add hyprop le_rfl
        _ = ‖z‖ + r / 2 := by ring
    have hxball : (3 : ℝ) ^ j • x.1 ∈
        Metric.closedBall (0 : SpatialCoordinates d) Rj := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hs]
      exact (mul_le_mul_of_nonneg_left hxnorm hs).trans_eq rfl
    have hyball : (3 : ℝ) ^ j • y.1 ∈
        Metric.closedBall (0 : SpatialCoordinates d) Rj := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hs]
      exact (mul_le_mul_of_nonneg_left hynorm hs).trans_eq rfl
    have hdist := hroot.dist_le_mul ((3 : ℝ) ^ j • x.1) hxball ((3 : ℝ) ^ j • y.1) hyball
    have hsup_eq :
        (↑((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (qj : ℤ)).sup' (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (qj : ℤ))
          (fun a =>
            (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable (_root_.SubdiffusiveProcess.Model.PotentialField.translate (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a)
                (omega (-(Int.ofNat j)))),
              _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0)) : ℝ≥0) : ℝ) =
          H qj (omega (-(Int.ofNat j))) := by
      simpa [H, Function.comp_apply] using!
        (Finset.apply_sup'_eq_sup'_comp (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (qj : ℤ))
          (fun x : ℝ≥0 => (x : ℝ))
          (fun x y : ℝ≥0 => NNReal.coe_max x y))
    rw [hsup_eq] at hdist
    have hdist' :
        |(omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • x.1) -
            (omega (-(Int.ofNat j))) ((3 : ℝ) ^ j • y.1)| ≤
          (Wj₀ j (omega (-(Int.ofNat j))) : ℝ) * ((3 : ℝ) ^ j * dist x.1 y.1) := by
      simpa [Wj₀, H, qj, ← smul_sub, dist_eq_norm, Real.norm_eq_abs,
        norm_smul, abs_of_nonneg hs, mul_assoc, mul_left_comm, mul_comm] using hdist
    rw [hfield x, hfield y]
    apply (div_le_iff₀ (dist_pos.mpr hxy)).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using! hdist'
  have hsourceBound₀ :
      ∀ omega : ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d, ∀ j,
        V (π₀ omega (-(Int.ofNat j))) ≤
          (3 : ℝ) ^ j * (Wj₀ j (omega (-(Int.ofNat j))) : ℝ) := by
    intro omega j
    exact hVle _ _ (mul_nonneg (by positivity) (hHnonneg _ _))
      (hscaled₀ omega j)
  have hUmeas : ∀ N, Measurable (U N) := by
    intro N
    dsimp [U]
    exact measurable_const.mul (Finset.measurable_sum _ fun j _ =>
      hVmeas.comp (measurable_pi_apply _))
  let μz : Measure (_root_.SubdiffusiveProcess.Model.PotentialField d) := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  have hHbig : ∀ q, Homogenization.IndependentSums.IsBigOWith μz (Homogenization.IndependentSums.gammaSigma 2) (H q)
      (((3 * Real.log ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).card : ℝ)) ^
          (2 : ℝ)⁻¹) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
    intro q
    let T : (_root_.SubdiffusiveProcess.Model.PotentialSample d) →
        _root_.SubdiffusiveProcess.Model.PotentialField d := fun omega =>
      SubdiffusiveProcess.CoarseGrainingVocab.unscalePotential 0 (omega 0)
    have hTmeas : Measurable T := by
      exact (SubdiffusiveProcess.CoarseGrainingVocab.measurable_unscalePotential 0).comp (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate 0)
    have hTmap : Measure.map T M.P.toMeasure = μz := by
      simpa [T, μz] using (SubdiffusiveProcess.CoarseGrainingVocab.map_unscalePotential_coordinate_eq_zero M 0)
    have hmap : Measure.map (H q) μz =
        Measure.map (SubdiffusiveProcess.CoarseGrainingVocab.largeCubeShellG2 0 (q : ℤ))
          M.P.toMeasure := by
      calc
        Measure.map (H q) μz = Measure.map (H q)
            (Measure.map T M.P.toMeasure) := by rw [hTmap]
        _ = Measure.map (H q ∘ T) M.P.toMeasure := by
          rw [Measure.map_map (hHmeas q) hTmeas]
        _ = Measure.map (SubdiffusiveProcess.CoarseGrainingVocab.largeCubeShellG2 0 (q : ℤ))
            M.P.toMeasure := by
          congr 1
    exact SubdiffusiveProcess.CoarseGrainingVocab.isBigOWith_of_map_eq (hHmeas q) (SubdiffusiveProcess.CoarseGrainingVocab.measurable_largeCubeShellG2 0 (q : ℤ)) hmap
      (SubdiffusiveProcess.CoarseGrainingVocab.isBigOWith_gammaTwo_largeCubeShellG2
        M 0 (q : ℤ))
  have hApos : ∀ q, 0 <
      ((3 * Real.log ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).card : ℝ)) ^
          (2 : ℝ)⁻¹) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
    intro q
    apply mul_pos
    · apply Real.rpow_pos_of_pos
      apply mul_pos (by norm_num)
      apply Real.log_pos
      have hcard := SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_card_ge_two M
        (q : ℤ)
      exact_mod_cast hcard
    · apply mul_pos
      · apply Real.rpow_pos_of_pos
        have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
        linarith
      · exact M.shellPrefix.delta_pos
  have hHnorm : ∀ q, eLpNorm (H q) (ENNReal.ofReal p) μz ≤
      ENNReal.ofReal (Homogenization.IndependentSums.gammaMomentConst 2 *
        Real.sqrt p * (((3 * Real.log ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).card : ℝ)) ^
            (2 : ℝ)⁻¹) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))) := by
    intro q
    have hHbig' : Homogenization.IndependentSums.IsBigO μz (Homogenization.IndependentSums.gammaSigma 2) (H q)
        (((3 * Real.log ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).card : ℝ)) ^
            (2 : ℝ)⁻¹) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
      change Homogenization.IndependentSums.IsBigOWith μz (Homogenization.IndependentSums.gammaSigma 2)
        (fun g => |H q g|) _
      have habs : (fun g => |H q g|) = H q := by
        funext g
        exact abs_of_nonneg (hHnonneg q g)
      rw [habs]
      exact hHbig q
    exact SubdiffusiveProcess.CoarseGrainingVocab.eLpNorm_le_of_isBigO_gammaTwo
      (hApos q) hp (hHmeas q).aemeasurable hHbig'
  have hHnorm' : ∀ q : ℕ, 0 < (q : ℤ) →
      eLpNorm (H q) (ENNReal.ofReal p) μz ≤
        ENNReal.ofReal ((Homogenization.IndependentSums.gammaMomentConst 2 *
          Real.sqrt p * Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta * Real.sqrt (q : ℝ)) := by
    intro q hq
    apply (hHnorm q).trans
    apply ENNReal.ofReal_le_ofReal
    have hfactor := SubdiffusiveProcess.CoarseGrainingVocab.shellCover_gaussianFactor_le_sqrt M
      (show (0 : ℤ) < (q : ℤ) from hq)
    calc
      Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          (((3 * Real.log ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).card : ℝ)) ^
              (2 : ℝ)⁻¹) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) ≤
          Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
            ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
              Real.sqrt (q : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
        have hfactor' :
            (3 * Real.log ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).card : ℝ)) ^
                (2 : ℝ)⁻¹ ≤
              Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) *
                Real.sqrt (q : ℝ) := by
          simpa using hfactor
        have hleft : 0 ≤
            Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p := by
          exact mul_nonneg (Homogenization.IndependentSums.gammaMomentConst_pos
              (show (0 : ℝ) < 2 by norm_num)).le (Real.sqrt_nonneg _)
        have hright : 0 ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta := by
          exact mul_nonneg (Real.rpow_nonneg (by
            have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
            linarith) _) M.shellPrefix.delta_pos.le
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hfactor' hright) hleft
      _ = (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta * Real.sqrt (q : ℝ) := by
        ring
  have hHmem : ∀ q, MemLp (H q) (ENNReal.ofReal p) μz := by
    intro q
    exact (hHnorm q).trans_lt ENNReal.ofReal_lt_top
  have hHrawmem : ∀ (q : ℕ) (j : ℤ),
      MemLp (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
        H q (omega j)) (ENNReal.ofReal p) μ₀ := by
    intro q j
    simpa [μ₀, Function.comp_def] using
      (hHmem q).comp_measurePreserving
        (measurePreserving_eval_infinitePi
          (fun _ : ℤ => μz) j)
  let T : ℕ → (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) → ℝ := fun j omega =>
    (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j)))
  let G : ℕ → (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) → ℝ := fun N =>
    ∑ j ∈ Finset.range (N + 1), T j
  have htermMem : ∀ N j, j ∈ Finset.range (N + 1) →
      MemLp (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
        (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
        (ENNReal.ofReal p) μ₀ := by
    intro N j hj
    simpa [Wj₀, Pi.smul_apply, smul_eq_mul] using
      ((hHrawmem (Q₀ + j + 1) (-Int.ofNat j)).const_mul ((3 : ℝ) ^ j))
  have hGmem : ∀ N, MemLp (G N) (ENNReal.ofReal p) μ₀ := by
    intro N
    dsimp [G]
    convert memLp_finsetSum' (Finset.range (N + 1))
      (fun j hj => by simpa [T] using htermMem N j hj) using 1
  have hGnonneg : ∀ N omega, 0 ≤ G N omega := by
    intro N omega
    have hs : 0 ≤ ∑ j ∈ Finset.range (N + 1), T j omega :=
      Finset.sum_nonneg (fun j hj => by
        dsimp [T]
        exact mul_nonneg (by positivity) (hHnonneg _ _))
    simpa [G, T] using hs
  have hUbound : ∀ N omega,
      U N (π₀ omega) ≤ (3 : ℝ) ^ (-(N : ℤ)) * G N omega := by
    intro N omega
    dsimp [U, G]
    simp only [Finset.sum_apply, T]
    apply mul_le_mul_of_nonneg_left
    · exact Finset.sum_le_sum (fun j hj => hsourceBound₀ omega j)
    · positivity
  have hgeom : ∀ N,
      (∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ j) ≤ 2 * (3 : ℝ) ^ N := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
        rw [Finset.sum_range_succ, pow_succ]
        have hpw : 0 ≤ (3 : ℝ) ^ N := by positivity
        nlinarith
  have hWnorm : ∀ j,
      eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
        Wj₀ j (omega (-(Int.ofNat j)))) (ENNReal.ofReal p) μ₀ ≤
      ENNReal.ofReal ((Homogenization.IndependentSums.gammaMomentConst 2 *
          Real.sqrt p * Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
        Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ)) := by
    intro j
    calc
      eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
          Wj₀ j (omega (-(Int.ofNat j)))) (ENNReal.ofReal p) μ₀ =
          eLpNorm (H (Q₀ + j + 1)) (ENNReal.ofReal p) μz := by
        simpa [Wj₀, Function.comp_def] using
          (eLpNorm_comp_measurePreserving
            (hHmeas (Q₀ + j + 1)).aestronglyMeasurable
            (measurePreserving_eval_infinitePi
              (fun _ : ℤ => μz) (-Int.ofNat j)))
      _ ≤ _ := hHnorm' (Q₀ + j + 1) (by omega)
  have htermNorm : ∀ N j, j ∈ Finset.range (N + 1) →
      eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
        (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
        (ENNReal.ofReal p) μ₀ ≤
      ENNReal.ofReal ((3 : ℝ) ^ j *
        ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
          Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ))) := by
    intro N j hj
    calc
      eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
          (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
          (ENNReal.ofReal p) μ₀ ≤
          ENNReal.ofReal ((3 : ℝ) ^ j) *
            eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
              Wj₀ j (omega (-(Int.ofNat j)))) (ENNReal.ofReal p) μ₀ := by
        have hsmul := eLpNorm_const_smul_le
          (c := (3 : ℝ) ^ j)
          (f := fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
            Wj₀ j (omega (-(Int.ofNat j))))
          (p := ENNReal.ofReal p) (μ := μ₀)
        have hcoef : ‖(3 : ℝ) ^ j‖ₑ = ENNReal.ofReal ((3 : ℝ) ^ j) := by
          rw [← ofReal_norm]
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [hcoef] at hsmul
        simpa [Pi.smul_apply, smul_eq_mul] using! hsmul
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ j) *
          ENNReal.ofReal ((Homogenization.IndependentSums.gammaMomentConst 2 *
            Real.sqrt p * Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
            Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ)) := by
        gcongr
        exact hWnorm j
      _ = ENNReal.ofReal ((3 : ℝ) ^ j *
          ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
            Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
            Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ))) := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (3 : ℝ) ^ j)]
  have hqSqrt : ∀ N j, j ∈ Finset.range (N + 1) →
      Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ) ≤
        Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) := by
    intro N j hj
    have hjlt : j < N + 1 := Finset.mem_range.mp hj
    have hjN : j ≤ N := by
      exact Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hjlt)
    have hnat : Q₀ + j + 1 ≤ (Q₀ + 1) * (N + 1) := by
      nlinarith [Nat.zero_le (Q₀ * N)]
    have hreal : ((Q₀ + j + 1 : ℕ) : ℝ) ≤
        (((Q₀ + 1) * (N + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    have hsqrt := Real.sqrt_le_sqrt hreal
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.sqrt_mul (by positivity)]
      at hsqrt
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hsqrt
  let B : ℝ := (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
      Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta
  have hB : 0 ≤ B := by
    dsimp [B]
    have hbase : 0 ≤
        Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
          Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Homogenization.IndependentSums.gammaMomentConst_pos
              (show (0 : ℝ) < 2 by norm_num)).le (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by
          have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
          linarith) _)
    exact mul_nonneg hbase M.shellPrefix.delta_pos.le
  have hGnorm : ∀ N,
      eLpNorm (G N) (ENNReal.ofReal p) μ₀ ≤
        ENNReal.ofReal (B * Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) *
          (2 * (3 : ℝ) ^ N)) := by
    intro N
    have hpenn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p :=
      ENNReal.one_le_ofReal.mpr hp
    let A : ℝ := B * Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1)
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg (mul_nonneg hB (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    have hterm : ∀ j, j ∈ Finset.range (N + 1) →
        eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
          (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
          (ENNReal.ofReal p) μ₀ ≤ ENNReal.ofReal ((3 : ℝ) ^ j * A) := by
      intro j hj
      apply (htermNorm N j hj).trans
      apply ENNReal.ofReal_le_ofReal
      dsimp [A, B]
      have hs := hqSqrt N j hj
      have hbase : 0 ≤
          Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
            Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (Homogenization.IndependentSums.gammaMomentConst_pos
                (show (0 : ℝ) < 2 by norm_num)).le (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _))
          (Real.rpow_nonneg (by
            have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
            linarith) _)
      have hcoef : 0 ≤ (3 : ℝ) ^ j * (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
            Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) * M.delta) := by
        exact mul_nonneg (by positivity)
          (mul_nonneg hbase M.shellPrefix.delta_pos.le)
      calc
        (3 : ℝ) ^ j *
            ((Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
              Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
              Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ)) = ((3 : ℝ) ^ j * (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) * M.delta)) *
              Real.sqrt ((Q₀ + j + 1 : ℕ) : ℝ) := by ring
        _ ≤ ((3 : ℝ) ^ j * (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) * M.delta)) *
              (Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1)) :=
          mul_le_mul_of_nonneg_left hs hcoef
        _ = (3 : ℝ) ^ j * A := by ring
    calc
      eLpNorm (G N) (ENNReal.ofReal p) μ₀ ≤
          ∑ j ∈ Finset.range (N + 1),
            eLpNorm (fun omega : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
              (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
              (ENNReal.ofReal p) μ₀ := by
        dsimp [G]
        simpa [T] using (eLpNorm_sum_le
          (f := fun (j : ℕ) (omega : ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) =>
            (3 : ℝ) ^ j * Wj₀ j (omega (-(Int.ofNat j))))
          (s := Finset.range (N + 1))
          hpenn)
      _ ≤ ∑ j ∈ Finset.range (N + 1),
          ENNReal.ofReal ((3 : ℝ) ^ j * A) :=
        Finset.sum_le_sum (fun j hj => hterm j hj)
      _ = ENNReal.ofReal ((∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ j) * A) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · rw [Finset.sum_mul]
        · intro j hj
          exact mul_nonneg (by positivity) hA
      _ ≤ ENNReal.ofReal (B * Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) *
          (2 * (3 : ℝ) ^ N)) := by
        apply ENNReal.ofReal_le_ofReal
        have hg := hgeom N
        have hbound := mul_le_mul_of_nonneg_right hg hA
        dsimp [A] at hbound ⊢
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          hbound
  have hUnonneg : ∀ N omega, 0 ≤ U N (π₀ omega) := by
    intro N omega
    dsimp [U]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun j hj => hV0 _))
  have hpoint : ∀ N, ∀ᵐ omega ∂μ₀,
      ‖(U N ∘ π₀) omega‖ ≤
        (3 : ℝ) ^ (-(N : ℤ)) * ‖G N omega‖ := by
    intro N
    filter_upwards [] with omega
    simpa [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (hUnonneg N omega),
      abs_of_nonneg (hGnonneg N omega)] using hUbound N omega
  have hπ₀pres : MeasurePreserving π₀ μ₀ (chaosSampleLaw M).toMeasure :=
    ⟨hπ₀meas, hπ₀measure⟩
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro N om
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun j hj => hV0 _)
  · have hLayer : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ j x y,
          x ∈ (K : Set (SpatialCoordinates d)) →
          y ∈ (K : Set (SpatialCoordinates d)) →
          |om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) y| ≤
            V (om (-(Int.ofNat j))) * dist x y := by
      let P : Set C(SpatialCoordinates d, ℝ) := {f |
        ∀ x y : K, x ≠ y →
          |f x.1 - f y.1| / dist x.1 y.1 ≤ V f}
      let E : Set (BilateralField d) := {om |
        ∀ j : ℕ, om (-(Int.ofNat j)) ∈ P}
      have hEmeas : MeasurableSet E := by
        rw [show E = ⋂ j : ℕ,
            (fun om : BilateralField d => om (-(Int.ofNat j))) ⁻¹' P by
          ext om
          simp [E]]
        exact MeasurableSet.iInter (fun j =>
          hPmeas.preimage (measurable_pi_apply _))
      have hsource : ∀ omega : ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d,
          π₀ omega ∈ E := by
        intro omega j
        exact hVdom _ _ (hscaled₀ omega j)
      have htarget : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, om ∈ E := by
        rw [← hπ₀measure]
        apply (MeasureTheory.ae_map_iff hπ₀meas.aemeasurable hEmeas).2
        exact Filter.Eventually.of_forall hsource
      filter_upwards [htarget] with om hom
      intro j x y hx hy
      by_cases hxy : x = y
      · subst y
        simp
      ·
        have hp := hom j
        change ∀ a b : K, a ≠ b →
          |(om (-(Int.ofNat j))) a.1 - (om (-(Int.ofNat j))) b.1| /
            dist a.1 b.1 ≤ V (om (-(Int.ofNat j))) at hp
        have hq := hp ⟨x, by simpa [K] using hx⟩ ⟨y, by simpa [K] using hy⟩
          (by intro h; exact hxy (congrArg Subtype.val h))
        exact (div_le_iff₀ (dist_pos.mpr hxy)).mp hq
    filter_upwards [hLayer] with om hom
    intro N x y hx hy
    dsimp [F, U]
    have hsum :
        (∑ j ∈ Finset.range (N + 1),
          |om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) y|) ≤
          ∑ j ∈ Finset.range (N + 1),
            V (om (-(Int.ofNat j))) * dist x y := by
      exact Finset.sum_le_sum (fun j hj => hom j x y hx hy)
    calc
      |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x -
          ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) y| =
          |∑ j ∈ Finset.range (N + 1),
            (om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) y)| := by
        rw [Finset.sum_sub_distrib]
      _ ≤
          ∑ j ∈ Finset.range (N + 1),
            |om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) y| := by
        simpa using (Finset.abs_sum_le_sum_abs (G := ℝ)
          (fun j : ℕ => om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) y)
          (Finset.range (N + 1)))
      _ ≤ ∑ j ∈ Finset.range (N + 1),
          V (om (-(Int.ofNat j))) * dist x y := hsum
      _ = (∑ j ∈ Finset.range (N + 1), V (om (-(Int.ofNat j)))) * dist x y := by
        rw [Finset.sum_mul]
      _ = U N om * (3 : ℝ) ^ N * dist x y := by
        dsimp [U]
        rw [zpow_neg, zpow_natCast]
        field_simp
  · intro N
    have hMemLp : MemLp (U N) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure := by
      rw [← hπ₀measure]
      exact (MeasureTheory.memLp_map_measure_iff
        (μ := μ₀) (f := π₀) (g := U N) (p := ENNReal.ofReal p)
        (hUmeas N).aestronglyMeasurable hπ₀meas.aemeasurable).2
        ((hGmem N).of_le_mul
          ((hUmeas N).comp hπ₀meas).aestronglyMeasurable (hpoint N))
    exact hMemLp
  · intro N
    have hENorm : eLpNorm (U N) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C₁ * M.delta * Real.sqrt (1 + (N : ℝ))) := by
      calc
        eLpNorm (U N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure =
            eLpNorm (U N ∘ π₀) (ENNReal.ofReal p) μ₀ := by
          symm
          exact eLpNorm_comp_measurePreserving
            (hUmeas N).aestronglyMeasurable hπ₀pres
        _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(N : ℤ))) *
              eLpNorm (G N) (ENNReal.ofReal p) μ₀ :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul
            ((hUmeas N).comp hπ₀meas).aestronglyMeasurable (hpoint N) _
        _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(N : ℤ))) *
              ENNReal.ofReal (B * Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) *
                (2 * (3 : ℝ) ^ N)) :=
          mul_le_mul_of_nonneg_left (hGnorm N) (by positivity)
        _ = ENNReal.ofReal (2 * (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
              Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          have hpow : (3 : ℝ) ^ (-(N : ℤ)) * (2 * (3 : ℝ) ^ N) = 2 := by
            rw [zpow_neg, zpow_natCast]
            field_simp
          congr 1
          calc
            (3 : ℝ) ^ (-(N : ℤ)) *
                (B * Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) *
                  (2 * (3 : ℝ) ^ N)) =
                (B * Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1)) * ((3 : ℝ) ^ (-(N : ℤ)) * (2 * (3 : ℝ) ^ N)) := by ring
            _ = 2 * (Homogenization.IndependentSums.gammaMomentConst 2 * Real.sqrt p *
                  Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverLogConst * (d : ℝ)) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * M.delta *
                Real.sqrt (Q₀ + 1) * Real.sqrt (N + 1) := by
              rw [hpow]
              dsimp [B]
              ring
        _ ≤ ENNReal.ofReal (C₁ * M.delta * Real.sqrt (1 + (N : ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          have hδ : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
          have hs : 0 ≤ Real.sqrt (1 + (N : ℝ)) := Real.sqrt_nonneg _
          have hmul := mul_le_mul_of_nonneg_right hCdom
            (mul_nonneg hδ hs)
          calc
            _ = (2 * Dglobal * Real.sqrt (Q₀ + 1)) *
                (M.delta * Real.sqrt (1 + (N : ℝ))) := by
              dsimp [Dglobal]
              ring
            _ ≤ C₁ * (M.delta * Real.sqrt (1 + (N : ℝ))) := hmul
            _ = C₁ * M.delta * Real.sqrt (1 + (N : ℝ)) := by ring
    exact hENorm

theorem aux_lem_extremes_envelope {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (K : Compacts (SpatialCoordinates d)) (Bnd : ℝ)
    (hKnorm : ∀ x : K, ‖(x : SpatialCoordinates d)‖ ≤ Bnd)
    (hKcontains : ∀ u : SpatialCoordinates d, dist u z ≤ r / 2 + 1 →
      u ∈ (K : Set (SpatialCoordinates d)))
    (Q1 : ℕ) (hQ1 : ‖z‖ + r / 2 < (3 : ℝ) ^ Q1 / 2)
    (Vr : C(SpatialCoordinates d, ℝ) → ℝ) (hVr0 : ∀ f, 0 ≤ Vr f)
    (hVrdom : ∀ (f : C(SpatialCoordinates d, ℝ)) (L : ℝ),
      (∀ x y : K, x ≠ y →
        |f (x : SpatialCoordinates d) - f (y : SpatialCoordinates d)| /
          dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤ L) →
      ∀ x y : K, x ≠ y →
        |f (x : SpatialCoordinates d) - f (y : SpatialCoordinates d)| /
          dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤ Vr f)
    (hVrset : MeasurableSet {f : C(SpatialCoordinates d, ℝ) | ∀ x y : K, x ≠ y →
      |f (x : SpatialCoordinates d) - f (y : SpatialCoordinates d)| /
        dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤ Vr f})
    (Ah : BilateralField d → ℝ)
    (hAhdef : ∀ om, Ah om = ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
    (Amax : ℕ → BilateralField d → ℝ)
    (hAmaxdef : ∀ N om, Amax N om =
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
        (fun q => |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j))
          ((3 : ℝ) ^ (-(N : ℤ)) • SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q)|))
    (Aosc : ℕ → BilateralField d → ℝ)
    (hAoscdef : ∀ N om, Aosc N om =
      (3 : ℝ) ^ (-(N : ℤ)) * ∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j)))) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ N x, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
        |Real.log (cutoffCoefficient M H om N x)| ≤
          2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
            Ah om + Amax N om + Aosc N om := by
  classical
  have : CompactSpace (K : Set (SpatialCoordinates d)) := isCompact_iff_compactSpace.mp K.isCompact
  set mu0 : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) with hmu0
  set forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩ with hforget
  set pz : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j)) with hpz
  have hpzmeas : Measurable pz := by
    apply Measurable.of_eval
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hpzmap : Measure.map pz mu0 = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, hmu0, hpz, hforget, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  set gpt : ℕ → (Fin d → ℤ) → SpatialCoordinates d := fun N q =>
    (3 : ℝ) ^ (-(N : ℤ)) • SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q with hgpt
  have hGoodmeas : MeasurableSet {om : BilateralField d | ∀ j : ℤ,
      ∀ x y : K, x ≠ y →
        |om j x - om j y| / dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤
          Vr (om j)} := by
    have heq : {om : BilateralField d | ∀ j : ℤ, ∀ x y : K, x ≠ y →
          |om j x - om j y| / dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤
            Vr (om j)} =
        ⋂ j : ℤ, (fun om : BilateralField d => om j) ⁻¹'
          {f : C(SpatialCoordinates d, ℝ) | ∀ x y : K, x ≠ y →
            |f x - f y| / dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤ Vr f} := by
      ext om
      simp only [mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    rw [heq]
    exact MeasurableSet.iInter (fun j => (measurable_pi_apply j) hVrset)
  have hGood : ∀ᵐ om ∂((chaosSampleLaw M).toMeasure), ∀ j : ℤ,
      ∀ x y : K, x ≠ y →
        |om j x - om j y| / dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤
          Vr (om j) := by
    rw [← hpzmap, ae_map_iff hpzmeas.aemeasurable hGoodmeas]
    filter_upwards with w
    intro j
    obtain ⟨q, hq⟩ :=
      aux_finite_cutoff_log_abs_majorant_exists_pow ((3 : ℝ) ^ (-j) * Bnd)
    have hc : (0 : ℝ) ≤ (3 : ℝ) ^ (-j) := by positivity
    have hratio := aux_finite_cutoff_log_abs_majorant_ratio_bound K Bnd hKnorm
      ((3 : ℝ) ^ (-j)) hc q hq (w j)
    refine hVrdom (pz w j) ((3 : ℝ) ^ (-j) *
      ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ))
        (fun a => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w j))))) ?_
    intro x y hxy
    have hval : ∀ u : SpatialCoordinates d,
        (pz w j) u = (w j) ((3 : ℝ) ^ (-j) • u) := fun u => rfl
    rw [hval, hval]
    exact hratio x y hxy
  filter_upwards [hGood] with om hom
  intro N x hx
  have hxd : dist x z ≤ r / 2 := hx
  have hxK : x ∈ (K : Set (SpatialCoordinates d)) := hKcontains x (by linarith)
  have hahom : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hlogid : Real.log (cutoffCoefficient M H om N x) =
      -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
        (H om x + (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x)
          - ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
    rw [cutoffCoefficient, Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),
      Real.log_inv, Real.log_exp, cutoffPotential]
  have hlogahom1 : Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) ≤ 0 :=
    Real.log_nonpos hahom.le (SubdiffusiveProcess.CoarseGrainingVocab.ahom_le_one M N)
  have hlogahom2 : -(((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≤
      Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) := by
    have h := SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M N
    have h2 := Real.log_le_log (Real.exp_pos _) h
    rw [Real.log_exp] at h2
    have : -((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
        -(((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by ring
    linarith [this ▸ h2]
  have hHbound : |H om x| ≤ Ah om := by
    rw [hAhdef]
    have hb : ‖((H om).restrict (K : Set (SpatialCoordinates d))) ⟨x, hxK⟩‖ ≤
        ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ :=
      ContinuousMap.norm_coe_le_norm _ _
    have heq : ((H om).restrict (K : Set (SpatialCoordinates d))) ⟨x, hxK⟩ = H om x := rfl
    rw [heq, Real.norm_eq_abs] at hb
    exact hb
  obtain ⟨q, hqmem, hqdist⟩ :=
    aux_finite_cutoff_log_abs_majorant_grid N Q1 z (r / 2) hQ1 x hx
  have hy0K : gpt N q ∈ (K : Set (SpatialCoordinates d)) := by
    refine hKcontains _ ?_
    have h3 : (3 : ℝ) ^ (-(N : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast]
      have h31 : (1 : ℝ) ≤ (3 : ℝ) ^ N := one_le_pow₀ (by norm_num)
      rw [inv_le_one₀ (by positivity)]
      exact h31
    have hd1 : dist (gpt N q) x ≤ 1 := by
      have hq2 : dist x (gpt N q) ≤ (3 : ℝ) ^ (-(N : ℤ)) := hqdist
      have hq3 : dist (gpt N q) x ≤ (3 : ℝ) ^ (-(N : ℤ)) := by
        rw [dist_comm]; exact hq2
      linarith
    calc dist (gpt N q) z ≤ dist (gpt N q) x + dist x z := dist_triangle _ _ _
      _ ≤ 1 + r / 2 := by linarith
      _ ≤ r / 2 + 1 := by linarith
  have hterm : ∀ j : ℕ, |om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) (gpt N q)| ≤
      Vr (om (-(Int.ofNat j))) * dist x (gpt N q) := by
    intro j
    by_cases hxy : x = gpt N q
    · rw [hxy]
      simp
    · have hne : (⟨x, hxK⟩ : (K : Set (SpatialCoordinates d))) ≠ ⟨gpt N q, hy0K⟩ := by
        intro h
        exact hxy (congrArg Subtype.val h)
      have hr0 := hom (-(Int.ofNat j)) ⟨x, hxK⟩ ⟨gpt N q, hy0K⟩ hne
      have hd0 : 0 < dist x (gpt N q) := dist_pos.mpr hxy
      exact (div_le_iff₀ hd0).mp hr0
  have hsumsplit : |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x| ≤
      Amax N om + Aosc N om := by
    have hgrid : |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)| ≤ Amax N om := by
      rw [hAmaxdef]
      exact Finset.le_sup' (f := fun q =>
        |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)|) hqmem
    have hdiff : |(∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
        ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)| ≤ Aosc N om := by
      have h1 : |(∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
          ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)| ≤
          ∑ j ∈ Finset.range (N + 1),
            |om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) (gpt N q)| := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      have h2 : (∑ j ∈ Finset.range (N + 1),
          |om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) (gpt N q)|) ≤
          ∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j))) * dist x (gpt N q) :=
        Finset.sum_le_sum (fun j _ => hterm j)
      have hqdist' : dist x (gpt N q) ≤ (3 : ℝ) ^ (-(N : ℤ)) := hqdist
      have hS : 0 ≤ ∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j))) :=
        Finset.sum_nonneg (fun j _ => hVr0 _)
      have h3 : (∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j))) * dist x (gpt N q)) ≤
          Aosc N om := by
        rw [← Finset.sum_mul]
        have hmul : (∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j)))) *
            dist x (gpt N q) ≤
            (∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j)))) * (3 : ℝ) ^ (-(N : ℤ)) :=
          mul_le_mul_of_nonneg_left hqdist' hS
        have heq : (∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j)))) *
            (3 : ℝ) ^ (-(N : ℤ)) = Aosc N om := by
          rw [hAoscdef]; ring
        linarith [heq ▸ hmul]
      linarith
    have h4 : |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x| ≤
        |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)| +
        |(∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
          ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)| := by
      have hab := abs_sub_abs_le_abs_sub
        (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x)
        (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q))
      linarith
    linarith
  rw [hlogid, abs_le]
  have htau0 : 0 ≤ ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P := by
    have := M.G4.tauSq_pos.le
    positivity
  have hVVexp : 2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
      Ah om + Amax N om + Aosc N om =
      ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
      ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P + Ah om + Amax N om + Aosc N om := by
    ring
  have hHb := abs_le.mp hHbound
  have hSb := abs_le.mp hsumsplit
  rw [hVVexp]
  constructor
  · linarith [hHb.1, hSb.1, hlogahom1]
  · linarith [hHb.2, hSb.2, hlogahom2]

theorem aux_lem_extremes_log_abs :
  ∀ (d : ℕ), 2 ≤ d →
  ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∃ Cd cd : ℝ, 0 < Cd ∧ 0 < cd ∧
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
  ∀ (p : ℝ), 1 ≤ p →
  ∃ C0 : ℝ, 0 < C0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ cd / p →
        ∃ V : ℕ → BilateralField d → ℝ,
          (∀ N om, 0 ≤ V N om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            ∀ N x, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M H om N x)| ≤ V N om) ∧
          (∀ N, MemLp (fun om => Real.exp (V N om))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
          (∀ N, eLpNorm (fun om => Real.exp (V N om))
              (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal
              (C0 * Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ)))) := by
  classical
  intro d hd instMS instBS
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  set Cval : ℝ := 6 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) with hCval
  set Ed : ℝ := 5 * (1 + Real.log 2 + 3 * (d : ℝ) * Real.log 3) with hEd
  have hEdnn : 0 ≤ Ed := by rw [hEd]; positivity
  set u1 : ℝ := (d : ℝ) * Real.log 3 + Cval ^ 2 / 4 + (9 / 16) * Ed with hu1
  have hu1nn : 0 ≤ u1 := by
    rw [hu1]
    have h1 : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 := by positivity
    have h2 : (0 : ℝ) ≤ Cval ^ 2 / 4 := by positivity
    have h3 : (0 : ℝ) ≤ (9 / 16) * Ed := by positivity
    linarith
  refine ⟨4 * u1 + 1, 1 / 4, by linarith, by norm_num, ?_⟩
  intro z r hr p hp
  have hr4 : (0 : ℝ) < r + 4 := by linarith
  set K : Compacts (SpatialCoordinates d) := closedCube z (r + 4) hr4 with hKdef
  set Bnd : ℝ := ‖z‖ + (r + 4) / 2 with hBnd
  have hKnorm : ∀ x : K, ‖(x : SpatialCoordinates d)‖ ≤ Bnd := by
    intro x
    have hx : dist (x : SpatialCoordinates d) z ≤ (r + 4) / 2 := x.2
    have hx' : ‖(x : SpatialCoordinates d) - z‖ ≤ (r + 4) / 2 := by
      rwa [dist_eq_norm] at hx
    calc ‖(x : SpatialCoordinates d)‖ = ‖z + ((x : SpatialCoordinates d) - z)‖ := by
          rw [add_sub_cancel]
      _ ≤ ‖z‖ + ‖(x : SpatialCoordinates d) - z‖ := norm_add_le _ _
      _ ≤ Bnd := by rw [hBnd]; linarith
  obtain ⟨Q1, hQ1⟩ := aux_finite_cutoff_log_abs_majorant_exists_pow_half (‖z‖ + r / 2)
  obtain ⟨CHf, hCHf0, hCHfb⟩ :=
    exists_uniform_compactExponentialMoment_of_admissible hd
  obtain ⟨Vr, hVrmeas, hVr0, hVrdom, hVrle, hVrset⟩ :=
    aux_finite_negative_layer_log_lipschitz_majorant_continuous_ratio K
  obtain ⟨Q0, hQ0⟩ := aux_finite_cutoff_log_abs_majorant_exists_pow Bnd
  set E0 : ℝ := 5 * (1 + Real.log 2 + (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3) with hE0
  have hE0pos : 0 < E0 := by
    rw [hE0]
    have h : (0 : ℝ) ≤ (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3 := by positivity
    linarith
  set u0 : ℝ := 3 * Real.log 2 + CHf K / 4 + (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 +
    Cval ^ 2 / 4 + (9 / 16) * E0 with hu0
  have hu0nn : 0 ≤ u0 := by
    rw [hu0]
    have h1 : (0 : ℝ) ≤ (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 := by positivity
    have h2 : (0 : ℝ) ≤ Cval ^ 2 / 4 := by positivity
    have h3 : (0 : ℝ) ≤ (9 / 16) * E0 := by linarith
    have h4 : (0 : ℝ) ≤ CHf K / 4 := by linarith [hCHf0 K]
    linarith
  refine ⟨Real.exp 1 * Real.exp (2 * (Real.log 3 + u0)) + Real.log 2,
    by positivity, ?_⟩
  intro M H hH hdel
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdhalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set t : ℝ := 1 / (4 * M.delta) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have hpt : p ≤ t := by
    rw [ht, le_div_iff₀ (by positivity)]
    have h1 : M.delta * p ≤ 1 / 4 := by
      have := (le_div_iff₀ hp0).mp hdel
      linarith
    linarith
  set mu0 : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) with hmu0
  set forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩ with hforget
  set pz : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j)) with hpz
  have hpzmeas : Measurable pz := by
    apply Measurable.of_eval
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hpzmap : Measure.map pz mu0 = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, hmu0, hpz, hforget, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  have hpzapp : ∀ (w : NativeBilateralPotentialSample d) (j : ℕ) (y : SpatialCoordinates d),
      (pz w) (-(Int.ofNat j)) y = (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • y) := by
    intro w j y
    show (layerScaling d (-(Int.ofNat j)) (forget (w (-(Int.ofNat j))))) y = _
    simp [layerScaling, ContinuousMap.compRightContinuousMap, hforget]
    rfl
  set gpt : ℕ → (Fin d → ℤ) → SpatialCoordinates d := fun N q =>
    (3 : ℝ) ^ (-(N : ℤ)) • SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q with hgpt
  set Amax : ℕ → BilateralField d → ℝ := fun N om =>
    (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
      (fun q => |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)|) with hAmax
  set Aosc : ℕ → BilateralField d → ℝ := fun N om =>
    (3 : ℝ) ^ (-(N : ℤ)) * ∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j))) with hAosc
  set Ah : BilateralField d → ℝ := fun om =>
    ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ with hAh
  set VV : ℕ → BilateralField d → ℝ := fun N om =>
    2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P + Ah om + Amax N om + Aosc N om with hVV
  -- measurability
  have hevmeas : ∀ (j : ℤ) (y : SpatialCoordinates d),
      Measurable (fun om : BilateralField d => om j y) := by
    intro j y
    exact ((continuous_eval_const y).measurable).comp (measurable_pi_apply j)
  have hAhmeas : Measurable Ah :=
    aux_finite_cutoff_log_abs_majorant_restrict_measurable K H hH.measurable
  have hAmaxmeas : ∀ N, Measurable (Amax N) := by
    intro N
    have h0 : Measurable
        ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
          (fun q (om : BilateralField d) =>
            |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)|)) := by
      refine Finset.measurable_sup' _ (fun q _ => ?_)
      exact (Finset.measurable_sum _ (fun j _ => hevmeas (-(Int.ofNat j)) (gpt N q))).abs
    have h1 : ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
        (fun q (om : BilateralField d) =>
          |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)|)) = Amax N := by
      funext om
      exact Finset.sup'_apply _ _ om
    rwa [h1] at h0
  have hAoscmeas : ∀ N, Measurable (Aosc N) := by
    intro N
    refine measurable_const.mul (Finset.measurable_sum _ (fun j _ => ?_))
    exact hVrmeas.comp (measurable_pi_apply _)
  have hVVmeas : ∀ N, Measurable (VV N) := by
    intro N
    exact ((measurable_const.add hAhmeas).add (hAmaxmeas N)).add (hAoscmeas N)
  have hAmax0 : ∀ N om, 0 ≤ Amax N om := by
    intro N om
    obtain ⟨q, hq⟩ := SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ))
    exact le_trans (abs_nonneg _) (Finset.le_sup' (f := fun q =>
      |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)|) hq)
  have hAosc0 : ∀ N om, 0 ≤ Aosc N om := by
    intro N om
    rw [hAosc]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hVr0 _))
  have hVV0 : ∀ N om, 0 ≤ VV N om := by
    intro N om
    have htau : 0 ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P := M.G4.tauSq_pos.le
    have h1 : 0 ≤ 2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P := by positivity
    have h2 : 0 ≤ Ah om := norm_nonneg _
    have := hAmax0 N om
    have := hAosc0 N om
    rw [hVV]
    simp only
    linarith
  set cN : ℕ → ℝ := fun N => 2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
    4 * M.delta * (Real.log 3 + u0 + u1 * (N : ℝ)) with hcN
  have h4dt : 4 * M.delta * t = 1 := by rw [ht]; field_simp
  have hu0a : Real.log 2 + CHf K / 4 ≤ u0 := by
    rw [hu0]
    have h1 : (0 : ℝ) ≤ (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 := by positivity
    have h2 : (0 : ℝ) ≤ Cval ^ 2 / 4 := by positivity
    have h3 : (0 : ℝ) ≤ (9 / 16) * E0 := by linarith
    linarith
  have hu0b : Real.log 2 + (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 + Cval ^ 2 / 4 ≤ u0 := by
    rw [hu0]
    have h3 : (0 : ℝ) ≤ (9 / 16) * E0 := by linarith
    have h4 : (0 : ℝ) ≤ CHf K / 4 := by linarith [hCHf0 K]
    linarith
  have hu1b : (d : ℝ) * Real.log 3 + Cval ^ 2 / 4 ≤ u1 := by
    rw [hu1]
    have h3 : (0 : ℝ) ≤ (9 / 16) * Ed := by positivity
    linarith
  have hu0c : Real.log 2 + (9 / 16) * E0 ≤ u0 := by
    rw [hu0]
    have h1 : (0 : ℝ) ≤ (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 := by positivity
    have h2 : (0 : ℝ) ≤ Cval ^ 2 / 4 := by positivity
    have h4 : (0 : ℝ) ≤ CHf K / 4 := by linarith [hCHf0 K]
    linarith
  have hu1c : (9 / 16) * Ed ≤ u1 := by
    rw [hu1]
    have h1 : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 := by positivity
    have h2 : (0 : ℝ) ≤ Cval ^ 2 / 4 := by positivity
    linarith
  set cN : ℕ → ℝ := fun N => 2 * ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
    4 * M.delta * (Real.log 3 + u0 + u1 * (N : ℝ)) with hcN
  have hkey : ∀ N : ℕ,
      Integrable (fun om => Real.exp (t * VV N om)) (chaosSampleLaw M).toMeasure ∧
      (∫ om, Real.exp (t * VV N om) ∂(chaosSampleLaw M).toMeasure) ≤
        Real.exp (t * cN N) := by
    intro N
    exact aux_lem_extremes_additive_moment M H K Bnd hKnorm Q0 Q1 hQ0 Vr hVr0 hVrle
      (CHf K) (hCHf0 K) (fun lam hlam => hCHfb M H hH K lam hlam) Cval E0 Ed u0 u1 t
      hCval hE0 hEd hu1nn hu0a hu0b hu1b hu0c hu1c ht Ah (fun om => rfl) hAhmeas
      Amax (fun N om => rfl) hAmaxmeas Aosc (fun N om => rfl) hAoscmeas N
  have hKcontains : ∀ u : SpatialCoordinates d, dist u z ≤ r / 2 + 1 →
      u ∈ (K : Set (SpatialCoordinates d)) := by
    intro u hu
    show dist u z ≤ (r + 4) / 2
    linarith
  refine ⟨VV, hVV0, ?_, ?_, ?_⟩
  · have henv := aux_lem_extremes_envelope M H z r hr K Bnd hKnorm
      hKcontains Q1 hQ1 Vr hVr0 hVrdom hVrset Ah (fun om => rfl) Amax (fun N om => rfl)
      Aosc (fun N om => rfl)
    exact henv
  · intro N
    exact (aux_finite_cutoff_log_abs_majorant_lp (chaosSampleLaw M).toMeasure (VV N)
      (hVVmeas N) t p htpos hpt M.delta (_root_.SubdiffusiveProcess.Model.tauSq M.P) u0 u1 hdelta
      hdhalf hu0nn hu1nn (SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M) N
      (hkey N).1 (hkey N).2).1
  · intro N
    exact (aux_finite_cutoff_log_abs_majorant_lp (chaosSampleLaw M).toMeasure (VV N)
      (hVVmeas N) t p htpos hpt M.delta (_root_.SubdiffusiveProcess.Model.tauSq M.P) u0 u1 hdelta
      hdhalf hu0nn hu1nn (SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M) N
      (hkey N).1 (hkey N).2).2

theorem aux_lem_extremes_upper :
  ∀ (d : ℕ), 2 ≤ d →
  ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∃ Cd cd : ℝ, 0 < Cd ∧ 0 < cd ∧
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
  ∀ (p : ℝ), 1 ≤ p →
  ∃ Cp : ℝ, 0 < Cp ∧
    (∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ cd / p →
      ∃ D mlow mhigh : ℕ → BilateralField d → ℝ,
        (∀ N om, 0 ≤ D N om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
          (∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M H om N x) -
                  Real.log (cutoffCoefficient M H om N y)| ≤
                D N om * (3 : ℝ) ^ N * dist x y) ∧
          (0 < mlow N om ∧
            ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              mlow N om ≤ cutoffCoefficient M H om N x ∧
                cutoffCoefficient M H om N x ≤ mhigh N om)) ∧
        (∀ N, MemLp (D N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N, MemLp (fun omega => mhigh N omega + (mlow N omega)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N, eLpNorm (D N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cp * Real.sqrt (1 + (N : ℝ)))) ∧
        (∀ N, eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N)))) := by
  intro d hd instMS instBS
  obtain ⟨Cd, cd, hCd, hcd, hVall0⟩ := aux_lem_extremes_log_abs d hd
  refine ⟨Cd, min 1 cd, hCd, lt_min one_pos hcd, ?_⟩
  intro z r hr p hp
  obtain ⟨Cg, hCg, hGall⟩ := infrared_admissible_lipschitz_majorant d hd z r hr p hp
  obtain ⟨Cu, hCu, hUall⟩ := aux_lem_extremes_fine_fixed_threshold d hd z r hr p hp
  obtain ⟨C0, hC0, hVall⟩ := hVall0 z r hr p hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hsp : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  set Cp : ℝ := 2 * C0 + Cg * Real.sqrt p + Cu with hCpdef
  have hCp : 0 < Cp := by rw [hCpdef]; positivity
  refine ⟨Cp, hCp, ?_⟩
  intro M H hH hdel
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdhalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hdel_u : M.delta ≤ 1 / p :=
    le_trans hdel (div_le_div_of_nonneg_right (min_le_left _ _) hp0.le)
  have hdel_d : M.delta ≤ cd / p :=
    le_trans hdel (div_le_div_of_nonneg_right (min_le_right _ _) hp0.le)
  obtain ⟨G, hG0, hGae, hGmem, hGnorm⟩ := hGall M H hH
  obtain ⟨U, hU0, hUae, hUmem, hUnorm⟩ := hUall M hdel_u
  obtain ⟨V, _hV0, hVae, hVmem, hVnorm⟩ := hVall M H hH hdel_d
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hApos : ∀ om N x, 0 < cutoffCoefficient M H om N x := by
    intro om N x
    have hahom : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
    rw [cutoffCoefficient]
    positivity
  have hlogid : ∀ om N x, Real.log (cutoffCoefficient M H om N x) =
      -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
        (H om x + (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x)
          - ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
    intro om N x
    have hahom : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
    rw [cutoffCoefficient, Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),
      Real.log_inv, Real.log_exp, cutoffPotential]
  have hfun : ∀ N, (fun om => Real.exp (V N om) + (Real.exp (-V N om))⁻¹) =
      (fun om => Real.exp (V N om)) + (fun om => Real.exp (V N om)) := by
    intro N
    funext om
    simp only [Pi.add_apply, Real.exp_neg, inv_inv]
  refine ⟨fun N om => G om + U N om, fun N om => Real.exp (-V N om),
    fun N om => Real.exp (V N om), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N om
    exact add_nonneg (hG0 om) (hU0 N om)
  · filter_upwards [hGae, hUae, hVae] with om hGom hUom hVom
    intro N
    refine ⟨?_, Real.exp_pos _, ?_⟩
    · intro x y hx hy
      rw [hlogid om N x, hlogid om N y]
      have hsplit :
          (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
              (H om x + (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x)
                - ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) -
            (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
              (H om y + (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) y)
                - ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) =
            (H om x - H om y) +
              ((∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
                ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) y) := by ring
      rw [hsplit]
      have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ N := one_le_pow₀ (by norm_num)
      have hdist : 0 ≤ dist x y := dist_nonneg
      have hGd : G om * dist x y ≤ G om * (3 : ℝ) ^ N * dist x y := by
        have h := mul_le_mul_of_nonneg_left h3 (hG0 om)
        rw [mul_one] at h
        exact mul_le_mul_of_nonneg_right h hdist
      have hexp : (G om + U N om) * (3 : ℝ) ^ N * dist x y =
          G om * (3 : ℝ) ^ N * dist x y + U N om * (3 : ℝ) ^ N * dist x y := by ring
      have htri := abs_add_le (H om x - H om y)
        ((∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
          ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) y)
      have hG1 := hGom x y hx hy
      have hU1 := hUom N x y hx hy
      show _ ≤ (G om + U N om) * (3 : ℝ) ^ N * dist x y
      rw [hexp]
      linarith
    · intro x hx
      have hVx := hVom N x hx
      have hA := hApos om N x
      have hAeq := Real.exp_log hA
      have hab := abs_le.mp hVx
      constructor
      · calc Real.exp (-V N om)
            ≤ Real.exp (Real.log (cutoffCoefficient M H om N x)) :=
              Real.exp_le_exp.mpr (by linarith [hab.1])
          _ = cutoffCoefficient M H om N x := hAeq
      · calc cutoffCoefficient M H om N x
            = Real.exp (Real.log (cutoffCoefficient M H om N x)) := hAeq.symm
          _ ≤ Real.exp (V N om) := Real.exp_le_exp.mpr hab.2
  · intro N
    exact hGmem.add (hUmem N)
  · intro N
    show MemLp (fun om => Real.exp (V N om) + (Real.exp (-V N om))⁻¹) _ _
    rw [hfun N]
    exact (hVmem N).add (hVmem N)
  · intro N
    have hs1 : (1 : ℝ) ≤ Real.sqrt (1 + (N : ℝ)) := by
      rw [Real.one_le_sqrt]
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hdel1 : M.delta ≤ 1 := by linarith
    have hreal : Cg * M.delta * Real.sqrt p + Cu * M.delta * Real.sqrt (1 + (N : ℝ)) ≤
        Cp * Real.sqrt (1 + (N : ℝ)) := by
      have ha : 0 ≤ Cg * Real.sqrt p := by positivity
      have h1 : Cg * M.delta * Real.sqrt p ≤ Cg * Real.sqrt p * Real.sqrt (1 + (N : ℝ)) := by
        have e : Cg * M.delta * Real.sqrt p = Cg * Real.sqrt p * M.delta := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left (le_trans hdel1 hs1) ha
      have h2 : Cu * M.delta * Real.sqrt (1 + (N : ℝ)) ≤ Cu * Real.sqrt (1 + (N : ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hdel1 hCu.le
        rw [mul_one] at h
        exact mul_le_mul_of_nonneg_right h (by positivity)
      have h3 : 0 ≤ 2 * C0 * Real.sqrt (1 + (N : ℝ)) := by positivity
      have e : Cp * Real.sqrt (1 + (N : ℝ)) =
          2 * C0 * Real.sqrt (1 + (N : ℝ)) + Cg * Real.sqrt p * Real.sqrt (1 + (N : ℝ)) +
            Cu * Real.sqrt (1 + (N : ℝ)) := by rw [hCpdef]; ring
      rw [e]
      linarith
    calc eLpNorm (fun om => G om + U N om) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure
        ≤ eLpNorm G (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure +
            eLpNorm (U N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure :=
          eLpNorm_add_le hp1
      _ ≤ ENNReal.ofReal (Cg * M.delta * Real.sqrt p) +
            ENNReal.ofReal (Cu * M.delta * Real.sqrt (1 + (N : ℝ))) :=
          add_le_add hGnorm (hUnorm N)
      _ = ENNReal.ofReal (Cg * M.delta * Real.sqrt p +
            Cu * M.delta * Real.sqrt (1 + (N : ℝ))) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (Cp * Real.sqrt (1 + (N : ℝ))) := ENNReal.ofReal_le_ofReal hreal
  · intro N
    show eLpNorm (fun om => Real.exp (V N om) + (Real.exp (-V N om))⁻¹) _ _ ≤ _
    rw [hfun N]
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hX : 0 ≤ C0 * Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ)) := by
      positivity
    have hCgsp : 0 ≤ Cg * Real.sqrt p := by positivity
    have hC0Cp : C0 ≤ Cp := by rw [hCpdef]; linarith
    have hreal : C0 * Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ)) +
        C0 * Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ)) ≤
        Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)) := by
      have hexp : Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ)) ≤
          Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)) := by
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ hNnn)
        have := mul_le_mul_of_nonneg_right hC0Cp (sq_nonneg M.delta)
        linarith
      have h2 : 2 * C0 ≤ Cp := by rw [hCpdef]; linarith
      have hE : 0 ≤ Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ)) :=
        (Real.exp_pos _).le
      calc C0 * Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ)) +
            C0 * Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ))
          = (2 * C0) * Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ)) := by ring
        _ ≤ Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ)) :=
          mul_le_mul h2 hexp hE hCp.le
    calc eLpNorm ((fun om => Real.exp (V N om)) + (fun om => Real.exp (V N om)))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure
        ≤ eLpNorm (fun om => Real.exp (V N om)) (ENNReal.ofReal p)
              (chaosSampleLaw M).toMeasure +
            eLpNorm (fun om => Real.exp (V N om)) (ENNReal.ofReal p)
              (chaosSampleLaw M).toMeasure :=
          eLpNorm_add_le hp1
      _ ≤ ENNReal.ofReal (C0 * Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ))) +
            ENNReal.ofReal (C0 * Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ))) :=
          add_le_add (hVnorm N) (hVnorm N)
      _ = ENNReal.ofReal (C0 * Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ)) +
            C0 * Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ))) :=
          (ENNReal.ofReal_add hX hX).symm
      _ ≤ ENNReal.ofReal (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * (N : ℝ))) :=
          ENNReal.ofReal_le_ofReal hreal

theorem lem_extremes :
  ∀ (d : ℕ), 2 ≤ d →
  ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∃ Cd cd : ℝ, 0 < Cd ∧ 0 < cd ∧
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
  ∀ (p : ℝ), 1 ≤ p →
  ∃ Cp : ℝ, 0 < Cp ∧
    (∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ cd / p →
      ∃ D mlow mhigh : ℕ → BilateralField d → ℝ,
        (∀ N om, 0 ≤ D N om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
          (∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M H om N x) -
                  Real.log (cutoffCoefficient M H om N y)| ≤
                D N om * (3 : ℝ) ^ N * dist x y) ∧
          (0 < mlow N om ∧
            ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              mlow N om ≤ cutoffCoefficient M H om N x ∧
                cutoffCoefficient M H om N x ≤ mhigh N om)) ∧
        (∀ N, MemLp (D N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N, MemLp (fun omega => mhigh N omega + (mlow N omega)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N, eLpNorm (D N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cp * Real.sqrt (1 + (N : ℝ)))) ∧
        (∀ N, eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N)))) := by
  intro d hd instMS instBS
  obtain ⟨Cd, cd, hCd, hcd, hall⟩ := aux_lem_extremes_upper d hd
  refine ⟨Cd, cd, hCd, hcd, ?_⟩
  intro z r hr p hp
  obtain ⟨Cp, hCp, hCpall⟩ := hall z r hr p hp
  exact ⟨Cp, hCp, fun M H hH hδ => hCpall M H hH hδ⟩

theorem aux_lem_extremes_compat :
  ∀ (d : ℕ), 2 ≤ d →
  ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
  ∀ (p : ℝ), 1 ≤ p →
  ∃ Cp Cd cd : ℝ, 0 < Cp ∧ 0 < Cd ∧ 0 < cd ∧
    (∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ cd / p →
      ∃ D mlow mhigh : ℕ → BilateralField d → ℝ,
        (∀ N om, 0 ≤ D N om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
          (∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M H om N x) -
                  Real.log (cutoffCoefficient M H om N y)| ≤
                D N om * (3 : ℝ) ^ N * dist x y) ∧
          (0 < mlow N om ∧
            ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              mlow N om ≤ cutoffCoefficient M H om N x ∧
                cutoffCoefficient M H om N x ≤ mhigh N om)) ∧
        (∀ N, MemLp (D N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N, MemLp (fun omega => mhigh N omega + (mlow N omega)⁻¹)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N, eLpNorm (D N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cp * Real.sqrt (1 + (N : ℝ)))) ∧
        (∀ N, eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cp * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N)))) := by
  intro d hd instMS instBS z r hr p hp
  obtain ⟨Cd, cd, hCd, hcd, hall⟩ := lem_extremes d hd
  obtain ⟨Cp, hCp, hCpall⟩ := hall z r hr p hp
  exact ⟨Cp, Cd, cd, hCp, hCd, hcd, hCpall⟩

end SubdiffusiveProcess.Paper
