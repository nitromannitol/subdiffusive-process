import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.AnchoredGrowth




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Filter MeasureTheory Topology
open Homogenization Homogenization.IndependentSums
open SubdiffusiveProcess.Frozen.Assumptions
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Transfer to the anchored carrier -/

/-- An almost sure statement on the ambient sample space transfers to the
anchored carrier law.  This uses only that `Subtype.val` is a measurable
embedding on a measurable good set. -/
theorem ae_anchoredC11SampleLaw_of_ae {P : PotentialSample d → Prop}
    (M : GMCModel d) (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1)
    (h : ∀ᵐ omega ∂M.P.toMeasure, P omega) :
    ∀ᵐ omega ∂(anchoredC11SampleLaw M hmeas hfull).toMeasure, P omega.1 := by
  have hemb : MeasurableEmbedding
      (Subtype.val : AnchoredC11Sample d → PotentialSample d) :=
    MeasurableEmbedding.subtype_coe hmeas
  rw [ae_iff] at h ⊢
  have hlaw : (anchoredC11SampleLaw M hmeas hfull).toMeasure =
      Measure.comap Subtype.val M.P.toMeasure := rfl
  rw [hlaw, hemb.comap_apply]
  refine measure_mono_null ?_ h
  rintro omega ⟨s, hs, rfl⟩
  exact hs

/-! ## The per-sample package -/

/-- **The two growth clauses for one sample**, given the two Borel–Cantelli
constants.  This is the deterministic content of `steps .4-.6`. -/
theorem anchored_clauses_of_envelopes (M : GMCModel d)
    (hdelta : M.delta ≤ anchoredDelta0 d) (omega : AnchoredC11Sample d)
    {C1 C2 : ℝ} (hC2 : 0 ≤ C2)
    (hval : ∀ n : ℕ, ∀ z : Fin d → ℤ, z ∈ latticeBox d n →
      ∀ L : ℕ, L ≤ maxCutoffLevel n →
        |anchoredPartialSum omega.1 L (latticePoint z)| ≤
          valueMaximalSlope d * M.delta * ((n : ℝ) + 1) + C1)
    (hgauge : ∀ n k : ℕ, ∀ p ∈ shellCoverShifts d (coverExp n k),
      translatedShellG2 k (shellCoverCenter p) omega.1 ≤
        C2 * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) :
    (∀ x : Vec d,
        aAnchored M omega x + (aAnchored M omega x)⁻¹ +
            euclideanNorm
              (aAnchored M omega x • shellGradient (anchoredLog omega) x) ≤
          polyEnvelopeOf d C1 C2 * (1 + ‖x‖) ^ anchoredKappa ∧
        ∀ L : ℕ,
          anchoredCutoff M L omega.1 x + (anchoredCutoff M L omega.1 x)⁻¹ +
              euclideanNorm (anchoredCutoff M L omega.1 x •
                shellGradient (anchoredPartialSumField omega.1 L) x) ≤
            polyEnvelopeOf d C1 C2 * (1 + ‖x‖) ^ anchoredKappa) ∧
      (∀ x : Vec d, ∀ L : ℕ,
        euclideanNorm (shellGradient (anchoredPartialSumField omega.1 L) x) +
            PotentialField.unitCubeDerivLipschitzSeminorm
              (PotentialField.translate x (anchoredPartialSumField omega.1 L)) ≤
          logEnvelopeOf d C2 * (1 + Real.sqrt (Real.log (2 + ‖x‖)))) := by
  have hbounds := growingBall_shell_bounds_of_forall_le omega.1 hC2 hgauge
  -- the three per-point estimates, at the dyadic index of the point
  have key : ∀ x : Vec d,
      (∀ L : ℕ, |anchoredPartialSum omega.1 L x| ≤
          valueMaximalSlope d * M.delta * ((dyadicIndex x : ℝ) + 1) + C1 +
            C2 * (gradSeriesConst + tailSeriesConst) *
              Real.sqrt ((dyadicIndex x : ℝ) + 1) / 2) ∧
        (∀ L : ℕ, ‖PotentialField.deriv (anchoredPartialSumField omega.1 L) x‖ ≤
          C2 * gradSeriesConst * Real.sqrt ((dyadicIndex x : ℝ) + 1)) ∧
        (∀ L : ℕ, PotentialField.unitCubeDerivLipschitzSeminorm
            (PotentialField.translate x (anchoredPartialSumField omega.1 L)) ≤
          C2 * gradSeriesConst * Real.sqrt ((dyadicIndex x : ℝ) + 1)) := by
    intro x
    set n : ℕ := dyadicIndex x with hn_def
    have hn : 2 + ‖x‖ ≤ (2 : ℝ) ^ n := two_add_norm_le_two_pow_dyadicIndex x
    have hxnorm : ‖x‖ ≤ (2 : ℝ) ^ n := by linarith
    have hxball : x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n) :=
      mem_closedBall_growingBallRadius hxnorm
    have hgrad : ∀ k : ℕ,
        ∀ y ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
          ‖PotentialField.deriv (omega.1 k) y‖ ≤
            C2 * ((((3 : ℝ) ^ k)⁻¹) * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) :=
      fun k => (hbounds n k).1
    have hlip : ∀ k : ℕ,
        ∀ y ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
          ∀ y' ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
            ‖PotentialField.deriv (omega.1 k) y -
                PotentialField.deriv (omega.1 k) y'‖ ≤
              C2 * ((((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹) *
                Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * ‖y - y'‖ :=
      fun k => (hbounds n k).2.1
    refine ⟨fun L => ?_, fun L => ?_, fun L => ?_⟩
    · exact abs_anchoredPartialSum_le hC2 (hval n) hgrad L hn
    · exact norm_deriv_anchoredPartialSumField_le hC2 hgrad L hxball
    · exact unitCubeDerivLipschitzSeminorm_translate_le hC2 hlip L (by linarith)
  constructor
  · intro x
    obtain ⟨hV, hG, _⟩ := key x
    have hvgrad : ∀ L : ℕ,
        euclideanNorm (shellGradient (anchoredPartialSumField omega.1 L) x) ≤
          (d : ℝ) * (C2 * gradSeriesConst *
            Real.sqrt ((dyadicIndex x : ℝ) + 1)) := by
      intro L
      refine (euclideanNorm_shellGradient_le _ x).trans ?_
      exact mul_le_mul_of_nonneg_left (hG L) (Nat.cast_nonneg d)
    constructor
    · -- the limit coefficient
      have hlimval : Tendsto
          (fun L => |anchoredPartialSum omega.1 L x|) atTop
          (𝓝 |anchoredLog omega x|) :=
        (((anchoredLog_spec omega).value_tendsto {x} isCompact_singleton).tendsto_at
          rfl).abs
      have hlimnorm : Tendsto
          (fun L => ‖PotentialField.deriv (anchoredPartialSumField omega.1 L) x‖)
          atTop (𝓝 ‖PotentialField.deriv (anchoredLog omega) x‖) :=
        (((anchoredLog_spec omega).deriv_tendsto {x}
          isCompact_singleton).tendsto_at rfl).norm
      have hSlim : |anchoredLog omega x| ≤
          valueMaximalSlope d * M.delta * ((dyadicIndex x : ℝ) + 1) + C1 +
            C2 * (gradSeriesConst + tailSeriesConst) *
              Real.sqrt ((dyadicIndex x : ℝ) + 1) / 2 :=
        le_of_tendsto' hlimval hV
      have hvlim : euclideanNorm (shellGradient (anchoredLog omega) x) ≤
          (d : ℝ) * (C2 * gradSeriesConst *
            Real.sqrt ((dyadicIndex x : ℝ) + 1)) :=
        (euclideanNorm_shellGradient_le _ x).trans
          (mul_le_mul_of_nonneg_left (le_of_tendsto' hlimnorm hG)
            (Nat.cast_nonneg d))
      exact exp_growth_bound hdelta hC2 hSlim hvlim
    · intro L
      have hcut : anchoredCutoff M L omega.1 x =
          Real.exp (anchoredPartialSum omega.1 L x) :=
        anchoredCutoff_eq_exp M L omega.1 x
      rw [hcut]
      exact exp_growth_bound hdelta hC2 (hV L) (hvgrad L)
  · intro x L
    obtain ⟨_, hG, hS⟩ := key x
    have hvgrad : euclideanNorm
        (shellGradient (anchoredPartialSumField omega.1 L) x) ≤
        (d : ℝ) * (C2 * gradSeriesConst *
          Real.sqrt ((dyadicIndex x : ℝ) + 1)) :=
      (euclideanNorm_shellGradient_le _ x).trans
        (mul_le_mul_of_nonneg_left (hG L) (Nat.cast_nonneg d))
    exact logDeriv_growth_bound hC2 hvgrad (hS L)

/-! ## The almost sure statement in the frozen shape -/

/-- **The two frozen growth clauses**, almost surely on the anchored carrier
law, with the deterministic exponent `anchoredKappa = 3/4` and the measurable
random constant `anchoredComega`. -/
theorem ae_anchored_growth_clauses (M : GMCModel d)
    (hdelta : M.delta ≤ anchoredDelta0 d)
    (hmeas : MeasurableSet (anchoredC11GoodSet d))
    (hfull : M.P.toMeasure (anchoredC11GoodSet d) = 1) :
    ∀ᵐ omega ∂(anchoredC11SampleLaw M hmeas hfull).toMeasure,
      0 ≤ anchoredComega M omega ∧
      (∀ x : Vec d,
          aAnchored M omega x + (aAnchored M omega x)⁻¹ +
              euclideanNorm
                (aAnchored M omega x • shellGradient (anchoredLog omega) x) ≤
            anchoredComega M omega * (1 + ‖x‖) ^ anchoredKappa ∧
          ∀ L : ℕ,
            anchoredCutoff M L omega.1 x + (anchoredCutoff M L omega.1 x)⁻¹ +
                euclideanNorm (anchoredCutoff M L omega.1 x •
                  shellGradient (anchoredPartialSumField omega.1 L) x) ≤
              anchoredComega M omega * (1 + ‖x‖) ^ anchoredKappa) ∧
      (∀ x : Vec d, ∀ L : ℕ,
        euclideanNorm (shellGradient (anchoredPartialSumField omega.1 L) x) +
            PotentialField.unitCubeDerivLipschitzSeminorm
              (PotentialField.translate x (anchoredPartialSumField omega.1 L)) ≤
          anchoredComega M omega * (1 + Real.sqrt (Real.log (2 + ‖x‖)))) := by
  have hbase : ∀ᵐ omega ∂M.P.toMeasure,
      (∀ n : ℕ, ∀ z : Fin d → ℤ, z ∈ latticeBox d n →
        ∀ L : ℕ, L ≤ maxCutoffLevel n →
          |anchoredPartialSum omega L (latticePoint z)| ≤
            valueMaximalSlope d * M.delta * ((n : ℝ) + 1) +
              valueEnvelope M omega) ∧
      (∀ n k : ℕ, ∀ p ∈ shellCoverShifts d (coverExp n k),
        translatedShellG2 k (shellCoverCenter p) omega ≤
          derivEnvelope omega * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) :=
    (ae_forall_abs_anchoredPartialSum_le_valueEnvelope M).and
      (ae_forall_translatedShellG2_le_derivEnvelope M)
  filter_upwards [ae_anchoredC11SampleLaw_of_ae M hmeas hfull hbase] with omega homega
  obtain ⟨hval, hgauge⟩ := homega
  have hC2 : (0 : ℝ) ≤ derivEnvelope omega.1 := derivEnvelope_nonneg omega.1
  obtain ⟨hpoly, hlog⟩ :=
    anchored_clauses_of_envelopes M hdelta omega hC2 hval hgauge
  have hpolyle : polyEnvelopeOf d (valueEnvelope M omega.1) (derivEnvelope omega.1) ≤
      anchoredComega M omega := le_max_left _ _
  have hlogle : logEnvelopeOf d (derivEnvelope omega.1) ≤ anchoredComega M omega :=
    le_max_right _ _
  refine ⟨anchoredComega_nonneg M omega, fun x => ?_, fun x L => ?_⟩
  · obtain ⟨hlim, hcut⟩ := hpoly x
    have hpow : (0 : ℝ) ≤ (1 + ‖x‖) ^ anchoredKappa :=
      Real.rpow_nonneg (by positivity) _
    refine ⟨hlim.trans (mul_le_mul_of_nonneg_right hpolyle hpow), fun L => ?_⟩
    exact (hcut L).trans (mul_le_mul_of_nonneg_right hpolyle hpow)
  · have hnn : (0 : ℝ) ≤ 1 + Real.sqrt (Real.log (2 + ‖x‖)) := by
      have := Real.sqrt_nonneg (Real.log (2 + ‖x‖))
      linarith
    exact (hlog x L).trans (mul_le_mul_of_nonneg_right hlogle hnn)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
