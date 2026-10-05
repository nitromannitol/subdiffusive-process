module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffPotential
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Vocab.Ahom
public import SubdiffusiveProcess.Probability.InfraredCommonFieldConvergence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.MeasurableEnvelope
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationGrowth
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedStoppingDerivative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.SeminormLimits

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_finiteDimensional_cutoff_nonexplosion_root_linear_growth_set
    {d : ℕ} (m : ℕ) :
    MeasurableSet {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
      ∀ x, ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤
        (m : ℝ) * (1 + ‖x‖)} := by
  have hclosed : IsClosed {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
      ∀ x, ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤
        (m : ℝ) * (1 + ‖x‖)} := by
    rw [show {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
        ∀ x, ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤
          (m : ℝ) * (1 + ‖x‖)} =
        ⋂ x : SpatialCoordinates d, {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
          ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤
            (m : ℝ) * (1 + ‖x‖)} by
      ext g
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]]
    apply isClosed_iInter
    intro x
    apply isClosed_le
    · exact continuous_norm.comp
        (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_eval_deriv x)
    · exact continuous_const
  exact hclosed.measurableSet

theorem aux_finiteDimensional_cutoff_nonexplosion_root_linear_growth_set_exists
    {d : ℕ} :
    MeasurableSet {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
      ∃ m : ℕ, ∀ x, ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤
        (m : ℝ) * (1 + ‖x‖)} := by
  rw [show {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
      ∃ m : ℕ, ∀ x, ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤
        (m : ℝ) * (1 + ‖x‖)} =
      ⋃ m : ℕ, {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
        ∀ x, ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤
          (m : ℝ) * (1 + ‖x‖)} by
    ext g
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]]
  exact MeasurableSet.iUnion fun m =>
    aux_finiteDimensional_cutoff_nonexplosion_root_linear_growth_set m

theorem aux_finiteDimensional_cutoff_nonexplosion_shell_linear_growth_set
    {d : ℕ} (m : ℕ) :
    MeasurableSet {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
      ∀ x, Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) ≤
        (m : ℝ) * (1 + ‖x‖)} := by
  have hclosed : IsClosed {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
      ∀ x, Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) ≤
        (m : ℝ) * (1 + ‖x‖)} := by
    rw [show {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
        ∀ x, Homogenization.euclideanNorm
            (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) ≤
          (m : ℝ) * (1 + ‖x‖)} =
        ⋂ x : SpatialCoordinates d, {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
          Homogenization.euclideanNorm
              (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) ≤
            (m : ℝ) * (1 + ‖x‖)} by
      ext g
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]]
    apply isClosed_iInter
    intro x
    apply isClosed_le
    · apply SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.continuous_euclideanNorm.comp
      change Continuous (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
          (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x))
      apply continuous_pi
      intro i
      exact ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).continuous).comp'
        (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_eval_deriv x)
    · exact continuous_const
  exact hclosed.measurableSet

/-- Fixed-cutoff drift/nonexplosion interface for the SDE.

Scope and inputs:
- `in_normalization` pins the concrete cutoff potential and deterministic
  homogenization factor used in the drift.
- `lem_infrared` supplies the local `C^{1,1}` regularity used by the
  fixed-cutoff SDE argument.
- The threshold is bound before the model, and the almost-sure event is
  simultaneous in the countable cutoff index.
- CONCLUDED HERE: the concrete fixed-cutoff linear-growth estimate that
  is the nonexplosion interface consumed by `resolvent_datum` and by
  `finiteDimensional_cutoff_path_kernel`.
- This is a proof-step fine child refining
  `finiteDimensional_cutoff`; no nonexplosion or growth premise is added to
  the parent theorem.
- The proof below supplies the displayed growth estimate.
- The paper's SDE/nonexplosion supplier is with its
  finite-cutoff tightness consumption. -/
theorem finiteDimensional_cutoff_nonexplosion
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
          ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
            ‖(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
                Homogenization.euclideanGradient
                  (cutoffPotential H omega N) x‖ ≤
              K * (1 + ‖x‖) := by
  classical
  refine ⟨1, zero_lt_one, ?_⟩
  intro M H hH hdelta
  let μ : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
  let F : NativeBilateralPotentialSample d →
      _root_.SubdiffusiveProcess.Model.PotentialSample d :=
    fun omega k =>
      _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k (omega (k : ℤ))
  have hFmeas : Measurable F := by
    apply Measurable.of_eval _
    intro k
    exact (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k).comp
      (measurable_pi_apply (k : ℤ))
  have hFmap : Measure.map F μ = M.P.toMeasure := by
    let μ0 : Measure (_root_.SubdiffusiveProcess.Model.PotentialField d) :=
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
    let S : Set ℤ := {j | 0 ≤ j}
    let e : ℕ ≃ {j : ℤ // j ∈ S} :=
      { toFun := fun k => ⟨(k : ℤ), by simp [S]⟩
        invFun := fun j => j.1.toNat
        left_inv := by intro k; simp
        right_inv := by
          intro j
          apply Subtype.ext
          simp [S, Int.toNat_of_nonneg j.2] }
    let R : (ℤ → _root_.SubdiffusiveProcess.Model.PotentialField d) →
        ({j : ℤ // j ∈ S} → _root_.SubdiffusiveProcess.Model.PotentialField d) :=
      S.domRestrict
    let E : ({j : ℤ // j ∈ S} → _root_.SubdiffusiveProcess.Model.PotentialField d) →
        (ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d) :=
      fun x k => x (e k)
    let T : (ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d) →
        (ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d) :=
      fun x k => _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k (x k)
    have hR : Measurable R := by
      exact measurable_pi_iff.mpr fun j => measurable_pi_apply j.1
    have hE : Measurable E := by
      exact Measurable.of_eval fun k => measurable_pi_apply (e k)
    have hT : Measurable T := by
      exact Measurable.of_eval fun k =>
        (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k).comp
          (measurable_pi_apply k)
    have hrestrict :
        Measure.map R μ =
          Measure.infinitePi (fun _ : {j : ℤ // j ∈ S} => μ0) := by
      simpa only [R, μ, μ0] using!
        (Measure.infinitePi_map_restrict' (μ := fun _ : ℤ => μ0) (I := S))
    have hreindex :
        Measure.map E (Measure.infinitePi
          (fun _ : {j : ℤ // j ∈ S} => μ0)) =
          Measure.infinitePi (fun _ : ℕ => μ0) := by
      have h := Measure.infinitePi_map_piCongrLeft
        (μ := fun _ : ℕ => μ0) e.symm
      simpa only [E, e] using! h
    have hscale :
        Measure.map T (Measure.infinitePi (fun _ : ℕ => μ0)) =
          Measure.infinitePi (fun k : ℕ =>
            (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure.map
              (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)) := by
      rw [Measure.infinitePi_map_pi
        (μ := fun _ : ℕ => μ0)
        (f := fun k : ℕ =>
          _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
        (fun k => _root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k)]
    have hprod :
        M.P.toMeasure =
          Measure.infinitePi
            (fun k : ℕ =>
              (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure) := by
      have hi :=
        (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
          (P := M.P.toMeasure)
          (X := fun k (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) => omega k)
          (fun k => measurable_pi_apply k)).mp M.shellPrefix.independent
      simpa only [Measure.map_id', _root_.SubdiffusiveProcess.Model.potentialMarginalLaw, ProbabilityMeasure.toMeasure_map] using! hi
    have hcomp : F = T ∘ E ∘ R := by
      funext omega k
      rfl
    calc
      Measure.map F μ = Measure.map (T ∘ E ∘ R) μ := by rw [hcomp]
      _ = Measure.map T (Measure.map E (Measure.map R μ)) := by
        calc
          Measure.map (T ∘ E ∘ R) μ =
              Measure.map T (Measure.map (E ∘ R) μ) :=
            (Measure.map_map hT (hE.comp hR)).symm
          _ = Measure.map T (Measure.map E (Measure.map R μ)) := by
            rw [Measure.map_map hE hR]
      _ = M.P.toMeasure := by
        rw [hrestrict, hreindex, hscale]
        calc
          Measure.infinitePi (fun k : ℕ =>
              (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure.map
                (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)) =
              Measure.infinitePi
                (fun k : ℕ =>
                  (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure) := by
            congr 1
            funext k
            have hm := congrArg
              (fun Q : ProbabilityMeasure
                (_root_.SubdiffusiveProcess.Model.PotentialField d) => Q.toMeasure)
              (M.shellPrefix.marginal_scaling k)
            calc
              Measure.map
                  (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
                  (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure =
                  ((_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).map
                    (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)).toMeasure := rfl
              _ = (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure := hm.symm
          _ = M.P.toMeasure := hprod.symm
  have hfull : ∀ᵐ omega ∂μ, ∀ x L,
      Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient
            (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) L) x) ≤
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.logEnvelopeOf d
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.derivEnvelope (F omega)) *
          (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
    have h0 := SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ae_partial_logGradient_growth M
    rw [← hFmap] at h0
    exact ae_of_ae_map hFmeas.aemeasurable h0
  have hpositive : ∀ᵐ omega ∂μ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x L,
      Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient
            (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField
              (positiveScaledNativeLayer omega) L) x) ≤
        C * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
    filter_upwards [hfull] with omega homega
    let C := SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.logEnvelopeOf d
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.derivEnvelope (F omega))
    have hC : 0 ≤ C := by
      exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.logEnvelopeOf_nonneg d
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.derivEnvelope_nonneg _)
    have hpos : positiveScaledNativeLayer omega = fun n => F omega (n + 1) := by
      funext n
      change _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale
          ((3 : ℝ) ^ (-(n + 1 : ℤ))) (omega ((n + 1 : ℕ) : ℤ)) =
        _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale
          (((3 : ℝ) ^ (n + 1))⁻¹) (omega ((n + 1 : ℕ) : ℤ))
      congr 2
    have hshift : ∀ L : ℕ,
        _root_.SubdiffusiveProcess.Model.anchoredPartialSumField
            (fun n => F omega (n + 1)) L =
          _root_.SubdiffusiveProcess.Model.PotentialField.add
            (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) (L + 1))
            (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1)
              (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) 0)) := by
      intro L
      induction L with
      | zero =>
          ext x
          simp [_root_.SubdiffusiveProcess.Model.anchoredPartialSumField,
            _root_.SubdiffusiveProcess.Model.PotentialField.add_apply,
            _root_.SubdiffusiveProcess.Model.PotentialField.scale_apply]
          ring
      | succ L ih =>
          rw [_root_.SubdiffusiveProcess.Model.anchoredPartialSumField,
            _root_.SubdiffusiveProcess.Model.anchoredPartialSumField, ih]
          ext x
          simp [_root_.SubdiffusiveProcess.Model.PotentialField.add_apply,
            _root_.SubdiffusiveProcess.Model.PotentialField.scale_apply]
          have hzero : _root_.SubdiffusiveProcess.Model.anchoredPartialSum (F omega) 0 x =
              (F omega 0) x - (F omega 0) 0 := by
            simp [_root_.SubdiffusiveProcess.Model.anchoredPartialSum]
          have hsum : _root_.SubdiffusiveProcess.Model.anchoredPartialSum (F omega) (L + 1 + 1) x =
              _root_.SubdiffusiveProcess.Model.anchoredPartialSum (F omega) (L + 1) x +
                ((F omega (L + 1 + 1)) x - (F omega (L + 1 + 1)) 0) := by
            unfold _root_.SubdiffusiveProcess.Model.anchoredPartialSum
            rw [show L + 1 + 1 + 1 = (L + 1 + 1) + 1 by rfl,
              Finset.sum_range_succ]
          rw [hzero]
          rw [hsum]
          ring
    refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
    intro x L
    rw [hpos, hshift]
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.shellGradient_eq_gradOfCLM]
    simp only [_root_.SubdiffusiveProcess.Model.PotentialField.add_deriv]
    have hscale : _root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1)
            (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) 0)) x =
        -_root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) 0) x := by
      change (-1 : ℝ) • _root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) 0) x = _
      module
    rw [hscale]
    have hvec : _root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) (L + 1)) x +
          -_root_.SubdiffusiveProcess.Model.PotentialField.deriv
            (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) 0) x =
        _root_.SubdiffusiveProcess.Model.PotentialField.deriv
          (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) (L + 1)) x -
          _root_.SubdiffusiveProcess.Model.PotentialField.deriv
            (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) 0) x := by abel
    rw [hvec]
    change Homogenization.euclideanNorm
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
          (_root_.SubdiffusiveProcess.Model.PotentialField.deriv
              (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) (L + 1)) x +
            -_root_.SubdiffusiveProcess.Model.PotentialField.deriv
              (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) 0) x)) ≤
      2 * C * (1 + Real.sqrt (Real.log (2 + ‖x‖)))
    have h1 := homega x (L + 1)
    have h0 := homega x 0
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.shellGradient_eq_gradOfCLM] at h1 h0
    have h1' : Homogenization.euclideanNorm
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
          (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) (L + 1)) x)) ≤
        C * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by simpa [C] using h1
    have h0' : Homogenization.euclideanNorm
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
          (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) 0) x)) ≤
        C * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by simpa [C] using h0
    have hgrad : SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
          (_root_.SubdiffusiveProcess.Model.PotentialField.deriv
              (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) (L + 1)) x +
            -_root_.SubdiffusiveProcess.Model.PotentialField.deriv
              (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) 0) x) =
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
          (_root_.SubdiffusiveProcess.Model.PotentialField.deriv
              (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) (L + 1)) x) -
          SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
            (_root_.SubdiffusiveProcess.Model.PotentialField.deriv
              (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) 0) x) := by
      rw [hvec, SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM_sub]
    rw [hgrad]
    calc
      Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
            (_root_.SubdiffusiveProcess.Model.PotentialField.deriv
              (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) (L + 1)) x) -
            SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
              (_root_.SubdiffusiveProcess.Model.PotentialField.deriv
                (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) 0) x)) ≤
        Homogenization.euclideanNorm
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
              (_root_.SubdiffusiveProcess.Model.PotentialField.deriv
                (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) (L + 1)) x)) +
          Homogenization.euclideanNorm
            (-SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
              (_root_.SubdiffusiveProcess.Model.PotentialField.deriv
                (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField (F omega) 0) x)) := by
        simpa only [sub_eq_add_neg] using
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.euclideanNorm_add_le _ _)
      _ ≤ C * (1 + Real.sqrt (Real.log (2 + ‖x‖))) +
          C * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
        rw [Homogenization.euclideanNorm_neg]
        exact add_le_add h1' h0'
      _ = 2 * C * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by ring
  obtain ⟨C0, hC0, hlem⟩ := lem_infrared hd
  obtain ⟨Hn, hHnmeas, hHnObs, hHnAE, hHnLp, hHnExp⟩ := hlem M μ rfl
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let π : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j))
  have hπmeas : Measurable π := by
    apply Measurable.of_eval
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hπmeasure : Measure.map π μ = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, μ, π, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  have hscaleinj : ∀ j : ℤ, Function.Injective (layerScaling d j) := by
    intro j f g hfg
    ext x
    have hx := congrArg (fun q : C(SpatialCoordinates d, ℝ) =>
      q ((3 : ℝ) ^ j • x)) hfg
    change f ((3 : ℝ) ^ (-j) • ((3 : ℝ) ^ j • x)) =
      g ((3 : ℝ) ^ (-j) • ((3 : ℝ) ^ j • x)) at hx
    have hp : (3 : ℝ) ^ (-j) * (3 : ℝ) ^ j = 1 := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      simp
    have hp' : ((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ j = 1 :=
      inv_mul_cancel₀ (by positivity)
    simpa [smul_smul, hp, hp'] using hx
  have hforgetinj : Function.Injective forget := by
    intro g h hgh
    apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
    intro x
    exact congrArg (fun f : C(SpatialCoordinates d, ℝ) => f x) hgh
  have hπinj : Function.Injective π := by
    intro omega omega' heq
    funext j
    apply hforgetinj
    apply hscaleinj j
    exact congrFun heq j
  have hπemb : MeasurableEmbedding π := hπmeas.measurableEmbedding hπinj
  have hHβ : ∀ᵐ omega ∂μ,
      Tendsto (fun L => infraredPartialSum (π omega) L) atTop
        (nhds (H (π omega))) := by
    have h0 := hH.2
    rw [← hπmeasure] at h0
    exact ae_of_ae_map hπmeas.aemeasurable h0
  have hsum : ∀ omega L,
      infraredPartialSum (π omega) L =
        forget (positiveAnchoredInfraredTruncation omega L) := by
    intro omega L
    have hπpos : ∀ n,
        forget (positiveScaledNativeLayer omega n) =
          π omega (Int.ofNat (n + 1)) := by
      intro n
      ext x
      change omega (n + 1) ((3 : ℝ) ^ (-(n + 1 : ℤ)) • x) =
        omega (Int.ofNat (n + 1)) ((3 : ℝ) ^ (-Int.ofNat (n + 1)) • x)
      congr 1
    induction L with
    | zero =>
        simp [infraredPartialSum, positiveAnchoredInfraredTruncation, forget,
          zeroNativePotentialField]
        rfl
    | succ L ih =>
        unfold infraredPartialSum
        rw [Finset.sum_range_succ]
        change infraredPartialSum (π omega) L +
            (π omega (Int.ofNat (L + 1)) -
              ContinuousMap.const _ ((π omega (Int.ofNat (L + 1))) 0)) = _
        rw [ih, ← hπpos L]
        ext x
        change (forget (positiveAnchoredInfraredTruncation omega L)) x +
            ((forget (positiveScaledNativeLayer omega L)) x -
              (forget (positiveScaledNativeLayer omega L)) 0) =
          (forget (positiveAnchoredInfraredTruncation omega L)) x +
            ((forget (positiveScaledNativeLayer omega L)) x -
              (forget (positiveScaledNativeLayer omega L)) 0)
        rfl
  have hnative_eq : ∀ᵐ omega ∂μ, ∀ x,
      H (π omega) x = (forget (Hn omega)) x := by
    filter_upwards [hHβ, hHnAE] with omega hbeta hnative
    intro x
    have hbeta_x :=
      ((continuous_eval_const x).tendsto (H (π omega))).comp hbeta
    have hbeta_x' : Tendsto
        (fun L => (forget (positiveAnchoredInfraredTruncation omega L)) x)
        atTop (nhds (H (π omega) x)) := by
      change Tendsto (fun L => (infraredPartialSum (π omega) L) x) atTop
        (nhds (H (π omega) x)) at hbeta_x
      rw [show (fun L => (infraredPartialSum (π omega) L) x) =
          (fun L => (forget (positiveAnchoredInfraredTruncation omega L)) x) by
        funext L; exact congrArg (fun q : C(SpatialCoordinates d, ℝ) => q x)
          (hsum omega L)] at hbeta_x
      exact hbeta_x
    have hpt : Tendsto
        (fun L => (forget (positiveAnchoredInfraredTruncation omega L)) x)
        atTop (nhds ((forget (Hn omega)) x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      apply squeeze_zero (fun L => norm_nonneg _)
      · intro L
        let q := _root_.SubdiffusiveProcess.Model.PotentialField.add
          (positiveAnchoredInfraredTruncation omega L)
          (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (Hn omega))
        change ‖(forget (positiveAnchoredInfraredTruncation omega L)) x -
            (forget (Hn omega)) x‖ ≤ compactPotentialC1Norm
              (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d)) q
        rw [show (forget (positiveAnchoredInfraredTruncation omega L)) x -
            (forget (Hn omega)) x = q x by
              change (positiveAnchoredInfraredTruncation omega L) x - (Hn omega) x = q x
              dsimp [q]
              ring]
        unfold compactPotentialC1Norm
        exact (ContinuousMap.norm_coe_le_norm
          (⟨fun z : (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d)) =>
              q z.1, q.1.1.continuous.comp continuous_subtype_val⟩ :
            C((⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d)), ℝ))
          ⟨x, Set.mem_singleton x⟩).trans
          (le_add_of_nonneg_right (by positivity))
      · simpa only [sub_zero] using
          hnative.2.1 (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d))
    exact tendsto_nhds_unique hbeta_x' hpt
  have hrootMP : ∀ᵐ g ∂M.P.toMeasure, ∃ m : ℕ, ∀ x,
      Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (g 0) x) ≤
        (m : ℝ) * (1 + ‖x‖) := by
    filter_upwards [SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ae_partial_logGradient_growth M]
      with g hg
    let C := SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.logEnvelopeOf d
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.derivEnvelope g)
    let m : ℕ := ⌈(5 / 2 : ℝ) * C⌉₊
    refine ⟨m, ?_⟩
    intro x
    have hC : 0 ≤ C := SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.logEnvelopeOf_nonneg d
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.derivEnvelope_nonneg _)
    have hlog := SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.one_add_sqrt_log_le
      ‖x‖ (norm_nonneg x)
    have hm : (5 / 2 : ℝ) * C ≤ (m : ℝ) := by
      exact_mod_cast (Nat.le_ceil ((5 / 2 : ℝ) * C))
    have hbase : Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (g 0) x) ≤
        C * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
      simpa [C, _root_.SubdiffusiveProcess.Model.anchoredPartialSumField] using hg x 0
    calc
      _ ≤ C * (5 / 2 * (1 + ‖x‖)) := by
        exact hbase.trans (mul_le_mul_of_nonneg_left hlog hC)
      _ = ((5 / 2 : ℝ) * C) * (1 + ‖x‖) := by ring
      _ ≤ (m : ℝ) * (1 + ‖x‖) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
  have hrootSet : MeasurableSet {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
      ∃ m : ℕ, ∀ x, Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) ≤ (m : ℝ) * (1 + ‖x‖)} := by
    rw [show {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
        ∃ m : ℕ, ∀ x, Homogenization.euclideanNorm
            (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) ≤ (m : ℝ) * (1 + ‖x‖)} =
        ⋃ m : ℕ, {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
          ∀ x, Homogenization.euclideanNorm
              (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) ≤ (m : ℝ) * (1 + ‖x‖)} by
      ext g
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]]
    exact MeasurableSet.iUnion fun m =>
      aux_finiteDimensional_cutoff_nonexplosion_shell_linear_growth_set m
  have hmap0 : Measure.map (fun g : _root_.SubdiffusiveProcess.Model.PotentialSample d => g 0)
      M.P.toMeasure =
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
    have h0 := SubdiffusiveProcess.CoarseGrainingVocab.map_unscalePotential_coordinate_eq_zero M 0
    convert h0 using 1
    congr 1
    funext g
    apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
    intro x
    simp [SubdiffusiveProcess.CoarseGrainingVocab.unscalePotential]
  have hroot0 : ∀ᵐ g ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure,
      ∃ m : ℕ, ∀ x,
        Homogenization.euclideanNorm (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) ≤
          (m : ℝ) * (1 + ‖x‖) := by
    rw [← hmap0]
    apply (ae_map_iff (measurable_pi_apply 0).aemeasurable hrootSet).2
    simpa only [Function.comp_apply] using hrootMP
  have hrootAll : ∀ᵐ omega ∂μ, ∀ j : ℤ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      Homogenization.euclideanNorm
        (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (omega j) x) ≤
      C * (1 + ‖x‖) := by
    apply ae_all_iff.2
    intro j
    have hj : Measure.map (fun omega : NativeBilateralPotentialSample d => omega j) μ =
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
      simpa [μ] using
        (Measure.infinitePi_map_eval
          (fun _ : ℤ => (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) j)
    rw [← hj] at hroot0
    filter_upwards [ae_of_ae_map (measurable_pi_apply j).aemeasurable hroot0] with omega hω
    obtain ⟨m, hm⟩ := hω
    exact ⟨m, Nat.cast_nonneg m, hm⟩
  have hPT : ∀ (omega : NativeBilateralPotentialSample d) (L : ℕ),
      positiveAnchoredInfraredTruncation omega (L + 1) =
        _root_.SubdiffusiveProcess.Model.anchoredPartialSumField
          (positiveScaledNativeLayer omega) L := by
    intro omega L
    induction L with
    | zero =>
        ext x
        change (zeroNativePotentialField d) x +
          (_root_.SubdiffusiveProcess.Model.PotentialField.anchor (positiveScaledNativeLayer omega 0)) x =
          (_root_.SubdiffusiveProcess.Model.PotentialField.anchor (positiveScaledNativeLayer omega 0)) x
        simp [zeroNativePotentialField]
    | succ L ih =>
        rw [positiveAnchoredInfraredTruncation,
          _root_.SubdiffusiveProcess.Model.anchoredPartialSumField, ih]
  have hgood : ∀ᵐ omega ∂μ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      Homogenization.euclideanNorm
          (Homogenization.euclideanGradient
            (fun y => H (π omega) y) x) ≤ C * (1 + ‖x‖) := by
    filter_upwards [hpositive, hnative_eq, hHnAE, hrootAll] with omega
      ⟨C, hC, hposbound⟩ heq hnative hroots
    have hgradHn : ∀ x,
        Homogenization.euclideanNorm
            (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (Hn omega) x) ≤
          (5 / 2 * C) * (1 + ‖x‖) := by
      intro x
      have hdiff : ∀ L, ‖
          SubdiffusiveProcess.CoarseGrainingVocab.shellGradient
              (positiveAnchoredInfraredTruncation omega (L + 1)) x -
            SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (Hn omega) x‖ ≤
          compactPotentialC1Norm
            (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d))
            (_root_.SubdiffusiveProcess.Model.PotentialField.add
              (positiveAnchoredInfraredTruncation omega (L + 1))
              (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (Hn omega))) := by
        intro L
        let q := _root_.SubdiffusiveProcess.Model.PotentialField.add
          (positiveAnchoredInfraredTruncation omega (L + 1))
          (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (Hn omega))
        have hq : ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv q x‖ ≤
            compactPotentialC1Norm
              (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d)) q := by
          unfold compactPotentialC1Norm
          exact (ContinuousMap.norm_coe_le_norm
            (⟨fun z : (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d)) =>
                _root_.SubdiffusiveProcess.Model.PotentialField.deriv q z.1,
              (_root_.SubdiffusiveProcess.Model.PotentialField.deriv q).continuous.comp
                continuous_subtype_val⟩ :
              C((⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d)),
                SpatialCoordinates d →L[ℝ] ℝ)) ⟨x, Set.mem_singleton x⟩).trans
            (le_add_of_nonneg_left (by positivity))
        have heqgrad :
            SubdiffusiveProcess.CoarseGrainingVocab.shellGradient
                (positiveAnchoredInfraredTruncation omega (L + 1)) x -
              SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (Hn omega) x =
            SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
              (_root_.SubdiffusiveProcess.Model.PotentialField.deriv q x) := by
          rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.shellGradient_eq_gradOfCLM,
            SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.shellGradient_eq_gradOfCLM,
            ← SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM_sub]
          congr 1
          dsimp [q]
          have hs : _root_.SubdiffusiveProcess.Model.PotentialField.deriv
                (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (Hn omega)) x =
              -_root_.SubdiffusiveProcess.Model.PotentialField.deriv (Hn omega) x := by
            change (-1 : ℝ) • _root_.SubdiffusiveProcess.Model.PotentialField.deriv (Hn omega) x = _
            module
          rw [hs]
          module
        rw [heqgrad]
        exact (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.norm_gradOfCLM_le _).trans hq
      have hconv := hnative.2.1
        (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d))
      have hconv' := (Filter.tendsto_add_atTop_iff_nat 1).2 hconv
      have hnorm : Tendsto (fun L => ‖
          SubdiffusiveProcess.CoarseGrainingVocab.shellGradient
              (positiveAnchoredInfraredTruncation omega (L + 1)) x -
            SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (Hn omega) x‖)
          atTop (nhds 0) :=
        squeeze_zero (fun L => norm_nonneg _) hdiff hconv'
      have hvec : Tendsto (fun L =>
          SubdiffusiveProcess.CoarseGrainingVocab.shellGradient
              (positiveAnchoredInfraredTruncation omega (L + 1)) x)
          atTop (nhds (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (Hn omega) x)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        exact hnorm
      have hnormlim :=
        (SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.continuous_euclideanNorm.tendsto _).comp hvec
      apply le_of_tendsto hnormlim
      filter_upwards [] with L
      change Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient
            (positiveAnchoredInfraredTruncation omega (L + 1)) x) ≤ _
      rw [hPT omega L]
      calc
        _ ≤ C * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := hposbound x L
        _ ≤ C * (5 / 2 * (1 + ‖x‖)) := by
          exact mul_le_mul_of_nonneg_left
            (SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.one_add_sqrt_log_le
              ‖x‖ (norm_nonneg x)) hC
        _ = (5 / 2 * C) * (1 + ‖x‖) := by ring
    refine ⟨5 / 2 * C, mul_nonneg (by norm_num) hC, ?_⟩
    intro x
    have hfun : (fun y => H (π omega) y) = fun y => (Hn omega) y := by
      funext y
      exact heq y
    rw [hfun, SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.euclideanGradient_potentialField]
    exact hgradHn x
  have hnative_final : ∀ᵐ omega ∂μ, ∀ N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
      ‖(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
          Homogenization.euclideanGradient (cutoffPotential H (π omega) N) x‖ ≤
        K * (1 + ‖x‖) := by
    filter_upwards [hgood, hrootAll, hnative_eq] with omega hgoodω hroots heq
    obtain ⟨B, hB, hBgrad⟩ := hgoodω
    have hfun : (fun y => H (π omega) y) = fun y => (Hn omega) y := by
      funext y
      exact heq y
    have hneg : ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
        Homogenization.euclideanNorm
            (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient
              (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale
                ((3 : ℝ) ^ j) (omega (-(Int.ofNat j)))) x) ≤
          K * (1 + ‖x‖) := by
      intro j
      obtain ⟨Cj, hCj, hrootj⟩ := hroots (-(Int.ofNat j))
      let r : ℝ := (3 : ℝ) ^ j
      refine ⟨Cj * r * (1 + r), ?_, ?_⟩
      · positivity
      intro x
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.shellGradient_eq_gradOfCLM]
      change Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
            (r • _root_.SubdiffusiveProcess.Model.PotentialField.deriv
              (omega (-(Int.ofNat j))) (r • x))) ≤ _
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM_smul,
        Homogenization.euclideanNorm_smul, abs_of_nonneg (by positivity : 0 ≤ r)]
      have hx := hrootj (r • x)
      have hxnorm : ‖r • x‖ = r * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ r)]
      rw [hxnorm] at hx
      calc
        r * Homogenization.euclideanNorm
              (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (omega (-(Int.ofNat j))) (r • x)) ≤
            r * (Cj * (1 + r * ‖x‖)) := by
              exact mul_le_mul_of_nonneg_left hx (by positivity)
        _ ≤ (Cj * r * (1 + r)) * (1 + ‖x‖) := by
              have hinside : 1 + r * ‖x‖ ≤ (1 + r) * (1 + ‖x‖) := by
                have hr : 0 ≤ r := by positivity
                have hs : 0 ≤ ‖x‖ := norm_nonneg x
                nlinarith
              calc
                r * (Cj * (1 + r * ‖x‖)) ≤
                    r * (Cj * ((1 + r) * (1 + ‖x‖))) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hinside hCj) (by positivity)
                _ = (Cj * r * (1 + r)) * (1 + ‖x‖) := by ring
    choose K hKnonneg hK using hneg
    have htri : ∀ (g h : _root_.SubdiffusiveProcess.Model.PotentialField d) (x),
        Homogenization.euclideanNorm
            (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient
              (_root_.SubdiffusiveProcess.Model.PotentialField.add g h) x) ≤
          Homogenization.euclideanNorm (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient g x) +
            Homogenization.euclideanNorm (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient h x) := by
      intro g h x
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.shellGradient_eq_gradOfCLM]
      change Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
            (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x) +
            SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.gradOfCLM
              (_root_.SubdiffusiveProcess.Model.PotentialField.deriv h x)) ≤ _
      exact SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.euclideanNorm_add_le _ _
    let negField : ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d := fun j =>
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ j)
        (omega (-(Int.ofNat j)))
    let G : ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d := fun N =>
      Nat.rec
        (_root_.SubdiffusiveProcess.Model.PotentialField.add (Hn omega) (negField 0))
        (fun n g => _root_.SubdiffusiveProcess.Model.PotentialField.add g (negField (n + 1))) N
    have hG_zero : G 0 =
        _root_.SubdiffusiveProcess.Model.PotentialField.add (Hn omega) (negField 0) := by
      rfl
    have hG_succ : ∀ N, G (N + 1) =
        _root_.SubdiffusiveProcess.Model.PotentialField.add (G N) (negField (N + 1)) := by
      intro N
      rfl
    have hG : ∀ N x,
        Homogenization.euclideanNorm
            (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (G N) x) ≤
          (B + ∑ j ∈ Finset.range (N + 1), K j) * (1 + ‖x‖) := by
      intro N
      induction N with
      | zero =>
          intro x
          rw [hG_zero]
          apply (htri (Hn omega) (negField 0) x).trans
          have hn0 := hK 0 x
          have hneg0 : Homogenization.euclideanNorm
              (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (negField 0) x) ≤
              K 0 * (1 + ‖x‖) := by
            change Homogenization.euclideanNorm
                (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient
                  (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ 0)
                    (omega (-(Int.ofNat 0)))) x) ≤ _
            exact hn0
          have hBgrad' : Homogenization.euclideanNorm
              (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (Hn omega) x) ≤
              B * (1 + ‖x‖) := by
            have hb := hBgrad x
            rw [hfun, SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.euclideanGradient_potentialField] at hb
            exact hb
          calc
            _ ≤ B * (1 + ‖x‖) + K 0 * (1 + ‖x‖) :=
              add_le_add hBgrad' hneg0
            _ = (B + ∑ j ∈ Finset.range (0 + 1), K j) * (1 + ‖x‖) := by
              simp
              ring
      | succ N ih =>
          intro x
          rw [hG_succ N]
          apply (htri (G N) (negField (N + 1)) x).trans
          have hn := hK (N + 1) x
          have ih' := ih x
          have hneg' : Homogenization.euclideanNorm
              (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (negField (N + 1)) x) ≤
              K (N + 1) * (1 + ‖x‖) := by
            change Homogenization.euclideanNorm
                (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient
                  (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale
                    ((3 : ℝ) ^ (N + 1))
                    (omega (-(Int.ofNat (N + 1))))) x) ≤ _
            exact hn
          rw [Finset.sum_range_succ]
          exact (add_le_add ih' hneg').trans_eq (by ring)
    have hnegfun : ∀ j : ℕ,
        (fun x => π omega (-(Int.ofNat j)) x) = fun x => negField j x := by
      intro j
      funext x
      simp only [π, negField, layerScaling,
        ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
        _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply,
        neg_neg, Int.ofNat_eq_natCast, zpow_natCast, forget]
      rfl
    have hcut : ∀ N,
        cutoffPotential H (π omega) N = fun x => G N x := by
      intro N
      induction N with
      | zero =>
          funext x
          calc
            cutoffPotential H (π omega) 0 x =
                H (π omega) x + π omega 0 x := by
                  simp [cutoffPotential]
            _ = (Hn omega) x + (negField 0) x := by
                  have hx := congrFun hfun x
                  have h0 := congrFun (hnegfun 0) x
                  have h0' : π omega 0 x = (negField 0) x := by simpa using h0
                  rw [hx, h0']
            _ = G 0 x := by
                  rw [hG_zero]
                  rfl
      | succ N ih =>
          funext x
          have hstep : cutoffPotential H (π omega) (N + 1) x =
                cutoffPotential H (π omega) N x +
                  π omega (-(Int.ofNat (N + 1))) x := by
            change H (π omega) x +
                (∑ j ∈ Finset.range ((N + 1) + 1), (π omega (-(Int.ofNat j))) x) =
              (H (π omega) x +
                (∑ j ∈ Finset.range (N + 1), (π omega (-(Int.ofNat j))) x)) +
                π omega (-(Int.ofNat (N + 1))) x
            rw [Finset.sum_range_succ]
            ring
          calc
            cutoffPotential H (π omega) (N + 1) x =
                cutoffPotential H (π omega) N x +
                  π omega (-(Int.ofNat (N + 1))) x := hstep
            _ = G N x + π omega (-(Int.ofNat (N + 1))) x := by
                  rw [congrFun ih x]
            _ = G (N + 1) x := by
                  have hn := congrFun (hnegfun (N + 1)) x
                  rw [hG_succ N]
                  have hn' : π omega (-(Int.ofNat (N + 1))) x =
                      (negField (N + 1)) x := by simpa using hn
                  rw [hn']
                  rfl
    intro N
    have ha : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
      SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
    let A := ‖(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹‖
    refine ⟨A * (B + ∑ j ∈ Finset.range (N + 1), K j), ?_, ?_⟩
    · exact mul_nonneg (by simp [A])
        (add_nonneg hB (Finset.sum_nonneg (fun j hj => hKnonneg j)))
    intro x
    rw [hcut N, SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.euclideanGradient_potentialField]
    calc
      ‖(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ •
          SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (G N) x‖ ≤
        A * Homogenization.euclideanNorm
          (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (G N) x) := by
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left
              (Homogenization.norm_le_euclideanNorm _) (by positivity)
      _ ≤ A * ((B + ∑ j ∈ Finset.range (N + 1), K j) * (1 + ‖x‖)) :=
        mul_le_mul_of_nonneg_left (hG N x) (by positivity)
      _ = (A * (B + ∑ j ∈ Finset.range (N + 1), K j)) * (1 + ‖x‖) := by ring
  rw [← hπmeasure]
  exact hπemb.ae_map_iff.mpr hnative_final

end SubdiffusiveProcess.Paper
