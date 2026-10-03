module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationGrowth
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationOrigin
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationRadialGenerator
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumGMCDenseRange
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeSmoothCore

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Homogenization hiding Vec
open Filter Topology MeasureTheory MarkovProcess SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

theorem contDiff_one_anchoredCutoff {d : ℕ} (M : GMCModel d)
    (L : ℕ) (omega : PotentialSample d) : ContDiff ℝ 1 (anchoredCutoff M L omega) := by
  have hfun : anchoredCutoff M L omega = fun x ↦ Real.exp (anchoredPartialSumField omega L x) :=
    funext (anchoredCutoff_eq_exp_field M L omega)
  rw [hfun]
  exact (PotentialField.contDiff_one (anchoredPartialSumField omega L)).exp

/-- One linear-growth constant works for the anchored coefficient, every
raw cutoff, and every anchored cutoff in the reversible equation. -/
theorem ae_reversible_family_linearGrowth {d : ℕ} (M : GMCModel d) :
    ∀ᵐ omega ∂(anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure,
      ∃ K : ℝ, 0 ≤ K ∧ ∀ b : Vec d → ℝ,
        (b = aAnchored M omega ∨
          (∃ L : ℕ, b = aCutoff M L omega.val) ∨
          (∃ L : ℕ, b = anchoredCutoff M L omega.val)) →
        ContDiff ℝ 1 b ∧ (∀ x, 0 < b x) ∧
          ∀ x, euclideanNorm (euclideanGradient b x) + b x ≤
            K * b x * (1 + ‖x‖) := by
  have hbase := ae_anchoredC11SampleLaw_of_ae M (measurableSet_anchoredC11GoodSet d)
    (measure_anchoredC11GoodSet_eq_one M) (ae_partial_logGradient_growth M)
  filter_upwards [hbase] with omega hpartial
  let C := logEnvelopeOf d (derivEnvelope omega.val)
  have hC : 0 ≤ C := logEnvelopeOf_nonneg d (derivEnvelope_nonneg omega.val)
  refine ⟨5 * C / 2 + 1, by positivity, ?_⟩
  rintro b (rfl | ⟨L, rfl⟩ | ⟨L, rfl⟩)
  · exact ⟨contDiff_one_aAnchored M omega, aAnchored_pos M omega,
      linearGrowth_exp_of_logGradient (anchoredLog omega) hC
        (logGradient_anchoredLog_le omega hpartial)⟩
  · refine ⟨contDiff_one_aCutoff M L omega.val, aCutoff_pos M L omega.val, ?_⟩
    rw [aCutoff_eq_origin_mul_exp_partial M omega L]
    exact reversible_linearGrowth_pos_mul
      ((PotentialField.contDiff_one (anchoredPartialSumField omega.val L)).exp.differentiable (by norm_num))
      (aCutoff_pos M L omega.val 0)
      (linearGrowth_exp_of_logGradient (anchoredPartialSumField omega.val L) hC
        (fun x ↦ hpartial x L))
  · refine ⟨contDiff_one_anchoredCutoff M L omega.val, anchoredCutoff_pos M L omega.val, ?_⟩
    have hfun : anchoredCutoff M L omega.val =
        fun x ↦ Real.exp (anchoredPartialSumField omega.val L x) :=
      funext (anchoredCutoff_eq_exp_field M L omega.val)
    rw [hfun]
    exact linearGrowth_exp_of_logGradient (anchoredPartialSumField omega.val L) hC
      (fun x ↦ hpartial x L)

/-- Reversible conservativity follows from the weak resolvent characterization
for all three coefficient families, without a smallness assumption. -/
theorem ae_reversible_family_conservative {d : ℕ} (M : GMCModel d) :
    ∀ᵐ omega ∂(anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure,
      ∀ b : Vec d → ℝ,
        (b = aAnchored M omega ∨
          (∃ L : ℕ, b = aCutoff M L omega.val) ∨
          (∃ L : ℕ, b = anchoredCutoff M L omega.val)) →
        ∀ (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu)),
          IsWeakEllipticResolvent b b D → (D.fellerKernelSemigroup hdense).IsConservative := by
  filter_upwards [ae_reversible_family_linearGrowth M] with omega homega
  obtain ⟨K, hK, hfamily⟩ := homega
  intro b hb D hdense hD
  obtain ⟨hc, hpos, hgrowth⟩ := hfamily b hb
  exact isConservative_of_weakResolvent_linearGrowth
    (Section7Clock.reversibleCubeBounds hc.continuous hpos) hc hc.continuous
    D hdense hD (fun x ↦ (hpos x).le) hK hgrowth

/-- In the small-parameter regime, every coefficient also has linear
growth for the divergence equation. -/
theorem ae_divergence_family_linearGrowth {d : ℕ} (M : GMCModel d)
    (hdelta : M.delta ≤ anchoredDelta0 d) :
    ∀ᵐ omega ∂(anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure,
      ∀ b : Vec d → ℝ,
        (b = aAnchored M omega ∨
          (∃ L : ℕ, b = aCutoff M L omega.val) ∨
          (∃ L : ℕ, b = anchoredCutoff M L omega.val)) →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
          euclideanNorm (euclideanGradient b x) + b x ≤ K * (1 + ‖x‖) := by
  filter_upwards [ae_anchored_growth_clauses M hdelta (measurableSet_anchoredC11GoodSet d)
    (measure_anchoredC11GoodSet_eq_one M)] with omega homega
  obtain ⟨hC, hpoly, hlog⟩ := homega
  have hcoeff : ∀ L : WithTop ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
      euclideanNorm (euclideanGradient (coefficientAt M L omega) x) +
        coefficientAt M L omega x ≤ K * (1 + ‖x‖) := by
    intro L
    obtain ⟨K, hK, _, hdiv⟩ := exists_linearGrowth_of_clauses M L omega hC hpoly hlog
    exact ⟨K, hK, fun x ↦ by simpa only [mul_one] using hdiv x⟩
  rintro b (rfl | ⟨L, rfl⟩ | ⟨L, rfl⟩)
  · exact hcoeff ⊤
  · exact hcoeff (L : WithTop ℕ)
  · obtain ⟨K, hK, hlinear⟩ := hcoeff (L : WithTop ℕ)
    let s := (aCutoff M L omega.val 0)⁻¹
    have hs : 0 < s := inv_pos.mpr (aCutoff_pos M L omega.val 0)
    refine ⟨s * K, mul_nonneg hs.le hK, ?_⟩
    rw [anchoredCutoff_eq_inv_origin_mul M omega.val L]
    exact divergence_linearGrowth_pos_mul
      ((contDiff_one_aCutoff M L omega.val).differentiable (by norm_num)) hs hlinear

/-- Divergence conservativity follows from the same resolvent criterion when
the model parameter satisfies the deterministic growth threshold. -/
theorem ae_divergence_family_conservative {d : ℕ} (M : GMCModel d)
    (hdelta : M.delta ≤ anchoredDelta0 d) :
    ∀ᵐ omega ∂(anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure,
      ∀ b : Vec d → ℝ,
        (b = aAnchored M omega ∨
          (∃ L : ℕ, b = aCutoff M L omega.val) ∨
          (∃ L : ℕ, b = anchoredCutoff M L omega.val)) →
        ∀ (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu)),
          IsWeakEllipticResolvent b (fun _ ↦ (1 : ℝ)) D →
            (D.fellerKernelSemigroup hdense).IsConservative := by
  filter_upwards [ae_reversible_family_linearGrowth M,
    ae_divergence_family_linearGrowth M hdelta] with omega hregular hdiv
  obtain ⟨_, _, hfamily⟩ := hregular
  intro b hb D hdense hD
  obtain ⟨hc, hpos, _⟩ := hfamily b hb
  obtain ⟨K, hK, hgrowth⟩ := hdiv b hb
  exact isConservative_of_weakResolvent_linearGrowth
    (Section7Clock.divergenceCubeBounds hc.continuous hpos) hc continuous_const
    D hdense hD (fun x ↦ (hpos x).le) hK
    (fun x ↦ by simpa only [mul_one] using hgrowth x)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
