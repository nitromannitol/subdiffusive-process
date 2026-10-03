module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderKilled
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderUniformBoundedness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKMassiveHolder

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKOperatorHalf
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderKilled
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumCarrier
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderContinuous
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderUniformBoundedness
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderRegularity

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
  {U : Set (Vec d)}

/-- Continuity upgrades the positive almost-everywhere coefficient lower bound
to positivity at every point of an open set. -/
theorem pos_of_continuousOn_of_coefficientOn (hU : IsOpen U)
    (hc : ContinuousOn c U) (hcoeff : CoefficientOn U c) :
    ∀ x ∈ U, 0 < c x := by
  obtain ⟨_, lo, hi, hlo, hb⟩ := hcoeff
  have hneg : ∀ x ∈ U, -c x ≤ -lo :=
    continuousOn_le_of_ae_restrict volume U hU (fun x ↦ -c x) hc.neg (-lo)
      (hb.mono fun _ hx ↦ neg_le_neg hx.1)
  intro x hx
  exact hlo.trans_le (neg_le_neg_iff.mp (hneg x hx))

section Killed

variable (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
  (hU : IsOpen U) (hUb : Bornology.IsBounded U)
  [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
  {s : ℝ} (hs : 0 < s)

/-- A qualitative Hölder estimate for each output is sufficient for all the
fields of the killed resolvent regularity datum. The exponent is chosen before
the datum; uniform boundedness supplies the common Hölder constant. -/
theorem exists_resolventRegularityDatum_of_qualitative_holder (N : ℕ) {C : ℝ}
    (hsup : ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
      ∀ᵐ x ∂((weightedMeasure rho).restrict U),
        |(((killedResolventLp hD hU hUb s hs) ^ N) f) x| ≤ C * ‖f‖)
    (hreg : ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
      ∃ w : Vec d → ℝ, ContinuousOn w U ∧
        (fun x ↦ (((killedResolventLp hD hU hUb s hs) ^ N) f) x)
          =ᵐ[(weightedMeasure rho).restrict U] w ∧
        ∀ K : Set (Vec d), K ⊆ U → IsCompact K → ∃ Ck : ℝ,
          ∀ x ∈ K, ∀ y ∈ K, |w x - w y| ≤ Ck * dist x y ^ ((1 : ℝ) / 2)) :
    ∃ D : ResolventRegularityDatum ((weightedMeasure rho).restrict U) U,
      D.semigroup = (fun t => killedLp hD hD.1 hU hUb (Real.toNNReal t)) ∧
      D.resolvent = (killedResolventLp hD hU hUb s hs) ^ N ∧
      D.smoothing = rrkSmoothing s N (killedResolventLp hD hU hUb s hs) := by
  have hcompl : ((weightedMeasure rho).restrict U) Uᶜ = 0 := by
    rw [Measure.restrict_apply hU.measurableSet.compl, Set.compl_inter_self]
    exact measure_empty
  have hsupp := fullSupportOn_weightedMeasure_restrict hU
    (coefficientOn_of_localDiffusion hD hUb)
  obtain ⟨g, hgae, hgpt⟩ := exists_repr_of_continuousOn_representative hU hsupp hcompl
    ((killedResolventLp hD hU hUb s hs) ^ N) hsup
    (fun f ↦ by
      obtain ⟨w, hwc, hwae, _⟩ := hreg f
      exact ⟨w, hwc, hwae⟩)
  refine exists_resolventRegularityDatum_of_holder_repr (hD := hD) (hU := hU) (hUb := hUb)
    (hs := hs) hD.1 N g hgae (fun K hKU hK ↦ ?_)
  obtain ⟨Ck, _, hCk⟩ := exists_norm_repr_sub_le_of_holder_representative hgpt hKU
    (fun f ↦ by
      obtain ⟨w, hwc, hwae, hw⟩ := hreg f
      exact ⟨w, hwc, hwae, hw K hKU hK⟩)
  exact ⟨Ck, 1 / 2, by norm_num, hCk⟩

/-- Qualitative Hölder regularity gives existence of the complete datum. -/
theorem resolventRegularityDatum_of_qualitative_holder (N : ℕ) {C : ℝ}
    (hsup : ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
      ∀ᵐ x ∂((weightedMeasure rho).restrict U),
        |(((killedResolventLp hD hU hUb s hs) ^ N) f) x| ≤ C * ‖f‖)
    (hreg : ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
      ∃ w : Vec d → ℝ, ContinuousOn w U ∧
        (fun x ↦ (((killedResolventLp hD hU hUb s hs) ^ N) f) x)
          =ᵐ[(weightedMeasure rho).restrict U] w ∧
        ∀ K : Set (Vec d), K ⊆ U → IsCompact K → ∃ Ck : ℝ,
          ∀ x ∈ K, ∀ y ∈ K, |w x - w y| ≤ Ck * dist x y ^ ((1 : ℝ) / 2)) :
    Nonempty (ResolventRegularityDatum ((weightedMeasure rho).restrict U) U) := by
  obtain ⟨D, _⟩ := exists_resolventRegularityDatum_of_qualitative_holder
    hD hU hUb hs N hsup hreg
  exact ⟨D⟩

/-- One extra resolvent application after a smoothing power supplies bounded
forcing and a bounded `H¹₀` solution, with their actual almost-everywhere
identification with the killed operator power. -/
theorem exists_bounded_massive_representative_pow_succ (N : ℕ) {C : ℝ}
    (hC : 0 ≤ C)
    (hsup : ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
      ∀ᵐ x ∂((weightedMeasure rho).restrict U),
        |(((killedResolventLp hD hU hUb s hs) ^ N) f) x| ≤ C * ‖f‖)
    (f : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    ∃ u : H10Function U,
      (fun x ↦ (((killedResolventLp hD hU hUb s hs) ^ (N + 1)) f) x)
        =ᵐ[(weightedMeasure rho).restrict U] u.toH1Function.toFun ∧
      IsMassiveWeakSolutionOn c rho s⁻¹ U u.toH1Function
        (fun x ↦ s⁻¹ * (((killedResolventLp hD hU hUb s hs) ^ N) f) x) ∧
      (∀ᵐ x ∂(volume.restrict U), |u.toH1Function.toFun x| ≤ C * ‖f‖) ∧
      (∀ᵐ x ∂(volume.restrict U),
        |s⁻¹ * (((killedResolventLp hD hU hUb s hs) ^ N) f) x| ≤
          s⁻¹ * (C * ‖f‖)) := by
  let R := killedResolventLp hD hU hUb s hs
  have hcoeff : CoefficientOn U rho := coefficientOn_of_localDiffusion hD hUb
  have hAc := volume_restrict_absolutelyContinuous_weightedMeasure_restrict
    hU.measurableSet hcoeff
  obtain ⟨u, hueq, hu⟩ := hD.2.2 U hU hUb s hs (⇑((R ^ N) f)) (Lp.memLp _)
  have hpow : (R ^ (N + 1)) f = R ((R ^ N) f) := by
    rw [pow_succ']
    rfl
  have hae : (fun x ↦ ((R ^ (N + 1)) f) x)
      =ᵐ[(weightedMeasure rho).restrict U] u.toH1Function.toFun := by
    rw [hpow]
    exact (killedResolventLp_coeFn ((R ^ N) f)).trans (Filter.EventuallyEq.symm hueq)
  have hpow' : (R ^ (N + 1)) f = (R ^ N) (R f) := by
    rw [pow_succ]
    rfl
  have hnorm : ‖R f‖ ≤ ‖f‖ := by
    calc
      ‖R f‖ ≤ ‖R‖ * ‖f‖ := R.le_opNorm f
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
        (norm_killedResolventLp_le (hD := hD) (hU := hU) (hUb := hUb)
          (s := s) (hs := hs)) (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  refine ⟨u, hae, hu, ?_, ?_⟩
  · have hb := hsup (R f)
    rw [← hpow'] at hb
    filter_upwards [hae.filter_mono hAc.ae_le, hb.filter_mono hAc.ae_le]
      with x hx hbx
    rw [← hx]
    exact hbx.trans (mul_le_mul_of_nonneg_left hnorm hC)
  · filter_upwards [(hsup f).filter_mono hAc.ae_le] with x hx
    rw [abs_mul, abs_of_pos (inv_pos.mpr hs)]
    exact mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hs.le)

/-- Continuous elliptic coefficients and any smoothing resolvent power supply
the complete regularity datum on an arbitrary bounded open carrier. One further
resolvent application gives bounded forcing, and Banach–Steinhaus makes the
interior Hölder bounds uniform over all `L²` data. -/
theorem exists_resolventRegularityDatum_of_continuousOn_of_ae_sup_bound
    [NeZero d] (hd : 2 ≤ d) (hc : ContinuousOn c U) (N : ℕ) {C : ℝ}
    (hC : 0 ≤ C)
    (hsup : ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
      ∀ᵐ x ∂((weightedMeasure rho).restrict U),
        |(((killedResolventLp hD hU hUb s hs) ^ N) f) x| ≤ C * ‖f‖) :
    ∃ D : ResolventRegularityDatum ((weightedMeasure rho).restrict U) U,
      D.semigroup = (fun t => killedLp hD hD.1 hU hUb (Real.toNNReal t)) ∧
      D.resolvent = (killedResolventLp hD hU hUb s hs) ^ (N + 1) ∧
      D.smoothing = rrkSmoothing s (N + 1) (killedResolventLp hD hU hUb s hs) := by
  have hrho := RRKDatumCarrier.coefficientOn_of_localDiffusion hD hUb
  have hcCoeff : CoefficientOn U c := coefficientOn_mono subset_closure
    (hD.2.1 (closure U) hUb.isCompact_closure).1
  have hcpos := pos_of_continuousOn_of_coefficientOn hU hc hcCoeff
  obtain ⟨hrhoMeas, lo, hi, hlo, hb⟩ := hrho
  have hrhoBdd : ∀ᵐ x ∂(volume.restrict U), |rho x| ≤ hi :=
    hb.mono fun x hx => (abs_of_nonneg (hlo.le.trans hx.1)).trans_le hx.2
  have hAc := weightedMeasure_restrict_absolutelyContinuous_volume_restrict
    (rho := rho) hU.measurableSet
  have hbounded := exists_bounded_massive_representative_pow_succ hD hU hUb hs N hC hsup
  have hsup' : ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
      ∀ᵐ x ∂((weightedMeasure rho).restrict U),
        |(((killedResolventLp hD hU hUb s hs) ^ (N + 1)) f) x| ≤ C * ‖f‖ := by
    intro f
    obtain ⟨u, hueq, _, huBound, _⟩ := hbounded f
    filter_upwards [hueq, huBound.filter_mono hAc.ae_le] with x hx hbx
    rwa [hx]
  apply exists_resolventRegularityDatum_of_qualitative_holder hD hU hUb hs (N + 1) hsup'
  intro f
  obtain ⟨u, hueq, hu, huBound, hfBound⟩ := hbounded f
  have hfVol : MemL2On U
      (fun x => s⁻¹ * (((killedResolventLp hD hU hUb s hs) ^ N) f) x) :=
    (memLp_volume_restrict_of_weighted hU.measurableSet
      (RRKDatumCarrier.coefficientOn_of_localDiffusion hD hUb) (Lp.memLp _)).const_mul _
  obtain ⟨hcont, hae, hholder⟩ :=
    holder_euclideanBallAverageRepresentative_of_bounded_massiveWeakSolution hd hU
      hc hcpos hrhoMeas hrhoBdd hfVol hfBound huBound hu
  exact ⟨_, hcont, hueq.trans (hae.filter_mono hAc.ae_le).symm, hholder⟩

/-- Existence of the complete datum from continuous coefficients and a
smoothing power. -/
theorem resolventRegularityDatum_of_continuousOn_of_ae_sup_bound
    [NeZero d] (hd : 2 ≤ d) (hc : ContinuousOn c U) (N : ℕ) {C : ℝ}
    (hC : 0 ≤ C)
    (hsup : ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
      ∀ᵐ x ∂((weightedMeasure rho).restrict U),
        |(((killedResolventLp hD hU hUb s hs) ^ N) f) x| ≤ C * ‖f‖) :
    Nonempty (ResolventRegularityDatum ((weightedMeasure rho).restrict U) U) := by
  obtain ⟨D, _⟩ := exists_resolventRegularityDatum_of_continuousOn_of_ae_sup_bound
    hD hU hUb hs hd hc N hC hsup
  exact ⟨D⟩

include hD hU hUb hs in
/-- On a bounded convex carrier the proved Sobolev iteration supplies the
smoothing power, so no regularity assumption on resolvent outputs remains. -/
theorem resolventRegularityDatum_of_continuousOn_of_sobolev
    [NeZero d] (hd : 2 ≤ d) (hc : ContinuousOn c U)
    (hUcvx : IsOpenBoundedConvexDomain U)
    (hm0 : (weightedMeasure rho) U ≠ 0) (hmtop : (weightedMeasure rho) U ≠ ∞)
    {p0 A F : ℝ} (hp0 : 2 < p0) (hA : 1 ≤ A) (hF : 0 < F)
    (hSob : SobolevAssumption c rho U p0 A F) :
    Nonempty (ResolventRegularityDatum ((weightedMeasure rho).restrict U) U) := by
  obtain ⟨N, _, C, hC, hsup⟩ :=
    exists_ae_sup_bound_killedResolventLp_pow (hD := hD) (hU := hU) (hUb := hUb)
      (hs := hs) hUcvx hm0 hmtop hp0 hA hF hSob
  exact resolventRegularityDatum_of_continuousOn_of_ae_sup_bound hD hU hUb hs
    hd hc N hC.le hsup

end Killed

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderRegularity
