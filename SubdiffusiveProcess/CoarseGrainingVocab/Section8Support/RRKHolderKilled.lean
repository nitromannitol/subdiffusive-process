module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderRiesz
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumUltracontractive
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDatumFields
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderContinuous

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDatumFields
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumCarrier
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumUltracontractive
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderRiesz
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderContinuous
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKOperatorHalf
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderKilled

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} {U : Set (Vec d)}

/-! ## An almost-everywhere sup bound out of an `L^∞` seminorm bound -/

/-- An `L^∞` seminorm bound is an almost-everywhere pointwise bound. -/
theorem ae_abs_le_of_eLpNorm_top {X : Type*} [MeasurableSpace X] {nu : Measure X}
    {g : X → ℝ} {B : ℝ} (hB : 0 ≤ B) (h : eLpNorm g ∞ nu ≤ ENNReal.ofReal B) :
    ∀ᵐ x ∂nu, |g x| ≤ B := by
  have hg : AEStronglyMeasurable g nu :=
    aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
  rw [eLpNorm_exponent_top hg] at h
  filter_upwards [ae_le_eLpNormEssSup (f := g) (μ := nu)] with x hx
  have hle : ENNReal.ofReal |g x| ≤ ENNReal.ofReal B := by
    rw [← Real.enorm_eq_ofReal_abs]
    exact hx.trans h
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hle

/-! ## The `L²` operator power is the raw iterate -/

section Killed

variable {hD : LocalDiffusion c rho law} [IsMarkovKernel law] {hU : IsOpen U}
  {hUb : Bornology.IsBounded U} [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
  {s : ℝ} {hs : 0 < s}

include hD hU hUb hs in
/-- The raw killed resolvent depends only on the almost-everywhere class of its
datum: this is `kernelIntegral_congr_ae` for the occupation kernel, whose
subinvariance is `resolventKernel_subinvariant`. -/
theorem killedResolvent_congr_ae {g1 g2 : Vec d → ℝ}
    (hg : g1 =ᵐ[(weightedMeasure rho).restrict U] g2)
    (h1 : Integrable g1 ((weightedMeasure rho).restrict U))
    (h2 : Integrable g2 ((weightedMeasure rho).restrict U)) :
    killedResolvent law U s g1 =ᵐ[(weightedMeasure rho).restrict U]
      killedResolvent law U s g2 := by
  have hsub := resolventKernel_subinvariant hD hU hUb s hs
  have e1 := resolventKernel_integral_ae law U hU s hs _ hsub g1 h1
  have e2 := resolventKernel_integral_ae law U hU s hs _ hsub g2 h2
  exact e1.symm.trans ((kernelIntegral_congr_ae hsub hg).trans e2)



theorem coeFn_killedResolventLp_pow (N : ℕ)
    (f : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    ⇑(((killedResolventLp hD hU hUb s hs) ^ N) f)
      =ᵐ[(weightedMeasure rho).restrict U] (killedResolvent law U s)^[N] ⇑f := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hint : ∀ F : Lp ℝ 2 ((weightedMeasure rho).restrict U),
          Integrable (⇑F) ((weightedMeasure rho).restrict U) :=
        fun F => (Lp.memLp F).integrable (by norm_num)
      have hiter : Integrable ((killedResolvent law U s)^[N] ⇑f)
          ((weightedMeasure rho).restrict U) :=
        (hint (((killedResolventLp hD hU hUb s hs) ^ N) f)).congr ih
      have hstep := killedResolventLp_coeFn (hD := hD) (hU := hU) (hUb := hUb)
        (s := s) (hs := hs) (((killedResolventLp hD hU hUb s hs) ^ N) f)
      have hpow : ((killedResolventLp hD hU hUb s hs) ^ (N + 1)) f
          = killedResolventLp hD hU hUb s hs ((((killedResolventLp hD hU hUb s hs) ^ N)) f) := by
        rw [pow_succ']
        rfl
      rw [hpow, Function.iterate_succ_apply']
      exact hstep.trans
        (killedResolvent_congr_ae (hD := hD) (hU := hU) (hUb := hUb) (hs := hs) ih
          (hint _) hiter)

/-! ## The almost-everywhere sup bound for the `L²` operator power -/

/-- **The `L² → L^∞` half of (RRK), read pointwise almost everywhere for the `L²`
operator power.**  This is `RRKDatumUltracontractive.exists_rrk_sup_bound`
transported along `coeFn_killedResolventLp_pow` and converted from an `L^∞`
seminorm bound to an almost-everywhere pointwise bound. -/
theorem exists_ae_sup_bound_killedResolventLp_pow
    (hUcvx : IsOpenBoundedConvexDomain U)
    (hm0 : (weightedMeasure rho) U ≠ 0) (hmtop : (weightedMeasure rho) U ≠ ∞)
    {p0 A Fs : ℝ} (hp0 : 2 < p0) (hA : 1 ≤ A) (hFs : 0 < Fs)
    (hSob : SobolevAssumption c rho U p0 A Fs) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 < C ∧ ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
      ∀ᵐ x ∂((weightedMeasure rho).restrict U),
        |(((killedResolventLp hD hU hUb s hs) ^ N) f) x| ≤ C * ‖f‖ := by
  obtain ⟨N, hN, C, hC, hbd⟩ :=
    exists_rrk_sup_bound hD hUcvx hm0 hmtop hp0 hA hFs hs hSob
  refine ⟨N, hN, C, hC, fun f => ?_⟩
  have h1 := hbd (⇑f) (Lp.memLp f)
  have h2 : eLpNorm (⇑f) 2 ((weightedMeasure rho).restrict U) = ENNReal.ofReal ‖f‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
  have h3 : eLpNorm (⇑(((killedResolventLp hD hU hUb s hs) ^ N) f)) ∞
      ((weightedMeasure rho).restrict U) ≤ ENNReal.ofReal (C * ‖f‖) := by
    rw [eLpNorm_congr_ae (coeFn_killedResolventLp_pow (hD := hD) (hU := hU) (hUb := hUb)
      (hs := hs) N f), ENNReal.ofReal_mul hC.le]
    rw [h2] at h1
    exact h1
  exact ae_abs_le_of_eLpNorm_top (by positivity) h3

/-! ## The `repr` and `resolvent_apply_ae` fields -/

/-- **The Riesz representative of evaluation at `x` of a power of the killed
resolvent.**

`RRKDatumUltracontractive.exists_rrk_sup_bound` gives the `L² → L^∞` half of
(RRK); `RRKHolderRiesz.exists_repr_of_ae_bound` turns it into an `L²`-valued
kernel.  The two conclusions are the fields `repr` and `resolvent_apply_ae` of
`HeatKernelRegularity.ResolventRegularityDatum` for
`resolvent = (killedResolventLp)^N`.

No Hölder estimate is used or produced: `holder_repr` is untouched. -/
theorem exists_repr_killedResolventLp_pow
    (hUcvx : IsOpenBoundedConvexDomain U)
    (hm0 : (weightedMeasure rho) U ≠ 0) (hmtop : (weightedMeasure rho) U ≠ ∞)
    {p0 A Fs : ℝ} (hp0 : 2 < p0) (hA : 1 ≤ A) (hFs : 0 < Fs)
    (hSob : SobolevAssumption c rho U p0 A Fs) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 < C ∧
      ∃ g : Vec d → Lp ℝ 2 ((weightedMeasure rho).restrict U),
        (∀ x, ‖g x‖ ≤ C) ∧
        ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
          (fun x => (((killedResolventLp hD hU hUb s hs) ^ N) f) x)
            =ᵐ[(weightedMeasure rho).restrict U] fun x => ⟪g x, f⟫ := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  obtain ⟨N, hN, C, hC, hae⟩ :=
    exists_ae_sup_bound_killedResolventLp_pow (hD := hD) (hU := hU) (hUb := hUb) (hs := hs)
      hUcvx hm0 hmtop hp0 hA hFs hSob
  obtain ⟨g, hgnorm, hgrepr⟩ :=
    exists_repr_of_ae_bound (mu := (weightedMeasure rho).restrict U)
      ((killedResolventLp hD hU hUb s hs) ^ N) hC.le hae
  exact ⟨N, hN, C, hC, g, hgnorm, hgrepr⟩

/-! ## The datum, modulo the Hölder clause -/

/-- **The (RRK) datum for the killed forms, from the Hölder clause alone.**

Every field of `ResolventRegularityDatum` other than `holder_repr` is supplied
here: the carrier fields from `RRKDatumCarrier`, the nine operator fields from
`KilledDatumFields.rrk_datum_fields_killed`, and `repr` / `resolvent_apply_ae`
from `exists_repr_killedResolventLp_pow`.  The hypothesis `hholder` is exactly the
manuscript's `‖g_x - g_y‖_{L²} ≤ C_K |x-y|^α` on compact subsets of the carrier,
i.e. the Hölder half of (RRK) for the representative constructed above. The
conclusion retains the identities of the semigroup, resolvent and smoothing
operator for downstream kernel and time-derivative estimates. -/
theorem exists_resolventRegularityDatum_of_holder_repr
    (hSM : StrongMarkov law) (N : ℕ)
    (g : Vec d → Lp ℝ 2 ((weightedMeasure rho).restrict U))
    (hrepr : ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
      (fun x => (((killedResolventLp hD hU hUb s hs) ^ N) f) x)
        =ᵐ[(weightedMeasure rho).restrict U] fun x => ⟪g x, f⟫)
    (hholder : ∀ K : Set (Vec d), K ⊆ U → IsCompact K → ∃ C a : ℝ, 0 < a ∧
      ∀ x ∈ K, ∀ y ∈ K, ‖g x - g y‖ ≤ C * dist x y ^ a) :
    ∃ D : ResolventRegularityDatum ((weightedMeasure rho).restrict U) U,
      D.semigroup = (fun t => killedLp hD hSM hU hUb (Real.toNNReal t)) ∧
      D.resolvent = (killedResolventLp hD hU hUb s hs) ^ N ∧
      D.smoothing = rrkSmoothing s N (killedResolventLp hD hU hUb s hs) := by
  obtain ⟨hsymmR, hinjR, hsymmB, hRB, hcontB, hsymmP, hPP, hPnn, hPone⟩ :=
    rrk_datum_fields_killed (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
      (s := s) (hs := hs) N
  refine ⟨{
    isOpen_carrier := hU
    measure_compl := by
      rw [Measure.restrict_apply hU.measurableSet.compl, Set.compl_inter_self]
      exact measure_empty
    fullSupport := fullSupportOn_weightedMeasure_restrict hU
      (coefficientOn_of_localDiffusion hD hUb)
    semigroup := fun t => killedLp hD hSM hU hUb (Real.toNNReal t)
    resolvent := (killedResolventLp hD hU hUb s hs) ^ N
    smoothing := rrkSmoothing s N (killedResolventLp hD hU hUb s hs)
    repr := g
    isSymmetricOp_semigroup := hsymmP
    semigroup_comp := hPP
    semigroup_nonneg := hPnn
    semigroup_le_one := hPone
    isSymmetricOp_resolvent := hsymmR
    injective_resolvent := hinjR
    isSymmetricOp_smoothing := hsymmB
    resolvent_comp_smoothing := hRB
    continuousOn_smoothing := hcontB
    resolvent_apply_ae := hrepr
    holder_repr := hholder }, rfl, rfl, rfl⟩

/-- Existence of the killed regularity datum, forgetting the operator identities
retained by `exists_resolventRegularityDatum_of_holder_repr`. -/
theorem resolventRegularityDatum_of_holder_repr
    (hSM : StrongMarkov law) (N : ℕ)
    (g : Vec d → Lp ℝ 2 ((weightedMeasure rho).restrict U))
    (hrepr : ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
      (fun x => (((killedResolventLp hD hU hUb s hs) ^ N) f) x)
        =ᵐ[(weightedMeasure rho).restrict U] fun x => ⟪g x, f⟫)
    (hholder : ∀ K : Set (Vec d), K ⊆ U → IsCompact K → ∃ C a : ℝ, 0 < a ∧
      ∀ x ∈ K, ∀ y ∈ K, ‖g x - g y‖ ≤ C * dist x y ^ a) :
    Nonempty (ResolventRegularityDatum ((weightedMeasure rho).restrict U) U) := by
  obtain ⟨D, _⟩ := exists_resolventRegularityDatum_of_holder_repr
    (hD := hD) (hU := hU) (hUb := hUb) (hs := hs) hSM N g hrepr hholder
  exact ⟨D⟩



theorem resolventRegularityDatum_of_rrk
    (hSM : StrongMarkov law) (N : ℕ) {C : ℝ}
    (hsup : ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
      ∀ᵐ x ∂((weightedMeasure rho).restrict U),
        |(((killedResolventLp hD hU hUb s hs) ^ N) f) x| ≤ C * ‖f‖)
    (hRRK : ∀ K : Set (Vec d), K ⊆ U → IsCompact K → ∃ Ck a : ℝ, 0 ≤ Ck ∧ 0 < a ∧
      ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U), ∃ w : Vec d → ℝ,
        ContinuousOn w U ∧
        (fun x => (((killedResolventLp hD hU hUb s hs) ^ N) f) x)
          =ᵐ[(weightedMeasure rho).restrict U] w ∧
        ∀ x ∈ K, ∀ y ∈ K, |w x - w y| ≤ Ck * ‖f‖ * dist x y ^ a) :
    Nonempty (ResolventRegularityDatum ((weightedMeasure rho).restrict U) U) := by
  have hcompl : ((weightedMeasure rho).restrict U) Uᶜ = 0 := by
    rw [Measure.restrict_apply hU.measurableSet.compl, Set.compl_inter_self]
    exact measure_empty
  have hsupp : FullSupportOn ((weightedMeasure rho).restrict U) U :=
    fullSupportOn_weightedMeasure_restrict hU (coefficientOn_of_localDiffusion hD hUb)
  -- the empty compact set already supplies a continuous representative for every datum
  obtain ⟨Ck0, a0, -, -, hempty⟩ := hRRK ∅ (Set.empty_subset U) isCompact_empty
  obtain ⟨g, hgae, hgpt⟩ :=
    exists_repr_of_continuousOn_representative hU hsupp hcompl
      ((killedResolventLp hD hU hUb s hs) ^ N) hsup
      (fun f => by
        obtain ⟨w, hw1, hw2, -⟩ := hempty f
        exact ⟨w, hw1, hw2⟩)
  refine resolventRegularityDatum_of_holder_repr (hD := hD) (hU := hU) (hUb := hUb)
    (hs := hs) hSM N g hgae (fun K hKU hKcpt => ?_)
  obtain ⟨Ck, a, hCk, ha, hK⟩ := hRRK K hKU hKcpt
  exact ⟨Ck, a, ha, norm_repr_sub_le hgpt hKU hCk hK⟩

end Killed

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderKilled
