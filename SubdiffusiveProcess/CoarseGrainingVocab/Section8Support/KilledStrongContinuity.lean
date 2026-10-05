module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledTestFunctions

@[expose] public section

/-!
# Strong continuity of the killed `L²` semigroup

`KilledSemigroupLp.lean` builds the killed transition semigroup `P_t` as a family of
contractions of `L²(U, ρ dx)` and proves every clause of
`MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup` *except* continuity of the
orbits `t ↦ P_t F`.  This file proves that last clause, `continuous_killedLp`, from
`Section9SupportInput.LocalDiffusion` alone.

## The argument

Write `R_s` for the killed resolvent operator of `KilledResolventLp.lean` and `μ` for
`(weightedMeasure rho).restrict U`.

1. `⟪P_t F, F⟫ = ‖P_{t/2} F‖²` (symmetry plus the semigroup law), so `t ↦ ⟪P_t F, F⟫` is
   nonincreasing, bounded by `‖F‖²` and nonnegative (`inner_killedLp_self` and friends), and
   `‖P_t F − F‖² ≤ 2(‖F‖² − ⟪P_t F, F⟫)` (`norm_sub_sq_le`).  Hence *continuity at `t = 0`*
   is the whole content, and it upgrades to continuity everywhere by
   `‖P_{m+h} F − P_m F‖ ≤ ‖P_h F − F‖` (`continuous_killedLp_of_tendsto_zero`).
2. Since `‖P_t‖ ≤ 1`, the set of `F` with a continuous orbit is closed, so it is enough to
   treat a dense set of initial data (`continuous_killedLp_of_denseRange`).  We take the
   smooth compactly supported test functions, dense by
   `KilledTestFunctions.denseRange_testToLpWeighted`, and bounded continuous — the form in
   which the development's Laplace identities are available.
3. `LocalResolventIteration.killedResolvent_pairing_eq_expMeasure` writes `⟪R_s F, F⟫` as the
   average of `t ↦ ⟪P_t F, F⟫` against the exponential law of mean `s`
   (`inner_killedResolventLp_eq_integral`).  That law charges `[s, ∞)` with probability
   `e⁻¹ ≥ 1/4`, so monotonicity gives the Abel step
   `‖F‖² − ⟪P_s F, F⟫ ≤ 4(‖F‖² − ⟪R_s F, F⟫)`
   (`inner_killedLp_ge_of_inner_killedResolventLp`).
4. For a test function `φ` with `u = R_s φ`, testing `IsMassiveWeakSolutionOn` against
   `KilledTestFunctions.h10OfTest φ` gives `⟪R_s φ, φ⟫ = ‖φ‖² − s ∫_U c ∇u·∇φ`, and testing
   it against `u` gives `s ∫_U c |∇u|² ≤ ⟪R_s φ, φ⟫ ≤ ‖φ‖²`.  The parametrised Young
   inequality `∫_U c ∇u·∇φ ≤ (λ/2) ∫_U c |∇u|² + (1/2λ) ∫_U c |∇φ|²` — proved pointwise,
   which avoids any square root — then yields
   `‖φ‖² ≤ ⟪R_s φ, φ⟫ + (λ/2)‖φ‖² + (s/2λ) E_c(φ)`
   (`normSq_le_inner_killedResolventLp_test`).  Choosing `λ` small and then `s` small makes
   the right-hand error arbitrarily small, which with step 3 is continuity at `t = 0` for
   test data.

The only place the diffusion enters is step 4; steps 1–3 are semigroup bookkeeping.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledTestFunctions
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity

/-! ## Test functions as bounded continuous functions -/

section Test

variable {d : ℕ} {rho : Vec d → ℝ} {U : Set (Vec d)}

/-- A smooth compactly supported test function as a bounded continuous function. -/
def testBCF (φ : H1WeakTestFunction U) : Vec d →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (φ : Vec d → ℝ) φ.smooth.continuous
    (Classical.choose
      (φ.smooth.continuous.bounded_above_of_compact_support φ.compactSupport))
    (Classical.choose_spec
      (φ.smooth.continuous.bounded_above_of_compact_support φ.compactSupport))

@[simp] theorem coe_testBCF (φ : H1WeakTestFunction U) :
    (testBCF φ : Vec d → ℝ) = (φ : Vec d → ℝ) := rfl

theorem testToLpWeighted_eq_toLp [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (hUm : MeasurableSet U) (hr : CoefficientOn U rho) (φ : H1WeakTestFunction U) :
    testToLpWeighted hUm hr φ
      = BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ (testBCF φ) := by
  refine Lp.ext ?_
  refine (coeFn_testToLpWeighted hUm hr φ).trans ?_
  exact (BoundedContinuousFunction.coeFn_toLp 2 ((weightedMeasure rho).restrict U) ℝ
    (testBCF φ)).symm

theorem denseRange_testBCF_toLp [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (hUo : IsOpen U) (hUvol : volume U ≠ ⊤) (hr : CoefficientOn U rho) :
    DenseRange (fun φ : H1WeakTestFunction U =>
      BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ (testBCF φ)) := by
  have h := denseRange_testToLpWeighted hUo hUvol hr
  have heq : (fun φ : H1WeakTestFunction U =>
      BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ (testBCF φ))
      = testToLpWeighted hUo.measurableSet hr :=
    funext fun φ => (testToLpWeighted_eq_toLp hUo.measurableSet hr φ).symm
  rw [heq]
  exact h

end Test

/-! ## The energy form: integrability and the parametrised Young inequality -/

section Energy

variable {d : ℕ} {c : Vec d → ℝ} {U : Set (Vec d)}

theorem integrableOn_energy_pairing (hc : CoefficientOn U c) {F G : Vec d → Vec d}
    (hF : MemVectorL2 U F) (hG : MemVectorL2 U G) :
    IntegrableOn (fun x => vecDot (c x • F x) (G x)) U := by
  obtain ⟨hmeas, lo, hi, hlo, hb⟩ := hc
  have hdot : IntegrableOn (fun x => vecDot (F x) (G x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF hG
  have hbound : ∀ᵐ x ∂(volume.restrict U), ‖c x‖ ≤ hi := by
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hlo.le.trans hx.1)]
    exact hx.2
  have := hdot.bdd_mul hmeas hbound
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  exact (vecDot_smul_left _ _ _).symm

theorem vecDot_young {lam : ℝ} (hlam : 0 < lam) (a b : Vec d) :
    vecDot a b ≤ lam / 2 * vecDot a a + 1 / (2 * lam) * vecDot b b := by
  simp only [vecDot, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← sub_nonneg]
  have hid : lam / 2 * (a i * a i) + 1 / (2 * lam) * (b i * b i) - a i * b i
      = (lam * a i - b i) ^ 2 / (2 * lam) := by
    field_simp
    ring
  rw [hid]
  positivity

theorem integral_energy_young (hc : CoefficientOn U c)
    {F G : Vec d → Vec d} (hF : MemVectorL2 U F) (hG : MemVectorL2 U G)
    {lam : ℝ} (hlam : 0 < lam) :
    (∫ x in U, vecDot (c x • F x) (G x))
      ≤ lam / 2 * (∫ x in U, vecDot (c x • F x) (F x))
        + 1 / (2 * lam) * (∫ x in U, vecDot (c x • G x) (G x)) := by
  have hFG := integrableOn_energy_pairing hc hF hG
  have hFF := integrableOn_energy_pairing hc hF hF
  have hGG := integrableOn_energy_pairing hc hG hG
  have hsum : lam / 2 * (∫ x in U, vecDot (c x • F x) (F x))
        + 1 / (2 * lam) * (∫ x in U, vecDot (c x • G x) (G x))
      = ∫ x in U, (lam / 2 * vecDot (c x • F x) (F x)
          + 1 / (2 * lam) * vecDot (c x • G x) (G x)) := by
    rw [integral_add (hFF.const_mul _) (hGG.const_mul _), integral_const_mul, integral_const_mul]
  rw [hsum]
  refine integral_mono_ae hFG ((hFF.const_mul _).add (hGG.const_mul _)) ?_
  obtain ⟨-, lo, hi, hlo, hb⟩ := hc
  filter_upwards [hb] with x hx
  have hcx : 0 ≤ c x := hlo.le.trans hx.1
  have hy := vecDot_young hlam (F x) (G x)
  rw [vecDot_smul_left, vecDot_smul_left, vecDot_smul_left]
  nlinarith [hy, hcx]

end Energy


variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} {U : Set (Vec d)}
  {hD : LocalDiffusion c rho law} {hSM : StrongMarkov law}
  {hU : IsOpen U} {hUb : Bornology.IsBounded U}

variable [IsMarkovKernel law] [IsFiniteMeasure ((weightedMeasure rho).restrict U)]

theorem norm_killedLp_apply_le (t : NNReal)
    (F : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    ‖killedLp hD hSM hU hUb t F‖ ≤ ‖F‖ := by
  simpa using (killedLp hD hSM hU hUb t).le_of_opNorm_le
    (norm_killedLp_le (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) t) F

/-- `⟪P_t F, F⟫ = ‖P_{t/2} F‖²`. -/
theorem inner_killedLp_self (t : NNReal)
    (F : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    ⟪killedLp hD hSM hU hUb t F, F⟫ = ‖killedLp hD hSM hU hUb (t / 2) F‖ ^ 2 := by
  have hsplit : killedLp hD hSM hU hUb t
      = (killedLp hD hSM hU hUb (t / 2)).comp (killedLp hD hSM hU hUb (t / 2)) := by
    rw [← killedLp_add (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb), add_halves]
  rw [hsplit]
  show ⟪killedLp hD hSM hU hUb (t / 2) (killedLp hD hSM hU hUb (t / 2) F), F⟫ = _
  rw [isSymmetricOp_killedLp (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) (t / 2),
    real_inner_self_eq_norm_sq]

theorem inner_killedLp_self_nonneg (t : NNReal)
    (F : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    0 ≤ ⟪killedLp hD hSM hU hUb t F, F⟫ := by
  rw [inner_killedLp_self]
  positivity

theorem inner_killedLp_self_le (t : NNReal)
    (F : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    ⟪killedLp hD hSM hU hUb t F, F⟫ ≤ ‖F‖ ^ 2 := by
  rw [inner_killedLp_self]
  have := norm_killedLp_apply_le (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) (t / 2) F
  nlinarith [norm_nonneg (killedLp hD hSM hU hUb (t / 2) F), norm_nonneg F]

/-- `t ↦ ⟪P_t F, F⟫` is nonincreasing. -/
theorem inner_killedLp_self_antitone {a b : NNReal} (hab : a ≤ b)
    (F : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    ⟪killedLp hD hSM hU hUb b F, F⟫ ≤ ⟪killedLp hD hSM hU hUb a F, F⟫ := by
  rw [inner_killedLp_self, inner_killedLp_self]
  have hb : b / 2 = (b - a) / 2 + a / 2 := by
    rw [← add_div, tsub_add_cancel_of_le hab]
  have hcomp : killedLp hD hSM hU hUb (b / 2) F
      = killedLp hD hSM hU hUb ((b - a) / 2) (killedLp hD hSM hU hUb (a / 2) F) := by
    rw [hb, killedLp_add (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)]
    rfl
  rw [hcomp]
  have := norm_killedLp_apply_le (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
    ((b - a) / 2) (killedLp hD hSM hU hUb (a / 2) F)
  nlinarith [norm_nonneg (killedLp hD hSM hU hUb ((b - a) / 2)
      (killedLp hD hSM hU hUb (a / 2) F)),
    norm_nonneg (killedLp hD hSM hU hUb (a / 2) F)]

/-- `‖P_t F − F‖² ≤ 2(‖F‖² − ⟪P_t F, F⟫)`. -/
theorem norm_sub_sq_le (t : NNReal) (F : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    ‖killedLp hD hSM hU hUb t F - F‖ ^ 2
      ≤ 2 * (‖F‖ ^ 2 - ⟪killedLp hD hSM hU hUb t F, F⟫) := by
  have hexp := @norm_sub_sq_real _ _ _ (killedLp hD hSM hU hUb t F) F
  have hle := norm_killedLp_apply_le (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) t F
  nlinarith [norm_nonneg (killedLp hD hSM hU hUb t F), norm_nonneg F]


/-! ## From continuity at zero to continuity, and the density extension -/

theorem norm_killedLp_shift_sub_le (m h : NNReal)
    (F : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    ‖killedLp hD hSM hU hUb (m + h) F - killedLp hD hSM hU hUb m F‖
      ≤ ‖killedLp hD hSM hU hUb h F - F‖ := by
  have hcomp : killedLp hD hSM hU hUb (m + h) F
      = killedLp hD hSM hU hUb m (killedLp hD hSM hU hUb h F) := by
    rw [killedLp_add (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)]
    rfl
  rw [hcomp, ← ContinuousLinearMap.map_sub]
  exact norm_killedLp_apply_le (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) m _

theorem norm_killedLp_sub_le_of_dist (a b : NNReal)
    (F : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    ∃ h : NNReal, (h : ℝ) = dist a b ∧
      ‖killedLp hD hSM hU hUb a F - killedLp hD hSM hU hUb b F‖
        ≤ ‖killedLp hD hSM hU hUb h F - F‖ := by
  rcases le_total b a with hba | hab
  · refine ⟨a - b, ?_, ?_⟩
    · rw [NNReal.coe_sub hba, NNReal.dist_eq, abs_of_nonneg (by
        have : (b : ℝ) ≤ (a : ℝ) := hba
        linarith)]
    · have := norm_killedLp_shift_sub_le (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
        b (a - b) F
      rwa [add_tsub_cancel_of_le hba] at this
  · refine ⟨b - a, ?_, ?_⟩
    · rw [NNReal.coe_sub hab, NNReal.dist_eq, abs_of_nonpos (by
        have : (a : ℝ) ≤ (b : ℝ) := hab
        linarith)]
      ring
    · have := norm_killedLp_shift_sub_le (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
        a (b - a) F
      rw [add_tsub_cancel_of_le hab] at this
      rw [← norm_neg, neg_sub]
      exact this

/-- Continuity at time zero implies continuity of the whole orbit. -/
theorem continuous_killedLp_of_tendsto_zero
    (F : Lp ℝ 2 ((weightedMeasure rho).restrict U))
    (h0 : Filter.Tendsto (fun t : NNReal => killedLp hD hSM hU hUb t F)
      (nhds 0) (nhds F)) :
    Continuous fun t : NNReal => killedLp hD hSM hU hUb t F := by
  rw [Metric.continuous_iff]
  intro b ε hε
  have h1 : ∀ᶠ t : NNReal in nhds 0, dist (killedLp hD hSM hU hUb t F) F < ε :=
    (Metric.tendsto_nhds.1 h0) ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h1
  refine ⟨δ, hδ, fun a ha => ?_⟩
  obtain ⟨h, hh, hle⟩ := norm_killedLp_sub_le_of_dist (hD := hD) (hSM := hSM) (hU := hU)
    (hUb := hUb) a b F
  have hdist : dist h (0 : NNReal) < δ := by
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg h.coe_nonneg, hh]
    exact ha
  have := hball hdist
  rw [dist_eq_norm] at this ⊢
  exact lt_of_le_of_lt hle this

/-- Orbits are continuous as soon as they are continuous on a dense set of initial data. -/
theorem continuous_killedLp_of_denseRange {ι : Type*}
    (g : ι → Lp ℝ 2 ((weightedMeasure rho).restrict U)) (hdense : DenseRange g)
    (hcont : ∀ i, Continuous fun t : NNReal => killedLp hD hSM hU hUb t (g i))
    (F : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    Continuous fun t : NNReal => killedLp hD hSM hU hUb t F := by
  refine continuous_of_uniform_approx_of_continuous ?_
  intro u hu
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨i, hi⟩ := Metric.denseRange_iff.1 hdense F (ε / 2) (by positivity)
  refine ⟨fun t => killedLp hD hSM hU hUb t (g i), hcont i, fun t => ?_⟩
  refine hsub ?_
  rw [dist_eq_norm, ← ContinuousLinearMap.map_sub]
  refine lt_of_le_of_lt
    (norm_killedLp_apply_le (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) t _) ?_
  rw [← dist_eq_norm]
  exact lt_of_lt_of_le hi (by linarith)


/-! ## The exponential mixing measure -/

theorem expMeasure_ae_pos {r : ℝ} (hr : 0 < r) : ∀ᵐ t ∂(expMeasure r), 0 < t := by
  let : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hzero : (expMeasure r) (Iic 0) = 0 := by
    rw [← ofReal_cdf, cdf_expMeasure_eq hr, ite_eq_left le_rfl]
    simp
  rw [ae_iff]
  have hset : {t : ℝ | ¬ 0 < t} = Iic 0 := by
    ext t; simp [not_lt]
  rw [hset, hzero]

theorem expMeasure_Ioi_toReal_ge {s : ℝ} (hs : 0 < s) :
    (1 / 4 : ℝ) ≤ ((expMeasure s⁻¹) (Ioi s)).toReal := by
  have hr : (0:ℝ) < s⁻¹ := inv_pos.2 hs
  let : IsProbabilityMeasure (expMeasure s⁻¹) := isProbabilityMeasure_expMeasure hr
  have hIic : (expMeasure s⁻¹) (Iic s) = ENNReal.ofReal (1 - Real.exp (-1)) := by
    rw [← ofReal_cdf, cdf_expMeasure_eq hr, ite_eq_left hs.le, inv_mul_cancel₀ hs.ne']
  have hIoi : (expMeasure s⁻¹) (Ioi s) = 1 - ENNReal.ofReal (1 - Real.exp (-1)) := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hIic]
  have he1 : Real.exp (-1) ≤ 1 := by
    rw [Real.exp_le_one_iff]; norm_num
  have he0 : (0:ℝ) < Real.exp (-1) := Real.exp_pos _
  have hle : ENNReal.ofReal (1 - Real.exp (-1)) ≤ 1 := by
    rw [show (1 : ENNReal) = ENNReal.ofReal (1:ℝ) by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [hIoi, ENNReal.toReal_sub_of_le hle (by simp), ENNReal.toReal_ofReal (by linarith)]
  simp only [ENNReal.toReal_one]
  have hexp : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have : (1/4 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    rw [le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    linarith
  linarith

/-! ## The resolvent as an exponential average of the semigroup -/

variable {s : ℝ} {hs : 0 < s}

/-- **The killed resolvent is the exponential time average of the killed semigroup**, in the
`L²` pairing against bounded continuous data. -/
theorem inner_killedResolventLp_eq_integral (f : Vec d →ᵇ ℝ) :
    ⟪killedResolventLp hD hU hUb s hs
        (BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f),
      BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f⟫
      = ∫ t, ⟪killedLp hD hSM hU hUb (Real.toNNReal t)
          (BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f),
        BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f⟫
        ∂(expMeasure s⁻¹) := by
  set mu := (weightedMeasure rho).restrict U with hmu
  rw [inner_killedResolventLp_toLp (hD := hD) (hU := hU) (hUb := hUb) (s := s) (hs := hs) f f,
    killedResolvent_pairing_eq_expMeasure law U hU mu f f s hs]
  refine (integral_congr_ae ?_).symm
  filter_upwards [expMeasure_ae_pos (inv_pos.2 hs)] with t ht
  exact inner_killedLp_toLp (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) ht f f


/-- **The Abel step.**  Because `t ↦ ⟪P_t F, F⟫` is nonincreasing and the exponential mixing
measure of mean `s` charges `[s, ∞)` with probability `e⁻¹ ≥ 1/4`, closeness of the resolvent
pairing to `‖F‖²` forces closeness of the semigroup pairing at time `s`. -/
theorem inner_killedLp_ge_of_inner_killedResolventLp (f : Vec d →ᵇ ℝ) :
    ‖BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f‖ ^ 2
        - ⟪killedLp hD hSM hU hUb (Real.toNNReal s)
            (BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f),
          BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f⟫
      ≤ 4 * (‖BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f‖ ^ 2
        - ⟪killedResolventLp hD hU hUb s hs
            (BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f),
          BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f⟫) := by
  set mu := (weightedMeasure rho).restrict U with hmu
  set F := BoundedContinuousFunction.toLp 2 mu ℝ f with hF
  let : IsProbabilityMeasure (expMeasure s⁻¹) :=
    isProbabilityMeasure_expMeasure (inv_pos.2 hs)
  set G : ℝ → ℝ := fun t => ⟪killedLp hD hSM hU hUb (Real.toNNReal t) F, F⟫ with hG
  have hGae : G =ᵐ[expMeasure s⁻¹] killedPairing law U hU mu f f := by
    filter_upwards [expMeasure_ae_pos (inv_pos.2 hs)] with t ht
    exact inner_killedLp_toLp (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) ht f f
  have hPint : Integrable (killedPairing law U hU mu f f) (expMeasure s⁻¹) := by
    refine Integrable.mono' (integrable_const (‖f‖ * ‖f‖ * (mu Set.univ).toReal))
      (measurable_killedPairing law U hU mu f f f.continuous.measurable
        f.continuous.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs]
    exact norm_killedPairing_le law U hU mu f f t
  have hGint : Integrable G (expMeasure s⁻¹) := hPint.congr hGae.symm
  have hres : ⟪killedResolventLp hD hU hUb s hs F, F⟫ = ∫ t, G t ∂(expMeasure s⁻¹) :=
    inner_killedResolventLp_eq_integral (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
      (s := s) (hs := hs) f
  have hInd : ∀ᵐ t ∂(expMeasure s⁻¹),
      (Ioi s).indicator (fun _ : ℝ => ‖F‖ ^ 2 - G s) t ≤ ‖F‖ ^ 2 - G t := by
    filter_upwards with t
    by_cases hts : t ∈ Ioi s
    · rw [Set.indicator_of_mem hts]
      have hmono : Real.toNNReal s ≤ Real.toNNReal t :=
        Real.toNNReal_mono (le_of_lt hts)
      have := inner_killedLp_self_antitone (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
        hmono F
      simp only [hG]
      linarith
    · rw [Set.indicator_of_notMem hts]
      have := inner_killedLp_self_le (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
        (Real.toNNReal t) F
      simp only [hG]
      linarith
  have hIndInt : Integrable ((Ioi s).indicator (fun _ : ℝ => ‖F‖ ^ 2 - G s))
      (expMeasure s⁻¹) :=
    (integrable_const _).indicator measurableSet_Ioi
  have hInt2 : Integrable (fun t => ‖F‖ ^ 2 - G t) (expMeasure s⁻¹) :=
    (integrable_const (‖F‖ ^ 2)).sub hGint
  have hmono := integral_mono_ae hIndInt hInt2 hInd
  rw [integral_indicator_const _ measurableSet_Ioi,
    integral_sub (integrable_const _) hGint, integral_const] at hmono
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hmono
  have htail := expMeasure_Ioi_toReal_ge hs
  have hnn : 0 ≤ ‖F‖ ^ 2 - G s := by
    have := inner_killedLp_self_le (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
      (Real.toNNReal s) F
    simp only [hG]
    linarith
  rw [hres]
  nlinarith [hmono, htail, hnn]





/-! ## The resolvent pairing of a test function -/

/-- **The resolvent pairing of a test function is close to its squared norm.**  Testing the
massive weak formulation against the test function itself gives
`⟪R_s φ, φ⟫ = ‖φ‖² − s ∫_U c ∇u·∇φ`, testing it against `u = R_s φ` gives
`s ∫_U c |∇u|² ≤ ⟪R_s φ, φ⟫ ≤ ‖φ‖²`, and the parametrised Young inequality closes the
estimate with an error `λ/2 ‖φ‖² + s/(2λ) E_c(φ)`. -/
theorem normSq_le_inner_killedResolventLp_test (φ : H1WeakTestFunction U)
    {lam : ℝ} (hlam : 0 < lam) :
    ‖BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ (testBCF φ)‖ ^ 2
      ≤ ⟪killedResolventLp hD hU hUb s hs
            (BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ (testBCF φ)),
          BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ (testBCF φ)⟫
        + lam / 2
            * ‖BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ
                (testBCF φ)‖ ^ 2
        + s / (2 * lam)
            * ∫ x in U, vecDot (c x • (h10OfTest φ).toH1Function.grad x)
                ((h10OfTest φ).toH1Function.grad x) := by
  classical
  set mu := (weightedMeasure rho).restrict U with hmu
  set Φ := BoundedContinuousFunction.toLp 2 mu ℝ (testBCF φ) with hΦ
  have hr : CoefficientOn U rho := coefficientOn_mono subset_closure
    (hD.2.1 (closure U) hUb.isCompact_closure).2
  have hc : CoefficientOn U c := coefficientOn_mono subset_closure
    (hD.2.1 (closure U) hUb.isCompact_closure).1
  obtain ⟨u, hueq, hu⟩ := hD.2.2 U hU hUb s hs (Φ : Vec d → ℝ) (Lp.memLp Φ)
  have hAc := volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU.measurableSet hr
  have hΦφ : (fun x => (Φ : Vec d → ℝ) x) =ᵐ[volume.restrict U] fun x => (φ : Vec d → ℝ) x :=
    Filter.EventuallyEq.filter_mono
      (BoundedContinuousFunction.coeFn_toLp 2 mu ℝ (testBCF φ)) hAc.ae_le
  have hRu : (fun x => (killedResolventLp hD hU hUb s hs Φ) x)
      =ᵐ[volume.restrict U] fun x => u.toH1Function.toFun x := by
    refine Filter.EventuallyEq.filter_mono ?_ hAc.ae_le
    filter_upwards [killedResolventLp_coeFn (hD := hD) (hU := hU) (hUb := hUb)
      (s := s) (hs := hs) Φ, hueq] with x hx hx2
    rw [hx, hx2]
  -- the six scalar quantities
  set Amass : ℝ := ∫ x in U, rho x * u.toH1Function.toFun x
    * (h10OfTest φ).toH1Function.toFun x with hAmassdef
  set X : ℝ := ∫ x in U, vecDot (c x • u.toH1Function.grad x)
    ((h10OfTest φ).toH1Function.grad x) with hXdef
  set Nphi : ℝ := ∫ x in U, rho x * (Φ : Vec d → ℝ) x
    * (h10OfTest φ).toH1Function.toFun x with hNphidef
  set Muu : ℝ := ∫ x in U, rho x * u.toH1Function.toFun x * u.toH1Function.toFun x with hMuudef
  set Eu : ℝ := ∫ x in U, vecDot (c x • u.toH1Function.grad x) (u.toH1Function.grad x)
    with hEudef
  set Auu : ℝ := ∫ x in U, rho x * (Φ : Vec d → ℝ) x * u.toH1Function.toFun x with hAuudef
  set Ephi : ℝ := ∫ x in U, vecDot (c x • (h10OfTest φ).toH1Function.grad x)
    ((h10OfTest φ).toH1Function.grad x) with hEphidef
  -- the resolvent pairing
  have hkey : ⟪killedResolventLp hD hU hUb s hs Φ, Φ⟫ = Auu := by
    rw [hAuudef, inner_eq_integral, integral_weightedMeasure_restrict_eq hU.measurableSet rho _ hr]
    refine integral_congr_ae ?_
    filter_upwards [hRu] with x hx
    rw [hx]
    ring
  have hnorm : ‖Φ‖ ^ 2 = Nphi := by
    rw [hNphidef, ← real_inner_self_eq_norm_sq, inner_eq_integral,
      integral_weightedMeasure_restrict_eq hU.measurableSet rho _ hr]
    refine integral_congr_ae ?_
    filter_upwards [hΦφ] with x hx
    simp only [h10OfTest_toFun]
    rw [hx]
    ring
  have hAmass : Amass = Auu := by
    rw [hAmassdef, hAuudef]
    refine integral_congr_ae ?_
    filter_upwards [hΦφ] with x hx
    simp only [h10OfTest_toFun]
    rw [hx]
    ring
  -- the two weak-formulation identities
  have hw1 := hu (h10OfTest φ)
  rw [integral_mass_scaled_forcing U rho (Φ : Vec d → ℝ)
    (h10OfTest φ).toH1Function.toFun s⁻¹] at hw1
  have hw2 := hu u
  rw [integral_mass_scaled_forcing U rho (Φ : Vec d → ℝ) u.toH1Function.toFun s⁻¹] at hw2
  have e1 : Amass + s * X = Nphi := by
    have h := congrArg (fun z : ℝ => s * z) hw1
    simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at h
    linarith [h]
  have e2 : Muu + s * Eu = Auu := by
    have h := congrArg (fun z : ℝ => s * z) hw2
    simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at h
    linarith [h]
  -- signs
  have hMuu : 0 ≤ Muu := by
    obtain ⟨-, lo, hi, hlo, hb⟩ := hr
    rw [hMuudef]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hb] with x hx
    have hrx : 0 ≤ rho x := hlo.le.trans hx.1
    simp only [Pi.zero_apply]
    nlinarith [mul_self_nonneg (u.toH1Function.toFun x)]
  have hEphi : 0 ≤ Ephi := by
    obtain ⟨-, lo, hi, hlo, hb⟩ := hc
    rw [hEphidef]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hb] with x hx
    simp only [Pi.zero_apply]
    rw [vecDot_smul_left]
    exact mul_nonneg (hlo.le.trans hx.1) (vecDot_self_nonneg _)
  have hcontr : Auu ≤ ‖Φ‖ ^ 2 := by
    rw [← hkey]
    refine (real_inner_le_norm _ _).trans ?_
    have h2 : ‖killedResolventLp hD hU hUb s hs Φ‖ ≤ ‖Φ‖ := by
      simpa using (killedResolventLp hD hU hUb s hs).le_of_opNorm_le
        (norm_killedResolventLp_le (hD := hD) (hU := hU) (hUb := hUb) (s := s) (hs := hs)) Φ
    nlinarith [norm_nonneg Φ]
  -- the Young step
  have hY : X ≤ lam / 2 * Eu + 1 / (2 * lam) * Ephi := by
    rw [hXdef, hEudef, hEphidef]
    exact integral_energy_young hc u.toH1Function.grad_memVectorL2
      (h10OfTest φ).toH1Function.grad_memVectorL2 hlam
  have hsEu : s * Eu ≤ Nphi := by
    rw [hnorm] at hcontr
    linarith [e2, hMuu, hAmass, hcontr]
  have hsX : s * X ≤ lam / 2 * (s * Eu) + s / (2 * lam) * Ephi := by
    refine (mul_le_mul_of_nonneg_left hY hs.le).trans (le_of_eq ?_)
    field_simp
  have hhalf : lam / 2 * (s * Eu) ≤ lam / 2 * Nphi :=
    mul_le_mul_of_nonneg_left hsEu (by positivity)
  rw [hkey, hnorm]
  linarith [e1, hAmass, hsX, hhalf]


/-! ## Strong continuity -/

section Continuity

variable (hD hSM hU hUb)

theorem tendsto_killedLp_test_zero (φ : H1WeakTestFunction U) :
    Filter.Tendsto (fun t : NNReal => killedLp hD hSM hU hUb t
        (BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ (testBCF φ)))
      (nhds 0)
      (nhds (BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ
        (testBCF φ))) := by
  set mu := (weightedMeasure rho).restrict U with hmu
  set Φ := BoundedContinuousFunction.toLp 2 mu ℝ (testBCF φ) with hΦ
  set E : ℝ := ∫ x in U, vecDot (c x • (h10OfTest φ).toH1Function.grad x)
    ((h10OfTest φ).toH1Function.grad x) with hEdef
  have hc : CoefficientOn U c := coefficientOn_mono subset_closure
    (hD.2.1 (closure U) hUb.isCompact_closure).1
  have hE0 : 0 ≤ E := by
    obtain ⟨-, lo, hi, hlo, hb⟩ := hc
    rw [hEdef]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hb] with x hx
    simp only [Pi.zero_apply]
    rw [vecDot_smul_left]
    exact mul_nonneg (hlo.le.trans hx.1) (vecDot_self_nonneg _)
  -- the quantitative statement
  have key : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      ‖Φ‖ ^ 2 - ⟪killedLp hD hSM hU hUb (Real.toNNReal r) Φ, Φ⟫ ≤ ε := by
    intro ε hε
    set lam : ℝ := ε / (4 * (‖Φ‖ ^ 2 + 1)) with hlamdef
    have hlam : 0 < lam := by rw [hlamdef]; positivity
    refine ⟨lam * ε / (4 * (E + 1)), by positivity, fun r hr hrd => ?_⟩
    have h1 := inner_killedLp_ge_of_inner_killedResolventLp (hD := hD) (hSM := hSM)
      (hU := hU) (hUb := hUb) (s := r) (hs := hr) (testBCF φ)
    have h2 := normSq_le_inner_killedResolventLp_test (hD := hD) (hU := hU) (hUb := hUb)
      (s := r) (hs := hr) φ hlam
    rw [← hEdef] at h2
    have hexp : 4 * (lam / 2 * ‖Φ‖ ^ 2 + r / (2 * lam) * E)
        = 2 * lam * ‖Φ‖ ^ 2 + 2 * r * E / lam := by
      field_simp
      ring
    have ha : 2 * lam * ‖Φ‖ ^ 2 ≤ ε / 2 := by
      have hid : 2 * lam * ‖Φ‖ ^ 2 = ε * ‖Φ‖ ^ 2 / (2 * (‖Φ‖ ^ 2 + 1)) := by
        rw [hlamdef]
        field_simp
        ring
      rw [hid, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg ‖Φ‖, hε]
    have hb : 2 * r * E / lam ≤ ε / 2 := by
      rw [div_le_iff₀ hlam]
      have h3 : r * (4 * (E + 1)) ≤ lam * ε := by
        rw [← le_div_iff₀ (by positivity)]
        exact hrd.le
      nlinarith [hE0, hlam, hε, h3, hr]
    linarith [h1, h2, hexp, ha, hb]
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hkey⟩ := key (ε ^ 2 / 4) (by positivity)
  have hrpos : (0:ℝ) < δ / 2 := by linarith
  have hnn : (0 : NNReal) < Real.toNNReal (δ / 2) := Real.toNNReal_pos.2 hrpos
  refine Filter.eventually_of_mem (Iio_mem_nhds hnn) fun a ha => ?_
  have hale : a ≤ Real.toNNReal (δ / 2) := le_of_lt ha
  have hmono := inner_killedLp_self_antitone (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
    hale Φ
  have hstep := hkey (δ / 2) hrpos (by linarith)
  have hsq := norm_sub_sq_le (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) a Φ
  have hlt : ‖killedLp hD hSM hU hUb a Φ - Φ‖ ^ 2 < ε ^ 2 := by
    nlinarith [hsq, hmono, hstep, hε]
  rw [dist_eq_norm]
  nlinarith [hlt, norm_nonneg (killedLp hD hSM hU hUb a Φ - Φ), hε]

/-- **Strong continuity of the killed `L²` semigroup.** -/
theorem continuous_killedLp (F : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    Continuous fun t : NNReal => killedLp hD hSM hU hUb t F := by
  have hr : CoefficientOn U rho := coefficientOn_mono subset_closure
    (hD.2.1 (closure U) hUb.isCompact_closure).2
  have hUvol : volume U ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono subset_closure)
      hUb.isCompact_closure.measure_lt_top)
  refine continuous_killedLp_of_denseRange (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
    (fun φ : H1WeakTestFunction U =>
      BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ (testBCF φ))
    (denseRange_testBCF_toLp hU hUvol hr)
    (fun φ => continuous_killedLp_of_tendsto_zero (hD := hD) (hSM := hSM) (hU := hU)
      (hUb := hUb) _ (tendsto_killedLp_test_zero hD hSM hU hUb φ)) F

end Continuity

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity
