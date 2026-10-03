module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKSemigroupIdentification

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledStrongContinuity
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKSemigroupIdentification
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKOperatorHalf
open MarkovProcess.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDatumFields

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} {U : Set (Vec d)}
  {hD : LocalDiffusion c rho law} {hSM : StrongMarkov law}
  {hU : IsOpen U} {hUb : Bornology.IsBounded U}

section SCCS

variable [IsMarkovKernel law] [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
variable (hD hSM hU hUb)

/-- **The killed transition semigroup as a strongly continuous contraction semigroup.**
The four structure fields other than strong continuity come from `KilledSemigroupLp.lean`;
strong continuity is `KilledStrongContinuity.continuous_killedLp`. -/
def killedSCCS :
    StronglyContinuousContractionSemigroup
      (Lp ℝ 2 ((weightedMeasure rho).restrict U)) where
  operator := killedLp hD hSM hU hUb
  operator_zero := killedLp_zero
  operator_add := killedLp_add
  opNorm_le_one := norm_killedLp_le
  continuous_orbit := continuous_killedLp hD hSM hU hUb

@[simp] theorem killedSCCS_apply (t : NNReal) :
    killedSCCS hD hSM hU hUb t = killedLp hD hSM hU hUb t := rfl

end SCCS


/-! ## The resolvent of a strongly continuous contraction semigroup, tested -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The resolvent of a strongly continuous contraction semigroup, paired with a vector:
the inner product passes inside the Bochner--Laplace integral. -/
theorem inner_resolvent_eq (S : StronglyContinuousContractionSemigroup E)
    (al : PositiveShift) (F G : E) :
    ⟪S.resolvent al F, G⟫
      = ∫ t in Ioi (0:ℝ), Real.exp (-(al : ℝ) * t) * ⟪S (Real.toNNReal t) F, G⟫ := by
  have hint : IntegrableOn (S.laplaceIntegrand (al : ℝ) F) (Ioi 0) :=
    S.integrableOn_laplaceIntegrand al.2 F
  have hcomm := ContinuousLinearMap.integral_comp_comm (innerSL ℝ G) hint
  rw [StronglyContinuousContractionSemigroup.resolvent_apply, real_inner_comm,
    show ⟪G, ∫ t in Ioi (0:ℝ), S.laplaceIntegrand (al : ℝ) F t⟫
      = (innerSL ℝ G) (∫ t in Ioi (0:ℝ), S.laplaceIntegrand (al : ℝ) F t) from rfl,
    ← hcomm]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  show ⟪G, S.laplaceIntegrand (al : ℝ) F t⟫ = _
  rw [StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, real_inner_smul_right,
    real_inner_comm]

omit [CompleteSpace E] in
/-- A bounded symmetric operator with dense range on a real Hilbert space is injective. -/
theorem injective_of_denseRange_of_isSymmetricOp {T : E →L[ℝ] E}
    (hT : IsSymmetricOp T) (hdense : DenseRange T) : Function.Injective T := by
  intro x y hxy
  have hzero : ∀ v : E, ⟪x - y, T v⟫ = 0 := by
    intro v
    rw [← hT (x - y) v]
    simp [map_sub, hxy]
  have : x - y = 0 := by
    refine inner_self_eq_zero (𝕜 := ℝ) |>.mp ?_
    have hcont : Continuous fun v : E => ⟪x - y, v⟫ := (innerSL ℝ (x - y)).continuous
    have := hdense.equalizer hcont continuous_const (funext fun v => by
      simpa using hzero v)
    simpa using congrFun this (x - y)
  exact sub_eq_zero.mp this

end Abstract


/-! ## The Laplace identification `P.resolvent s⁻¹ = s • R` -/

section Laplace

variable [IsMarkovKernel law] [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
  {s : ℝ} {hs : 0 < s}

/-- **The Laplace transform of the killed semigroup at the shift `s⁻¹` is `s R`**, tested
against bounded continuous data. -/
theorem laplace_killedLp_toLp (f g : Vec d →ᵇ ℝ) :
    s * ⟪killedResolventLp hD hU hUb s hs
        (BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f),
      BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ g⟫
      = ∫ t in Ioi (0:ℝ), Real.exp (-s⁻¹ * t) *
          ⟪killedLp hD hSM hU hUb (Real.toNNReal t)
              (BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f),
            BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ g⟫ := by
  set mu := (weightedMeasure rho).restrict U with hmu
  rw [inner_killedResolventLp_toLp (hD := hD) (hU := hU) (hUb := hUb) (s := s) (hs := hs) f g,
    killedResolvent_pairing_eq_expMeasure law U hU mu g f s hs,
    integral_expMeasure s hs, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [inner_killedLp_toLp (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) ht f g]
  congr 1
  congr 1
  field_simp

/-- **The resolvent identification.**  The Laplace transform of the killed `L²` semigroup
at the shift `s⁻¹` is `s` times the killed resolvent operator — the fifth and last input of
`RRKSemigroupIdentification.rrk_datum_fields_of_positive`. -/
theorem resolvent_killedSCCS :
    (killedSCCS hD hSM hU hUb).resolvent ⟨s⁻¹, mem_Ioi.2 (inv_pos.2 hs)⟩
      = s • killedResolventLp hD hU hUb s hs := by
  set mu := (weightedMeasure rho).restrict U with hmu
  set A := (killedSCCS hD hSM hU hUb).resolvent ⟨s⁻¹, mem_Ioi.2 (inv_pos.2 hs)⟩ with hA
  set B := (s : ℝ) • killedResolventLp hD hU hUb s hs with hB
  have hbc : ∀ f g : Vec d →ᵇ ℝ,
      ⟪A (BoundedContinuousFunction.toLp 2 mu ℝ f),
        BoundedContinuousFunction.toLp 2 mu ℝ g⟫
        = ⟪B (BoundedContinuousFunction.toLp 2 mu ℝ f),
            BoundedContinuousFunction.toLp 2 mu ℝ g⟫ := by
    intro f g
    rw [hA, inner_resolvent_eq, hB, ContinuousLinearMap.smul_apply, real_inner_smul_left]
    exact (laplace_killedLp_toLp (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
      (s := s) (hs := hs) f g).symm
  have hc1 : Continuous (fun p : Lp ℝ 2 mu × Lp ℝ 2 mu => ⟪A p.1, p.2⟫) :=
    continuous_inner.comp ((A.continuous.comp continuous_fst).prodMk continuous_snd)
  have hc2 : Continuous (fun p : Lp ℝ 2 mu × Lp ℝ 2 mu => ⟪B p.1, p.2⟫) :=
    continuous_inner.comp ((B.continuous.comp continuous_fst).prodMk continuous_snd)
  have hdense := denseRange_toLp (rho := rho) (U := U)
  have hEq := (hdense.prodMap hdense).equalizer hc1 hc2 (funext fun q => hbc q.1 q.2)
  refine ContinuousLinearMap.ext fun F => ?_
  refine ext_inner_right ℝ fun G => ?_
  exact congrFun hEq (F, G)

/-! ## Injectivity, and the nine fields -/

include hSM in
/-- **`R` is injective.**  Hille--Yosida gives the resolvent dense range, the Laplace
identification transports it to `R`, and a symmetric operator with dense range on a
Hilbert space has trivial kernel. -/
theorem injective_killedResolventLp :
    Function.Injective (killedResolventLp hD hU hUb s hs) := by
  have hdr := (killedSCCS hD hSM hU hUb).denseRange_resolvent
    ⟨s⁻¹, mem_Ioi.2 (inv_pos.2 hs)⟩
  rw [resolvent_killedSCCS (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) (hs := hs)] at hdr
  exact injective_of_denseRange_of_isSymmetricOp isSymmetricOp_killedResolventLp
    (denseRange_of_smul hs hdr)



theorem rrk_datum_fields_killed (N : ℕ) :
    IsSymmetricOp (killedResolventLp hD hU hUb s hs ^ N) ∧
      Function.Injective (killedResolventLp hD hU hUb s hs ^ N) ∧
      (∀ t, 0 < t →
        IsSymmetricOp (rrkSmoothing s N (killedResolventLp hD hU hUb s hs) t)) ∧
      (∀ t, 0 < t → (killedResolventLp hD hU hUb s hs ^ N).comp
          (rrkSmoothing s N (killedResolventLp hD hU hUb s hs) t)
          = killedLp hD hSM hU hUb (Real.toNNReal (t / 2))) ∧
      ContinuousOn (rrkSmoothing s N (killedResolventLp hD hU hUb s hs)) (Ioi 0) ∧
      (∀ t, 0 < t → IsSymmetricOp (killedLp hD hSM hU hUb (Real.toNNReal t))) ∧
      (∀ t u, 0 < t → 0 < u →
        (killedLp hD hSM hU hUb (Real.toNNReal t)).comp
            (killedLp hD hSM hU hUb (Real.toNNReal u))
          = killedLp hD hSM hU hUb (Real.toNNReal (t + u))) ∧
      (∀ t, 0 < t → ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
        ((0 : Vec d → ℝ) ≤ᵐ[(weightedMeasure rho).restrict U] fun x => f x) →
        (0 : Vec d → ℝ) ≤ᵐ[(weightedMeasure rho).restrict U]
          fun x => (killedLp hD hSM hU hUb (Real.toNNReal t) f) x) ∧
      (∀ t, 0 < t → ∀ f : Lp ℝ 2 ((weightedMeasure rho).restrict U),
        ((0 : Vec d → ℝ) ≤ᵐ[(weightedMeasure rho).restrict U] fun x => f x) →
        (∀ᵐ x ∂((weightedMeasure rho).restrict U), f x ≤ 1) →
        ∀ᵐ x ∂((weightedMeasure rho).restrict U),
          (killedLp hD hSM hU hUb (Real.toNNReal t) f) x ≤ 1) :=
  rrk_datum_fields_of_positive hs N isSymmetricOp_killedResolventLp
    (injective_killedResolventLp (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) (hs := hs))
    (fun f => inner_killedResolventLp_nonneg f)
    (killedSCCS hD hSM hU hUb)
    (resolvent_killedSCCS (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) (hs := hs))
    (fun t f hf => killedLp_nonneg (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) t f hf)
    (fun t f hf hf1 =>
      killedLp_le_one (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) t f hf hf1)

end Laplace

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDatumFields
