import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularityKilled
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKilledSymmetry
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
import MarkovProcess.Kernel.OperatorSemigroup
import Mathlib.MeasureTheory.Function.ContinuousMapDense




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp

instance factOneLeTwoNNReal : Fact (1 ≤ (2 : NNReal)) := ⟨by norm_num⟩

variable {d : ℕ}

/-! ## The killed kernels as a sub-Markov kernel semigroup -/

open Classical in
/-- The killed transition kernels, patched to the identity kernel at time zero. -/
def killedFamily (law : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (hU : IsOpen U)
    (t : NNReal) : Kernel (Vec d) (Vec d) :=
  if t = 0 then Kernel.id else killedKernel law U hU t

@[simp] theorem killedFamily_zero (law : Kernel (Vec d) (Path d)) (U : Set (Vec d))
    (hU : IsOpen U) : killedFamily law U hU 0 = Kernel.id := by
  classical
  simp [killedFamily]

theorem killedFamily_of_ne (law : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (hU : IsOpen U)
    {t : NNReal} (ht : t ≠ 0) : killedFamily law U hU t = killedKernel law U hU t := by
  classical
  simp [killedFamily, ht]

theorem measurable_killedFamily (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) :
    Measurable (fun p : NNReal × Vec d => killedFamily law U hU p.1 p.2) := by
  classical
  have hs : MeasurableSet {p : NNReal × Vec d | p.1 = 0} :=
    measurable_fst (measurableSet_singleton (0 : NNReal))
  have hfun : (fun p : NNReal × Vec d => killedFamily law U hU p.1 p.2)
      = fun p : NNReal × Vec d => (Kernel.piecewise hs
          ((Kernel.id : Kernel (Vec d) (Vec d)).comap Prod.snd measurable_snd)
          (killedJointKernel law U hU)) p := by
    funext p
    rw [Kernel.piecewise_apply]
    simp only [killedFamily, Set.mem_setOf_eq]
    split_ifs <;> rfl
  rw [hfun]
  exact (Kernel.piecewise hs _ _).measurable

theorem killedFamily_subMarkov (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) :
    IsSubMarkovKernel (killedFamily law U hU t) := by
  classical
  rcases eq_or_ne t 0 with rfl | ht
  · rw [killedFamily_zero]; exact IsSubMarkovKernel.id
  · rw [killedFamily_of_ne law U hU ht]; exact killedKernel_subMarkov law U hU t

/-- **Chapman--Kolmogorov for the patched family.**  At positive times this is
`LocalResolventIterationSemigroup.semigroup`; the time-zero cases are the unit laws of
kernel composition. -/
theorem killedFamily_add (law : Kernel (Vec d) (Path d)) (hSM : StrongMarkov law)
    (U : Set (Vec d)) (hU : IsOpen U) (s t : NNReal) :
    killedFamily law U hU (s + t)
      = (killedFamily law U hU t).comp (killedFamily law U hU s) := by
  classical
  rcases eq_or_ne s 0 with rfl | hs
  · rw [zero_add, killedFamily_zero]
    exact (Kernel.comp_id _).symm
  rcases eq_or_ne t 0 with rfl | ht
  · rw [add_zero, killedFamily_zero]
    exact (Kernel.id_comp _).symm
  have hst : s + t ≠ 0 := fun h => hs (by
    simpa using (add_eq_zero_iff_of_nonneg (zero_le s) (zero_le t)).1 h |>.1)
  rw [killedFamily_of_ne law U hU hst, killedFamily_of_ne law U hU hs,
    killedFamily_of_ne law U hU ht]
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup.semigroup
    law hSM U hU s t

/-- **The killed transition kernels as a sub-Markov kernel semigroup.** -/
def killedSMKS (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law] (hSM : StrongMarkov law)
    (U : Set (Vec d)) (hU : IsOpen U) : SubMarkovKernelSemigroup (Vec d) where
  kernel := killedFamily law U hU
  measurable_kernel := measurable_killedFamily law U hU
  kernel_zero := killedFamily_zero law U hU
  kernel_add := killedFamily_add law hSM U hU
  isSubMarkovKernel := killedFamily_subMarkov law U hU

@[simp] theorem killedSMKS_apply (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (hSM : StrongMarkov law) (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) :
    killedSMKS law hSM U hU t = killedFamily law U hU t := rfl


/-! ## Subinvariance of the weighted measure -/

variable {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} {U : Set (Vec d)}

/-- **The restricted weighted measure is subinvariant for the killed family.**  At positive
times this is `LocalResolventIteration.resolventKernel`-style rectangle symmetry, namely
`killedKernel_rectangle_symmetry`, fed to `subinvariant_of_rectangle_symmetry`. -/
theorem isSubInvariant_killedSMKS (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    (hSM : StrongMarkov law) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] :
    (killedSMKS law hSM U hU).IsSubInvariant ((weightedMeasure rho).restrict U) := by
  classical
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · rw [killedSMKS_apply, killedFamily_zero, Measure.id_comp]
  · rw [killedSMKS_apply, killedFamily_of_ne law U hU ht]
    exact subinvariant_of_rectangle_symmetry _ _ (killedKernel_subMarkov law U hU t)
      (killedKernel_rectangle_symmetry hD hU hUb t)

/-! ## The `L²` contractions -/

/-- **The killed transition semigroup as operators on `L²(U, ρ dx)`.** -/
def killedLp (hD : LocalDiffusion c rho law) [IsMarkovKernel law] (hSM : StrongMarkov law)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] (t : NNReal) :
    Lp ℝ 2 ((weightedMeasure rho).restrict U) →L[ℝ]
      Lp ℝ 2 ((weightedMeasure rho).restrict U) :=
  (killedSMKS law hSM U hU).operatorFinite ((weightedMeasure rho).restrict U)
    (isSubInvariant_killedSMKS hD hSM hU hUb) 2 t

variable {hD : LocalDiffusion c rho law} {hSM : StrongMarkov law}
  {hU : IsOpen U} {hUb : Bornology.IsBounded U}

/-- The killed `L²` operator is represented by the raw kernel integral. -/
theorem killedLp_coeFn [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] (t : NNReal)
    (f : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    killedLp hD hSM hU hUb t f
      =ᵐ[(weightedMeasure rho).restrict U] kernelIntegral (killedFamily law U hU t) f :=
  (killedSMKS law hSM U hU).isAssociatedFinite_operatorFinite _
    (isSubInvariant_killedSMKS hD hSM hU hUb) 2 t f

@[simp] theorem killedLp_zero [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] :
    killedLp hD hSM hU hUb 0
      = ContinuousLinearMap.id ℝ (Lp ℝ 2 ((weightedMeasure rho).restrict U)) :=
  (killedSMKS law hSM U hU).operatorFinite_zero _ (isSubInvariant_killedSMKS hD hSM hU hUb) 2

theorem killedLp_add [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] (s t : NNReal) :
    killedLp hD hSM hU hUb (s + t)
      = (killedLp hD hSM hU hUb s).comp (killedLp hD hSM hU hUb t) :=
  (killedSMKS law hSM U hU).operatorFinite_add _
    (isSubInvariant_killedSMKS hD hSM hU hUb) 2 s t

theorem norm_killedLp_le [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] (t : NNReal) :
    ‖killedLp hD hSM hU hUb t‖ ≤ 1 :=
  (killedSMKS law hSM U hU).norm_operatorFinite_le _
    (isSubInvariant_killedSMKS hD hSM hU hUb) 2 t


/-! ## The two sub-Markov clauses -/

theorem killedLp_nonneg [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] (t : NNReal)
    (f : Lp ℝ 2 ((weightedMeasure rho).restrict U))
    (hf : (0 : Vec d → ℝ) ≤ᵐ[(weightedMeasure rho).restrict U] fun x => f x) :
    (0 : Vec d → ℝ) ≤ᵐ[(weightedMeasure rho).restrict U]
      fun x => (killedLp hD hSM hU hUb t f) x := by
  have hker : ∀ᵐ x ∂((weightedMeasure rho).restrict U),
      ∀ᵐ y ∂(killedFamily law U hU t) x, (0:ℝ) ≤ f y :=
    ae_ae_kernel_of_comp_le (isSubInvariant_killedSMKS hD hSM hU hUb t) hf
  filter_upwards [killedLp_coeFn (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) t f, hker]
    with x hx hax
  rw [hx]
  exact integral_nonneg_of_ae hax

theorem killedLp_le_one [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] (t : NNReal)
    (f : Lp ℝ 2 ((weightedMeasure rho).restrict U))
    (hf : (0 : Vec d → ℝ) ≤ᵐ[(weightedMeasure rho).restrict U] fun x => f x)
    (hf1 : ∀ᵐ x ∂((weightedMeasure rho).restrict U), f x ≤ 1) :
    ∀ᵐ x ∂((weightedMeasure rho).restrict U), (killedLp hD hSM hU hUb t f) x ≤ 1 := by
  have hsub : IsSubMarkovKernel (killedFamily law U hU t) := killedFamily_subMarkov law U hU t
  letI : IsFiniteKernel (killedFamily law U hU t) := hsub.isFiniteKernel
  have hker0 : ∀ᵐ x ∂((weightedMeasure rho).restrict U),
      ∀ᵐ y ∂(killedFamily law U hU t) x, (0:ℝ) ≤ f y :=
    ae_ae_kernel_of_comp_le (isSubInvariant_killedSMKS hD hSM hU hUb t) hf
  have hker1 : ∀ᵐ x ∂((weightedMeasure rho).restrict U),
      ∀ᵐ y ∂(killedFamily law U hU t) x, f y ≤ 1 :=
    ae_ae_kernel_of_comp_le (isSubInvariant_killedSMKS hD hSM hU hUb t) hf1
  filter_upwards [killedLp_coeFn (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb) t f,
    hker0, hker1] with x hx h0 h1
  rw [hx]
  have hmono : (∫ y, f y ∂(killedFamily law U hU t) x) ≤ ∫ _y, (1:ℝ) ∂(killedFamily law U hU t) x :=
    integral_mono_of_nonneg h0 (integrable_const (1:ℝ)) h1
  refine hmono.trans ?_
  rw [integral_const, smul_eq_mul, mul_one]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by simpa using hsub.measure_le_one x Set.univ)


/-! ## Pairings against bounded continuous data, and symmetry -/



theorem inner_killedLp_toLp [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] {t : ℝ} (ht : 0 < t)
    (f g : Vec d →ᵇ ℝ) :
    ⟪killedLp hD hSM hU hUb (Real.toNNReal t)
        (BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f),
      BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ g⟫
      = killedPairing law U hU ((weightedMeasure rho).restrict U) g f t := by
  set mu := (weightedMeasure rho).restrict U with hmu
  have htn : Real.toNNReal t ≠ 0 := by
    simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
    exact ht
  have hsubinv : (killedFamily law U hU (Real.toNNReal t)) ∘ₘ mu ≤ mu :=
    isSubInvariant_killedSMKS hD hSM hU hUb (Real.toNNReal t)
  have hfam : killedFamily law U hU (Real.toNNReal t)
      = killedKernel law U hU (Real.toNNReal t) := killedFamily_of_ne law U hU htn
  rw [inner_eq_integral, killedPairing]
  refine integral_congr_ae ?_
  filter_upwards [killedLp_coeFn (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
      (Real.toNNReal t) (BoundedContinuousFunction.toLp 2 mu ℝ f),
    kernelIntegral_congr_ae hsubinv (BoundedContinuousFunction.coeFn_toLp 2 mu ℝ f),
    BoundedContinuousFunction.coeFn_toLp 2 mu ℝ g] with x hx hx2 hx3
  rw [hx, hx2, hx3, hfam, mul_comm]



theorem inner_toLp_killedLp [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] {t : ℝ} (ht : 0 < t)
    (f g : Vec d →ᵇ ℝ) :
    ⟪BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f,
      killedLp hD hSM hU hUb (Real.toNNReal t)
        (BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ g)⟫
      = killedPairing law U hU ((weightedMeasure rho).restrict U) f g t := by
  set mu := (weightedMeasure rho).restrict U with hmu
  have htn : Real.toNNReal t ≠ 0 := by
    simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
    exact ht
  have hsubinv : (killedFamily law U hU (Real.toNNReal t)) ∘ₘ mu ≤ mu :=
    isSubInvariant_killedSMKS hD hSM hU hUb (Real.toNNReal t)
  have hfam : killedFamily law U hU (Real.toNNReal t)
      = killedKernel law U hU (Real.toNNReal t) := killedFamily_of_ne law U hU htn
  rw [inner_eq_integral, killedPairing]
  refine integral_congr_ae ?_
  filter_upwards [killedLp_coeFn (hD := hD) (hSM := hSM) (hU := hU) (hUb := hUb)
      (Real.toNNReal t) (BoundedContinuousFunction.toLp 2 mu ℝ g),
    kernelIntegral_congr_ae hsubinv (BoundedContinuousFunction.coeFn_toLp 2 mu ℝ g),
    BoundedContinuousFunction.coeFn_toLp 2 mu ℝ f] with x hx hx2 hx3
  rw [hx, hx2, hx3, hfam]

/-- Bounded continuous functions have dense image in `L²` of the restricted weighted
measure. -/
theorem denseRange_toLp [IsFiniteMeasure ((weightedMeasure rho).restrict U)] :
    DenseRange (BoundedContinuousFunction.toLp (α := Vec d) (E := ℝ) 2
      ((weightedMeasure rho).restrict U) ℝ) :=
  BoundedContinuousFunction.toLp_denseRange _ _ ℝ (by norm_num)

/-- **Each killed `L²` operator is symmetric.**

`LocalResolventIteration.killedPairing_symm` supplies the identity for bounded continuous
data; the two sides are continuous bilinear expressions, so density of the bounded
continuous functions in `L²` of a finite Borel measure extends it to all of `L²`. -/
theorem isSymmetricOp_killedLp [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] (t : NNReal) :
    IsSymmetricOp (killedLp hD hSM hU hUb t) := by
  classical
  set mu := (weightedMeasure rho).restrict U with hmu
  rcases eq_or_ne t 0 with rfl | ht
  · intro F G
    rw [killedLp_zero]
    rfl
  set T := killedLp hD hSM hU hUb t with hT
  have htpos : (0:ℝ) < (t : ℝ) := lt_of_le_of_ne t.coe_nonneg
    (fun h => ht (NNReal.coe_injective h.symm))
  have hcoe : Real.toNNReal ((t : ℝ)) = t := Real.toNNReal_coe
  have hdense := denseRange_toLp (rho := rho) (U := U)
  have hc1 : Continuous (fun p : Lp ℝ 2 mu × Lp ℝ 2 mu => ⟪T p.1, p.2⟫) :=
    continuous_inner.comp ((T.continuous.comp continuous_fst).prodMk continuous_snd)
  have hc2 : Continuous (fun p : Lp ℝ 2 mu × Lp ℝ 2 mu => ⟪p.1, T p.2⟫) :=
    continuous_inner.comp (continuous_fst.prodMk (T.continuous.comp continuous_snd))
  have hEq := (hdense.prodMap hdense).equalizer hc1 hc2 (funext fun q => by
    show ⟪T (BoundedContinuousFunction.toLp 2 mu ℝ q.1),
        BoundedContinuousFunction.toLp 2 mu ℝ q.2⟫
      = ⟪BoundedContinuousFunction.toLp 2 mu ℝ q.1,
          T (BoundedContinuousFunction.toLp 2 mu ℝ q.2)⟫
    rw [hT, ← hcoe, inner_killedLp_toLp htpos q.1 q.2, inner_toLp_killedLp htpos q.1 q.2]
    exact killedPairing_symm hD hU hUb q.2 q.1 (t : ℝ) t.coe_nonneg)
  intro F G
  exact congrFun hEq (F, G)

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
