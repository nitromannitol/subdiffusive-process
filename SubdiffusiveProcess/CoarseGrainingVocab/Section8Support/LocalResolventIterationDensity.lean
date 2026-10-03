module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKilledSymmetry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationFiber
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationMeasure

@[expose] public section

/-!
# The killed transition density bound

The finite-resolvent ultracontractivity estimate transfers to the killed
semigroup through the exponential mixture comparison of
`LocalResolventIterationHeat`, and the resulting rectangle bound becomes an
almost-everywhere bound on the transition density.
-/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationHeat
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationBootstrap
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationScaling
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationFiber
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open scoped ENNReal NNReal ProbabilityTheory
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration

variable {d : ℕ}

/-- The killed transition kernel is the density integral against the local weighted measure. -/
theorem killedKernel_apply_eq_density {rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    {U : Set (Vec d)} (hU : IsOpen U) {p : ℝ → Vec d → Vec d → ℝ}
    (hp : IsKilledDensity law rho U p) (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ U)
    (B : Set (Vec d)) (hB : MeasurableSet B) :
    killedKernel law U hU (Real.toNNReal t) x B
      = ∫⁻ y in B, ENNReal.ofReal (p t x y) ∂((weightedMeasure rho).restrict U) := by
  rw [killed_apply law U hU _ x B hB]
  have hset : {w : Path d | position (Real.toNNReal t) w ∈ B ∧
      ((Real.toNNReal t : NNReal) : ℝ≥0∞) < LifetimePath.exitTime U w}
      = {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w ∧
        LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B} := by
    ext w
    constructor
    · rintro ⟨hmem, hlt⟩
      obtain ⟨z, _, hcoord⟩ :=
        LifetimePath.exists_coordinate_eq_alive_of_lt_exitTime U w (Real.toNNReal t) hlt
      refine ⟨hlt, ?_⟩
      rw [hcoord]
      exact ⟨z, by rwa [← position_of_alive (Real.toNNReal t) w z hcoord], rfl⟩
    · rintro ⟨hlt, himg⟩
      obtain ⟨z, hzB, hz⟩ := himg
      exact ⟨by rw [position_of_alive (Real.toNNReal t) w z hz.symm]; exact hzB, hlt⟩
  rw [hset, hp.2.2 t ht x hx B hB, Measure.restrict_restrict hB, weightedMeasure]


/-- The killed transition rows are bounded by the ultracontractivity constant. -/
theorem killedKernel_row_le {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hm0 : (weightedMeasure rho) U ≠ 0) (hmtop : (weightedMeasure rho) U ≠ ∞)
    {p0 A F : ℝ} (hp0 : 2 < p0) (hA : 1 ≤ A) (hF : 0 < F)
    (hSob : SobolevAssumption c rho U p0 A F)
    (k : ℕ) (hk : qExp p0 ≤ rExp p0 ^ k)
    (t : ℝ) (ht : 0 < t) (B : Set (Vec d)) (hB : MeasurableSet B) :
    ∀ᵐ x ∂((weightedMeasure rho).restrict U),
      killedKernel law U hU.isOpen (Real.toNNReal t) x B ≤
        ((2 : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) *
            (1 + F / (t / ((k : ℝ) + 1))) ^ ((1 - 2 / p0)⁻¹)) *
          ((weightedMeasure rho) U)⁻¹) *
        ((weightedMeasure rho).restrict U) B := by
  have hmuniv : ((weightedMeasure rho).restrict U) Set.univ = (weightedMeasure rho) U :=
    Measure.restrict_apply_univ _
  haveI hfinite : IsFiniteMeasure ((weightedMeasure rho).restrict U) :=
    ⟨by rw [hmuniv]; exact lt_of_le_of_ne le_top hmtop⟩
  have hm0' : ((weightedMeasure rho).restrict U) Set.univ ≠ 0 := by rw [hmuniv]; exact hm0
  have hmtop' : ((weightedMeasure rho).restrict U) Set.univ ≠ ∞ := by rw [hmuniv]; exact hmtop
  haveI hprob : IsProbabilityMeasure
      (LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U)) :=
    isProbabilityMeasure_normalize hm0' hmtop'
  have hUb : Bornology.IsBounded U := hU.isBoundedDomain.isBounded
  have hNpos : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hs : 0 < t / ((k : ℝ) + 1) := div_pos ht hNpos
  set s : ℝ := t / ((k : ℝ) + 1) with hsdef
  set a : NNReal := Real.toNNReal s with hadef
  have hacoe : ((a : NNReal) : ℝ) = s := Real.coe_toNNReal s hs.le
  have ha : 0 < a := by
    rw [← NNReal.coe_pos, hacoe]
    exact hs
  set Q : NNReal → Kernel (Vec d) (Vec d) := fun tau => killedKernel law U hU.isOpen tau with hQdef
  have hsubQ : ∀ tau, IsSubMarkovKernel (Q tau) :=
    fun tau => killedKernel_subMarkov law U hU.isOpen tau
  have hrectQ : ∀ tau, ∀ C D : Set (Vec d), MeasurableSet C → MeasurableSet D →
      (∫⁻ x in C, Q tau x D ∂((weightedMeasure rho).restrict U))
        = ∫⁻ x in D, Q tau x C ∂((weightedMeasure rho).restrict U) :=
    fun tau => killedKernel_rectangle_symmetry hD hU.isOpen hUb tau
  have hmuQ : ∀ tau, Q tau ∘ₘ
      (LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U)) ≤
      LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U) :=
    fun tau => comp_smul_le _ (subinvariant_of_rectangle_symmetry _ _ (hsubQ tau) (hrectQ tau))
  have hsymQ : ∀ tau,
      ((LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U)) ⊗ₘ
        Q tau).map Prod.swap =
      (LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U)) ⊗ₘ Q tau :=
    fun tau => compProd_symm (hsubQ tau) (rectangle_symmetry_smul _ (hrectQ tau))
  have hsemQ : ∀ u v : NNReal, Q (u + v) = Q v ∘ₖ Q u :=
    fun u v => semigroup law hD.1 U hU.isOpen u v
  have hjointQ : ∀ B : Set (Vec d), MeasurableSet B →
      Measurable (fun q : NNReal × Vec d => Q q.1 q.2 B) :=
    fun B hB => killedKernel_joint_measurable law U hU.isOpen B hB
  have hRsub : IsSubMarkovKernel (resolventKernel law U hU.isOpen s hs) :=
    resolventKernel_subMarkov law U hU.isOpen s hs
  have hmix : ∀ (x : Vec d) (B : Set (Vec d)), MeasurableSet B →
      resolventKernel law U hU.isOpen s hs x B =
        ∫⁻ u : ℝ, Q (Real.toNNReal u) x B ∂expMeasure ((a : ℝ)⁻¹) := by
    intro x B hB
    rw [hacoe]
    exact resolventKernel_apply_mixture law U hU.isOpen s hs x B hB
  have hbound : ∀ f : Vec d → ℝ,
      MemLp f 1 (LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U)) →
      eLpNorm ((kernelIntegral (resolventKernel law U hU.isOpen s hs))^[k + 1] f) ∞
          (LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U)) ≤
        ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) *
            (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) *
          eLpNorm f 1 (LocalResolventIterationScaling.normalize
            ((weightedMeasure rho).restrict U)) :=
    fun f hf => iterate_eLpNorm_normalized_le hD hU hm0 hmtop hp0 hA hF hs hSob k hk hf
  have hNa : ((k + 1 : ℕ) : NNReal) * a = Real.toNNReal t := by
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_mul, hacoe, hsdef, Real.coe_toNNReal t ht.le]
    push_cast
    field_simp
  have hrect := fun (C : Set (Vec d)) (hC : MeasurableSet C) =>
    heat_rectangle hRsub hsubQ hmuQ hsymQ hsemQ hjointQ ha hmix k hbound C B hC hB
  rw [hNa] at hrect
  set M : ℝ≥0∞ := ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) *
    (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) with hMdef
  have hnuB : (LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U)) B
      = ((weightedMeasure rho) U)⁻¹ * ((weightedMeasure rho).restrict U) B := by
    rw [LocalResolventIterationScaling.normalize, Measure.smul_apply, smul_eq_mul, hmuniv]
  have haeNu : ∀ᵐ x ∂(LocalResolventIterationScaling.normalize
      ((weightedMeasure rho).restrict U)),
      Q (Real.toNNReal t) x B ≤ (2 : ℝ≥0∞) ^ (k + 1) * M *
        (LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U)) B := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      ((Q (Real.toNNReal t)).measurable_coe hB) ?_
    intro C hC _
    rw [setLIntegral_const]
    calc
      (∫⁻ x in C, Q (Real.toNNReal t) x B
          ∂(LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U)))
          ≤ (2 : ℝ≥0∞) ^ (k + 1) * M *
            (LocalResolventIterationScaling.normalize
              ((weightedMeasure rho).restrict U)) C *
            (LocalResolventIterationScaling.normalize
              ((weightedMeasure rho).restrict U)) B := hrect C hC
      _ = (2 : ℝ≥0∞) ^ (k + 1) * M *
            (LocalResolventIterationScaling.normalize
              ((weightedMeasure rho).restrict U)) B *
            (LocalResolventIterationScaling.normalize
              ((weightedMeasure rho).restrict U)) C := by ring
  have hac : ((weightedMeasure rho).restrict U) ≪
      LocalResolventIterationScaling.normalize ((weightedMeasure rho).restrict U) := by
    refine Measure.absolutelyContinuous_of_le_smul (c := (weightedMeasure rho) U) ?_
    rw [LocalResolventIterationScaling.normalize, smul_smul, hmuniv,
      ENNReal.mul_inv_cancel hm0 hmtop, one_smul]
  filter_upwards [hac haeNu] with x hx
  rw [hnuB] at hx
  calc
    killedKernel law U hU.isOpen (Real.toNNReal t) x B ≤ (2 : ℝ≥0∞) ^ (k + 1) * M *
        (((weightedMeasure rho) U)⁻¹ * ((weightedMeasure rho).restrict U) B) := hx
    _ = ((2 : ℝ≥0∞) ^ (k + 1) * M * ((weightedMeasure rho) U)⁻¹) *
        ((weightedMeasure rho).restrict U) B := by ring


/-- The killed transition density obeys the ultracontractivity bound almost everywhere. -/
theorem density_ae_le {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hm0 : (weightedMeasure rho) U ≠ 0) (hmtop : (weightedMeasure rho) U ≠ ∞)
    {p0 A F : ℝ} (hp0 : 2 < p0) (hA : 1 ≤ A) (hF : 0 < F)
    (hSob : SobolevAssumption c rho U p0 A F)
    (k : ℕ) (hk : qExp p0 ≤ rExp p0 ^ k)
    {p : ℝ → Vec d → Vec d → ℝ} (hp : IsKilledDensity law rho U p)
    (t : ℝ) (ht : 0 < t) :
    ∀ᵐ z ∂(((weightedMeasure rho).restrict U).prod ((weightedMeasure rho).restrict U)),
      p t z.1 z.2 ≤ 2 ^ (k + 1) * ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) /
        (((weightedMeasure rho) U).toReal) *
        (1 + F / (t / ((k : ℝ) + 1))) ^ ((1 - 2 / p0)⁻¹) := by
  have hmuniv : ((weightedMeasure rho).restrict U) Set.univ = (weightedMeasure rho) U :=
    Measure.restrict_apply_univ _
  haveI hfinite : IsFiniteMeasure ((weightedMeasure rho).restrict U) :=
    ⟨by rw [hmuniv]; exact lt_of_le_of_ne le_top hmtop⟩
  have hmass : 0 < (((weightedMeasure rho) U)).toReal := ENNReal.toReal_pos hm0 hmtop
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hNpos : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hs : 0 < t / ((k : ℝ) + 1) := div_pos ht hNpos
  have hVpos : (0:ℝ) < 1 + F / (t / ((k : ℝ) + 1)) := by positivity
  set bound : ℝ := 2 ^ (k + 1) * ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) /
    (((weightedMeasure rho) U).toReal) *
    (1 + F / (t / ((k : ℝ) + 1))) ^ ((1 - 2 / p0)⁻¹) with hbdef
  have hboundpos : 0 < bound := by
    rw [hbdef]
    exact mul_pos (div_pos (mul_pos (mul_pos (by positivity) (ultraConstant_pos p0))
      (Real.rpow_pos_of_pos hApos _)) hmass) (Real.rpow_pos_of_pos hVpos _)
  have hconst : (2 : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) *
        (1 + F / (t / ((k : ℝ) + 1))) ^ ((1 - 2 / p0)⁻¹)) * ((weightedMeasure rho) U)⁻¹
      = ENNReal.ofReal bound := by
    have h2 : (2 : ℝ≥0∞) ^ (k + 1) = ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      norm_num
    have hinv : ((weightedMeasure rho) U)⁻¹
        = ENNReal.ofReal ((((weightedMeasure rho) U).toReal)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos hmass, ENNReal.ofReal_toReal hmtop]
    have hnn1 : (0:ℝ) ≤ ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) *
        (1 + F / (t / ((k : ℝ) + 1))) ^ ((1 - 2 / p0)⁻¹) :=
      le_of_lt (mul_pos (mul_pos (ultraConstant_pos p0) (Real.rpow_pos_of_pos hApos _))
        (Real.rpow_pos_of_pos hVpos _))
    rw [h2, hinv, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hnn1), hbdef]
    congr 1
    field_simp
  have hrows : ∀ B : Set (Vec d), MeasurableSet B →
      ∀ᵐ x ∂((weightedMeasure rho).restrict U),
        (∫⁻ y in B, ENNReal.ofReal (p t x y) ∂((weightedMeasure rho).restrict U))
          ≤ ENNReal.ofReal bound * ((weightedMeasure rho).restrict U) B := by
    intro B hB
    filter_upwards [killedKernel_row_le hD hU hm0 hmtop hp0 hA hF hSob k hk t ht B hB,
      ae_restrict_mem hU.isOpen.measurableSet] with x hx hxU
    rw [← killedKernel_apply_eq_density hU.isOpen hp t ht x hxU B hB, ← hconst]
    exact hx
  have hmeas : Measurable (Function.uncurry (fun x y => ENNReal.ofReal (p t x y))) :=
    (hp.1 t ht).ennreal_ofReal
  have hae := ae_prod_le_of_forall_setLIntegral_le (nu := (weightedMeasure rho).restrict U)
    (mu := (weightedMeasure rho).restrict U) hmeas ENNReal.ofReal_ne_top hrows
  filter_upwards [hae] with z hz
  exact (ENNReal.ofReal_le_ofReal_iff hboundpos.le).mp hz




def frozenConstant (p0 : ℝ) (k : ℕ) : ℝ :=
  (1 - 2 / p0)⁻¹ + 2 ^ (k + 1) * ultraConstant p0 * (((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹))

theorem frozenConstant_pos {p0 : ℝ} (hp0 : 2 < p0) (k : ℕ) : 0 < frozenConstant p0 k := by
  have h1 : (0:ℝ) < (1 - 2 / p0)⁻¹ := inv_pos.mpr (theta_pos hp0)
  have h2 : (0:ℝ) < 2 ^ (k + 1) * ultraConstant p0 * (((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹)) :=
    mul_pos (mul_pos (by positivity) (ultraConstant_pos p0))
      (Real.rpow_pos_of_pos (by positivity) _)
  rw [frozenConstant]
  linarith

theorem theta_inv_le_frozenConstant {p0 : ℝ} (k : ℕ) :
    (1 - 2 / p0)⁻¹ ≤ frozenConstant p0 k := by
  have h2 : (0:ℝ) ≤ 2 ^ (k + 1) * ultraConstant p0 * (((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹)) :=
    le_of_lt (mul_pos (mul_pos (by positivity) (ultraConstant_pos p0))
      (Real.rpow_pos_of_pos (by positivity) _))
  rw [frozenConstant]
  linarith

theorem heat_le_frozenConstant {p0 : ℝ} (hp0 : 2 < p0) (k : ℕ) :
    2 ^ (k + 1) * ultraConstant p0 * (((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹))
      ≤ frozenConstant p0 k := by
  have h1 : (0:ℝ) < (1 - 2 / p0)⁻¹ := inv_pos.mpr (theta_pos hp0)
  rw [frozenConstant]
  linarith

theorem ultra_le_frozenConstant {p0 : ℝ} (hp0 : 2 < p0) (k : ℕ) :
    ultraConstant p0 ≤ frozenConstant p0 k := by
  have h1 : (1:ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have h2 : (1:ℝ) ≤ ((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹) :=
    Real.one_le_rpow (by simp) (inv_pos.mpr (theta_pos hp0)).le
  have h4 : (1:ℝ) ≤ 2 ^ (k + 1) * ((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹) := by nlinarith
  have h5 : ultraConstant p0 * 1 ≤ ultraConstant p0 *
      (2 ^ (k + 1) * ((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹)) :=
    mul_le_mul_of_nonneg_left h4 (ultraConstant_pos p0).le
  have h6 : 2 ^ (k + 1) * ultraConstant p0 * (((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹))
      = ultraConstant p0 * (2 ^ (k + 1) * ((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹)) := by ring
  have h3 : ultraConstant p0 ≤ 2 ^ (k + 1) * ultraConstant p0 *
      (((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹)) := by rw [h6]; linarith
  exact h3.trans (heat_le_frozenConstant hp0 k)

/-- The part-one constant comparison. -/
theorem ultraBound_le {p0 A C mass V : ℝ} (hA : 1 ≤ A)
    (hC1 : ultraConstant p0 ≤ C) (hC2 : (1 - 2 / p0)⁻¹ ≤ C)
    (hmass : 0 < mass) (hV : 0 < V) :
    ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) / mass * V ^ ((1 - 2 / p0)⁻¹)
      ≤ C * A ^ C / mass * V ^ ((1 - 2 / p0)⁻¹) := by
  have hApow : A ^ ((1 - 2 / p0)⁻¹) ≤ A ^ C := Real.rpow_le_rpow_of_exponent_le hA hC2
  have hnum : ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) ≤ C * A ^ C :=
    mul_le_mul hC1 hApow (Real.rpow_nonneg (le_trans zero_le_one hA) _)
      (le_trans (ultraConstant_pos p0).le hC1)
  have hdiv : ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) / mass ≤ C * A ^ C / mass := by
    gcongr
  exact mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg hV.le _)

/-- The part-two constant comparison, absorbing the time rescaling. -/
theorem heatBound_le {p0 A C F t mass : ℝ} (k : ℕ) (hp0 : 2 < p0) (hA : 1 ≤ A)
    (hF : 0 < F) (ht : 0 < t) (hmass : 0 < mass)
    (hC1 : 2 ^ (k + 1) * ultraConstant p0 * (((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹)) ≤ C)
    (hC2 : (1 - 2 / p0)⁻¹ ≤ C) :
    2 ^ (k + 1) * ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) / mass *
        (1 + F / (t / ((k : ℝ) + 1))) ^ ((1 - 2 / p0)⁻¹)
      ≤ C * A ^ C / mass * (1 + F / t) ^ ((1 - 2 / p0)⁻¹) := by
  have hth : (0:ℝ) < (1 - 2 / p0)⁻¹ := inv_pos.mpr (theta_pos hp0)
  have hNpos : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hVpos : (0:ℝ) < 1 + F / t := by positivity
  have hArg : 1 + F / (t / ((k : ℝ) + 1)) ≤ ((k : ℝ) + 1) * (1 + F / t) := by
    rw [div_div_eq_mul_div, mul_comm F ((k : ℝ) + 1), mul_div_assoc]
    have h1 : (1:ℝ) ≤ (k : ℝ) + 1 := by simp
    nlinarith [div_pos hF ht]
  have hArgpos : (0:ℝ) < 1 + F / (t / ((k : ℝ) + 1)) := by positivity
  have hpow : (1 + F / (t / ((k : ℝ) + 1))) ^ ((1 - 2 / p0)⁻¹)
      ≤ ((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹) * (1 + F / t) ^ ((1 - 2 / p0)⁻¹) := by
    rw [← Real.mul_rpow hNpos.le hVpos.le]
    exact Real.rpow_le_rpow hArgpos.le hArg hth.le
  have hApow : A ^ ((1 - 2 / p0)⁻¹) ≤ A ^ C := Real.rpow_le_rpow_of_exponent_le hA hC2
  have hApos : (0:ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hUC : (0:ℝ) < ultraConstant p0 := ultraConstant_pos p0
  have hcoefpos : (0:ℝ) ≤ 2 ^ (k + 1) * ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) / mass :=
    le_of_lt (div_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos hApos _)) hmass)
  calc
    2 ^ (k + 1) * ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) / mass *
        (1 + F / (t / ((k : ℝ) + 1))) ^ ((1 - 2 / p0)⁻¹)
        ≤ 2 ^ (k + 1) * ultraConstant p0 * A ^ ((1 - 2 / p0)⁻¹) / mass *
          (((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹) * (1 + F / t) ^ ((1 - 2 / p0)⁻¹)) :=
      mul_le_mul_of_nonneg_left hpow hcoefpos
    _ = (2 ^ (k + 1) * ultraConstant p0 * (((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹))) *
          A ^ ((1 - 2 / p0)⁻¹) / mass * (1 + F / t) ^ ((1 - 2 / p0)⁻¹) := by
      field_simp
    _ ≤ C * A ^ C / mass * (1 + F / t) ^ ((1 - 2 / p0)⁻¹) := by
      have hCpos : (0:ℝ) ≤ C :=
        le_trans (le_of_lt (mul_pos (mul_pos (by positivity) hUC)
          (Real.rpow_pos_of_pos hNpos _))) hC1
      have hnum : (2 ^ (k + 1) * ultraConstant p0 * (((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹))) *
          A ^ ((1 - 2 / p0)⁻¹) ≤ C * A ^ C :=
        mul_le_mul hC1 hApow (Real.rpow_nonneg hApos.le _) hCpos
      have hdiv : (2 ^ (k + 1) * ultraConstant p0 * (((k : ℝ) + 1) ^ ((1 - 2 / p0)⁻¹))) *
          A ^ ((1 - 2 / p0)⁻¹) / mass ≤ C * A ^ C / mass := by gcongr
      exact mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg hVpos.le _)

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
