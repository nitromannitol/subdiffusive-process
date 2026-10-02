import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpperContraction




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationHeat
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationBootstrap
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}

/-- The constant one is in every `Lᵖ` space of a finite measure. -/
theorem memLp_one_const {α : Type*} [MeasurableSpace α] {mu : Measure α} [IsFiniteMeasure mu]
    (p : ℝ≥0∞) : MemLp (fun _ : α => (1 : ℝ)) p mu :=
  memLp_const 1

/-- The `L²` seminorm of the constant one. -/
theorem eLpNorm_two_const_one {α : Type*} [MeasurableSpace α] (mu : Measure α) :
    eLpNorm (fun _ : α => (1 : ℝ)) 2 mu = mu Set.univ ^ (1 / (2 : ℝ)) := by
  rcases eq_or_ne mu 0 with hmu | hmu
  · simp [hmu]
  · rw [eLpNorm_const (1 : ℝ) (by norm_num) hmu]
    simp

/-- **Decay of the killed survival mass.**  The resolvent contraction and the exponential mixture
comparison bound the total survival mass at a multiple of the resolvent scale. -/
theorem lintegral_killedKernel_univ_le
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    {U : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hmtop : (weightedMeasure rho) U ≠ ∞)
    {A F s : ℝ} (hA : 0 < A) (hF : 0 < F) (hs : 0 < s)
    (hPoin : PoincareAssumption c rho U A F) (n : ℕ) :
    (∫⁻ x, killedKernel law U hU (((n + 1 : ℕ) : NNReal) * Real.toNNReal s) x Set.univ
        ∂((weightedMeasure rho).restrict U)) ≤
      ((2 : ℝ≥0∞) * ENNReal.ofReal ((1 + s / (A * F))⁻¹)) ^ (n + 1) *
        ((weightedMeasure rho).restrict U) Set.univ := by
  set mu := (weightedMeasure rho).restrict U with hmudef
  have hmuniv : mu Set.univ = (weightedMeasure rho) U := Measure.restrict_apply_univ _
  haveI hfinite : IsFiniteMeasure mu := ⟨by rw [hmuniv]; exact lt_of_le_of_ne le_top hmtop⟩
  set a : NNReal := Real.toNNReal s with hadef
  have hacoe : ((a : NNReal) : ℝ) = s := Real.coe_toNNReal s hs.le
  have ha : 0 < a := by rw [← NNReal.coe_pos, hacoe]; exact hs
  set Q : NNReal → Kernel (Vec d) (Vec d) := fun tau => killedKernel law U hU tau with hQdef
  set R : Kernel (Vec d) (Vec d) := resolventKernel law U hU s hs with hRdef
  have hsubQ : ∀ tau, IsSubMarkovKernel (Q tau) :=
    fun tau => killedKernel_subMarkov law U hU tau
  have hrectQ : ∀ tau, ∀ C D : Set (Vec d), MeasurableSet C → MeasurableSet D →
      (∫⁻ x in C, Q tau x D ∂mu) = ∫⁻ x in D, Q tau x C ∂mu :=
    fun tau => killedKernel_rectangle_symmetry hD hU hUb tau
  have hmuQ : ∀ tau, Q tau ∘ₘ mu ≤ mu :=
    fun tau => subinvariant_of_rectangle_symmetry _ _ (hsubQ tau) (hrectQ tau)
  have hsymQ : ∀ tau, (mu ⊗ₘ Q tau).map Prod.swap = mu ⊗ₘ Q tau :=
    fun tau => compProd_symm (hsubQ tau) (hrectQ tau)
  have hsemQ : ∀ u v : NNReal, Q (u + v) = Q v ∘ₖ Q u :=
    fun u v => semigroup law hD.1 U hU u v
  have hjointQ : ∀ B : Set (Vec d), MeasurableSet B →
      Measurable (fun q : NNReal × Vec d => Q q.1 q.2 B) :=
    fun B hB => killedKernel_joint_measurable law U hU B hB
  have hRsub : IsSubMarkovKernel R := resolventKernel_subMarkov law U hU s hs
  have hmix : ∀ (x : Vec d) (B : Set (Vec d)), MeasurableSet B →
      R x B = ∫⁻ u : ℝ, Q (Real.toNNReal u) x B ∂expMeasure ((a : ℝ)⁻¹) := by
    intro x B hB
    rw [hacoe]
    exact resolventKernel_apply_mixture law U hU s hs x B hB
  letI : IsProbabilityMeasure (expMeasure ((a : ℝ)⁻¹)) :=
    isProbabilityMeasure_expMeasure (inv_pos.mpr (by rw [hacoe]; exact hs))
  -- the constant test function
  set one : Vec d → ℝ≥0∞ := fun _ => 1 with honedef
  have hone : Measurable one := measurable_const
  have hpairing : ∀ tau : NNReal, pairing mu (Q tau) one one = ∫⁻ x, Q tau x Set.univ ∂mu := by
    intro tau
    simp [pairing, positiveIntegral, one]
  -- the mixture lower bound
  have hlow : (1 / 2 : ℝ≥0∞) ^ (n + 1) * pairing mu (Q (((n + 1 : ℕ) : NNReal) * a)) one one ≤
      ∫⁻ x, one x * ((positiveIntegral R)^[n + 1] one) x ∂mu := by
    rw [iteration_mixture hsubQ hjointQ hmix hsemQ hone hone n]
    simpa only [zero_add] using time_average_lower (exponential_half_mass ha)
      (diagonal_antitone hsubQ hmuQ hsymQ hsemQ hone) (n + 1) 0
  -- the iterate in real carriers
  have h1nn : ∀ x : Vec d, (0 : ℝ) ≤ (fun _ : Vec d => (1 : ℝ)) x := fun _ => zero_le_one
  have h1le : ∀ x : Vec d, (fun _ : Vec d => (1 : ℝ)) x ≤ 1 := fun _ => le_rfl
  have hiter := iterate_ofReal hRsub (stronglyMeasurable_const (b := (1 : ℝ))) h1nn h1le (n + 1)
  set g : Vec d → ℝ := (kernelIntegral R)^[n + 1] (fun _ : Vec d => (1 : ℝ)) with hgdef
  have hofone : (fun x : Vec d => ENNReal.ofReal ((fun _ : Vec d => (1 : ℝ)) x)) = one := by
    funext x
    simp [one]
  have hval : (positiveIntegral R)^[n + 1] one = fun x => ENNReal.ofReal (g x) := by
    rw [← hofone, hiter.2.2]
  -- the `L¹` bound for the iterate
  have hmem1 : MemLp (fun _ : Vec d => (1 : ℝ)) 1 mu := memLp_one_const 1
  have hmem2 : MemLp (fun _ : Vec d => (1 : ℝ)) 2 mu := memLp_one_const 2
  obtain ⟨haeq, hmemg1⟩ := iterate_killedResolvent_ae hD hU hUb hs hmem1 (n + 1)
  obtain ⟨hmemk2, hbound2⟩ :=
    eLpNorm_two_iterate_killedResolvent_le hD hU hUb hA hF hs hPoin hmem2 (n + 1)
  have hgmem2 : MemLp g 2 mu := (memLp_congr_ae haeq).mp hmemk2
  have hgnorm2 : eLpNorm g 2 mu ≤
      ENNReal.ofReal ((1 + s / (A * F))⁻¹) ^ (n + 1) * mu Set.univ ^ (1 / (2 : ℝ)) := by
    rw [← eLpNorm_congr_ae haeq, ← eLpNorm_two_const_one mu]
    exact hbound2
  have hgint : (∫⁻ x, ENNReal.ofReal (g x) ∂mu) ≤
      ENNReal.ofReal ((1 + s / (A * F))⁻¹) ^ (n + 1) * mu Set.univ := by
    have henorm : (∫⁻ x, ENNReal.ofReal (g x) ∂mu) = eLpNorm g 1 mu := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact lintegral_congr fun x => (Real.enorm_eq_ofReal (hiter.2.1 x).1).symm
    have hholder : eLpNorm g 1 mu ≤ eLpNorm g 2 mu * mu Set.univ ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) := by
      simpa using
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := mu) (f := g)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hgmem2.1
    have hsplit : mu Set.univ ^ (1 / (2 : ℝ)) * mu Set.univ ^ (1 / (2 : ℝ)) = mu Set.univ := by
      rw [← ENNReal.rpow_add_of_nonneg (1 / (2 : ℝ)) (1 / (2 : ℝ)) (by norm_num) (by norm_num)]
      norm_num
    calc (∫⁻ x, ENNReal.ofReal (g x) ∂mu) = eLpNorm g 1 mu := henorm
      _ ≤ eLpNorm g 2 mu * mu Set.univ ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) := hholder
      _ = eLpNorm g 2 mu * mu Set.univ ^ (1 / (2 : ℝ)) := by norm_num
      _ ≤ (ENNReal.ofReal ((1 + s / (A * F))⁻¹) ^ (n + 1) * mu Set.univ ^ (1 / (2 : ℝ))) *
            mu Set.univ ^ (1 / (2 : ℝ)) := by gcongr
      _ = ENNReal.ofReal ((1 + s / (A * F))⁻¹) ^ (n + 1) * mu Set.univ := by
            rw [mul_assoc, hsplit]
  -- combine
  have hstep : (1 / 2 : ℝ≥0∞) ^ (n + 1) * (∫⁻ x, Q (((n + 1 : ℕ) : NNReal) * a) x Set.univ ∂mu) ≤
      ENNReal.ofReal ((1 + s / (A * F))⁻¹) ^ (n + 1) * mu Set.univ := by
    rw [← hpairing]
    refine le_trans hlow ?_
    calc (∫⁻ x, one x * ((positiveIntegral R)^[n + 1] one) x ∂mu)
        = ∫⁻ x, ENNReal.ofReal (g x) ∂mu := by
          rw [hval]
          exact lintegral_congr fun x => one_mul _
      _ ≤ _ := hgint
  have htwo : ((2 : ℝ≥0∞) ^ (n + 1)) * ((1 / 2 : ℝ≥0∞) ^ (n + 1)) = 1 := by
    rw [← mul_pow]
    rw [show (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 by
      rw [one_div, ENNReal.mul_inv_cancel (by simp) (by simp)]]
    simp
  calc (∫⁻ x, Q (((n + 1 : ℕ) : NNReal) * a) x Set.univ ∂mu)
      = ((2 : ℝ≥0∞) ^ (n + 1)) *
          ((1 / 2 : ℝ≥0∞) ^ (n + 1) * ∫⁻ x, Q (((n + 1 : ℕ) : NNReal) * a) x Set.univ ∂mu) := by
        rw [← mul_assoc, htwo, one_mul]
    _ ≤ ((2 : ℝ≥0∞) ^ (n + 1)) *
          (ENNReal.ofReal ((1 + s / (A * F))⁻¹) ^ (n + 1) * mu Set.univ) := by gcongr
    _ = ((2 : ℝ≥0∞) * ENNReal.ofReal ((1 + s / (A * F))⁻¹)) ^ (n + 1) * mu Set.univ := by
        rw [mul_pow, mul_assoc]

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventExitUpper
