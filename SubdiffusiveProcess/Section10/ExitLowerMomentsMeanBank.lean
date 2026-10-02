import SubdiffusiveProcess.Section10.ExitLowerMomentsMeanConsumer

open MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.ExitLowerMoments

/-- Markov's inequality gives one good environment event of mass at least half.
Its threshold is deterministic and independent of the starting point. -/
theorem good_mean_bank_mass {Ω : Type*} [MeasurableSpace Ω]
    (nu : Measure Ω) [IsProbabilityMeasure nu] (K : Ω → ℝ≥0) (hK : Measurable K)
    (M : ℝ≥0) (hM : 1 ≤ M) (hmean : (∫⁻ omega, (K omega : ℝ≥0∞) ∂nu) ≤ M) :
    (1/2 : ℝ≥0∞) ≤ nu {omega | K omega ≤ 2*M} := by
  let G := {omega | K omega ≤ 2*M}
  have hG : MeasurableSet G := measurableSet_le hK measurable_const
  have h2M : 0 < 2*M := mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hM)
  have hb : nu Gᶜ ≤ (1/2 : ℝ≥0∞) := by
    calc
      nu Gᶜ ≤ nu {omega | ((2*M : ℝ≥0) : ℝ≥0∞) ≤ (K omega : ℝ≥0∞)} := by
        apply measure_mono
        intro omega hw
        change ¬ K omega ≤ 2*M at hw
        change ((2*M : ℝ≥0) : ℝ≥0∞) ≤ (K omega : ℝ≥0∞)
        exact_mod_cast (lt_of_not_ge hw).le
      _ ≤ (∫⁻ omega, (K omega : ℝ≥0∞) ∂nu) / ((2*M : ℝ≥0) : ℝ≥0∞) :=
        meas_ge_le_lintegral_div hK.coe_nnreal_ennreal.aemeasurable
          (ENNReal.coe_ne_zero.mpr h2M.ne') ENNReal.coe_ne_top
      _ ≤ (M : ℝ≥0∞) / ((2*M : ℝ≥0) : ℝ≥0∞) := ENNReal.div_le_div_right hmean _
      _ = 1/2 := by
        have hn : M/(2*M) = (1/2 : ℝ≥0) := by
          apply NNReal.coe_injective
          have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast
            (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hM))
          simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one]
          field_simp
        rw [← ENNReal.coe_div h2M.ne', hn]
        norm_num
  have hs : (1 : ℝ≥0∞) ≤ nu G + 1/2 := by
    calc
      1 = nu G + nu Gᶜ := by rw [measure_add_measure_compl hG, measure_univ]
      _ ≤ _ := add_le_add le_rfl hb
  have h := tsub_le_iff_right.mpr hs
  norm_num at h ⊢
  exact h

def meanBankLowerConstant (c : ℝ) (M : ℝ≥0) (p : ℝ) : ℝ :=
  let A := c / (2*(M : ℝ))^2
  let B := SubdiffusiveProcess.Section10.ExitTailMoments.upperMomentConstant 2 * (2*(M : ℝ))^2
  ((A/4)^p * (A^2/(4*B))) / 2

lemma meanBankLowerConstant_pos (c : ℝ) (M : ℝ≥0) (p : ℝ)
    (hc : 0 < c) (hM : 1 ≤ M) : 0 < meanBankLowerConstant c M p := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  have hC := SubdiffusiveProcess.Section10.ExitTailMoments.upperMomentConstant_pos 2 (by norm_num)
  unfold meanBankLowerConstant
  positivity

/-- The normalized physical mean bank implies averaged inf-start lower moments
at every real p>0. The mean envelope is explicit; neither a measurable moment
infimum nor a Jensen step is needed. -/
theorem averaged_lower_moment_of_mean_bank {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (nu : Measure Ω) [IsProbabilityMeasure nu]
    (law : Ω → Kernel (Homogenization.Vec d) (DiffusionPath d))
    [∀ omega, IsMarkovKernel (law omega)]
    (U V : Set (Homogenization.Vec d)) (hU : IsOpen U)
    (K : Ω → ℝ≥0) (hK : Measurable K) (hKone : ∀ omega, 1 ≤ K omega)
    (M : ℝ≥0) (hM : 1 ≤ M)
    (hmean : (∫⁻ omega, (K omega : ℝ≥0∞) ∂nu) ≤ M)
    (c : ℝ) (hc : 0 < c)
    (hSM : ∀ᵐ omega ∂nu, SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov
      ((law omega).map LifetimePath.ofContinuousPath))
    (hbank : ∀ᵐ omega ∂nu,
      (∀ x ∈ U, (∫⁻ w, ContinuousPath.exitTime U w ∂law omega x) ≤ (K omega : ℝ≥0∞)) ∧
      (∀ x ∈ V, ENNReal.ofReal (c/(K omega : ℝ)^2) ≤
        ∫⁻ w, ContinuousPath.exitTime U w ∂law omega x))
    (p : ℝ) (hp : 0 < p) :
    ENNReal.ofReal (meanBankLowerConstant c M p) ≤
      ∫⁻ omega, (⨅ x ∈ V, ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂law omega x) ∂nu := by
  let G := {omega | K omega ≤ 2*M}
  let A : ℝ := c/(2*(M : ℝ))^2
  let B : ℝ := SubdiffusiveProcess.Section10.ExitTailMoments.upperMomentConstant 2 * (2*(M : ℝ))^2
  let F : ℝ := (A/4)^p * (A^2/(4*B))
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  have hA : 0 < A := div_pos hc (pow_pos (mul_pos (by norm_num) hMpos) _)
  have hG : MeasurableSet G := measurableSet_le hK measurable_const
  have hpoint : ∀ᵐ omega ∂nu,
      G.indicator (fun _ => ENNReal.ofReal F) omega ≤
        ⨅ x ∈ V, ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂law omega x := by
    filter_upwards [hSM, hbank] with omega hs hb
    by_cases hg : omega ∈ G
    · rw [Set.indicator_of_mem hg]
      apply le_iInf
      intro x
      apply le_iInf
      intro hx
      have hk : (K omega : ℝ) ≤ 2*(M : ℝ) := by exact_mod_cast hg
      have hlow : ENNReal.ofReal A ≤ ∫⁻ w, ContinuousPath.exitTime U w ∂law omega x := by
        apply le_trans _ (hb.2 x hx)
        apply ENNReal.ofReal_le_ofReal
        have hkpos : (0 : ℝ) < K omega := by
          exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) (hKone omega))
        exact div_le_div_of_nonneg_left hc.le (pow_pos hkpos _)
          (pow_le_pow_left₀ (K omega).coe_nonneg hk 2)
      have hup : ∀ y ∈ U, (∫⁻ w, ContinuousPath.exitTime U w ∂law omega y) ≤
          ((2*M : ℝ≥0) : ℝ≥0∞) := by
        intro y hy
        exact (hb.1 y hy).trans (by exact_mod_cast hg)
      exact continuous_moment_lower_of_mean_bounds (law omega) hs U hU (2*M)
        (hM.trans (le_mul_of_one_le_left (zero_le M) (by norm_num))) hup A hA x hlow p hp
    · rw [Set.indicator_of_notMem hg]
      exact zero_le _
  calc
    _ = ENNReal.ofReal F * (1/2 : ℝ≥0∞) := by
      change ENNReal.ofReal (F/2) = _
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_ofNat, div_eq_mul_inv, one_div]
    _ ≤ ENNReal.ofReal F * nu G :=
      mul_le_mul_right (good_mean_bank_mass nu K hK M hM hmean) _
    _ = ∫⁻ omega, G.indicator (fun _ => ENNReal.ofReal F) omega ∂nu := by
      rw [lintegral_indicator hG, setLIntegral_const]
    _ ≤ _ := lintegral_mono_ae hpoint

end SubdiffusiveProcess.Section10.ExitLowerMoments
