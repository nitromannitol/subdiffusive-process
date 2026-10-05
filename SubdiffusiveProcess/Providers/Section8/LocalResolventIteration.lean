module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationDensity

@[expose] public section

set_option autoImplicit false

noncomputable section

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationBootstrap
open scoped ENNReal NNReal


/-- Ultracontractivity of a fixed resolvent power and the killed transition density bound. -/

theorem SubdiffusiveProcess.Providers.Section8.local_resolvent_iteration (p0 : ℝ) (hp0 : 2 < p0) :
    ∃ N0 : ℕ, ∃ C : ℝ, 0 < N0 ∧ 0 < C ∧
      ∀ d : ℕ, ∀ _hd : 2 ≤ d, ∀ c rho : Vec d → ℝ, ∀ law : Kernel (Vec d) (Path d),
        LocalDiffusion c rho law → ∀ y : Vec d, ∀ side : ℝ, 0 < side →
        let U := Homogenization.axisCube y side
        let mu := (weightedMeasure rho).restrict U
        let mass := ((weightedMeasure rho) U).toReal
        ∀ A F : ℝ, 1 ≤ A → 0 < F → SobolevAssumption c rho U p0 A F →
          (∀ s : ℝ, 0 < s → ∀ f : Vec d → ℝ, MemLp f 1 mu →
            eLpNorm ((killedResolvent law U s)^[N0] f) ∞ mu ≤
              ENNReal.ofReal (C * A ^ C / mass * (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) *
                eLpNorm f 1 mu) ∧
          (∀ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law rho U p →
            (∀ t : ℝ, 0 < t →
              ∀ᵐ z ∂(mu.prod mu),
                p t z.1 z.2 ≤ C * A ^ C / mass * (1 + F / t) ^ ((1 - 2 / p0)⁻¹)) ∧
            (ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2)
                (Ioi 0 ×ˢ U ×ˢ U) →
              ∀ t : ℝ, 0 < t → ∀ x ∈ U,
                p t x x ≤ C * A ^ C / mass * (1 + F / t) ^ ((1 - 2 / p0)⁻¹)))

:= by
  obtain ⟨k, hk⟩ := iteration_count (qExp p0) (rExp p0) (one_lt_rExp hp0)
  refine ⟨k + 1, frozenConstant p0 k, Nat.succ_pos k, frozenConstant_pos hp0 k, ?_⟩
  intro d _hd c rho law hD y side hside U mu mass A F hA hF hSob
  have hMk := isMarkovKernel_of_localDiffusion hD
  have hrho : ∀ K : Set (Vec d), IsCompact K → CoefficientOn K rho :=
    fun K hK => (hD.2.1 K hK).2
  have hUdom : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_axisCube y side
  have hm0 : (weightedMeasure rho) U ≠ 0 :=
    (weightedMeasure_axisCube_pos hrho y side hside).ne'
  have hmtop : (weightedMeasure rho) U ≠ ∞ := (weightedMeasure_axisCube_lt_top hrho y side).ne
  have hmass : 0 < mass := ENNReal.toReal_pos hm0 hmtop
  have hC2 : (1 - 2 / p0)⁻¹ ≤ frozenConstant p0 k := theta_inv_le_frozenConstant k
  constructor
  · intro s hs f hf
    refine le_trans (iterate_eLpNorm_le hD hUdom hm0 hmtop hp0 hA hF hs hSob k hk hf) ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    exact ultraBound_le hA (ultra_le_frozenConstant hp0 k) hC2 hmass (by positivity)
  · intro p hp
    have hae : ∀ t : ℝ, 0 < t → ∀ᵐ z ∂(mu.prod mu),
        p t z.1 z.2 ≤ frozenConstant p0 k * A ^ (frozenConstant p0 k) / mass *
          (1 + F / t) ^ ((1 - 2 / p0)⁻¹) := by
      intro t ht
      filter_upwards [density_ae_le hD hUdom hm0 hmtop hp0 hA hF hSob k hk hp t ht] with z hz
      exact hz.trans (heatBound_le k hp0 hA hF ht hmass (heat_le_frozenConstant hp0 k) hC2)
    refine ⟨hae, fun hcont => ?_⟩
    exact continuousOn_density_diagonal_le hrho y side p
      (fun t => frozenConstant p0 k * A ^ (frozenConstant p0 k) / mass *
        (1 + F / t) ^ ((1 - 2 / p0)⁻¹)) hcont hae
