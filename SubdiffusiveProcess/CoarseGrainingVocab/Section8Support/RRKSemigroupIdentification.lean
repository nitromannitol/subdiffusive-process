module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKLaplace
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKOperatorHalf
public import MarkovProcess.Semigroup.ResolventGeneration

@[expose] public section




open MeasureTheory Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKScalar
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKLaplace
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKComplexLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKOperatorHalf
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open MarkovProcess.Semigroup
open scoped RealInnerProductSpace

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKSemigroupIdentification

variable {X : Type*} [MeasurableSpace X] {mu : Measure X}

local instance : IsometricContinuousFunctionalCalculus ℝ
    (Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) IsSelfAdjoint := by
  simpa using! (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
    (A := Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu))

/-- `realOp` bundled as a continuous linear map. -/
def realOpL (mu : Measure X) :
    (Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) →L[ℝ] (Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) :=
  LinearMap.mkContinuous
    { toFun := realOp
      map_add' := fun T S => by
        refine ContinuousLinearMap.ext fun f => ?_
        simp only [realOp_apply, add_apply, map_add]
      map_smul' := fun c T => by
        refine ContinuousLinearMap.ext fun f => ?_
        simp only [realOp_apply, smul_apply, map_smul, RingHom.id_apply] }
    1 (fun T => by simpa using norm_realOp_le T)

@[simp] theorem realOpL_apply (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) : realOpL mu T = realOp T := rfl

variable {s : ℝ} {R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu}

theorem continuousOn_rrkSemigroup (hs : 0 < s) : ContinuousOn (rrkSemigroup s R) (Ioi 0) := by
  have hdiv : ContinuousOn (fun t : ℝ => t / s) (Ioi 0) := (continuous_id.div_const s).continuousOn
  have hmaps : MapsTo (fun t : ℝ => t / s) (Ioi 0) (Ioi 0) := fun t ht => div_pos ht hs
  exact continuous_realOp.comp_continuousOn ((continuousOn_cfc_rrkFn 0 R).comp hdiv hmaps)

/-- `φ_t(R) ∘ R` is the real operator of `φ_t(A) A`. -/
theorem realOp_cfc_mul_cxOp (hs : 0 < s) (hR : IsSymmetricOp R) {t : ℝ} (ht : 0 < t) :
    realOp (cfc (rrkFn (t / s) 0) (cxOp R) * cxOp R) = (rrkSemigroup s R t).comp R := by
  rw [realOp_mul_of_conjOp
      (conjOp_cfc hR _ (continuous_rrkFn (div_pos ht hs) 0).continuousOn), realOp_cxOp]
  rfl

theorem norm_rrkSemigroup_le_one (hs : 0 < s) (hspec : spectrum ℝ (cxOp R) ⊆ Icc 0 1)
    {t : ℝ} (ht : 0 < t) : ‖rrkSemigroup s R t‖ ≤ 1 :=
  le_trans (norm_realOp_le _) (norm_cfc_rrkFn_le_one hspec (div_pos ht hs))

theorem norm_rrkSemigroup_comp_sub_le (hs : 0 < s) (hR : IsSymmetricOp R)
    (hspec : spectrum ℝ (cxOp R) ⊆ Icc 0 1) {t : ℝ} (ht : 0 < t) :
    ‖(rrkSemigroup s R t).comp R - R‖ ≤ t / s := by
  have h1 : (rrkSemigroup s R t).comp R - R
      = realOp (cfc (rrkFn (t / s) 0) (cxOp R) * cxOp R - cxOp R) := by
    rw [realOp_sub, realOp_cfc_mul_cxOp hs hR ht, realOp_cxOp]
  rw [h1]
  exact le_trans (norm_realOp_le _)
    (norm_cfc_rrkFn_mul_sub_le (isSelfAdjoint_cxOp hR) hspec (div_pos ht hs))

/-- The semigroup family on `NNReal`, with the identity at time `0`. -/
def rrkOperator (s : ℝ) (R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (t : NNReal) :
    Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu :=
  if t = 0 then ContinuousLinearMap.id ℝ _ else rrkSemigroup s R (t : ℝ)

@[simp] theorem rrkOperator_zero : rrkOperator s R 0 = ContinuousLinearMap.id ℝ _ :=
  ite_eq_left rfl

theorem rrkOperator_of_ne {t : NNReal} (ht : t ≠ 0) :
    rrkOperator s R t = rrkSemigroup s R (t : ℝ) := ite_eq_right ht

theorem coe_pos_of_ne {t : NNReal} (ht : t ≠ 0) : (0:ℝ) < (t : ℝ) :=
  lt_of_le_of_ne t.coe_nonneg (fun h => ht (NNReal.coe_injective h.symm))

theorem continuous_rrkOperator_apply (hs : 0 < s) (hR : IsSymmetricOp R)
    (hspec : spectrum ℝ (cxOp R) ⊆ Icc 0 1) (hdense : DenseRange R) (x : Lp ℝ 2 mu) :
    Continuous (fun t : NNReal => rrkOperator s R t x) := by
  rw [continuous_iff_continuousAt]
  intro t0
  rcases eq_or_ne t0 0 with rfl | ht0
  · -- strong continuity at time zero
    have hQ0 : rrkOperator s R 0 x = x := by rw [rrkOperator_zero]; rfl
    show ContinuousAt (fun t : NNReal => rrkOperator s R t x) 0
    rw [ContinuousAt, hQ0]
    refine Metric.tendsto_nhds_nhds.2 fun ε hε => ?_
    obtain ⟨z, hz⟩ := Metric.denseRange_iff.1 hdense x (ε / 3) (by linarith)
    set C : ℝ := ‖z‖ + 1 with hC
    have hCpos : 0 < C := by positivity
    refine ⟨s * ε / (3 * C), by positivity, fun {t} hd => ?_⟩
    rcases eq_or_ne t 0 with rfl | ht
    · simpa [hQ0] using hε
    · have htpos : (0:ℝ) < (t : ℝ) := coe_pos_of_ne ht
      have hdt : (t : ℝ) < s * ε / (3 * C) := by
        rw [NNReal.dist_eq] at hd
        simpa [abs_of_nonneg t.coe_nonneg] using hd
      have hzx : ‖R z - x‖ < ε / 3 := by
        rw [← dist_eq_norm, dist_comm]; simpa [dist_comm] using hz
      have h1 : ‖rrkSemigroup s R (t : ℝ) (x - R z)‖ ≤ ε / 3 := by
        calc ‖rrkSemigroup s R (t : ℝ) (x - R z)‖
            ≤ ‖rrkSemigroup s R (t : ℝ)‖ * ‖x - R z‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ 1 * ‖x - R z‖ :=
              mul_le_mul_of_nonneg_right (norm_rrkSemigroup_le_one hs hspec htpos) (norm_nonneg _)
          _ = ‖R z - x‖ := by rw [one_mul, ← norm_neg]; congr 1; abel
          _ ≤ ε / 3 := hzx.le
      have h2 : ‖rrkSemigroup s R (t : ℝ) (R z) - R z‖ < ε / 3 := by
        have hb : ‖rrkSemigroup s R (t : ℝ) (R z) - R z‖
            ≤ ‖(rrkSemigroup s R (t : ℝ)).comp R - R‖ * ‖z‖ := by
          have := ContinuousLinearMap.le_opNorm
            ((rrkSemigroup s R (t : ℝ)).comp R - R) z
          simpa using this
        have hb2 : ‖(rrkSemigroup s R (t : ℝ)).comp R - R‖ * ‖z‖ ≤ ((t : ℝ) / s) * ‖z‖ :=
          mul_le_mul_of_nonneg_right
            (norm_rrkSemigroup_comp_sub_le hs hR hspec htpos) (norm_nonneg z)
        have hb3 : ((t : ℝ) / s) * ‖z‖ < ε / 3 := by
          have hz1 : ‖z‖ < C := by rw [hC]; linarith
          have hkey : (t : ℝ) / s < ε / (3 * C) := by
            rw [div_lt_div_iff₀ hs (by positivity)]
            calc (t : ℝ) * (3 * C) < (s * ε / (3 * C)) * (3 * C) := by
                  exact mul_lt_mul_of_pos_right hdt (by positivity)
              _ = s * ε := by field_simp
              _ = ε * s := by ring
          calc ((t : ℝ) / s) * ‖z‖ ≤ ((t : ℝ) / s) * C :=
                mul_le_mul_of_nonneg_left hz1.le (by positivity)
            _ < (ε / (3 * C)) * C := mul_lt_mul_of_pos_right hkey hCpos
            _ = ε / 3 := by field_simp
        linarith
      have hsplit : rrkSemigroup s R (t : ℝ) x - x
          = rrkSemigroup s R (t : ℝ) (x - R z)
            + (rrkSemigroup s R (t : ℝ) (R z) - R z) + (R z - x) := by
        rw [map_sub]; abel
      rw [rrkOperator_of_ne ht, dist_eq_norm, hsplit]
      calc ‖rrkSemigroup s R (t : ℝ) (x - R z)
              + (rrkSemigroup s R (t : ℝ) (R z) - R z) + (R z - x)‖
          ≤ ‖rrkSemigroup s R (t : ℝ) (x - R z) + (rrkSemigroup s R (t : ℝ) (R z) - R z)‖
              + ‖R z - x‖ := norm_add_le _ _
        _ ≤ ‖rrkSemigroup s R (t : ℝ) (x - R z)‖ + ‖rrkSemigroup s R (t : ℝ) (R z) - R z‖
              + ‖R z - x‖ := by
            have := norm_add_le (rrkSemigroup s R (t : ℝ) (x - R z))
              (rrkSemigroup s R (t : ℝ) (R z) - R z)
            linarith
        _ < ε := by linarith
  · -- norm continuity at positive times
    have hpos : (0:ℝ) < (t0 : ℝ) := coe_pos_of_ne ht0
    have heq : (fun t : NNReal => rrkSemigroup s R (t : ℝ) x)
        =ᶠ[𝓝 t0] fun t : NNReal => rrkOperator s R t x := by
      filter_upwards [isOpen_ne.mem_nhds ht0] with t ht
      rw [rrkOperator_of_ne ht]
    refine ContinuousAt.congr ?_ heq
    have hcont : ContinuousAt (fun u : ℝ => rrkSemigroup s R u) (t0 : ℝ) :=
      (continuousOn_rrkSemigroup hs).continuousAt (Ioi_mem_nhds hpos)
    have h1 : ContinuousAt (fun t : NNReal => rrkSemigroup s R (t : ℝ)) t0 :=
      hcont.comp (NNReal.continuous_coe.continuousAt)
    exact ((ContinuousLinearMap.apply ℝ (Lp ℝ 2 mu) x).continuous.continuousAt).comp h1

/-- **`t ↦ φ_t(R)` is a strongly continuous contraction semigroup.** -/
def rrkSCCS (hs : 0 < s) (hR : IsSymmetricOp R) (hspec : spectrum ℝ (cxOp R) ⊆ Icc 0 1)
    (hdense : DenseRange R) : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu) where
  operator := rrkOperator s R
  operator_zero := rrkOperator_zero
  operator_add := by
    intro u v
    rcases eq_or_ne u 0 with rfl | hu
    · rw [zero_add, rrkOperator_zero, ContinuousLinearMap.id_comp]
    rcases eq_or_ne v 0 with rfl | hv
    · rw [add_zero, rrkOperator_zero, ContinuousLinearMap.comp_id]
    · have huv : u + v ≠ 0 := by
        intro h
        exact hu (by simpa using (add_eq_zero_iff_of_nonneg zero_le zero_le).1 h |>.1)
      rw [rrkOperator_of_ne huv, rrkOperator_of_ne hu, rrkOperator_of_ne hv,
        rrkSemigroup_comp hs hR (coe_pos_of_ne hu) (coe_pos_of_ne hv)]
      norm_cast
  opNorm_le_one := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · rw [rrkOperator_zero]; exact ContinuousLinearMap.norm_id_le
    · rw [rrkOperator_of_ne ht]
      exact norm_rrkSemigroup_le_one hs hspec (coe_pos_of_ne ht)
  continuous_orbit := continuous_rrkOperator_apply hs hR hspec hdense

@[simp] theorem rrkSCCS_operator (hs : 0 < s) (hR : IsSymmetricOp R)
    (hspec : spectrum ℝ (cxOp R) ⊆ Icc 0 1) (hdense : DenseRange R) (t : NNReal) :
    (rrkSCCS hs hR hspec hdense) t = rrkOperator s R t := rfl

/-- **The Laplace transform of `t ↦ φ_t(R)` at the shift `s⁻¹` is `s R`.** -/
theorem integral_rrkOperator_apply (hs : 0 < s) (hR : IsSymmetricOp R)
    (hspec : spectrum ℝ (cxOp R) ⊆ Icc 0 1) (x : Lp ℝ 2 mu) :
    (∫ t in Ioi (0:ℝ), Real.exp (-s⁻¹ * t) • rrkOperator s R (Real.toNNReal t) x) = s • R x := by
  have hA : IsSelfAdjoint (cxOp R) := isSelfAdjoint_cxOp hR
  set Psi : (Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) →L[ℝ] Lp ℝ 2 mu :=
    (ContinuousLinearMap.apply ℝ (Lp ℝ 2 mu) x).comp (realOpL mu) with hPsi
  have hPsi_apply : ∀ T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu, Psi T = realOp T x := fun T => rfl
  have hcongr : ∀ t ∈ Ioi (0:ℝ),
      Real.exp (-s⁻¹ * t) • rrkOperator s R (Real.toNNReal t) x
        = Psi (Real.exp (-s⁻¹ * t) • cfc (rrkFn (t / s) 0) (cxOp R)) := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    have hne : Real.toNNReal t ≠ 0 := by
      simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
      exact ht'
    rw [rrkOperator_of_ne hne, Real.coe_toNNReal t ht'.le, map_smul, hPsi_apply]
    rfl
  have hmap : (∫ t in Ioi (0 : ℝ),
      Psi (Real.exp (-s⁻¹ * t) • cfc (rrkFn (t / s) 0) (cxOp R))) =
      Psi (∫ t in Ioi (0 : ℝ),
        Real.exp (-s⁻¹ * t) • cfc (rrkFn (t / s) 0) (cxOp R)) := by
    simpa only using! Psi.integral_comp_comm (integrable_expSmulCfc hA hspec hs)
  have hint : (∫ t in Ioi (0 : ℝ),
      Real.exp (-s⁻¹ * t) • cfc (rrkFn (t / s) 0) (cxOp R)) = s • cxOp R := by
    simpa using! integral_expSmulCfc hA hspec hs
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hmap,
    hint, map_smul, hPsi_apply, realOp_cxOp]

/-- **A strongly continuous contraction semigroup is determined by its resolvent at a single
positive shift.** -/
theorem sccs_ext_of_resolvent_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (S T : StronglyContinuousContractionSemigroup E) (al : PositiveShift)
    (h : S.resolvent al = T.resolvent al) : S = T := by
  refine S.ext_of_generator T ?_ ?_
  · apply SetLike.coe_injective
    rw [S.generatorDomain_eq_range_resolvent al, T.generatorDomain_eq_range_resolvent al, h]
  · intro f hS hT
    obtain ⟨g, hg⟩ : f ∈ Set.range (S.resolvent al) := by
      rw [← S.generatorDomain_eq_range_resolvent al]; exact hS
    rw [S.generator_eq_of_resolvent_eq al hS hg,
      T.generator_eq_of_resolvent_eq al hT (by rw [← h]; exact hg)]

theorem denseRange_of_smul (hs : 0 < s) (hd : DenseRange ((s : ℝ) • R)) : DenseRange R := by
  have hrange : Set.range ((s : ℝ) • R) = Set.range R := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨s • v, by rw [map_smul]; rfl⟩
    · rintro ⟨v, rfl⟩
      refine ⟨s⁻¹ • v, ?_⟩
      rw [smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have : Dense (Set.range ((s : ℝ) • R)) := hd
  rwa [hrange] at this

/-- **The identification `IsResolventSemigroup`.**  A strongly continuous contraction
semigroup whose Laplace transform at the shift `s⁻¹` is `s R` *is* the semigroup `φ_t(R)`
built by the continuous functional calculus. -/
theorem isResolventSemigroup_of_resolvent_eq (hs : 0 < s) (hR : IsSymmetricOp R)
    (hspec : spectrum ℝ (cxOp R) ⊆ Icc 0 1)
    (P : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu))
    (hres : P.resolvent ⟨s⁻¹, mem_Ioi.2 (inv_pos.2 hs)⟩ = (s : ℝ) • R) :
    IsResolventSemigroup s R (fun t : ℝ => P (Real.toNNReal t)) := by
  have hdense : DenseRange R := by
    refine denseRange_of_smul hs ?_
    rw [← hres]
    exact P.denseRange_resolvent _
  have hQ : rrkSCCS hs hR hspec hdense = P := by
    refine sccs_ext_of_resolvent_eq _ _ ⟨s⁻¹, mem_Ioi.2 (inv_pos.2 hs)⟩ ?_
    rw [hres]
    refine ContinuousLinearMap.ext fun x => ?_
    rw [StronglyContinuousContractionSemigroup.resolvent_apply]
    have hlap : ∀ t : ℝ,
        (rrkSCCS hs hR hspec hdense).laplaceIntegrand
          ((⟨s⁻¹, mem_Ioi.2 (inv_pos.2 hs)⟩ : PositiveShift) : ℝ) x t
          = Real.exp (-s⁻¹ * t) • rrkOperator s R (Real.toNNReal t) x := fun t => rfl
    simp only [hlap]
    rw [integral_rrkOperator_apply hs hR hspec x]
    rfl
  intro u hu
  have hop := congrArg
    (fun S : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu) =>
      S.operator (Real.toNNReal u)) hQ
  have hne : Real.toNNReal u ≠ 0 := by
    simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; exact hu
  show P.operator (Real.toNNReal u) = rrkSemigroup s R u
  rw [← hop]
  show rrkOperator s R (Real.toNNReal u) = rrkSemigroup s R u
  rw [rrkOperator_of_ne hne, Real.coe_toNNReal u hu.le]

/-- **The nine non-carrier fields of `ResolventRegularityDatum`**, for the formalization's
diffusion: the seven analytic ones from `rrk_operator_half` through the identification,
and the two sub-Markov ones straight from the probabilistic semigroup. -/
theorem rrk_datum_fields (hs : 0 < s) (N : ℕ) (hR : IsSymmetricOp R)
    (hinj : Function.Injective R) (hspec : spectrum ℝ (cxOp R) ⊆ Icc 0 1)
    (P : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu))
    (hres : P.resolvent ⟨s⁻¹, mem_Ioi.2 (inv_pos.2 hs)⟩ = (s : ℝ) • R)
    (hnn : ∀ t : NNReal, ∀ f : Lp ℝ 2 mu, (0 ≤ᵐ[mu] fun x => f x) →
      0 ≤ᵐ[mu] fun x => (P t f) x)
    (hle : ∀ t : NNReal, ∀ f : Lp ℝ 2 mu, (0 ≤ᵐ[mu] fun x => f x) →
      (∀ᵐ x ∂mu, f x ≤ 1) → ∀ᵐ x ∂mu, (P t f) x ≤ 1) :
    IsSymmetricOp (R ^ N) ∧
      Function.Injective (R ^ N) ∧
      (∀ t, 0 < t → IsSymmetricOp (rrkSmoothing s N R t)) ∧
      (∀ t, 0 < t → (R ^ N).comp (rrkSmoothing s N R t) = P (Real.toNNReal (t / 2))) ∧
      ContinuousOn (rrkSmoothing s N R) (Ioi 0) ∧
      (∀ t, 0 < t → IsSymmetricOp (P (Real.toNNReal t))) ∧
      (∀ t u, 0 < t → 0 < u →
        (P (Real.toNNReal t)).comp (P (Real.toNNReal u)) = P (Real.toNNReal (t + u))) ∧
      (∀ t, 0 < t → ∀ f : Lp ℝ 2 mu, (0 ≤ᵐ[mu] fun x => f x) →
        0 ≤ᵐ[mu] fun x => (P (Real.toNNReal t) f) x) ∧
      (∀ t, 0 < t → ∀ f : Lp ℝ 2 mu, (0 ≤ᵐ[mu] fun x => f x) →
        (∀ᵐ x ∂mu, f x ≤ 1) → ∀ᵐ x ∂mu, (P (Real.toNNReal t) f) x ≤ 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    rrk_operator_half (N := N) hs hR hinj
      (isResolventSemigroup_of_resolvent_eq hs hR hspec P hres)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun t _ => hnn _, fun t _ => hle _⟩

/-! ### The spectral window `[0,1]` from positivity and contractivity -/

theorem reApplyInnerSelf_cxOp (R : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (u : Lp ℂ 2 mu) :
    (cxOp R).reApplyInnerSelf u
      = ⟪R (reC mu u), reC mu u⟫ + ⟪R (imC mu u), imC mu u⟫ := by
  set p := reC mu u with hp
  set q := imC mu u with hq
  have hu : toC mu p + Complex.I • toC mu q = u := toC_reC_add_smul u
  rw [ContinuousLinearMap.reApplyInnerSelf, ← hu, cxOp_apply]
  simp only [map_add, reC_toC, imC_toC, reC_smul_I, imC_smul_I, neg_zero, add_zero, zero_add]
  rw [inner_decomp (R p) (R q) p q]
  simp

theorem isPositive_cxOp (hR : IsSymmetricOp R) (hpos : ∀ f : Lp ℝ 2 mu, 0 ≤ ⟪R f, f⟫) :
    (cxOp R).IsPositive := by
  refine ⟨?_, fun u => ?_⟩
  · rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    exact isSelfAdjoint_cxOp hR
  · rw [reApplyInnerSelf_cxOp]
    exact add_nonneg (hpos _) (hpos _)

theorem isPositive_one_sub_cxOp (hR : IsSymmetricOp R) (hnorm : ‖R‖ ≤ 1) :
    (1 - cxOp R).IsPositive := by
  have hle : ∀ f : Lp ℝ 2 mu, ⟪R f, f⟫ ≤ ⟪f, f⟫ := by
    intro f
    have h1 : ⟪R f, f⟫ ≤ ‖R f‖ * ‖f‖ := real_inner_le_norm _ _
    have h2 : ‖R f‖ ≤ ‖f‖ := by
      calc ‖R f‖ ≤ ‖R‖ * ‖f‖ := R.le_opNorm f
        _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg f)
        _ = ‖f‖ := one_mul _
    have h3 : ‖R f‖ * ‖f‖ ≤ ‖f‖ * ‖f‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg f)
    have h4 : ⟪f, f⟫ = ‖f‖ * ‖f‖ := real_inner_self_eq_norm_mul_norm f
    rw [h4]
    linarith
  refine ⟨?_, fun u => ?_⟩
  · rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    exact (IsSelfAdjoint.one (R := Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)).sub (isSelfAdjoint_cxOp hR)
  · have hone : (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu).reApplyInnerSelf u
        = ⟪reC mu u, reC mu u⟫ + ⟪imC mu u, imC mu u⟫ := by
      have := reApplyInnerSelf_cxOp (1 : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) u
      rwa [cxOp_one] at this
    have hsub : (1 - cxOp R).reApplyInnerSelf u
        = (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu).reApplyInnerSelf u
          - (cxOp R).reApplyInnerSelf u := by
      simp only [ContinuousLinearMap.reApplyInnerSelf, sub_apply,
        inner_sub_left, map_sub]
    rw [hsub, hone, reApplyInnerSelf_cxOp]
    have h1 := hle (reC mu u)
    have h2 := hle (imC mu u)
    linarith

/-- **The spectral window.**  A symmetric, positive, contractive operator has real spectrum
inside `[0,1]` after complexification. -/
theorem spectrum_cxOp_subset_Icc (hR : IsSymmetricOp R)
    (hpos : ∀ f : Lp ℝ 2 mu, 0 ≤ ⟪R f, f⟫) (hnorm : ‖R‖ ≤ 1) :
    spectrum ℝ (cxOp R) ⊆ Icc 0 1 := by
  have hlow : ∀ x ∈ spectrum ℝ (cxOp R), 0 ≤ x :=
    SpectrumRestricts.nnreal_iff.1 (isPositive_cxOp hR hpos).spectrumRestricts
  have hone : ∀ x ∈ spectrum ℝ (1 - cxOp R), 0 ≤ x :=
    SpectrumRestricts.nnreal_iff.1 (isPositive_one_sub_cxOp hR hnorm).spectrumRestricts
  intro x hx
  refine ⟨hlow x hx, ?_⟩
  have hmem : (1 : ℝ) - x ∈ spectrum ℝ (1 - cxOp R) := by
    have h1 : (algebraMap ℝ (Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)) 1 - cxOp R
        = 1 - cxOp R := by rw [map_one]
    rw [← h1, ← spectrum.singleton_sub_eq]
    exact Set.sub_mem_sub (Set.mem_singleton 1) hx
  have := hone _ hmem
  linarith

/-- The Hille--Yosida bound turns the resolvent identification into `‖R‖ ≤ 1`. -/
theorem norm_le_one_of_resolvent (hs : 0 < s)
    (P : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu))
    (hres : P.resolvent ⟨s⁻¹, mem_Ioi.2 (inv_pos.2 hs)⟩ = (s : ℝ) • R) : ‖R‖ ≤ 1 := by
  have h := P.opNorm_resolvent_le ⟨s⁻¹, mem_Ioi.2 (inv_pos.2 hs)⟩
  rw [hres] at h
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hs, inv_inv] at h
  nlinarith [norm_nonneg R]

/-- **The identification, from the probabilistic side.**  If `P` is a strongly continuous
contraction semigroup on `L²(μ;ℝ)` and `R` is a symmetric positive operator with
`s⁻¹ ∫₀^∞ e^{-t/s} P_t dt = R` — the formalization's `killedResolvent` — then `P` is the
semigroup `φ_t(R)` of the continuous functional calculus. -/
theorem isResolventSemigroup_of_positive (hs : 0 < s) (hR : IsSymmetricOp R)
    (hpos : ∀ f : Lp ℝ 2 mu, 0 ≤ ⟪R f, f⟫)
    (P : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu))
    (hres : P.resolvent ⟨s⁻¹, mem_Ioi.2 (inv_pos.2 hs)⟩ = (s : ℝ) • R) :
    IsResolventSemigroup s R (fun t : ℝ => P (Real.toNNReal t)) :=
  isResolventSemigroup_of_resolvent_eq hs hR
    (spectrum_cxOp_subset_Icc hR hpos (norm_le_one_of_resolvent hs P hres)) P hres

/-- **The nine non-carrier fields of `ResolventRegularityDatum` for the formalization's
diffusion**, with the spectral window derived from positivity and the Hille--Yosida bound. -/
theorem rrk_datum_fields_of_positive (hs : 0 < s) (N : ℕ) (hR : IsSymmetricOp R)
    (hinj : Function.Injective R) (hpos : ∀ f : Lp ℝ 2 mu, 0 ≤ ⟪R f, f⟫)
    (P : StronglyContinuousContractionSemigroup (Lp ℝ 2 mu))
    (hres : P.resolvent ⟨s⁻¹, mem_Ioi.2 (inv_pos.2 hs)⟩ = (s : ℝ) • R)
    (hnn : ∀ t : NNReal, ∀ f : Lp ℝ 2 mu, (0 ≤ᵐ[mu] fun x => f x) →
      0 ≤ᵐ[mu] fun x => (P t f) x)
    (hle : ∀ t : NNReal, ∀ f : Lp ℝ 2 mu, (0 ≤ᵐ[mu] fun x => f x) →
      (∀ᵐ x ∂mu, f x ≤ 1) → ∀ᵐ x ∂mu, (P t f) x ≤ 1) :
    IsSymmetricOp (R ^ N) ∧
      Function.Injective (R ^ N) ∧
      (∀ t, 0 < t → IsSymmetricOp (rrkSmoothing s N R t)) ∧
      (∀ t, 0 < t → (R ^ N).comp (rrkSmoothing s N R t) = P (Real.toNNReal (t / 2))) ∧
      ContinuousOn (rrkSmoothing s N R) (Ioi 0) ∧
      (∀ t, 0 < t → IsSymmetricOp (P (Real.toNNReal t))) ∧
      (∀ t u, 0 < t → 0 < u →
        (P (Real.toNNReal t)).comp (P (Real.toNNReal u)) = P (Real.toNNReal (t + u))) ∧
      (∀ t, 0 < t → ∀ f : Lp ℝ 2 mu, (0 ≤ᵐ[mu] fun x => f x) →
        0 ≤ᵐ[mu] fun x => (P (Real.toNNReal t) f) x) ∧
      (∀ t, 0 < t → ∀ f : Lp ℝ 2 mu, (0 ≤ᵐ[mu] fun x => f x) →
        (∀ᵐ x ∂mu, f x ≤ 1) → ∀ᵐ x ∂mu, (P (Real.toNNReal t) f) x ≤ 1) :=
  rrk_datum_fields hs N hR hinj
    (spectrum_cxOp_subset_Icc hR hpos (norm_le_one_of_resolvent hs P hres)) P hres hnn hle

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKSemigroupIdentification
