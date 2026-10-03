module

public import SubdiffusiveProcess.Paper.conditional_response_setup
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Probability.ProductLpContraction
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal

namespace Paper
noncomputable section



theorem lem_17
    (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (K : Set (SpatialCoordinates d)) [CompactSpace K] (H : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Pa nu : Measure (BilateralField d))
    [IsProbabilityMeasure Pa] [IsProbabilityMeasure nu]
    (R : Response Q) (kappa : ℕ → ℝ)
    (restrictQ : C(K, ℝ) →L[ℝ] Potential Q)
    (V : BilateralField d → C(K, ℝ))
    (t : ℕ → BilateralField d → C(K, ℝ))
    (Sigma : Set (BilateralField d))
    (RN : ℕ → (BilateralField d × BilateralField d) → ℝ)
    (FN : ℕ → C(K, ℝ) → ℝ≥0∞)
    (hsetup : Paper.conditional_response_setup d Q K H Pa nu R kappa
      (fun v => restrictQ v) V t Sigma RN FN)
    (hmeas : ∀ N, H ≤ N → ∀ v : C(K, ℝ),
      AEStronglyMeasurable
        (fun y => R.eval (restrictQ (v + t N y))) nu)
    (hprod : ∀ N, H ≤ N →
      AEStronglyMeasurable
        (fun z : BilateralField d × BilateralField d =>
          R.eval (restrictQ (V z.1 + t N z.2))) (Pa.prod nu))
    (hint : ∀ N, H ≤ N → Integrable (RN N) (Pa.prod nu)) :
    ∀ N, H ≤ N →
      let F : C(K, ℝ) → ℝ :=
        fun v => ∫ y, R.eval (restrictQ (v + t N y)) ∂nu
      (∀ v : C(K, ℝ),
          Integrable (fun y => R.eval (restrictQ (v + t N y))) nu ∧
            FN N v < ⊤ ∧ ENNReal.ofReal (F v) = FN N v) ∧
        (∀ v w : C(K, ℝ),
          Real.exp (-‖v - w‖) * F w ≤ F v ∧
            F v ≤ Real.exp ‖v - w‖ * F w) ∧
        Continuous F ∧
        ((Pa.prod nu)[RN N |
            (inferInstance : MeasurableSpace (BilateralField d)).comap Prod.fst])
          =ᵐ[Pa.prod nu] (fun z => F (V z.1)) ∧
      (∀ q : ℝ, 1 ≤ q →
          eLpNorm (fun z => F (V z.1)) (ENNReal.ofReal q) (Pa.prod nu) ≤
            eLpNorm (RN N) (ENNReal.ofReal q) (Pa.prod nu)) := by
  intro N hN
  dsimp
  unfold Paper.conditional_response_setup at hsetup
  rcases hsetup with ⟨⟨hQK, hkappa⟩, ⟨hrestrict, hrestrict_norm⟩, hV, hSigma,
    ⟨hSigma_meas, hSigma_one⟩, ht, hRN, hFN⟩
  have hSigma_ae : ∀ᵐ y ∂nu, y ∈ Sigma := by
    rw [ae_iff]
    change nu Sigmaᶜ = 0
    rw [measure_compl hSigma_meas (measure_ne_top nu Sigma)]
    simp [hSigma_one]
  have hSigma_prod_ae : ∀ᵐ z : BilateralField d × BilateralField d ∂Pa.prod nu,
      z.2 ∈ Sigma := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      (hSigma_meas.preimage measurable_snd)).2
    exact ae_of_all Pa (fun _ => hSigma_ae)
  have hRN_ae : RN N =ᵐ[Pa.prod nu]
      (fun z => R.eval (restrictQ (V z.1 + t N z.2))) := by
    filter_upwards [hSigma_prod_ae] with z hz
    exact hRN N hN z.1 z.2 hz
  have hRint : Integrable
      (fun z : BilateralField d × BilateralField d =>
        R.eval (restrictQ (V z.1 + t N z.2))) (Pa.prod nu) :=
    (hint N hN).congr hRN_ae
  obtain ⟨a0, ha0⟩ := hRint.prod_right_ae.exists
  have hpoint_upper (v w : C(K, ℝ)) (y : BilateralField d) :
      R.eval (restrictQ (v + t N y)) ≤
        Real.exp ‖v - w‖ * R.eval (restrictQ (w + t N y)) := by
    calc
      R.eval (restrictQ (v + t N y)) ≤
          Real.exp ‖restrictQ (v + t N y) - restrictQ (w + t N y)‖ *
            R.eval (restrictQ (w + t N y)) :=
        R.exp_comparison _ _
      _ ≤ Real.exp ‖v - w‖ * R.eval (restrictQ (w + t N y)) := by
        apply mul_le_mul_of_nonneg_right
        · exact Real.exp_le_exp.mpr (by
            rw [← map_sub, add_sub_add_right_eq_sub]
            exact hrestrict_norm (v - w))
        · exact R.eval_nonneg _
  have hpoint_lower (v w : C(K, ℝ)) (y : BilateralField d) :
      Real.exp (-‖v - w‖) * R.eval (restrictQ (w + t N y)) ≤
        R.eval (restrictQ (v + t N y)) := by
    have hu := hpoint_upper w v y
    rw [norm_sub_rev] at hu
    calc
      Real.exp (-‖v - w‖) * R.eval (restrictQ (w + t N y)) ≤
          Real.exp (-‖v - w‖) *
            (Real.exp ‖v - w‖ * R.eval (restrictQ (v + t N y))) :=
        mul_le_mul_of_nonneg_left hu (le_of_lt (Real.exp_pos _))
      _ = R.eval (restrictQ (v + t N y)) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
  have hInt : ∀ v : C(K, ℝ),
      Integrable (fun y => R.eval (restrictQ (v + t N y))) nu := by
    intro v
    apply Integrable.mono (ha0.const_mul (Real.exp ‖v - V a0‖)) (hmeas N hN v)
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (R.eval_nonneg _)] using! hpoint_upper v (V a0) y
  have hSigma_univ : Sigma =ᵐ[nu] (Set.univ : Set (BilateralField d)) := by
    filter_upwards [hSigma_ae] with y hy
    exact propext ⟨(fun _ => trivial), (fun _ => hy)⟩
  have hFN_eq (v : C(K, ℝ)) :
      ENNReal.ofReal (∫ y, R.eval (restrictQ (v + t N y)) ∂nu) = FN N v := by
    rw [hFN N hN v, setLIntegral_congr hSigma_univ]
    simpa using! (ofReal_integral_eq_lintegral_ofReal (hInt v)
      (ae_of_all nu (fun y => R.eval_nonneg _)))
  have hFcomp (v w : C(K, ℝ)) :
      Real.exp (-‖v - w‖) * (∫ y, R.eval (restrictQ (w + t N y)) ∂nu) ≤
          ∫ y, R.eval (restrictQ (v + t N y)) ∂nu ∧
      (∫ y, R.eval (restrictQ (v + t N y)) ∂nu) ≤
        Real.exp ‖v - w‖ * (∫ y, R.eval (restrictQ (w + t N y)) ∂nu) := by
    constructor
    · rw [← integral_const_mul]
      apply integral_mono_ae
      · exact (hInt w).const_mul (Real.exp (-‖v - w‖))
      · exact hInt v
      · exact ae_of_all nu (fun y => hpoint_lower v w y)
      
    · rw [← integral_const_mul]
      apply integral_mono_ae
      · exact hInt v
      · exact (hInt w).const_mul (Real.exp ‖v - w‖)
      · exact ae_of_all nu (fun y => hpoint_upper v w y)
  have hm :
      (inferInstance : MeasurableSpace (BilateralField d)).comap Prod.fst ≤
        (inferInstance : MeasurableSpace (BilateralField d × BilateralField d)) :=
    MeasurableSpace.comap_le_iff_le_map.mpr measurable_fst
  have hinner_int : Integrable
      (fun a : BilateralField d =>
        ∫ y, R.eval (restrictQ (V a + t N y)) ∂nu) Pa := by
    simpa using! hRint.integral_prod_left
  have hinner_prod_int : Integrable
      (fun z : BilateralField d × BilateralField d =>
        ∫ y, R.eval (restrictQ (V z.1 + t N y)) ∂nu) (Pa.prod nu) := by
    exact hinner_int.comp_fst nu
  have hinner_meas : AEStronglyMeasurable[
      (inferInstance : MeasurableSpace (BilateralField d)).comap Prod.fst]
      (fun z : BilateralField d × BilateralField d =>
        ∫ y, R.eval (restrictQ (V z.1 + t N y)) ∂nu) (Pa.prod nu) := by
    have hcomp_strong : StronglyMeasurable[
        (inferInstance : MeasurableSpace (BilateralField d)).comap Prod.fst]
        (fun z : BilateralField d × BilateralField d =>
          (hinner_int.1.mk (fun a : BilateralField d =>
            ∫ y, R.eval (restrictQ (V a + t N y)) ∂nu)) z.1) := by
      have hfst_meas : Measurable[
          (inferInstance : MeasurableSpace (BilateralField d)).comap Prod.fst,
          (inferInstance : MeasurableSpace (BilateralField d))]
          (Prod.fst : BilateralField d × BilateralField d → BilateralField d) :=
        comap_measurable _
      simpa only [Function.comp_apply] using!
        hinner_int.1.stronglyMeasurable_mk.comp_measurable hfst_meas
    apply hcomp_strong.aestronglyMeasurable.congr
    simpa only [Function.comp_apply] using!
      (Measure.quasiMeasurePreserving_fst (μ := Pa) (ν := nu)).ae_eq_comp
        hinner_int.1.ae_eq_mk |>.symm
  have hcond :
      (fun z : BilateralField d × BilateralField d =>
        ∫ y, R.eval (restrictQ (V z.1 + t N y)) ∂nu) =ᵐ[Pa.prod nu]
        (Pa.prod nu)[RN N |
          (inferInstance : MeasurableSpace (BilateralField d)).comap Prod.fst] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hm (hint N hN)
    · intro s hs hsfin
      exact (hinner_int.comp_fst nu).integrableOn
    · intro s hs hsfin
      rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨u, hu, rfl⟩
      have hpre : Prod.fst ⁻¹' u =
          (u ×ˢ (Set.univ : Set (BilateralField d))) := by
        ext z
        simp
      calc
        ∫ z in Prod.fst ⁻¹' u,
              (∫ y, R.eval (restrictQ (V z.1 + t N y)) ∂nu) ∂Pa.prod nu =
            ∫ z in u ×ˢ (Set.univ : Set (BilateralField d)),
              (∫ y, R.eval (restrictQ (V z.1 + t N y)) ∂nu) ∂Pa.prod nu := by
          rw [hpre]
        _ = ∫ a in u, ∫ y, R.eval (restrictQ (V a + t N y)) ∂nu ∂Pa := by
          simpa [setIntegral_univ] using!
            (setIntegral_prod
              (s := u) (t := (Set.univ : Set (BilateralField d)))
              (fun z : BilateralField d × BilateralField d =>
                ∫ y, R.eval (restrictQ (V z.1 + t N y)) ∂nu)
              hinner_prod_int.integrableOn)
        _ =
            ∫ z in u ×ˢ (Set.univ : Set (BilateralField d)),
              R.eval (restrictQ (V z.1 + t N z.2)) ∂Pa.prod nu := by
          simpa only [setIntegral_univ] using!
            (setIntegral_prod
              (s := u) (t := (Set.univ : Set (BilateralField d)))
              (fun z : BilateralField d × BilateralField d =>
                R.eval (restrictQ (V z.1 + t N z.2))) hRint.integrableOn).symm
        _ = ∫ z in u ×ˢ (Set.univ : Set (BilateralField d)), RN N z ∂Pa.prod nu := by
          exact integral_congr_ae (ae_restrict_of_ae hRN_ae.symm)
        _ = ∫ z in Prod.fst ⁻¹' u, RN N z ∂Pa.prod nu := by rw [hpre]
    · exact hinner_meas
  have hcont : Continuous (fun v : C(K, ℝ) =>
      ∫ y, R.eval (restrictQ (v + t N y)) ∂nu) := by
    rw [continuous_iff_continuousAt]
    intro v
    have hnorm_cont : Continuous (fun w : C(K, ℝ) => ‖w - v‖) :=
      continuous_norm.comp (continuous_id.sub continuous_const)
    have hnorm : Tendsto (fun w : C(K, ℝ) => ‖w - v‖) (𝓝 v) (𝓝 0) := by
      simpa using! hnorm_cont.tendsto v
    have hexp_pos : Tendsto (fun w : C(K, ℝ) => Real.exp ‖w - v‖)
        (𝓝 v) (𝓝 1) := by
      simpa using! (Real.continuous_exp.comp hnorm_cont).tendsto v
    have hneg_cont : Continuous (fun w : C(K, ℝ) => -‖w - v‖) :=
      continuous_neg.comp hnorm_cont
    have hexp_neg : Tendsto (fun w : C(K, ℝ) => Real.exp (-‖w - v‖))
        (𝓝 v) (𝓝 1) := by
      simpa using! (Real.continuous_exp.comp hneg_cont).tendsto v
    change Tendsto (fun w : C(K, ℝ) =>
      ∫ y, R.eval (restrictQ (w + t N y)) ∂nu) (𝓝 v) (𝓝 _)
    simpa using! (tendsto_of_tendsto_of_tendsto_of_le_of_le
      (hexp_neg.mul tendsto_const_nhds) (hexp_pos.mul tendsto_const_nhds)
      (fun w => (hFcomp w v).1) (fun w => (hFcomp w v).2))
  refine ⟨?_, ?_, hcont, hcond.symm, ?_⟩
  · intro v
    refine ⟨hInt v, ?_, hFN_eq v⟩
    rw [← hFN_eq v]
    exact ENNReal.ofReal_lt_top
  · intro v w
    exact hFcomp v w
  intro q hq
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa using! (ENNReal.ofReal_le_ofReal hq)
  have hfiber := eLpNorm_prod_integral_le (μ := Pa) (ν := nu) hp
    ENNReal.ofReal_ne_top (hprod N hN)
  calc
    eLpNorm (fun z => ∫ y, R.eval (restrictQ (V z.1 + t N y)) ∂nu)
        (ENNReal.ofReal q) (Pa.prod nu) ≤
        eLpNorm (fun z => R.eval (restrictQ (V z.1 + t N z.2)))
          (ENNReal.ofReal q) (Pa.prod nu) := by
      exact hfiber
    _ = eLpNorm (RN N) (ENNReal.ofReal q) (Pa.prod nu) := by
      exact eLpNorm_congr_ae hRN_ae.symm

end
end Paper
