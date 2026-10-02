import SubdiffusiveProcess.Paper.catalog_cutoff_existence
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Paper.lem_19
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.lem_cutoffs
import SubdiffusiveProcess.Paper.prop_killed_inverse
import SubdiffusiveProcess.Paper.conv_represented_sequence
import SubdiffusiveProcess.Paper.conv_catalog_cutoffs

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section LocRecAux

open scoped Distributions

section LocRecA

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Multiplication by an essentially bounded function on scalar `L²`. -/
def aux_prop_locality_recovery_mulL (f : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    DomainL2 Ω →L[ℝ] DomainL2 Ω :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).holderL
    (volume.restrict (Ω : Set (SpatialCoordinates d))) ∞ 2 2 f

theorem aux_prop_locality_recovery_mulL_coeFn (f : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (g : DomainL2 Ω) :
    (aux_prop_locality_recovery_mulL f g : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => f x * g x := by
  filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).coeFn_holder (r := 2) f g] with x hx
  change ((ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).holder 2 f g : SpatialCoordinates d → ℝ) x = _
  rw [hx]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- A test function as an essentially bounded class. -/
def aux_prop_locality_recovery_testLinf (φ : 𝓓(Ω, ℝ)) :
    Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
  (φ.contDiff.continuous.memLp_of_hasCompactSupport (p := ∞) φ.hasCompactSupport).toLp φ

/-- A coordinate derivative of a test function as an essentially bounded class. -/
def aux_prop_locality_recovery_testPartialLinf (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
  ((φ.contDiff.continuous_fderiv_apply (by simp)).comp
    (continuous_id.prodMk continuous_const) |>.memLp_of_hasCompactSupport (p := ∞)
      (φ.hasCompactSupport.fderiv_apply ℝ (Pi.single i 1))).toLp
    (fun x => fderiv ℝ φ x (Pi.single i 1))

theorem aux_prop_locality_recovery_testLinf_coeFn (φ : 𝓓(Ω, ℝ)) :
    (aux_prop_locality_recovery_testLinf φ : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] φ :=
  MemLp.coeFn_toLp _

theorem aux_prop_locality_recovery_testPartialLinf_coeFn (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    (aux_prop_locality_recovery_testPartialLinf φ i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
  MemLp.coeFn_toLp _

/-- Multiplication of function/gradient data by a test function, with the product rule. -/
def aux_prop_locality_recovery_mulTest (φ : 𝓓(Ω, ℝ)) : SobolevData Ω →L[ℝ] SobolevData Ω :=
  ((aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ)).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (ContinuousLinearMap.pi fun i =>
      (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ i)).comp (ContinuousLinearMap.fst ℝ _ _) +
      (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ)).comp
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _)))

theorem aux_prop_locality_recovery_mulTest_fst (φ : 𝓓(Ω, ℝ)) (w : SobolevData Ω) :
    (aux_prop_locality_recovery_mulTest φ w).1 = aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) w.1 := rfl

theorem aux_prop_locality_recovery_mulTest_snd (φ : 𝓓(Ω, ℝ)) (w : SobolevData Ω) (i : Fin d) :
    (aux_prop_locality_recovery_mulTest φ w).2 i =
      aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ i) w.1 +
        aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) (w.2 i) := rfl

/-- The product of two test functions. -/
def aux_prop_locality_recovery_testMul (ψ φ : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) :=
  ⟨fun x => ψ x * φ x, ψ.contDiff.mul φ.contDiff, ψ.hasCompactSupport.mul_right,
    (tsupport_mul_subset_left).trans ψ.tsupport_subset⟩

theorem aux_prop_locality_recovery_mulTest_smooth (φ ψ : 𝓓(Ω, ℝ)) :
    aux_prop_locality_recovery_mulTest φ (smoothSobolevData ψ) = smoothSobolevData (aux_prop_locality_recovery_testMul ψ φ) := by
  apply Prod.ext
  · apply Lp.ext
    rw [aux_prop_locality_recovery_mulTest_fst]
    filter_upwards [aux_prop_locality_recovery_mulL_coeFn (aux_prop_locality_recovery_testLinf φ) (smoothSobolevData ψ).1,
      aux_prop_locality_recovery_testLinf_coeFn φ, testL2_coeFn ψ, testL2_coeFn (aux_prop_locality_recovery_testMul ψ φ)]
      with x h1 h2 h3 h4
    change _ = (testL2 (aux_prop_locality_recovery_testMul ψ φ) : SpatialCoordinates d → ℝ) x
    rw [h1, h4]
    change aux_prop_locality_recovery_testLinf φ x * (testL2 ψ : SpatialCoordinates d → ℝ) x = ψ x * φ x
    rw [h2, h3, mul_comm]
  · funext i
    apply Lp.ext
    rw [aux_prop_locality_recovery_mulTest_snd]
    filter_upwards [Lp.coeFn_add
        (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ i) (smoothSobolevData ψ).1)
        (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) ((smoothSobolevData ψ).2 i)),
      aux_prop_locality_recovery_mulL_coeFn (aux_prop_locality_recovery_testPartialLinf φ i) (smoothSobolevData ψ).1,
      aux_prop_locality_recovery_mulL_coeFn (aux_prop_locality_recovery_testLinf φ) ((smoothSobolevData ψ).2 i),
      aux_prop_locality_recovery_testLinf_coeFn φ, aux_prop_locality_recovery_testPartialLinf_coeFn φ i, testL2_coeFn ψ,
      testPartialL2_coeFn ψ i, testPartialL2_coeFn (aux_prop_locality_recovery_testMul ψ φ) i]
      with x h0 h1 h2 h3 h4 h5 h6 h7
    change _ = (testPartialL2 (aux_prop_locality_recovery_testMul ψ φ) i : SpatialCoordinates d → ℝ) x
    rw [h0, Pi.add_apply, h1, h2, h7]
    change aux_prop_locality_recovery_testPartialLinf φ i x * (testL2 ψ : SpatialCoordinates d → ℝ) x +
      aux_prop_locality_recovery_testLinf φ x * (testPartialL2 ψ i : SpatialCoordinates d → ℝ) x = _
    rw [h3, h4, h5, h6]
    have hfun : ((aux_prop_locality_recovery_testMul ψ φ : 𝓓(Ω, ℝ)) : SpatialCoordinates d → ℝ) =
        (ψ : SpatialCoordinates d → ℝ) * (φ : SpatialCoordinates d → ℝ) := rfl
    rw [hfun, fderiv_mul (ψ.contDiff.differentiable (by simp) x)
      (φ.contDiff.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

/-- The killed graph is stable under multiplication by test functions. -/
theorem aux_prop_locality_recovery_mulTest_mem (φ : 𝓓(Ω, ℝ)) {w : SobolevData Ω}
    (hw : w ∈ killedSobolevGraph Ω) :
    aux_prop_locality_recovery_mulTest φ w ∈ killedSobolevGraph Ω := by
  have hmap : Submodule.map (aux_prop_locality_recovery_mulTest φ : SobolevData Ω →ₗ[ℝ] SobolevData Ω)
      (LinearMap.range (smoothSobolevDataLinear (Ω := Ω))) ≤
        LinearMap.range (smoothSobolevDataLinear (Ω := Ω)) := by
    rintro _ ⟨_, ⟨ψ, rfl⟩, rfl⟩
    exact ⟨aux_prop_locality_recovery_testMul ψ φ, (aux_prop_locality_recovery_mulTest_smooth φ ψ).symm⟩
  have h1 := Submodule.topologicalClosure_map (aux_prop_locality_recovery_mulTest φ)
    (LinearMap.range (smoothSobolevDataLinear (Ω := Ω)))
  exact Submodule.topologicalClosure_mono hmap (h1 ⟨w, hw, rfl⟩)

/-- Weak gradients vanish almost everywhere on an open set where the function is constant. -/
theorem aux_prop_locality_recovery_grad_ae_zero_of_const (w : SobolevData Ω) (hw : w ∈ weakSobolevGraph Ω)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (k : ℝ)
    (hconst : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∈ U → w.1 x = k)
    (i : Fin d) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∈ U → w.2 i x = 0 := by
  have htest := (mem_weakSobolevGraph_iff w).mp hw
  have hi := (hU.inter Ω.isOpen).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume.restrict (Ω : Set (SpatialCoordinates d)))
    (((Lp.memLp (w.2 i)).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
    (fun g hg hc hgU => ?_)
  · filter_upwards [hi, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hΩ hxU
    exact hx ⟨hxU, hΩ⟩
  · let φb : 𝓓(Ω, ℝ) := ⟨g, hg, hc, hgU.trans inter_subset_right⟩
    have he := htest φb i
    let v : SpatialCoordinates d := Pi.single i 1
    have hgd : Continuous (fun x => fderiv ℝ g x v) :=
      (hg.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
    have h2 : (∫ x in (Ω : Set (SpatialCoordinates d)),
        fderiv ℝ φb x (Pi.single i 1) * w.1 x) = 0 := by
      calc
        _ = ∫ x in (Ω : Set (SpatialCoordinates d)), k * fderiv ℝ g x v := by
          apply integral_congr_ae
          filter_upwards [hconst] with x hx
          by_cases hxt : x ∈ tsupport g
          · change fderiv ℝ g x v * w.1 x = _
            rw [hx (hgU hxt).1, mul_comm]
          · have h0 : fderiv ℝ g x = 0 := fderiv_of_notMem_tsupport ℝ hxt
            change fderiv ℝ g x v * w.1 x = _
            simp [h0]
        _ = ∫ x, k * fderiv ℝ g x v :=
          setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
            have h0 : fderiv ℝ g x = 0 :=
              fderiv_of_notMem_tsupport ℝ (fun h => hx (hgU h).2)
            simp [h0]
        _ = 0 := by
          have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (μ := (volume : Measure (SpatialCoordinates d))) (f := fun _ => k) (g := g) (v := v)
            (by simp) ((continuous_const.mul hgd).integrable_of_hasCompactSupport
              (hc.fderiv_apply ℝ v).mul_left)
            ((continuous_const.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left)
            (differentiable_const k) (hg.differentiable (by simp))
          rw [hibp]
          simp
    rw [h2, add_zero] at he
    simpa only [smul_eq_mul] using he

/-- The response energy is the sum of coordinate weighted forms. -/
theorem aux_prop_locality_recovery_responseForm_eq_sum (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (u v : S.space) :
    responseForm S a u v = ∑ i : Fin d,
      weightedL2Form a.val ((u : SobolevData Ω).2 i) ((v : SobolevData Ω).2 i) := by
  simp only [responseForm, weightedGradientForm, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.sum_apply, PiLp.proj_apply]
  rfl

theorem aux_prop_locality_recovery_coeff_nonneg (a : PositiveCoefficient Ω) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 ≤ a.val x := by
  obtain ⟨c, hc, ha⟩ := a.property
  filter_upwards [ha] with x hx
  exact hc.le.trans hx

end LocRecA

section LocRecForm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem aux_prop_locality_recovery_weighted_nonneg (a : Lp ℝ ∞ μ) (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (P : Lp ℝ 2 μ) :
    0 ≤ weightedL2Form a P P := by
  simpa using weightedL2Form_lower (E := ℝ) a (c := 0) ha P

/-- Young splitting of a nonnegative weighted quadratic form. -/
theorem aux_prop_locality_recovery_quad_split (a : Lp ℝ ∞ μ) (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (P R : Lp ℝ 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    weightedL2Form a (P + R) (P + R) ≤
      (1 + ε) * weightedL2Form a P P + (1 + ε⁻¹) * weightedL2Form a R R := by
  have hsymm := weightedL2Form_symm (E := ℝ) a P R
  have hnn := aux_prop_locality_recovery_weighted_nonneg a ha (ε • P - R)
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hnn ⊢
  set x := weightedL2Form a P P
  set y := weightedL2Form a P R
  set y' := weightedL2Form a R P
  set z := weightedL2Form a R R
  have hy : y' = y := hsymm.symm
  rw [hy] at hnn ⊢
  have key : ε⁻¹ * (ε * (ε * x - y) - (ε * y - z)) = ε * x - 2 * y + ε⁻¹ * z := by
    field_simp
    ring
  have h2 := mul_nonneg (inv_nonneg.2 hε.le) hnn
  rw [key] at h2
  nlinarith

/-- Pointwise domination gives domination of weighted quadratic forms. -/
theorem aux_prop_locality_recovery_weighted_mono (a : Lp ℝ ∞ μ) (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (P D : Lp ℝ 2 μ)
    (h : ∀ᵐ x ∂μ, |P x| ≤ |D x|) :
    weightedL2Form a P P ≤ weightedL2Form a D D := by
  rw [weightedL2Form_apply, weightedL2Form_apply]
  apply integral_mono_ae (integrable_weighted_inner a P P) (integrable_weighted_inner a D D)
  filter_upwards [ha, h] with x hax hx
  simp only [RCLike.inner_apply, conj_trivial]
  apply mul_le_mul_of_nonneg_left _ hax
  have := mul_self_le_mul_self (abs_nonneg _) hx
  simpa [abs_mul_abs_self] using this

/-- A sum of weighted squares whose integrands factor, as an extended integral. -/
theorem aux_prop_locality_recovery_sum_weighted_eq {ι : Type*} (s : Finset ι)
    (a : Lp ℝ ∞ μ) (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (R g : ι → Lp ℝ 2 μ) (f : α → ℝ)
    (hR : ∀ i, ∀ᵐ x ∂μ, (R i x) ^ 2 = (f x) ^ 2 * (g i x) ^ 2) :
    ENNReal.ofReal (∑ i ∈ s, weightedL2Form a (R i) (R i)) =
      ∫⁻ x, ENNReal.ofReal (a x * ∑ i ∈ s, (g i x) ^ 2) * ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  have hint : ∀ i, Integrable (fun x => a x * (R i x * R i x)) μ := by
    intro i
    refine (integrable_weighted_inner a (R i) (R i)).congr ?_
    filter_upwards with x
    simp only [RCLike.inner_apply, conj_trivial]
  have hsum : ∑ i ∈ s, weightedL2Form a (R i) (R i) =
      ∫ x, ∑ i ∈ s, a x * (R i x * R i x) ∂μ := by
    rw [integral_finset_sum s (fun i _ => hint i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [weightedL2Form_apply]
    apply integral_congr_ae
    filter_upwards with x
    simp only [RCLike.inner_apply, conj_trivial]
  rw [hsum, ofReal_integral_eq_lintegral_ofReal (integrable_finset_sum s (fun i _ => hint i))]
  · apply lintegral_congr_ae
    have hRall : ∀ᵐ x ∂μ, ∀ i ∈ s, (R i x) ^ 2 = (f x) ^ 2 * (g i x) ^ 2 := by
      exact (Filter.eventually_all_finset s).2 (fun i _ => hR i)
    filter_upwards [ha, hRall] with x hax hx
    rw [← ENNReal.ofReal_mul (mul_nonneg hax (Finset.sum_nonneg fun i _ => sq_nonneg _))]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hx i hi
    rw [← sq, this]
    ring
  · filter_upwards [ha] with x hax
    exact Finset.sum_nonneg fun i _ => mul_nonneg hax (mul_self_nonneg _)

end LocRecForm

section LocRecApprox

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Test-function data approximate any killed element in graph norm and in one energy. -/
theorem aux_prop_locality_recovery_smooth_approx (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (a : PositiveCoefficient Ω) (w : S.space) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓓(Ω, ℝ), ∃ hφ : smoothSobolevData φ ∈ S.space,
      ‖(smoothSobolevData φ).1 - (w : SobolevData Ω).1‖ < ε ∧
      |responseForm S a ⟨_, hφ⟩ ⟨_, hφ⟩ - responseForm S a w w| < ε := by
  have hwk : (w : SobolevData Ω) ∈ killedSobolevGraph Ω :=
    (congrArg (fun V : Submodule ℝ (SobolevData Ω) => (w : SobolevData Ω) ∈ V) hS).mp w.2
  have hw : (w : SobolevData Ω) ∈ closure
      ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω)) : Submodule ℝ (SobolevData Ω)) :
        Set (SobolevData Ω)) :=
    (Submodule.topologicalClosure_coe _).subst (motive := fun X => (w : SobolevData Ω) ∈ X) hwk
  let F : SobolevData Ω → ℝ := fun y =>
    weightedGradientForm a.val (sobolevGradient y) (sobolevGradient y)
  have hF : Continuous F :=
    ((weightedGradientForm a.val).continuous.comp sobolevGradient.continuous).clm_apply
      sobolevGradient.continuous
  have hFw : F w = responseForm S a w w := rfl
  let t : Set (SobolevData Ω) :=
    {y | ‖y.1 - (w : SobolevData Ω).1‖ < ε} ∩ {y | |F y - F w| < ε}
  have ht : t ∈ 𝓝 (w : SobolevData Ω) := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt ((continuous_fst.sub continuous_const).norm) continuous_const).inter
        (isOpen_lt ((hF.sub continuous_const).abs) continuous_const)
    · refine ⟨?_, ?_⟩
      · change ‖(w : SobolevData Ω).1 - (w : SobolevData Ω).1‖ < ε
        simpa using hε
      · change |F w - F w| < ε
        simpa using hε
  have hne : (t ∩ ((LinearMap.range (smoothSobolevDataLinear (Ω := Ω)) : Submodule ℝ (SobolevData Ω)) :
        Set (SobolevData Ω))).Nonempty := mem_closure_iff_nhds.1 hw t ht
  obtain ⟨b, hb⟩ := hne
  have hb1 : ‖b.1 - (w : SobolevData Ω).1‖ < ε := hb.1.1
  have hb2 : |F b - F w| < ε := hb.1.2
  have hb3 : b ∈ LinearMap.range (smoothSobolevDataLinear (Ω := Ω)) := hb.2
  have hb4 := LinearMap.mem_range.1 hb3
  obtain ⟨φ, hφb⟩ := hb4
  have hmem : smoothSobolevData φ ∈ S.space :=
    (congrArg (fun V : Submodule ℝ (SobolevData Ω) => smoothSobolevData φ ∈ V) hS).mpr
      (smoothSobolevData_mem_killed φ)
  have hbφ : smoothSobolevData φ = b := hφb
  refine ⟨φ, hmem, ?_, ?_⟩
  · rw [hbφ]; exact hb1
  · have hFb : responseForm S a ⟨_, hmem⟩ ⟨_, hmem⟩ = F (smoothSobolevData φ) := rfl
    rw [hFb, ← hFw, hbφ]
    exact hb2

/-- Test-function sequences with the same `L²` and energy limits. -/
theorem aux_prop_locality_recovery_smooth_seq (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (a : ℕ → PositiveCoefficient Ω) (wN : ℕ → S.space) (w : DomainL2 Ω) (L : ℝ)
    (h1 : Tendsto (fun n => (wN n : SobolevData Ω).1) atTop (𝓝 w))
    (hE : Tendsto (fun n => responseForm S (a n) (wN n) (wN n)) atTop (𝓝 L)) :
    ∃ (φ : ℕ → 𝓓(Ω, ℝ)) (Φ : ℕ → S.space),
      (∀ n, (Φ n : SobolevData Ω) = smoothSobolevData (φ n)) ∧
      Tendsto (fun n => (Φ n : SobolevData Ω).1) atTop (𝓝 w) ∧
      Tendsto (fun n => responseForm S (a n) (Φ n) (Φ n)) atTop (𝓝 L) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose φ hφ hφ1 hφE using fun n => aux_prop_locality_recovery_smooth_approx S hS (a n) (wN n) (hpos n)
  let Φ : ℕ → S.space := fun n => ⟨smoothSobolevData (φ n), hφ n⟩
  refine ⟨φ, Φ, fun n => rfl, ?_, ?_⟩
  · have hd : Tendsto (fun n => (Φ n : SobolevData Ω).1 - (wN n : SobolevData Ω).1)
        atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => (hφ1 n).le) tendsto_one_div_add_atTop_nhds_zero_nat
    have := hd.add h1
    simp only [sub_add_cancel, zero_add] at this
    exact this
  · have hd : Tendsto (fun n => responseForm S (a n) (Φ n) (Φ n) -
        responseForm S (a n) (wN n) (wN n)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact (hφE n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have := hd.add hE
    simp only [sub_add_cancel, zero_add] at this
    exact this

theorem aux_prop_locality_recovery_eps_choice (L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ (1 + ε) * L + (1 + ε⁻¹) * 0 < L + δ := by
  refine ⟨δ / (2 * (L + 1)), by positivity, ?_⟩
  have h1 : δ / (2 * (L + 1)) * L ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  nlinarith

/-- Abstract recovery transfer: an `L²`-dominated modification with Young-split
energy bounds and vanishing error has the limit energy, given the Mosco lower bound. -/
theorem aux_prop_locality_recovery_recovery_abstract {H : Type*} [SeminormedAddCommGroup H]
    (y φ : ℕ → H) (w : H) (Ew : EReal) (hw0 : 0 ≤ Ew) (hw : Ew < ⊤)
    (eY eΦ T : ℕ → ℝ)
    (hlow : Tendsto y atTop (𝓝 w) → Ew ≤ liminf (fun n => ((eY n : ℝ) : EReal)) atTop)
    (hΦ1 : Tendsto φ atTop (𝓝 w)) (hΦE : Tendsto eΦ atTop (𝓝 Ew.toReal))
    (hY1 : ∀ n, ‖y n - w‖ ≤ ‖φ n - w‖)
    (hYE : ∀ n, ∀ ε : ℝ, 0 < ε → eY n ≤ (1 + ε) * eΦ n + (1 + ε⁻¹) * T n)
    (hT : Tendsto T atTop (𝓝 0)) :
    Tendsto (fun n => (y n, ((eY n : ℝ) : EReal))) atTop (𝓝 (w, Ew)) := by
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Ew.toReal := ⟨_, rfl⟩
  rw [← hLdef] at hΦE
  have hL0 : 0 ≤ L := hLdef ▸ EReal.toReal_nonneg hw0
  have hEL : Ew = (L : EReal) := by
    rw [hLdef, EReal.coe_toReal hw.ne]
    exact ne_bot_of_le_ne_bot (by simp) hw0
  have hY1t : Tendsto y atTop (𝓝 w) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hY1 (tendsto_iff_norm_sub_tendsto_zero.mp hΦ1)
  have hlow' := hlow hY1t
  rw [hEL] at hlow'
  have hYreal : Tendsto eY atTop (𝓝 L) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    have hlt : ((L - δ : ℝ) : EReal) < liminf (fun n => ((eY n : ℝ) : EReal)) atTop :=
      lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) hlow'
    have hlo : ∀ᶠ n in atTop, L - δ < eY n := by
      filter_upwards [eventually_lt_of_lt_liminf hlt] with n hn
      exact EReal.coe_lt_coe_iff.1 hn
    obtain ⟨ε, hε, hlt⟩ := aux_prop_locality_recovery_eps_choice L δ hL0 hδ
    have hbound : Tendsto (fun n => (1 + ε) * eΦ n + (1 + ε⁻¹) * T n) atTop
        (𝓝 ((1 + ε) * L + (1 + ε⁻¹) * 0)) :=
      (hΦE.const_mul _).add (hT.const_mul _)
    have hhi := hbound.eventually_lt_const hlt
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlo.and hhi)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := hN n hn
    have h3 := hYE n ε hε
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith only [h1], by linarith only [h2, h3]⟩
  refine hY1t.prodMk_nhds ?_
  rw [hEL]
  exact EReal.tendsto_coe.2 hYreal

end LocRecApprox

section LocRecTraceGeneric

variable {α : Type*} [MeasurableSpace α]

/-- Monotone truncation of a density. -/
theorem aux_prop_locality_recovery_lintegral_trunc_le (μ : Measure α) (ρ : α → ℝ≥0∞) (hρ : Measurable ρ)
    (F : α → ℝ≥0∞) (hF : Measurable F) (bound : ℝ≥0∞)
    (h : ∀ M : ℕ, ∫⁻ x, F x ∂(μ.withDensity (fun x => min (M : ℝ≥0∞) (ρ x))) ≤ bound) :
    ∫⁻ x, ρ x * F x ∂μ ≤ bound := by
  have hsup : ∀ x, ρ x * F x = ⨆ M : ℕ, min (M : ℝ≥0∞) (ρ x) * F x := by
    intro x
    rw [← ENNReal.iSup_mul]
    congr 1
    have : (⨆ M : ℕ, min (M : ℝ≥0∞) (ρ x)) = min (⨆ M : ℕ, (M : ℝ≥0∞)) (ρ x) := by
      exact (iSup_inf_eq (fun M : ℕ => (M : ℝ≥0∞)) (ρ x)).symm
    rw [this, ENNReal.iSup_natCast]
    simp
  simp_rw [hsup]
  rw [lintegral_iSup]
  · refine iSup_le fun M => ?_
    have := h M
    rw [lintegral_withDensity_eq_lintegral_mul μ (measurable_const.min hρ) hF] at this
    exact this
  · exact fun M => (measurable_const.min hρ).mul hF
  · intro M N hMN x
    have hle : min (M : ℝ≥0∞) (ρ x) ≤ min (N : ℝ≥0∞) (ρ x) :=
      min_le_min_right _ (by exact_mod_cast hMN)
    show min (M : ℝ≥0∞) (ρ x) * F x ≤ min (N : ℝ≥0∞) (ρ x) * F x
    exact mul_le_mul_of_nonneg_right hle (zero_le _)

/-- The squared `L²` norm of a representative, as an extended integral. -/
theorem aux_prop_locality_recovery_lintegral_sq_eq_norm {ν : Measure α} {f : α → ℝ} (hf : MemLp f 2 ν) :
    ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν = ENNReal.ofReal (‖hf.toLp f‖ ^ 2) := by
  have h1 : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hf] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial, sq]
  rw [h1, ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg _)]

end LocRecTraceGeneric

section LocRecTraceCube

variable {d : ℕ}

/-- The finite-measure trace bound of `lem_19`, extended to arbitrary absolutely
continuous densities with total mass and growth control by monotone truncation. -/
theorem aux_prop_locality_recovery_trace_lintegral (hd : 2 ≤ d) (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : (d : ℝ) - 1 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : SpatialCoordinates d → ℝ≥0∞), Measurable ρ → ∀ K : ℝ, 0 ≤ K →
      (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ρ x) ≤ ENNReal.ofReal K →
      (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr →
        rr ≤ 1 →
        ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity ρ)
          (Metric.ball x rr) ≤ ENNReal.ofReal (K * rr ^ t)) →
      ∀ w : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
        ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ρ x * ENNReal.ofReal
              (((w.val 0 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) x ^ 2) ≤
          ENNReal.ofReal
            (C * (2 * K) * (cubeFractionalL2Norm hd z r hr halfFractionalOrder w) ^ 2) := by
  obtain ⟨C, hC, hT⟩ := (lem_19 d hd hInterp z r hr t ht).1
  refine ⟨C, hC, ?_⟩
  intro ρ hρ K hK hmass hgrowth w
  have hF : Measurable (fun x => ENNReal.ofReal
      (((w.val 0 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) x ^ 2)) :=
    ((Lp.stronglyMeasurable (w.val 0)).measurable.pow_const 2).ennreal_ofReal
  apply aux_prop_locality_recovery_lintegral_trunc_le _ ρ hρ _ hF
  intro M
  have hmeasM : Measurable (fun x => min (M : ℝ≥0∞) (ρ x)) := measurable_const.min hρ
  -- the truncated measure
  have hle_rho : (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
      (fun x => min (M : ℝ≥0∞) (ρ x)) ≤
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity ρ :=
    withDensity_mono (Eventually.of_forall fun x => min_le_right _ _)
  have huniv_le : ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
      (fun x => min (M : ℝ≥0∞) (ρ x))) Set.univ ≤ ENNReal.ofReal K := by
    refine (hle_rho Set.univ).trans ?_
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hmass
  have huniv : ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
      (fun x => min (M : ℝ≥0∞) (ρ x))) Set.univ < ⊤ :=
    huniv_le.trans_lt ENNReal.ofReal_lt_top
  have hcompl : ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
      (fun x => min (M : ℝ≥0∞) (ρ x)))
        (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0 := by
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply isClosed_closure.isOpen_compl.measurableSet]
    have : (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ ∩
        (centeredCube z r hr : Set (SpatialCoordinates d)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx1, hx2⟩
      exact hx1 (subset_closure hx2)
    rw [this, measure_empty]
  have hgrowM : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun x => min (M : ℝ≥0∞) (ρ x))) (Metric.ball x rr) ≤ ENNReal.ofReal (K * rr ^ t) :=
    fun x hx rr hrr hrr1 => (hle_rho _).trans (hgrowth x hx rr hrr hrr1)
  have hdens : (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
      (fun x => min (M : ℝ≥0∞) (ρ x)) ≤
      ENNReal.ofReal (M : ℝ) • volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [ENNReal.ofReal_natCast, ← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun x => min_le_left _ _)
  obtain ⟨T, hTprops, -⟩ := hT _ K huniv hcompl hK hgrowM
  have hTbound := hTprops.2.2.2.1 w
  obtain ⟨hmem, hTeq⟩ := hTprops.2.2.2.2 (M : ℝ) (Nat.cast_nonneg M) hdens w
  rw [hTeq hmem] at hTbound
  rw [aux_prop_locality_recovery_lintegral_sq_eq_norm hmem]
  apply ENNReal.ofReal_le_ofReal
  refine hTbound.trans ?_
  have hcl : ((((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
      (fun x => min (M : ℝ≥0∞) (ρ x)))
        (closure (centeredCube z r hr : Set (SpatialCoordinates d))))).toReal ≤ K :=
    ENNReal.toReal_le_of_le_ofReal hK ((measure_mono (Set.subset_univ _)).trans huniv_le)
  have hN := sq_nonneg (cubeFractionalL2Norm hd z r hr halfFractionalOrder w)
  have : C * (K + ((((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
      (fun x => min (M : ℝ≥0∞) (ρ x)))
        (closure (centeredCube z r hr : Set (SpatialCoordinates d))))).toReal) ≤ C * (2 * K) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  exact mul_le_mul_of_nonneg_right this hN

/-- Energy-measure mass of a cutoff equals its response energy. -/
theorem aux_prop_locality_recovery_mass_eq {Ω : Opens (SpatialCoordinates d)} (S : ResponseSpace Ω)
    (a : PositiveCoefficient Ω) (χ : S.space) :
    ∫⁻ x in (Ω : Set (SpatialCoordinates d)),
        ENNReal.ofReal (a.val x * ∑ i : Fin d, ((χ : SobolevData Ω).2 i x) ^ 2) =
      ENNReal.ofReal (responseForm S a χ χ) := by
  rw [aux_prop_locality_recovery_responseForm_eq_sum]
  rw [aux_prop_locality_recovery_sum_weighted_eq Finset.univ a.val (aux_prop_locality_recovery_coeff_nonneg a)
    (fun i => (χ : SobolevData Ω).2 i) (fun i => (χ : SobolevData Ω).2 i) (fun _ => 1)
    (fun i => Eventually.of_forall fun x => by ring)]
  apply lintegral_congr
  intro x
  simp

/-- Fractional `3/4` bound from coercivity and a uniform energy bound. -/
theorem aux_prop_locality_recovery_frac_norm_bound (s m q A c : ℝ) (hq : 0 < q) (hc : 0 ≤ c)
    (h : m ^ 2 + q * s ^ 2 ≤ A) :
    s + c * (Real.sqrt (m ^ 2) / Real.sqrt q) ≤
      Real.sqrt (A / q) + c * (Real.sqrt A / Real.sqrt q) := by
  have hA : 0 ≤ A := le_trans (by positivity) h
  have h1 : s ≤ Real.sqrt (A / q) := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hq]
    nlinarith [sq_nonneg m]
  have h2 : Real.sqrt (m ^ 2) ≤ Real.sqrt A := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s])
  have h3 : Real.sqrt (m ^ 2) / Real.sqrt q ≤ Real.sqrt A / Real.sqrt q :=
    div_le_div_of_nonneg_right h2 (Real.sqrt_nonneg _)
  have h4 := mul_le_mul_of_nonneg_left h3 hc
  linarith

theorem aux_prop_locality_recovery_cube_vol_pos (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  rw [measureReal_def, centeredCube_volume, ENNReal.toReal_ofReal (by positivity)]
  positivity

theorem aux_prop_locality_recovery_frac_norm_single (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) (f : DomainL2 (centeredCube z r hr))
    (hf : cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => f) < ⊤) :
    cubeFractionalL2Norm hd z r hr s (⟨fun _ : Fin 1 => f, hf⟩ :
        CubeFractionalL2 (k := 1) hd z r hr s) =
      (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => f)).toReal +
        r ^ (-(s : ℝ)) * (Real.sqrt (‖f‖ ^ 2) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
  unfold cubeFractionalL2Norm
  rw [Fin.sum_univ_one]

/-- Cutoff-error trace integrals vanish along an `L²`-convergent sequence of uniformly
bounded energy. -/
theorem aux_prop_locality_recovery_trace_tendsto (hd : 2 ≤ d) (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n) (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (cut : ℕ → S.space) (B : ℝ) (hB : 0 ≤ B)
    (hcutE : ∀ n, responseForm S (a n) (cut n) (cut n) ≤ B)
    (hgrowth : ∀ n, ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((cut n).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))
    (Φ : ℕ → S.space) (w : DomainL2 (centeredCube z r hr))
    (hΦ : Tendsto (fun n => (Φ n).val.1) atTop (𝓝 w))
    (Eb : ℝ) (hEb : ∀ n, responseForm S (a n) (Φ n) (Φ n) ≤ Eb) :
    Tendsto (fun n => (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((a n).val x * ∑ i : Fin d, ((cut n).val.2 i x) ^ 2) *
        ENNReal.ofReal (((Φ n).val.1 x - w x) ^ 2)).toReal) atTop (𝓝 0) := by
  obtain ⟨C, hC, htrace⟩ := aux_prop_locality_recovery_trace_lintegral hd hInterp z r hr t ht
  -- the `3/4` carriers and their uniform norm bound
  let W : ℕ → CubeFractionalL2 (k := 1) hd z r hr Lane4.threeQuarterOrder :=
    fun n => ⟨fun _ => (Φ n).val.1, hfrac (Φ n)⟩
  have hq := aux_prop_locality_recovery_cube_vol_pos z r hr
  have hKs : 0 ≤ Kstar := (hKN 0).trans (hKstar 0)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = Kstar * Eb := ⟨_, rfl⟩
  have hW : ∀ n, cubeFractionalL2Norm hd z r hr Lane4.threeQuarterOrder (W n) ≤
      Real.sqrt (A / volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) +
        r ^ (-(Lane4.threeQuarterOrder : ℝ)) *
          (Real.sqrt A /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
    intro n
    have hE0 := responseForm_nonneg S (a n) (Φ n)
    have hco := hcoercive n (Φ n)
    have hA : ‖(Φ n).val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => (Φ n).val.1)).toReal) ^ 2 ≤ A := by
      refine hco.trans ?_
      rw [hAdef]
      calc KN n * responseForm S (a n) (Φ n) (Φ n) ≤ Kstar * responseForm S (a n) (Φ n) (Φ n) :=
            mul_le_mul_of_nonneg_right (hKstar n) hE0
        _ ≤ Kstar * Eb := mul_le_mul_of_nonneg_left (hEb n) hKs
    rw [aux_prop_locality_recovery_frac_norm_single hd z r hr Lane4.threeQuarterOrder (Φ n).val.1 (hfrac (Φ n))]
    exact aux_prop_locality_recovery_frac_norm_bound _ _ _ _ _ hq
      (Real.rpow_nonneg hr.le _) hA
  obtain ⟨-, -, diff, hdiff, hdiff0⟩ := (lem_19 d hd hInterp z r hr t ht).2
    Lane4.threeQuarterOrder rfl W w _ hW hΦ
  -- the pointwise-in-`n` trace bound
  have hbound : ∀ n, (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((a n).val x * ∑ i : Fin d, ((cut n).val.2 i x) ^ 2) *
        ENNReal.ofReal (((Φ n).val.1 x - w x) ^ 2)).toReal ≤
      C * (2 * B) * (cubeFractionalL2Norm hd z r hr halfFractionalOrder (diff n)) ^ 2 := by
    intro n
    have hρ : Measurable (fun y => ENNReal.ofReal ((a n).val y *
        ∑ i : Fin d, ((cut n).val.2 i y) ^ 2)) :=
      ((Lp.stronglyMeasurable (a n).val).measurable.mul
        (Finset.measurable_sum _ fun i _ =>
          (Lp.stronglyMeasurable ((cut n).val.2 i)).measurable.pow_const 2)).ennreal_ofReal
    have hmass : (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal ((a n).val x * ∑ i : Fin d, ((cut n).val.2 i x) ^ 2)) ≤
        ENNReal.ofReal B := by
      rw [aux_prop_locality_recovery_mass_eq S (a n) (cut n)]
      exact ENNReal.ofReal_le_ofReal (hcutE n)
    have h := htrace _ hρ B hB hmass (hgrowth n) (diff n)
    have heq : (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal ((a n).val x * ∑ i : Fin d, ((cut n).val.2 i x) ^ 2) *
          ENNReal.ofReal (((Φ n).val.1 x - w x) ^ 2)) =
        ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal ((a n).val x * ∑ i : Fin d, ((cut n).val.2 i x) ^ 2) *
            ENNReal.ofReal
              ((((diff n).val 0 : DomainL2 (centeredCube z r hr)) :
                SpatialCoordinates d → ℝ) x ^ 2) := by
      apply lintegral_congr_ae
      rw [hdiff n]
      filter_upwards [Lp.coeFn_sub (Φ n).val.1 w] with x hx
      rw [hx, Pi.sub_apply]
    rw [heq]
    exact ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (mul_nonneg hC (by linarith)) (sq_nonneg _)) h
  have hlim : Tendsto (fun n =>
      C * (2 * B) * (cubeFractionalL2Norm hd z r hr halfFractionalOrder (diff n)) ^ 2)
      atTop (𝓝 0) := by
    have := (hdiff0.pow 2).const_mul (C * (2 * B))
    simpa using this
  exact squeeze_zero (fun n => ENNReal.toReal_nonneg) hbound hlim

end LocRecTraceCube

/-- Nested open sets between a compact set and an open neighbourhood inside the cube. -/
theorem aux_prop_locality_recovery_nested_sets {d : ℕ} (K W Q : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (hW : IsOpen W) (hQ : IsOpen Q) (hKW : K ⊆ W) (hKQ : K ⊆ Q) :
    ∃ O₁ O₂ : Set (SpatialCoordinates d), IsOpen O₁ ∧ IsOpen O₂ ∧ K ⊆ O₁ ∧
      IsCompact (closure O₁) ∧ closure O₁ ⊆ O₂ ∧ closure O₂ ⊆ W ∩ Q := by
  obtain ⟨O₁, hO₁, hKO₁, hO₁cl, hO₁c⟩ :=
    exists_open_between_and_isCompact_closure hK (hW.inter hQ) (subset_inter hKW hKQ)
  obtain ⟨O₂, hO₂, hKO₂, hO₂cl, -⟩ :=
    exists_open_between_and_isCompact_closure hO₁c (hW.inter hQ) hO₁cl
  exact ⟨O₁, O₂, hO₁, hO₂, hKO₁, hO₁c, hKO₂, hO₂cl⟩

section LocRecC

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

theorem aux_prop_locality_recovery_mem_space (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    {x : SobolevData Ω} (hx : x ∈ killedSobolevGraph Ω) : x ∈ S.space :=
  (congrArg (fun V : Submodule ℝ (SobolevData Ω) => x ∈ V) hS).mpr hx

theorem aux_prop_locality_recovery_mem_killed (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (x : S.space) : (x : SobolevData Ω) ∈ killedSobolevGraph Ω :=
  (congrArg (fun V : Submodule ℝ (SobolevData Ω) => (x : SobolevData Ω) ∈ V) hS).mp x.2

/-- The outer modification `c χ + (1 - χ) φ` of a test function. -/
def aux_prop_locality_recovery_modU (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (φ : 𝓓(Ω, ℝ)) (χ : S.space) (c : ℝ) : S.space :=
  ⟨smoothSobolevData φ + c • (χ : SobolevData Ω) - aux_prop_locality_recovery_mulTest φ (χ : SobolevData Ω),
    aux_prop_locality_recovery_mem_space S hS (Submodule.sub_mem _
      (Submodule.add_mem _ (smoothSobolevData_mem_killed φ)
        (Submodule.smul_mem _ c (aux_prop_locality_recovery_mem_killed S hS χ)))
      (aux_prop_locality_recovery_mulTest_mem φ (aux_prop_locality_recovery_mem_killed S hS χ)))⟩

/-- The inner modification `ψ φ` of a test function. -/
def aux_prop_locality_recovery_modV (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (φ : 𝓓(Ω, ℝ)) (ψ : S.space) : S.space :=
  ⟨aux_prop_locality_recovery_mulTest φ (ψ : SobolevData Ω),
    aux_prop_locality_recovery_mem_space S hS (aux_prop_locality_recovery_mulTest_mem φ (aux_prop_locality_recovery_mem_killed S hS ψ))⟩

/-- Principal part `(1 - χ) ∂φ` of the outer gradient. -/
def aux_prop_locality_recovery_modU_P (φ : 𝓓(Ω, ℝ)) (χ : SobolevData Ω) (i : Fin d) : DomainL2 Ω :=
  testPartialL2 φ i - aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ i) χ.1

/-- Cutoff-error part `(c - φ) ∂χ` of the outer gradient. -/
def aux_prop_locality_recovery_modU_R (φ : 𝓓(Ω, ℝ)) (χ : SobolevData Ω) (c : ℝ) (i : Fin d) : DomainL2 Ω :=
  c • χ.2 i - aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) (χ.2 i)

theorem aux_prop_locality_recovery_modU_grad (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (φ : 𝓓(Ω, ℝ)) (χ : S.space) (c : ℝ) (i : Fin d) :
    (aux_prop_locality_recovery_modU S hS φ χ c : SobolevData Ω).2 i =
      aux_prop_locality_recovery_modU_P φ (χ : SobolevData Ω) i + aux_prop_locality_recovery_modU_R φ (χ : SobolevData Ω) c i := by
  change testPartialL2 φ i + c • (χ : SobolevData Ω).2 i -
      (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ i) (χ : SobolevData Ω).1 +
        aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) ((χ : SobolevData Ω).2 i)) = _
  unfold aux_prop_locality_recovery_modU_P aux_prop_locality_recovery_modU_R
  abel

theorem aux_prop_locality_recovery_modU_P_ae (φ : 𝓓(Ω, ℝ)) (χ : SobolevData Ω) (i : Fin d) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      aux_prop_locality_recovery_modU_P φ χ i x = (1 - χ.1 x) * fderiv ℝ φ x (Pi.single i 1) := by
  unfold aux_prop_locality_recovery_modU_P
  filter_upwards [Lp.coeFn_sub (testPartialL2 φ i)
      (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ i) χ.1),
    testPartialL2_coeFn φ i, aux_prop_locality_recovery_mulL_coeFn (aux_prop_locality_recovery_testPartialLinf φ i) χ.1,
    aux_prop_locality_recovery_testPartialLinf_coeFn φ i] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, h4]
  ring

theorem aux_prop_locality_recovery_modU_R_ae (φ : 𝓓(Ω, ℝ)) (χ : SobolevData Ω) (c : ℝ) (i : Fin d) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      aux_prop_locality_recovery_modU_R φ χ c i x = (c - φ x) * χ.2 i x := by
  unfold aux_prop_locality_recovery_modU_R
  filter_upwards [Lp.coeFn_sub (c • χ.2 i) (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) (χ.2 i)),
    Lp.coeFn_smul c (χ.2 i), aux_prop_locality_recovery_mulL_coeFn (aux_prop_locality_recovery_testLinf φ) (χ.2 i),
    aux_prop_locality_recovery_testLinf_coeFn φ] with x h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3, Pi.smul_apply, h4, smul_eq_mul]
  ring

theorem aux_prop_locality_recovery_modU_fst_ae (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (φ : 𝓓(Ω, ℝ)) (χ : S.space) (c : ℝ) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (aux_prop_locality_recovery_modU S hS φ χ c : SobolevData Ω).1 x =
        φ x + c * (χ : SobolevData Ω).1 x - φ x * (χ : SobolevData Ω).1 x := by
  change ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
    ((testL2 φ + c • (χ : SobolevData Ω).1 -
      aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) (χ : SobolevData Ω).1 : DomainL2 Ω) :
        SpatialCoordinates d → ℝ) x = _
  filter_upwards [Lp.coeFn_sub (testL2 φ + c • (χ : SobolevData Ω).1)
      (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) (χ : SobolevData Ω).1),
    Lp.coeFn_add (testL2 φ) (c • (χ : SobolevData Ω).1),
    Lp.coeFn_smul c (χ : SobolevData Ω).1, testL2_coeFn φ,
    aux_prop_locality_recovery_mulL_coeFn (aux_prop_locality_recovery_testLinf φ) (χ : SobolevData Ω).1,
    aux_prop_locality_recovery_testLinf_coeFn φ] with x h1 h2 h3 h4 h5 h6
  rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3, Pi.smul_apply, h4, h5, h6, smul_eq_mul]

theorem aux_prop_locality_recovery_modV_grad (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (φ : 𝓓(Ω, ℝ)) (ψ : S.space) (i : Fin d) :
    (aux_prop_locality_recovery_modV S hS φ ψ : SobolevData Ω).2 i =
      aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ i) (ψ : SobolevData Ω).1 +
        aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) ((ψ : SobolevData Ω).2 i) := rfl

theorem aux_prop_locality_recovery_modV_P_ae (φ : 𝓓(Ω, ℝ)) (ψ : SobolevData Ω) (i : Fin d) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ i) ψ.1 x =
        ψ.1 x * fderiv ℝ φ x (Pi.single i 1) := by
  filter_upwards [aux_prop_locality_recovery_mulL_coeFn (aux_prop_locality_recovery_testPartialLinf φ i) ψ.1,
    aux_prop_locality_recovery_testPartialLinf_coeFn φ i] with x h1 h2
  rw [h1, h2, mul_comm]

theorem aux_prop_locality_recovery_modV_R_ae (φ : 𝓓(Ω, ℝ)) (ψ : SobolevData Ω) (i : Fin d) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) (ψ.2 i) x = φ x * ψ.2 i x := by
  filter_upwards [aux_prop_locality_recovery_mulL_coeFn (aux_prop_locality_recovery_testLinf φ) (ψ.2 i),
    aux_prop_locality_recovery_testLinf_coeFn φ] with x h1 h2
  rw [h1, h2]

theorem aux_prop_locality_recovery_modV_fst_ae (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (φ : 𝓓(Ω, ℝ)) (ψ : S.space) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (aux_prop_locality_recovery_modV S hS φ ψ : SobolevData Ω).1 x = φ x * (ψ : SobolevData Ω).1 x := by
  change ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
    (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) (ψ : SobolevData Ω).1 :
      SpatialCoordinates d → ℝ) x = _
  filter_upwards [aux_prop_locality_recovery_mulL_coeFn (aux_prop_locality_recovery_testLinf φ) (ψ : SobolevData Ω).1,
    aux_prop_locality_recovery_testLinf_coeFn φ] with x h1 h2
  rw [h1, h2]

/-- Young splitting of a modified response energy into principal and trace parts. -/
theorem aux_prop_locality_recovery_energy_split (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (Y Φ : S.space) (P R g : Fin d → DomainL2 Ω) (f : SpatialCoordinates d → ℝ)
    (hY : ∀ i, (Y : SobolevData Ω).2 i = P i + R i)
    (hP : ∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      |P i x| ≤ |(Φ : SobolevData Ω).2 i x|)
    (hR : ∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (R i x) ^ 2 = (f x) ^ 2 * (g i x) ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    responseForm S a Y Y ≤ (1 + ε) * responseForm S a Φ Φ + (1 + ε⁻¹) *
      (∫⁻ x in (Ω : Set (SpatialCoordinates d)),
        ENNReal.ofReal (a.val x * ∑ i : Fin d, (g i x) ^ 2) * ENNReal.ofReal ((f x) ^ 2)).toReal := by
  have ha := aux_prop_locality_recovery_coeff_nonneg a
  rw [aux_prop_locality_recovery_responseForm_eq_sum S a Y Y, aux_prop_locality_recovery_responseForm_eq_sum S a Φ Φ]
  have hsplit : ∀ i, weightedL2Form a.val ((Y : SobolevData Ω).2 i) ((Y : SobolevData Ω).2 i) ≤
      (1 + ε) * weightedL2Form a.val (P i) (P i) + (1 + ε⁻¹) * weightedL2Form a.val (R i) (R i) := by
    intro i
    rw [hY i]
    exact aux_prop_locality_recovery_quad_split a.val ha (P i) (R i) hε
  have hPi : ∀ i, weightedL2Form a.val (P i) (P i) ≤
      weightedL2Form a.val ((Φ : SobolevData Ω).2 i) ((Φ : SobolevData Ω).2 i) :=
    fun i => aux_prop_locality_recovery_weighted_mono a.val ha _ _ (hP i)
  have hRsum : ∑ i : Fin d, weightedL2Form a.val (R i) (R i) =
      (∫⁻ x in (Ω : Set (SpatialCoordinates d)),
        ENNReal.ofReal (a.val x * ∑ i : Fin d, (g i x) ^ 2) * ENNReal.ofReal ((f x) ^ 2)).toReal := by
    rw [← aux_prop_locality_recovery_sum_weighted_eq Finset.univ a.val ha R g f hR,
      ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => aux_prop_locality_recovery_weighted_nonneg a.val ha _)]
  rw [← hRsum]
  have h1 : ∑ i : Fin d, weightedL2Form a.val ((Y : SobolevData Ω).2 i) ((Y : SobolevData Ω).2 i) ≤
      ∑ i : Fin d, ((1 + ε) * weightedL2Form a.val (P i) (P i) +
        (1 + ε⁻¹) * weightedL2Form a.val (R i) (R i)) :=
    Finset.sum_le_sum fun i _ => hsplit i
  have h2 : ∑ i : Fin d, weightedL2Form a.val (P i) (P i) ≤
      ∑ i : Fin d, weightedL2Form a.val ((Φ : SobolevData Ω).2 i) ((Φ : SobolevData Ω).2 i) :=
    Finset.sum_le_sum fun i _ => hPi i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
  have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 + ε)
  linarith

/-- Exact vanishing of a cross energy with pointwise disjoint gradients. -/
theorem aux_prop_locality_recovery_cross_zero (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (Y Z : S.space)
    (h : ∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (Y : SobolevData Ω).2 i x = 0 ∨ (Z : SobolevData Ω).2 i x = 0) :
    responseForm S a Y Z = 0 := by
  rw [responseForm_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  apply integral_eq_zero_of_ae
  filter_upwards [h i] with x hx
  rcases hx with hx | hx <;> simp [hx]

end LocRecC

section LocRecD

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Support facts for the outer cutoff: range, and function and gradient supported
where `u = c`. -/
theorem aux_prop_locality_recovery_outer_ae (χ : SobolevData Ω) (hχ : χ ∈ weakSobolevGraph Ω)
    (chic : SpatialCoordinates d → ℝ)
    (hχc : (χ.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] chic)
    (h01 : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), 0 ≤ chic x ∧ chic x ≤ 1)
    (O W : Set (SpatialCoordinates d))
    (hvan : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), x ∉ O → chic x = 0)
    (hOW : closure O ⊆ W)
    (u : DomainL2 Ω) (uc : SpatialCoordinates d → ℝ)
    (huc : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] uc)
    (c : ℝ) (hconst : ∀ x ∈ W, uc x = c) :
    (∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 ≤ χ.1 x ∧ χ.1 x ≤ 1) ∧
    (∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), χ.1 x ≠ 0 → u x = c) ∧
    (∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), χ.2 i x ≠ 0 → u x = c) := by
  have hΩ := ae_restrict_mem (μ := volume) Ω.isOpen.measurableSet
  refine ⟨?_, ?_, fun i => ?_⟩
  · filter_upwards [hχc, hΩ] with x h1 h2
    rw [h1]; exact h01 x h2
  · filter_upwards [hχc, hΩ, huc] with x h1 h2 h3 hx
    rw [h1] at hx
    have hxO : x ∈ O := by
      by_contra hn
      exact hx (hvan x h2 hn)
    rw [h3]
    exact hconst x (hOW (subset_closure hxO))
  · have hzero : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
        x ∈ (closure O)ᶜ → χ.1 x = 0 := by
      filter_upwards [hχc, hΩ] with x h1 h2 hx
      rw [h1]
      exact hvan x h2 (fun h => hx (subset_closure h))
    have hg := aux_prop_locality_recovery_grad_ae_zero_of_const χ hχ (closure O)ᶜ isClosed_closure.isOpen_compl
      0 hzero i
    filter_upwards [hg, huc] with x h1 h3 hx
    have hxcl : x ∈ closure O := by
      by_contra hn
      exact hx (h1 hn)
    rw [h3]
    exact hconst x (hOW hxcl)

/-- Support facts for the inner cutoff: range, plateau on `supp v`, and gradient
supported where `v = 0`. -/
theorem aux_prop_locality_recovery_inner_ae (ψ : SobolevData Ω) (hψ : ψ ∈ weakSobolevGraph Ω)
    (psic : SpatialCoordinates d → ℝ)
    (hψc : (ψ.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] psic)
    (h01 : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), 0 ≤ psic x ∧ psic x ≤ 1)
    (V : Set (SpatialCoordinates d)) (hV : IsOpen V) (hone : ∀ x ∈ V, psic x = 1)
    (v : DomainL2 Ω) (vc : SpatialCoordinates d → ℝ)
    (hvc : (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] vc)
    (hKV : tsupport vc ⊆ V) :
    (∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 ≤ ψ.1 x ∧ ψ.1 x ≤ 1) ∧
    (∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), v x ≠ 0 → ψ.1 x = 1) ∧
    (∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), ψ.2 i x ≠ 0 → v x = 0) := by
  have hΩ := ae_restrict_mem (μ := volume) Ω.isOpen.measurableSet
  refine ⟨?_, ?_, fun i => ?_⟩
  · filter_upwards [hψc, hΩ] with x h1 h2
    rw [h1]; exact h01 x h2
  · filter_upwards [hψc, hvc] with x h1 h3 hx
    rw [h3] at hx
    rw [h1]
    exact hone x (hKV (subset_tsupport _ hx))
  · have hone' : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∈ V → ψ.1 x = 1 := by
      filter_upwards [hψc] with x h1 hx
      rw [h1]; exact hone x hx
    have hg := aux_prop_locality_recovery_grad_ae_zero_of_const ψ hψ V hV 1 hone' i
    filter_upwards [hg, hvc] with x h1 h3 hx
    have hxV : x ∉ V := fun h => hx (h1 h)
    rw [h3]
    exact image_eq_zero_of_notMem_tsupport (fun h => hxV (hKV h))

/-- Nested plateaux: at almost every point either the outer cutoff is flat at one or
the inner cutoff is flat at zero. -/
theorem aux_prop_locality_recovery_cross_ae (χ ψ : SobolevData Ω) (hχ : χ ∈ weakSobolevGraph Ω)
    (hψ : ψ ∈ weakSobolevGraph Ω) (chic psic : SpatialCoordinates d → ℝ)
    (hχc : (χ.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] chic)
    (hψc : (ψ.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] psic)
    (V O : Set (SpatialCoordinates d)) (hV : IsOpen V) (hOV : closure O ⊆ V)
    (hone : ∀ x ∈ V, chic x = 1)
    (hvan : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), x ∉ O → psic x = 0) (i : Fin d) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (χ.1 x = 1 ∧ χ.2 i x = 0) ∨ (ψ.1 x = 0 ∧ ψ.2 i x = 0) := by
  have hΩ := ae_restrict_mem (μ := volume) Ω.isOpen.measurableSet
  have hone' : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), x ∈ V → χ.1 x = 1 := by
    filter_upwards [hχc] with x h1 hx
    rw [h1]; exact hone x hx
  have hzero' : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      x ∈ (closure O)ᶜ → ψ.1 x = 0 := by
    filter_upwards [hψc, hΩ] with x h1 h2 hx
    rw [h1]
    exact hvan x h2 (fun h => hx (subset_closure h))
  have hgχ := aux_prop_locality_recovery_grad_ae_zero_of_const χ hχ V hV 1 hone' i
  have hgψ := aux_prop_locality_recovery_grad_ae_zero_of_const ψ hψ (closure O)ᶜ isClosed_closure.isOpen_compl
    0 hzero' i
  filter_upwards [hone', hzero', hgχ, hgψ] with x h1 h2 h3 h4
  by_cases hx : x ∈ V
  · exact Or.inl ⟨h1 hx, h3 hx⟩
  · have hx' : x ∈ (closure O)ᶜ := fun h => hx (hOV h)
    exact Or.inr ⟨h2 hx', h4 hx'⟩

/-- Properties of the outer modification along one test function. -/
theorem aux_prop_locality_recovery_modU_props (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (φ : 𝓓(Ω, ℝ)) (Φ : S.space) (hΦ : (Φ : SobolevData Ω) = smoothSobolevData φ)
    (χ : S.space) (c : ℝ) (u : DomainL2 Ω)
    (h01 : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      0 ≤ (χ : SobolevData Ω).1 x ∧ (χ : SobolevData Ω).1 x ≤ 1)
    (hχu : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (χ : SobolevData Ω).1 x ≠ 0 → u x = c)
    (hgu : ∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (χ : SobolevData Ω).2 i x ≠ 0 → u x = c) :
    (∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      |aux_prop_locality_recovery_modU_P φ (χ : SobolevData Ω) i x| ≤ |(Φ : SobolevData Ω).2 i x|) ∧
    (∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (aux_prop_locality_recovery_modU_R φ (χ : SobolevData Ω) c i x) ^ 2 =
        ((Φ : SobolevData Ω).1 x - u x) ^ 2 * ((χ : SobolevData Ω).2 i x) ^ 2) ∧
    (∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      |(aux_prop_locality_recovery_modU S hS φ χ c : SobolevData Ω).1 x - u x| ≤
        |(Φ : SobolevData Ω).1 x - u x|) := by
  rw [hΦ]
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · filter_upwards [aux_prop_locality_recovery_modU_P_ae φ (χ : SobolevData Ω) i, testPartialL2_coeFn φ i, h01]
      with x h1 h2 h3
    change |aux_prop_locality_recovery_modU_P φ (χ : SobolevData Ω) i x| ≤ |(testPartialL2 φ i) x|
    rw [h1, h2, abs_mul]
    have : |1 - (χ : SobolevData Ω).1 x| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [h3.1, h3.2]
    exact mul_le_of_le_one_left (abs_nonneg _) this
  · filter_upwards [aux_prop_locality_recovery_modU_R_ae φ (χ : SobolevData Ω) c i, testL2_coeFn φ, hgu i]
      with x h1 h2 h3
    change (aux_prop_locality_recovery_modU_R φ (χ : SobolevData Ω) c i x) ^ 2 =
      ((testL2 φ : SpatialCoordinates d → ℝ) x - u x) ^ 2 * ((χ : SobolevData Ω).2 i x) ^ 2
    rw [h1, h2]
    by_cases hg : (χ : SobolevData Ω).2 i x = 0
    · rw [hg]; ring
    · rw [h3 hg]; ring
  · filter_upwards [aux_prop_locality_recovery_modU_fst_ae S hS φ χ c, testL2_coeFn φ, h01, hχu]
      with x h1 h2 h3 h4
    change |(aux_prop_locality_recovery_modU S hS φ χ c : SobolevData Ω).1 x - u x| ≤
      |(testL2 φ : SpatialCoordinates d → ℝ) x - u x|
    rw [h1, h2]
    by_cases hχ0 : (χ : SobolevData Ω).1 x = 0
    · rw [hχ0]; simp
    · rw [h4 hχ0]
      have he : φ x + c * (χ : SobolevData Ω).1 x - φ x * (χ : SobolevData Ω).1 x - c =
          (1 - (χ : SobolevData Ω).1 x) * (φ x - c) := by ring
      rw [he, abs_mul]
      have : |1 - (χ : SobolevData Ω).1 x| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [h3.1, h3.2]
      exact mul_le_of_le_one_left (abs_nonneg _) this

/-- Properties of the inner modification along one test function. -/
theorem aux_prop_locality_recovery_modV_props (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (φ : 𝓓(Ω, ℝ)) (Φ : S.space) (hΦ : (Φ : SobolevData Ω) = smoothSobolevData φ)
    (ψ : S.space) (v : DomainL2 Ω)
    (h01 : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      0 ≤ (ψ : SobolevData Ω).1 x ∧ (ψ : SobolevData Ω).1 x ≤ 1)
    (hvψ : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      v x ≠ 0 → (ψ : SobolevData Ω).1 x = 1)
    (hgv : ∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (ψ : SobolevData Ω).2 i x ≠ 0 → v x = 0) :
    (∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      |aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ i) (ψ : SobolevData Ω).1 x| ≤
        |(Φ : SobolevData Ω).2 i x|) ∧
    (∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) ((ψ : SobolevData Ω).2 i) x) ^ 2 =
        ((Φ : SobolevData Ω).1 x - v x) ^ 2 * ((ψ : SobolevData Ω).2 i x) ^ 2) ∧
    (∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      |(aux_prop_locality_recovery_modV S hS φ ψ : SobolevData Ω).1 x - v x| ≤
        |(Φ : SobolevData Ω).1 x - v x|) := by
  rw [hΦ]
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · filter_upwards [aux_prop_locality_recovery_modV_P_ae φ (ψ : SobolevData Ω) i, testPartialL2_coeFn φ i, h01]
      with x h1 h2 h3
    change |aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ i) (ψ : SobolevData Ω).1 x| ≤
      |(testPartialL2 φ i) x|
    rw [h1, h2, abs_mul]
    have : |(ψ : SobolevData Ω).1 x| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [h3.1, h3.2]
    exact mul_le_of_le_one_left (abs_nonneg _) this
  · filter_upwards [aux_prop_locality_recovery_modV_R_ae φ (ψ : SobolevData Ω) i, testL2_coeFn φ, hgv i]
      with x h1 h2 h3
    change (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ) ((ψ : SobolevData Ω).2 i) x) ^ 2 =
      ((testL2 φ : SpatialCoordinates d → ℝ) x - v x) ^ 2 * ((ψ : SobolevData Ω).2 i x) ^ 2
    rw [h1, h2]
    by_cases hg : (ψ : SobolevData Ω).2 i x = 0
    · rw [hg]; ring
    · rw [h3 hg]; ring
  · filter_upwards [aux_prop_locality_recovery_modV_fst_ae S hS φ ψ, testL2_coeFn φ, h01, hvψ]
      with x h1 h2 h3 h4
    change |(aux_prop_locality_recovery_modV S hS φ ψ : SobolevData Ω).1 x - v x| ≤
      |(testL2 φ : SpatialCoordinates d → ℝ) x - v x|
    rw [h1, h2]
    by_cases hv0 : v x = 0
    · rw [hv0, sub_zero, sub_zero, abs_mul]
      have : |(ψ : SobolevData Ω).1 x| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [h3.1, h3.2]
      exact mul_le_of_le_one_right (abs_nonneg _) this
    · rw [h4 hv0, mul_one]

/-- The nested modifications have exactly zero cross energy. -/
theorem aux_prop_locality_recovery_modUV_cross (S : ResponseSpace Ω) (hS : S.space = killedSobolevGraph Ω)
    (a : PositiveCoefficient Ω) (φ φ' : 𝓓(Ω, ℝ)) (χ ψ : S.space) (c : ℝ)
    (hX : ∀ i, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      ((χ : SobolevData Ω).1 x = 1 ∧ (χ : SobolevData Ω).2 i x = 0) ∨
        ((ψ : SobolevData Ω).1 x = 0 ∧ (ψ : SobolevData Ω).2 i x = 0)) :
    responseForm S a (aux_prop_locality_recovery_modU S hS φ χ c) (aux_prop_locality_recovery_modV S hS φ' ψ) = 0 := by
  apply aux_prop_locality_recovery_cross_zero
  intro i
  rw [aux_prop_locality_recovery_modU_grad, aux_prop_locality_recovery_modV_grad]
  filter_upwards [hX i,
    Lp.coeFn_add (aux_prop_locality_recovery_modU_P φ (χ : SobolevData Ω) i)
      (aux_prop_locality_recovery_modU_R φ (χ : SobolevData Ω) c i),
    Lp.coeFn_add (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf φ' i) (ψ : SobolevData Ω).1)
      (aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf φ') ((ψ : SobolevData Ω).2 i)),
    aux_prop_locality_recovery_modU_P_ae φ (χ : SobolevData Ω) i, aux_prop_locality_recovery_modU_R_ae φ (χ : SobolevData Ω) c i,
    aux_prop_locality_recovery_modV_P_ae φ' (ψ : SobolevData Ω) i, aux_prop_locality_recovery_modV_R_ae φ' (ψ : SobolevData Ω) i]
    with x hx h1 h2 h3 h4 h5 h6
  rcases hx with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    rw [h1, Pi.add_apply, h3, h4, ha, hb]
    ring
  · right
    rw [h2, Pi.add_apply, h5, h6, ha, hb]
    ring

end LocRecD

theorem aux_prop_locality_recovery_recovery_parts {Hs : Type*} [TopologicalSpace Hs] (y : ℕ → Hs) (e : ℕ → ℝ)
    (w : Hs) (Ew : EReal) (h0 : 0 ≤ Ew) (hw : Ew < ⊤)
    (h : Tendsto (fun n => (y n, ((e n : ℝ) : EReal))) atTop (𝓝 (w, Ew))) :
    Tendsto y atTop (𝓝 w) ∧ Tendsto e atTop (𝓝 Ew.toReal) := by
  refine ⟨(continuous_fst.tendsto _).comp h, ?_⟩
  have h2 : Tendsto (fun n => ((e n : ℝ) : EReal)) atTop (𝓝 Ew) :=
    (continuous_snd.tendsto _).comp h
  have hEL : Ew = ((Ew.toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hw.ne (ne_bot_of_le_ne_bot (by simp) h0)).symm
  rw [hEL] at h2
  exact EReal.tendsto_coe.1 h2

/-- One side of the construction: an `L²`-dominated modification whose gradient splits
into a principal part dominated by the smooth recovery gradient and a cutoff-error part
controlled by the cutoff energy measure is again a recovery sequence. -/
theorem aux_prop_locality_recovery_side {d : ℕ} (hd : 2 ≤ d) (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hLower : ∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n) (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (cut : ℕ → S.space) (B : ℝ) (hB : 0 ≤ B)
    (hcutE : ∀ n, responseForm S (a n) (cut n) (cut n) ≤ B)
    (hgrowth : ∀ n, ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((cut n).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))
    (w : DomainL2 (centeredCube z r hr)) (hw : limitFormEnergy G w < ⊤)
    (Φ : ℕ → S.space) (hΦ1 : Tendsto (fun n => (Φ n).val.1) atTop (𝓝 w))
    (hΦE : Tendsto (fun n => responseForm S (a n) (Φ n) (Φ n)) atTop
      (𝓝 (limitFormEnergy G w).toReal))
    (Y : ℕ → S.space) (P R : ℕ → Fin d → DomainL2 (centeredCube z r hr))
    (hY : ∀ n i, (Y n).val.2 i = P n i + R n i)
    (hP : ∀ n i, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      |P n i x| ≤ |(Φ n).val.2 i x|)
    (hR : ∀ n i, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (R n i x) ^ 2 = ((Φ n).val.1 x - w x) ^ 2 * ((cut n).val.2 i x) ^ 2)
    (hL2 : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      |(Y n).val.1 x - w x| ≤ |(Φ n).val.1 x - w x|) :
    Tendsto (fun n => ((Y n).val.1,
      ((responseForm S (a n) (Y n) (Y n) : ℝ) : EReal))) atTop
      (𝓝 (w, limitFormEnergy G w)) := by
  obtain ⟨Eb, hEb⟩ := hΦE.bddAbove_range
  have hEb' : ∀ n, responseForm S (a n) (Φ n) (Φ n) ≤ Eb := fun n => hEb ⟨n, rfl⟩
  have hT := aux_prop_locality_recovery_trace_tendsto hd hInterp z r hr t ht S a KN hKN Kstar hKstar hfrac
    hcoercive cut B hB hcutE hgrowth Φ w hΦ1 Eb hEb'
  refine aux_prop_locality_recovery_recovery_abstract (fun n => (Y n).val.1) (fun n => (Φ n).val.1) w
    (limitFormEnergy G w) (limitFormEnergy_nonneg G w) hw
    (fun n => responseForm S (a n) (Y n) (Y n)) (fun n => responseForm S (a n) (Φ n) (Φ n))
    (fun n => (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((a n).val x * ∑ i : Fin d, ((cut n).val.2 i x) ^ 2) *
        ENNReal.ofReal (((Φ n).val.1 x - w x) ^ 2)).toReal)
    (fun h => hLower Y w (fun f => tendsto_const_nhds.inner h)) hΦ1 hΦE
    (fun n => ?_) (fun n ε hε => ?_) hT
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (Y n).val.1 w, Lp.coeFn_sub (Φ n).val.1 w, hL2 n]
      with x h1 h2 h3
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
    exact h3
  · exact aux_prop_locality_recovery_energy_split S (a n) (Y n) (Φ n) (P n) (R n)
      (fun i => (cut n).val.2 i) (fun x => (Φ n).val.1 x - w x) (hY n) (hP n) (hR n) hε

/-- Let-free form of the principal construction. -/
theorem aux_prop_locality_recovery_main
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hLower : ∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr), Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (hRecovery : ∀ w ∈ limitFormDomain G, ∃ wN : ℕ → S.space,
      Tendsto (fun n => ((wN n).val.1,
        ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop
        (𝓝 (w, limitFormEnergy G w)))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real ((centeredCube z r hr) : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ ((centeredCube z r hr) : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure ((centeredCube z r hr) : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict ((centeredCube z r hr) : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ ((centeredCube z r hr) : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ ((centeredCube z r hr) : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure ((centeredCube z r hr) : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict ((centeredCube z r hr) : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (u v : DomainL2 (centeredCube z r hr)) (hu : MemFormCore G u) (hv : MemFormCore G v)
    (uc vc : SpatialCoordinates d → ℝ)
    (huc : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((centeredCube z r hr) : Set (SpatialCoordinates d))] uc)
    (hvc : (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((centeredCube z r hr) : Set (SpatialCoordinates d))] vc)
    (_hucont : Continuous uc) (_hvcont : Continuous vc)
    (hvsupp : HasCompactSupport vc)
    (_husuppQ : tsupport uc ⊆ ((centeredCube z r hr) : Set (SpatialCoordinates d)))
    (hvsuppQ : tsupport vc ⊆ ((centeredCube z r hr) : Set (SpatialCoordinates d)))
    (_husupp : HasCompactSupport uc)
    (c : ℝ) (W : Set (SpatialCoordinates d)) (hW : IsOpen W)
    (hsupp : tsupport vc ⊆ W) (hconst : ∀ x ∈ W, uc x = c) :
    ∃ uN' vN' : ℕ → S.space,
      Tendsto (fun n => ((uN' n).val.1,
        ((responseForm S (a n) (uN' n) (uN' n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy G u)) ∧
      Tendsto (fun n => ((vN' n).val.1,
        ((responseForm S (a n) (vN' n) (vN' n) : ℝ) : EReal))) atTop
        (𝓝 (v, limitFormEnergy G v)) ∧
      ∀ n : ℕ, responseForm S (a n) (uN' n) (vN' n) = 0 := by
  -- nested compact/open pairs inside `W`
  have hob1 :=
    aux_prop_locality_recovery_nested_sets (tsupport vc) W (centeredCube z r hr : Set (SpatialCoordinates d)) hvsupp.isCompact hW
      (centeredCube z r hr).isOpen hsupp hvsuppQ
  obtain ⟨O₁, O₂, hO₁, hO₂, hKO₁, hO₁c, hO₁O₂, hO₂WQ⟩ := hob1
  have hO₂W : closure O₂ ⊆ W := fun x hx => (hO₂WQ hx).1
  have hO₂Q : closure O₂ ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := fun x hx => (hO₂WQ hx).2
  have hO₁Q : closure O₁ ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    fun x hx => hO₂Q (subset_closure (hO₁O₂ hx))
  -- inner cutoffs `ψ_n` for `supp v ⊆ O₁`, outer cutoffs `χ_n` for `closure O₁ ⊆ O₂`
  have hob2 :=
    hcutoffs (tsupport vc) O₁ hvsupp.isCompact hO₁ hKO₁ hO₁Q
  obtain ⟨V₁, psi, psic, B₁, hV₁, hKV₁, -, hB₁, hpsi⟩ := hob2
  have hob3 :=
    hcutoffs (closure O₁) O₂ hO₁c hO₂ hO₁O₂ hO₂Q
  obtain ⟨V₂, chi, chic, B₂, hV₂, hKV₂, -, hB₂, hchi⟩ := hob3
  -- recovery sequences, replaced by test functions
  have hob4 := hRecovery u hu.1
  obtain ⟨uN, huN⟩ := hob4
  have hob5 := hRecovery v hv.1
  obtain ⟨vN, hvN⟩ := hob5
  have hob6 := aux_prop_locality_recovery_recovery_parts _ _ _ _ (limitFormEnergy_nonneg G u) hu.1 huN
  obtain ⟨huN1, huNE⟩ := hob6
  have hob7 := aux_prop_locality_recovery_recovery_parts _ _ _ _ (limitFormEnergy_nonneg G v) hv.1 hvN
  obtain ⟨hvN1, hvNE⟩ := hob7
  have hob8 := aux_prop_locality_recovery_smooth_seq S hS a uN u _ huN1 huNE
  obtain ⟨φ, Φ, hΦv, hΦ1, hΦE⟩ := hob8
  have hob9 := aux_prop_locality_recovery_smooth_seq S hS a vN v _ hvN1 hvNE
  obtain ⟨φ', Φ', hΦ'v, hΦ'1, hΦ'E⟩ := hob9
  -- support facts of the cutoffs
  have hout := fun n => aux_prop_locality_recovery_outer_ae (chi n).val (S.le_weak (chi n).2) (chic n)
    (hchi n).2.1 (hchi n).2.2.1 O₂ W (hchi n).2.2.2.2.1 hO₂W u uc huc c hconst
  have hin := fun n => aux_prop_locality_recovery_inner_ae (psi n).val (S.le_weak (psi n).2) (psic n)
    (hpsi n).2.1 (hpsi n).2.2.1 V₁ hV₁ (hpsi n).2.2.2.1 v vc hvc hKV₁
  have hX := fun n i => aux_prop_locality_recovery_cross_ae (chi n).val (psi n).val (S.le_weak (chi n).2)
    (S.le_weak (psi n).2) (chic n) (psic n) (hchi n).2.1 (hpsi n).2.1 V₂ O₁ hV₂ hKV₂
    (hchi n).2.2.2.1 (hpsi n).2.2.2.2.1 i
  refine ⟨fun n => aux_prop_locality_recovery_modU S hS (φ n) (chi n) c,
    fun n => aux_prop_locality_recovery_modV S hS (φ' n) (psi n), ?_, ?_,
    fun n => aux_prop_locality_recovery_modUV_cross S hS (a n) (φ n) (φ' n) (chi n) (psi n) c (hX n)⟩
  · have hprops := fun n => aux_prop_locality_recovery_modU_props S hS (φ n) (Φ n) (hΦv n) (chi n) c u
      (hout n).1 (hout n).2.1 (hout n).2.2
    exact aux_prop_locality_recovery_side hd hInterp z r hr t ht S a G hLower KN hKN Kstar hKstar hfrac hcoercive
      chi B₂ hB₂ (fun n => (hchi n).2.2.2.2.2.1) (fun n => (hchi n).2.2.2.2.2.2) u hu.1 Φ hΦ1 hΦE
      (fun n => aux_prop_locality_recovery_modU S hS (φ n) (chi n) c)
      (fun n i => aux_prop_locality_recovery_modU_P (φ n) (chi n).val i)
      (fun n i => aux_prop_locality_recovery_modU_R (φ n) (chi n).val c i)
      (fun n i => aux_prop_locality_recovery_modU_grad S hS (φ n) (chi n) c i)
      (fun n => (hprops n).1) (fun n => (hprops n).2.1) (fun n => (hprops n).2.2)
  · have hprops := fun n => aux_prop_locality_recovery_modV_props S hS (φ' n) (Φ' n) (hΦ'v n) (psi n) v
      (hin n).1 (hin n).2.1 (hin n).2.2
    exact aux_prop_locality_recovery_side hd hInterp z r hr t ht S a G hLower KN hKN Kstar hKstar hfrac hcoercive
      psi B₁ hB₁ (fun n => (hpsi n).2.2.2.2.2.1) (fun n => (hpsi n).2.2.2.2.2.2) v hv.1 Φ' hΦ'1
      hΦ'E (fun n => aux_prop_locality_recovery_modV S hS (φ' n) (psi n))
      (fun n i => aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testPartialLinf (φ' n) i) (psi n).val.1)
      (fun n i => aux_prop_locality_recovery_mulL (aux_prop_locality_recovery_testLinf (φ' n)) ((psi n).val.2 i))
      (fun n i => aux_prop_locality_recovery_modV_grad S hS (φ' n) (psi n) i)
      (fun n => (hprops n).1) (fun n => (hprops n).2.1) (fun n => (hprops n).2.2)

end LocRecAux

/--
- exact construction half, paper 2046–2073; zero-cross recovery is a conclusion;
- S is actual H1_0 on concrete cube;
- prop_killed_inverse supplies both original Mosco clauses, so G cannot vary independently of a;
- lem_coercivity, conv_represented_sequence supply finite fractional norm bounds and indexed constants bounded on this path;
- lem_19/published CubeFractionalInterpolationInput supplies trace/interpolation tools; H1/2 convergence not assumed;
- catalog_cutoff_existence/conv_catalog_cutoffs supply the nested cutoff choices and common all-radii control;
- u/v are core elements with their actual continuous compact representatives;
- the modification, vanishing error, recovery and exact zero cross energy remain to prove after phase 1.
-/
theorem prop_locality_recovery
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    let Q := centeredCube z r hr
    let H := DomainL2 Q
    ∀ (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (a : ℕ → PositiveCoefficient Q)
    (G : H →L[ℝ] H)
    (hLower : ∀ (wN : ℕ → S.space) (w : H),
      (∀ f : H, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (hRecovery : ∀ w ∈ limitFormDomain G, ∃ wN : ℕ → S.space,
      Tendsto (fun n => ((wN n).val.1,
        ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop
        (𝓝 (w, limitFormEnergy G w)))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (Q : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (u v : H) (hu : MemFormCore G u) (hv : MemFormCore G v)
    (uc vc : SpatialCoordinates d → ℝ)
    (huc : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] uc)
    (hvc : (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc)
    (hucont : Continuous uc) (hvcont : Continuous vc)
    (hvsupp : HasCompactSupport vc)
    (husuppQ : tsupport uc ⊆ (Q : Set (SpatialCoordinates d)))
    (hvsuppQ : tsupport vc ⊆ (Q : Set (SpatialCoordinates d)))
    (husupp : HasCompactSupport uc)
    (c : ℝ) (W : Set (SpatialCoordinates d)) (hW : IsOpen W)
    (hsupp : tsupport vc ⊆ W) (hconst : ∀ x ∈ W, uc x = c),
    ∃ uN' vN' : ℕ → S.space,
      Tendsto (fun n => ((uN' n).val.1,
        ((responseForm S (a n) (uN' n) (uN' n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy G u)) ∧
      Tendsto (fun n => ((vN' n).val.1,
        ((responseForm S (a n) (vN' n) (vN' n) : ℝ) : EReal))) atTop
        (𝓝 (v, limitFormEnergy G v)) ∧
      ∀ n : ℕ, responseForm S (a n) (uN' n) (vN' n) = 0 := by
  intro Q H
  exact aux_prop_locality_recovery_main d hd z r hr


end Paper
