module

public import SubdiffusiveProcess.Probability.Diffusion.SegmentTaylorTwo

@[expose] public section




set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The ambient (sup) norm on `Vec d` is dominated by the Euclidean one. -/
theorem norm_sq_le_vecNormSq (z : Vec d) : ‖z‖ ^ 2 ≤ vecNormSq z := by
  have hnn := vecNormSq_nonneg z
  have hle : ‖z‖ ≤ Real.sqrt (vecNormSq z) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs, show |z i| = Real.sqrt ((z i) ^ 2) from (Real.sqrt_sq_eq_abs _).symm]
    exact Real.sqrt_le_sqrt (sq_apply_le_vecNormSq z i)
  calc ‖z‖ ^ 2 ≤ (Real.sqrt (vecNormSq z)) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg z) hle 2
    _ = vecNormSq z := Real.sq_sqrt hnn

/-- The scaled second differential. -/
theorem iteratedFDeriv_two_smul {ψ : Vec d → ℝ} (x z : Vec d) (σ : ℝ) :
    iteratedFDeriv ℝ 2 ψ x ![σ • z, σ • z] = σ ^ 2 * iteratedFDeriv ℝ 2 ψ x ![z, z] := by
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [map_smul, map_smul, ContinuousLinearMap.smul_apply]
  simp only [smul_eq_mul]
  ring

/-- **The pointwise Taylor remainder against the Gaussian variable.**  A single bound valid on the
whole space: on the bulk the modulus `eps` applies, and on the tail the crude cap `K` is inflated
by the Chebyshev factor `σ² q / delta² > 1`, so no indicator is needed. -/
theorem abs_gaussian_remainder_le {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {K eps delta σ : ℝ} (hK : 0 ≤ K) (heps : 0 ≤ eps) (hdelta : 0 < delta) (hσ : 0 < σ)
    (hbound : ∀ y y' : Vec d, ‖iteratedFDeriv ℝ 2 ψ y - iteratedFDeriv ℝ 2 ψ y'‖ ≤ K)
    (hmod : ∀ y y' : Vec d, ‖y - y'‖ ≤ delta →
      ‖iteratedFDeriv ℝ 2 ψ y - iteratedFDeriv ℝ 2 ψ y'‖ ≤ eps)
    (x z : Vec d) :
    |ψ (x + σ • z) - ψ x - σ * fderiv ℝ ψ x z
        - σ ^ 2 / 2 * iteratedFDeriv ℝ 2 ψ x ![z, z]|
      ≤ eps * (σ ^ 2 * vecNormSq z) + K * (σ ^ 4 * vecNormSq z ^ 2) / delta ^ 2 := by
  have hq : (0:ℝ) ≤ vecNormSq z := vecNormSq_nonneg z
  have hnormsmul : ‖σ • z‖ = σ * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
  have hnsq : ‖σ • z‖ ^ 2 ≤ σ ^ 2 * vecNormSq z := by
    rw [hnormsmul, mul_pow]
    exact mul_le_mul_of_nonneg_left (norm_sq_le_vecNormSq z) (by positivity)
  have hrewrite : ψ (x + σ • z) - ψ x - σ * fderiv ℝ ψ x z
      - σ ^ 2 / 2 * iteratedFDeriv ℝ 2 ψ x ![z, z]
      = ψ (x + σ • z) - ψ x - fderiv ℝ ψ x (σ • z)
        - (1/2) * iteratedFDeriv ℝ 2 ψ x ![σ • z, σ • z] := by
    rw [iteratedFDeriv_two_smul, map_smul]
    simp [smul_eq_mul]
    ring
  rw [hrewrite]
  by_cases hbulk : σ ^ 2 * vecNormSq z ≤ delta ^ 2
  · have hseg : ∀ s ∈ Set.Icc (0:ℝ) 1,
        ‖iteratedFDeriv ℝ 2 ψ (x + s • (σ • z)) - iteratedFDeriv ℝ 2 ψ x‖ ≤ eps := by
      intro s hs
      refine hmod _ _ ?_
      have : x + s • (σ • z) - x = s • (σ • z) := by abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1, hnormsmul]
      have hzd : σ * ‖z‖ ≤ delta := by
        nlinarith [norm_nonneg z, norm_sq_le_vecNormSq z, hdelta.le, hσ.le, sq_nonneg (σ * ‖z‖)]
      nlinarith [norm_nonneg z, hσ.le, hs.1, hs.2]
    have hmain := abs_taylor_two_le hψ x (σ • z) hseg
    refine hmain.trans ?_
    have h1 : eps * ‖σ • z‖ ^ 2 ≤ eps * (σ ^ 2 * vecNormSq z) :=
      mul_le_mul_of_nonneg_left hnsq heps
    have h2 : (0:ℝ) ≤ K * (σ ^ 4 * vecNormSq z ^ 2) / delta ^ 2 := by positivity
    linarith
  · push_neg at hbulk
    have hseg : ∀ s ∈ Set.Icc (0:ℝ) 1,
        ‖iteratedFDeriv ℝ 2 ψ (x + s • (σ • z)) - iteratedFDeriv ℝ 2 ψ x‖ ≤ K :=
      fun s _ => hbound _ _
    have hmain := abs_taylor_two_le hψ x (σ • z) hseg
    refine hmain.trans ?_
    have h1 : K * ‖σ • z‖ ^ 2 ≤ K * (σ ^ 2 * vecNormSq z) :=
      mul_le_mul_of_nonneg_left hnsq hK
    have hbulk' : (0:ℝ) ≤ σ ^ 2 * vecNormSq z - delta ^ 2 := by linarith
    have hd2 : (0:ℝ) < delta ^ 2 := by positivity
    have hratio : K * (σ ^ 2 * vecNormSq z)
        ≤ K * (σ ^ 4 * vecNormSq z ^ 2) / delta ^ 2 := by
      rw [le_div_iff₀ hd2]
      nlinarith [mul_nonneg (mul_nonneg hK (mul_nonneg (sq_nonneg σ) hq)) hbulk']
    have h3 : (0:ℝ) ≤ eps * (σ ^ 2 * vecNormSq z) := by positivity
    linarith

/-! ## Basis expansion and the two Gaussian moment identities -/

/-- The standard basis expansion on `Vec d`. -/
theorem vec_eq_sum_single (z : Vec d) : z = ∑ i, z i • (Pi.single i (1:ℝ) : Vec d) := by
  classical
  funext j
  rw [Finset.sum_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq]

/-- A continuous linear map on `Vec d` is determined by its values on the standard basis. -/
theorem clm_apply_eq_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Vec d →L[ℝ] F) (z : Vec d) :
    L z = ∑ i, z i • L (Pi.single i (1:ℝ)) := by
  conv_lhs => rw [vec_eq_sum_single z]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]

/-- Each coordinate is integrable. -/
theorem integrable_coord (i : Fin d) :
    Integrable (fun z : Vec d => z i) (stdGaussianVec d) := by
  simpa using integrable_coord_pow i 1

/-- Products of two coordinates are integrable. -/
theorem integrable_coord_mul (i j : Fin d) :
    Integrable (fun z : Vec d => z i * z j) (stdGaussianVec d) := by
  classical
  by_cases hij : i = j
  · subst hij
    simpa [sq] using integrable_coord_pow i 2
  · have hprod : (fun z : Vec d => z i * z j) =
        fun z : Vec d => ∏ k : Fin d,
          (if k = i then (fun y : ℝ => y) else if k = j then (fun y : ℝ => y)
            else fun _ => (1:ℝ)) (z k) := by
      funext z
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      rw [Finset.prod_eq_single j]
      · simp [Ne.symm hij, mul_comm]
      · intro k hk hkj
        rcases Finset.mem_erase.mp hk with ⟨hki, -⟩
        simp [hki, hkj]
      · intro hmem
        exact absurd (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩) hmem
    rw [hprod, stdGaussianVec_eq_pi]
    refine Integrable.fintype_prod (f := fun k : Fin d =>
      if k = i then (fun y : ℝ => y) else if k = j then (fun y : ℝ => y)
        else fun _ => (1:ℝ)) ?_
    intro k
    by_cases hki : k = i
    · simpa [hki] using integrable_pow_gaussianReal_std 1
    · by_cases hkj : k = j
      · simpa [hki, hkj] using integrable_pow_gaussianReal_std 1
      · simp only [hki, hkj, if_false]
        exact integrable_const (1:ℝ)

/-- **The first moment of a linear form vanishes.** -/
theorem integral_clm_apply (L : Vec d →L[ℝ] ℝ) :
    ∫ z : Vec d, L z ∂(stdGaussianVec d) = 0 := by
  have hrw : ∀ z : Vec d, L z = ∑ i, z i * L (Pi.single i (1:ℝ)) := fun z => by
    simpa [smul_eq_mul] using clm_apply_eq_sum L z
  have hcongr : ∫ z : Vec d, L z ∂(stdGaussianVec d)
      = ∫ z : Vec d, (∑ i, z i * L (Pi.single i (1:ℝ))) ∂(stdGaussianVec d) :=
    integral_congr_ae (Filter.Eventually.of_forall hrw)
  rw [hcongr, integral_finset_sum _ fun i _ => (integrable_coord i).mul_const _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_mul_const, integral_coord i, zero_mul]

/-- A bilinear form applied on the diagonal, expanded in the standard basis. -/
theorem clm_bilin_diag_eq_sum (T : Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)) (z : Vec d) :
    T z z = ∑ i, ∑ j, (z i * z j) * T (Pi.single i (1:ℝ)) (Pi.single j (1:ℝ)) := by
  have h1 : T z z = ∑ i, z i * (T (Pi.single i (1:ℝ)) z) := by
    conv_lhs => rw [clm_apply_eq_sum T z]
    rw [ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : T (Pi.single i (1:ℝ)) z = ∑ j, z j * T (Pi.single i (1:ℝ)) (Pi.single j (1:ℝ)) := by
    simpa [smul_eq_mul] using clm_apply_eq_sum (T (Pi.single i (1:ℝ))) z
  rw [h2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The second moment of a bilinear form is its trace.** -/
theorem integral_clm_bilin_diag (T : Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)) :
    ∫ z : Vec d, T z z ∂(stdGaussianVec d)
      = ∑ i, T (Pi.single i (1:ℝ)) (Pi.single i (1:ℝ)) := by
  classical
  have hcongr : ∫ z : Vec d, T z z ∂(stdGaussianVec d)
      = ∫ z : Vec d, (∑ i, ∑ j, (z i * z j) *
          T (Pi.single i (1:ℝ)) (Pi.single j (1:ℝ))) ∂(stdGaussianVec d) :=
    integral_congr_ae (Filter.Eventually.of_forall (clm_bilin_diag_eq_sum T))
  rw [hcongr, integral_finset_sum _ fun i _ =>
    integrable_finset_sum _ fun j _ => (integrable_coord_mul i j).mul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => (integrable_coord_mul i j).mul_const _]
  have hterm : ∀ j : Fin d,
      ∫ z : Vec d, (z i * z j) * T (Pi.single i (1:ℝ)) (Pi.single j (1:ℝ)) ∂(stdGaussianVec d)
        = if j = i then T (Pi.single i (1:ℝ)) (Pi.single i (1:ℝ)) else 0 := by
    intro j
    rw [integral_mul_const]
    by_cases hji : j = i
    · subst hji
      have : ∫ z : Vec d, z j * z j ∂(stdGaussianVec d) = 1 := by
        simpa [sq] using integral_coord_sq (d := d) j
      rw [this]
      simp
    · rw [integral_coord_mul_of_ne (Ne.symm hji)]
      simp [hji]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq' Finset.univ i]
  simp

/-! ## The moment identity and the quantitative estimate -/

/-- The second differential as a bilinear form. -/
theorem iteratedFDeriv_two_eq_bilin {ψ : Vec d → ℝ} (x z : Vec d) :
    iteratedFDeriv ℝ 2 ψ x ![z, z] = (fderiv ℝ (fderiv ℝ ψ) x) z z := by
  rw [iteratedFDeriv_two_apply]
  simp


/-- A linear form is integrable against the standard Gaussian vector. -/
theorem integrable_clm_apply (L : Vec d →L[ℝ] ℝ) :
    Integrable (fun z : Vec d => L z) (stdGaussianVec d) := by
  have hsum : Integrable (fun z : Vec d => ∑ i, z i * L (Pi.single i (1:ℝ)))
      (stdGaussianVec d) :=
    integrable_finset_sum _ fun i _ => (integrable_coord i).mul_const _
  refine hsum.congr (Filter.Eventually.of_forall fun z => ?_)
  simpa [smul_eq_mul] using (clm_apply_eq_sum L z).symm

/-- A bilinear form on the diagonal is integrable against the standard Gaussian vector. -/
theorem integrable_clm_bilin_diag (T : Vec d →L[ℝ] (Vec d →L[ℝ] ℝ)) :
    Integrable (fun z : Vec d => T z z) (stdGaussianVec d) := by
  have hsum : Integrable (fun z : Vec d => ∑ i, ∑ j, (z i * z j) *
      T (Pi.single i (1:ℝ)) (Pi.single j (1:ℝ))) (stdGaussianVec d) :=
    integrable_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => (integrable_coord_mul i j).mul_const _
  exact hsum.congr (Filter.Eventually.of_forall fun z => (clm_bilin_diag_eq_sum T z).symm)

/-- A bounded continuous test function is integrable against the standard Gaussian vector. -/
theorem integrable_comp_gaussian {ψ : Vec d → ℝ} (hcont : Continuous ψ) {C : ℝ}
    (hC : ∀ y, ‖ψ y‖ ≤ C) (x : Vec d) (σ : ℝ) :
    Integrable (fun z : Vec d => ψ (x + σ • z)) (stdGaussianVec d) := by
  have hmeas : AEStronglyMeasurable (fun z : Vec d => ψ (x + σ • z)) (stdGaussianVec d) :=
    (hcont.comp (by fun_prop)).aestronglyMeasurable
  exact Integrable.mono' (integrable_const C) hmeas
    (Filter.Eventually.of_forall fun z => hC _)

/-- The Taylor remainder is integrable against the standard Gaussian vector. -/
theorem integrable_gaussianRemainder {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 2 ψ) {C : ℝ}
    (hC : ∀ y, ‖ψ y‖ ≤ C) (x : Vec d) (σ : ℝ) :
    Integrable (fun z : Vec d => ψ (x + σ • z) - ψ x - σ * fderiv ℝ ψ x z
      - σ ^ 2 / 2 * iteratedFDeriv ℝ 2 ψ x ![z, z]) (stdGaussianVec d) := by
  have h1 := integrable_comp_gaussian (hψ.continuous) hC x σ
  have h2 : Integrable (fun _ : Vec d => ψ x) (stdGaussianVec d) := integrable_const _
  have h3 : Integrable (fun z : Vec d => σ * fderiv ℝ ψ x z) (stdGaussianVec d) :=
    (integrable_clm_apply (fderiv ℝ ψ x)).const_mul σ
  have hquad : (fun z : Vec d => σ ^ 2 / 2 * iteratedFDeriv ℝ 2 ψ x ![z, z])
      = fun z : Vec d => σ ^ 2 / 2 * (fderiv ℝ (fderiv ℝ ψ) x) z z := by
    funext z
    rw [iteratedFDeriv_two_eq_bilin]
  have h4 : Integrable (fun z : Vec d => σ ^ 2 / 2 * iteratedFDeriv ℝ 2 ψ x ![z, z])
      (stdGaussianVec d) := by
    rw [hquad]
    exact (integrable_clm_bilin_diag (fderiv ℝ (fderiv ℝ ψ) x)).const_mul (σ ^ 2 / 2)
  have h12 : Integrable (fun z : Vec d => ψ (x + σ • z) - ψ x) (stdGaussianVec d) := h1.sub h2
  have h123 : Integrable (fun z : Vec d => ψ (x + σ • z) - ψ x - σ * fderiv ℝ ψ x z)
      (stdGaussianVec d) := h12.sub h3
  exact h123.sub h4

/-- **The moment identity.**  The first moment drops out and the second is the full Laplacian. -/
theorem integral_comp_gaussian_eq {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 2 ψ) {C : ℝ}
    (hC : ∀ y, ‖ψ y‖ ≤ C) (x : Vec d) (σ : ℝ) :
    ∫ z : Vec d, (ψ (x + σ • z) - ψ x - σ * fderiv ℝ ψ x z
        - σ ^ 2 / 2 * iteratedFDeriv ℝ 2 ψ x ![z, z]) ∂(stdGaussianVec d)
      = (∫ z : Vec d, ψ (x + σ • z) ∂(stdGaussianVec d)) - ψ x
        - σ ^ 2 / 2 *
          (∑ i, iteratedFDeriv ℝ 2 ψ x ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)]) := by
  have h1 := integrable_comp_gaussian (hψ.continuous) hC x σ
  have h2 : Integrable (fun _ : Vec d => ψ x) (stdGaussianVec d) := integrable_const _
  have h3 : Integrable (fun z : Vec d => σ * fderiv ℝ ψ x z) (stdGaussianVec d) :=
    (integrable_clm_apply (fderiv ℝ ψ x)).const_mul σ
  have hquad : (fun z : Vec d => σ ^ 2 / 2 * iteratedFDeriv ℝ 2 ψ x ![z, z])
      = fun z : Vec d => σ ^ 2 / 2 * (fderiv ℝ (fderiv ℝ ψ) x) z z := by
    funext z
    rw [iteratedFDeriv_two_eq_bilin]
  have h4 : Integrable (fun z : Vec d => σ ^ 2 / 2 * iteratedFDeriv ℝ 2 ψ x ![z, z])
      (stdGaussianVec d) := by
    rw [hquad]
    exact (integrable_clm_bilin_diag (fderiv ℝ (fderiv ℝ ψ) x)).const_mul (σ ^ 2 / 2)
  have h12 : Integrable (fun z : Vec d => ψ (x + σ • z) - ψ x) (stdGaussianVec d) := h1.sub h2
  have h123 : Integrable (fun z : Vec d => ψ (x + σ • z) - ψ x - σ * fderiv ℝ ψ x z)
      (stdGaussianVec d) := h12.sub h3
  rw [integral_sub h123 h4, integral_sub h12 h3, integral_sub h1 h2]
  have e2 : ∫ _ : Vec d, ψ x ∂(stdGaussianVec d) = ψ x := by simp
  have e3 : ∫ z : Vec d, σ * fderiv ℝ ψ x z ∂(stdGaussianVec d) = 0 := by
    rw [integral_const_mul, integral_clm_apply, mul_zero]
  have e4 : ∫ z : Vec d, σ ^ 2 / 2 * iteratedFDeriv ℝ 2 ψ x ![z, z] ∂(stdGaussianVec d)
      = σ ^ 2 / 2 *
        (∑ i, iteratedFDeriv ℝ 2 ψ x ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)]) := by
    rw [hquad, integral_const_mul, integral_clm_bilin_diag]
    congr 1
    exact Finset.sum_congr rfl fun i _ => (iteratedFDeriv_two_eq_bilin x (Pi.single i (1:ℝ))).symm
  rw [e2, e3, e4]
  ring

/-- **The quantitative estimate, uniform in the centre `x`.** -/
theorem abs_gaussianQuotient_sub_laplacian_le {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {C K eps delta σ : ℝ} (hC : ∀ y, ‖ψ y‖ ≤ C)
    (hK : 0 ≤ K) (heps : 0 ≤ eps) (hdelta : 0 < delta) (hσ : 0 < σ)
    (hbound : ∀ y y' : Vec d, ‖iteratedFDeriv ℝ 2 ψ y - iteratedFDeriv ℝ 2 ψ y'‖ ≤ K)
    (hmod : ∀ y y' : Vec d, ‖y - y'‖ ≤ delta →
      ‖iteratedFDeriv ℝ 2 ψ y - iteratedFDeriv ℝ 2 ψ y'‖ ≤ eps)
    (x : Vec d) :
    |2 * ((∫ z : Vec d, ψ (x + σ • z) ∂(stdGaussianVec d)) - ψ x) / σ ^ 2
        - ∑ i, iteratedFDeriv ℝ 2 ψ x ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)]|
      ≤ 2 * eps * (d : ℝ) + 2 * K * ((d : ℝ) * ((d : ℝ) + 2)) * σ ^ 2 / delta ^ 2 := by
  have hσ2 : (0:ℝ) < σ ^ 2 := by positivity
  set Lap : ℝ := ∑ i, iteratedFDeriv ℝ 2 ψ x ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)] with hLap
  set I : ℝ := ∫ z : Vec d, ψ (x + σ • z) ∂(stdGaussianVec d) with hI
  set Rem : Vec d → ℝ := fun z => ψ (x + σ • z) - ψ x - σ * fderiv ℝ ψ x z
    - σ ^ 2 / 2 * iteratedFDeriv ℝ 2 ψ x ![z, z] with hRem
  have hid : ∫ z : Vec d, Rem z ∂(stdGaussianVec d) = I - ψ x - σ ^ 2 / 2 * Lap :=
    integral_comp_gaussian_eq hψ hC x σ
  have hRint : Integrable Rem (stdGaussianVec d) := integrable_gaussianRemainder hψ hC x σ
  set dom : Vec d → ℝ := fun z => (eps * σ ^ 2) * vecNormSq z
    + (K * σ ^ 4 / delta ^ 2) * vecNormSq z ^ 2 with hdom
  have hdomint : Integrable dom (stdGaussianVec d) :=
    (integrable_vecNormSq.const_mul _).add (integrable_vecNormSq_sq.const_mul _)
  have hptwise : ∀ z : Vec d, |Rem z| ≤ dom z := by
    intro z
    refine (abs_gaussian_remainder_le hψ hK heps hdelta hσ hbound hmod x z).trans (le_of_eq ?_)
    rw [hdom]
    ring
  have habs : |∫ z : Vec d, Rem z ∂(stdGaussianVec d)| ≤ ∫ z : Vec d, dom z ∂(stdGaussianVec d) :=
    le_trans (abs_integral_le_integral_abs)
      (integral_mono hRint.abs hdomint hptwise)
  have hdomval : ∫ z : Vec d, dom z ∂(stdGaussianVec d)
      = (eps * σ ^ 2) * (d : ℝ) + (K * σ ^ 4 / delta ^ 2) * ((d : ℝ) * ((d : ℝ) + 2)) := by
    rw [hdom, integral_add (integrable_vecNormSq.const_mul _)
      (integrable_vecNormSq_sq.const_mul _), integral_const_mul, integral_const_mul,
      integral_vecNormSq, integral_vecNormSq_sq]
  have hquot : 2 * (I - ψ x) / σ ^ 2 - Lap
      = 2 / σ ^ 2 * (∫ z : Vec d, Rem z ∂(stdGaussianVec d)) := by
    rw [hid]
    field_simp
  rw [hquot, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / σ ^ 2)]
  have hstep : 2 / σ ^ 2 * |∫ z : Vec d, Rem z ∂(stdGaussianVec d)|
      ≤ 2 / σ ^ 2 * ((eps * σ ^ 2) * (d : ℝ)
        + (K * σ ^ 4 / delta ^ 2) * ((d : ℝ) * ((d : ℝ) + 2))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hdomval]
    exact habs
  refine hstep.trans (le_of_eq ?_)
  field_simp



theorem tendstoUniformly_gaussian_differenceQuotient {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hsupp : HasCompactSupport ψ) :
    TendstoUniformly
      (fun σ : ℝ => fun x : Vec d =>
        2 * ((∫ z : Vec d, ψ (x + σ • z) ∂(stdGaussianVec d)) - ψ x) / σ ^ 2)
      (fun x => ∑ i, iteratedFDeriv ℝ 2 ψ x ![Pi.single i (1:ℝ), Pi.single i (1:ℝ)])
      (nhdsWithin 0 (Set.Ioi (0:ℝ))) := by
  obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hsupp
  have hD2cont : Continuous (iteratedFDeriv ℝ 2 ψ) := hψ.continuous_iteratedFDeriv le_rfl
  obtain ⟨C2, hC2⟩ := hD2cont.bounded_above_of_compact_support (hsupp.iteratedFDeriv 2)
  have hC2nn : 0 ≤ C2 := le_trans (norm_nonneg _) (hC2 0)
  set K : ℝ := 2 * C2 with hKdef
  have hK : 0 ≤ K := by positivity
  have hbound : ∀ y y' : Vec d,
      ‖iteratedFDeriv ℝ 2 ψ y - iteratedFDeriv ℝ 2 ψ y'‖ ≤ K := by
    intro y y'
    refine (norm_sub_le _ _).trans ?_
    rw [hKdef]
    linarith [hC2 y, hC2 y']
  have hUC : UniformContinuous (iteratedFDeriv ℝ 2 ψ) :=
    (hsupp.iteratedFDeriv 2).uniformContinuous_of_continuous hD2cont
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  set eps : ℝ := ε / (4 * ((d : ℝ) + 1)) with hepsdef
  have hdpos : (0:ℝ) < (d : ℝ) + 1 := by positivity
  have heps : 0 < eps := by rw [hepsdef]; positivity
  obtain ⟨delta0, hdelta0, hdelta0'⟩ := Metric.uniformContinuous_iff.mp hUC eps heps
  set delta : ℝ := delta0 / 2 with hdeltadef
  have hdelta : 0 < delta := by rw [hdeltadef]; linarith
  have hmod : ∀ y y' : Vec d, ‖y - y'‖ ≤ delta →
      ‖iteratedFDeriv ℝ 2 ψ y - iteratedFDeriv ℝ 2 ψ y'‖ ≤ eps := by
    intro y y' hyy
    have hd : dist y y' < delta0 := by
      rw [dist_eq_norm]
      rw [hdeltadef] at hyy
      linarith
    have := hdelta0' hd
    rw [dist_eq_norm] at this
    exact this.le
  set A : ℝ := 2 * K * ((d : ℝ) * ((d : ℝ) + 2)) / delta ^ 2 with hAdef
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  set sigma0 : ℝ := Real.sqrt (ε / (2 * (A + 1))) with hsigma0
  have hsigma0pos : 0 < sigma0 := by
    rw [hsigma0]
    exact Real.sqrt_pos.mpr (by positivity)
  have hmem : Set.Ioo (0:ℝ) sigma0 ∈ nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ)) :=
    Ioo_mem_nhdsGT hsigma0pos
  refine Filter.eventually_of_mem hmem ?_
  intro σ hσmem x
  obtain ⟨hσ, hσlt⟩ := hσmem
  have hmain := abs_gaussianQuotient_sub_laplacian_le hψ hC hK heps.le hdelta hσ hbound hmod x
  rw [Real.dist_eq, abs_sub_comm]
  refine lt_of_le_of_lt hmain ?_
  have hterm1 : 2 * eps * (d : ℝ) ≤ ε / 2 := by
    have hkey : ε / 2 - 2 * (ε / (4 * ((d : ℝ) + 1))) * (d : ℝ)
        = ε / (2 * ((d : ℝ) + 1)) := by
      field_simp
      ring
    have hnn : (0:ℝ) ≤ ε / (2 * ((d : ℝ) + 1)) := by positivity
    rw [hepsdef]
    linarith [hkey, hnn]
  have hσ2 : σ ^ 2 < ε / (2 * (A + 1)) := by
    have hsq : σ ^ 2 < sigma0 ^ 2 := by nlinarith
    rw [hsigma0, Real.sq_sqrt (by positivity)] at hsq
    exact hsq
  have hterm2 : 2 * K * ((d : ℝ) * ((d : ℝ) + 2)) * σ ^ 2 / delta ^ 2 < ε / 2 := by
    have hrw : 2 * K * ((d : ℝ) * ((d : ℝ) + 2)) * σ ^ 2 / delta ^ 2 = A * σ ^ 2 := by
      rw [hAdef]; ring
    rw [hrw]
    have h1 : A * σ ^ 2 ≤ (A + 1) * σ ^ 2 := by nlinarith [sq_nonneg σ]
    have h2 : (A + 1) * σ ^ 2 < (A + 1) * (ε / (2 * (A + 1))) :=
      mul_lt_mul_of_pos_left hσ2 (by positivity)
    have h3 : (A + 1) * (ε / (2 * (A + 1))) = ε / 2 := by
      field_simp
    linarith
  linarith

end SubdiffusiveProcess.Probability.Diffusion
