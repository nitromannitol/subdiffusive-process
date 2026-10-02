import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveSolver
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDatumFields




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveH1Hilbert
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDatumFields
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open MarkovProcess.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.Packet455

variable {d : ℕ} {U : Set (Vec d)} {c rho : Vec d → ℝ} {lam Lam : ℝ}

/-- The existing H1 graph realization is linear on actual `H1Function`s. -/
def h1GraphLinear : H1Function U →ₗ[ℝ] Space (W := U) where
  toFun := ofH1Function
  map_add' u v := by
    apply Subtype.ext
    change (ambientEquiv (W := U)).symm
      ((u + v).toScalarL2, (u + v).gradToHilbertVectorL2) = _
    rw [H1Function.toScalarL2_add, H1Function.gradToHilbertVectorL2_add]
    exact (ambientEquiv (W := U)).symm.map_add
      (u.toScalarL2, u.gradToHilbertVectorL2) (v.toScalarL2, v.gradToHilbertVectorL2)
  map_smul' r u := by
    apply Subtype.ext
    change (ambientEquiv (W := U)).symm
      ((r • u).toScalarL2, (r • u).gradToHilbertVectorL2) = _
    rw [H1Function.toScalarL2_smul, H1Function.gradToHilbertVectorL2_smul]
    exact (ambientEquiv (W := U)).symm.map_smul r (u.toScalarL2, u.gradToHilbertVectorL2)

/-- The common scalar Dirichlet form, bilinear on `H1Function U`. -/
def dirichletBilin (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c)) :
    H1Function U →ₗ[ℝ] H1Function U →ₗ[ℝ] ℝ where
  toFun u := ((coeffGradientBilin hEll (h1GraphLinear u)).toLinearMap).comp h1GraphLinear
  map_add' u v := by
    ext w
    simp only [map_add, ContinuousLinearMap.add_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, LinearMap.add_apply]
  map_smul' r u := by
    ext w
    simp only [map_smul, ContinuousLinearMap.smul_apply, LinearMap.comp_apply,
      ContinuousLinearMap.coe_coe, LinearMap.smul_apply, RingHom.id_apply]

/-- The bilinear object has exactly the printed integral as its value. -/
theorem dirichletBilin_apply
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c)) (u v : H1Function U) :
    dirichletBilin hEll u v = ∫ x in U, c x * vecDot (u.grad x) (v.grad x) := by
  simpa only [dirichletBilin, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, h1GraphLinear, vecDot_smul_left] using
      coeffGradientBilin_apply_ofH1Function hEll u v

/-- The diagonal recovers the existing source vocabulary without redefining `energy`. -/
theorem dirichletBilin_self
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c)) (u : H1Function U) :
    dirichletBilin hEll u u = energy c U u := dirichletBilin_apply hEll u u

/-- Scalar coefficients give a symmetric form. -/
theorem dirichletBilin_symm
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c)) (u v : H1Function U) :
    dirichletBilin hEll u v = dirichletBilin hEll v u := by
  simp only [dirichletBilin_apply]
  congr 1
  funext x
  rw [vecDot_comm]

/-- The normalized weak resolvent identity expressed through the bilinear API. -/
theorem resolvent_form_identity
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c))
    {s : ℝ} (hs : 0 < s) {f : Vec d → ℝ} {u : H1Function U}
    (hu : IsMassiveWeakSolutionOn c rho s⁻¹ U u (fun x => s⁻¹ * f x))
    (v : H10Function U) :
    (∫ x in U, rho x * u.toFun x * v.toH1Function.toFun x) +
        s * dirichletBilin hEll u v.toH1Function =
      ∫ x in U, rho x * f x * v.toH1Function.toFun x := by
  have h := hu v
  simp only [vecDot_smul_left] at h
  have heq : (∫ x in U, rho x * (s⁻¹ * f x) * v.toH1Function.toFun x) =
      s⁻¹ * ∫ x in U, rho x * f x * v.toH1Function.toFun x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [heq] at h
  rw [dirichletBilin_apply]
  have h' := congrArg (fun a : ℝ => s * a) h
  field_simp at h'
  nlinarith [mul_inv_cancel₀ hs.ne']

/-- `LocalDiffusion` already supplies the form identity for every normalized resolvent. -/
theorem exists_killedResolvent_form_identity {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c))
    {s : ℝ} (hs : 0 < s) (f : Vec d → ℝ)
    (hf : MemLp f 2 ((weightedMeasure rho).restrict U)) :
    ∃ u : H10Function U,
      (∀ᵐ x ∂(weightedMeasure rho).restrict U,
        u.toH1Function.toFun x = killedResolvent law U s f x) ∧
      ∀ v : H10Function U,
        (∫ x in U, rho x * u.toH1Function.toFun x * v.toH1Function.toFun x) +
            s * dirichletBilin hEll u.toH1Function v.toH1Function =
          ∫ x in U, rho x * f x * v.toH1Function.toFun x := by
  obtain ⟨u, hueq, hu⟩ := hD.2.2 U hU hUb s hs f hf
  exact ⟨u, hueq, fun v => resolvent_form_identity hEll hs hu v⟩

section Generator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative pairing has the positive-form sign `-generator`. -/
theorem tendsto_generator_pairing (P : StronglyContinuousContractionSemigroup E)
    (u : P.generatorDomain) (v : E) :
    Tendsto (fun t : NNReal => (t : ℝ)⁻¹ * ⟪(u : E) - P t u, v⟫)
      (𝓝[>] 0) (𝓝 (-⟪P.generator u, v⟫)) := by
  have h := (((P.tendsto_generator u).inner (𝕜 := ℝ) (tendsto_const_nhds (x := v))).neg)
  convert h using 1
  funext t
  simp only [StronglyContinuousContractionSemigroup.differenceQuotient,
    real_inner_smul_left, inner_sub_left]
  ring

/-- Identifying the generator pairing with the form gives its derivative characterization. -/
theorem tendsto_form_pairing (P : StronglyContinuousContractionSemigroup E)
    (u : P.generatorDomain) (v : E) (B : ℝ) (hform : B = -⟪P.generator u, v⟫) :
    Tendsto (fun t : NNReal => (t : ℝ)⁻¹ * ⟪(u : E) - P t u, v⟫)
      (𝓝[>] 0) (𝓝 B) := by
  rw [hform]
  exact tendsto_generator_pairing P u v

end Generator

/-- Every vector in the actual killed generator domain has a zero-trace Sobolev
representative, and its generator is the operator associated with the common form.
The test vector `V` records the weighted L2 realization of the H10 test function. -/
theorem exists_generator_form_identity {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c))
    (f : (killedSCCS hD hD.1 hU hUb).generatorDomain) :
    ∃ u : H10Function U,
      ((f : Lp ℝ 2 ((weightedMeasure rho).restrict U)) : Vec d → ℝ)
        =ᵐ[(weightedMeasure rho).restrict U] u.toH1Function.toFun ∧
      ∀ (v : H10Function U) (V : Lp ℝ 2 ((weightedMeasure rho).restrict U)),
        (V : Vec d → ℝ) =ᵐ[(weightedMeasure rho).restrict U] v.toH1Function.toFun →
        dirichletBilin hEll u.toH1Function v.toH1Function =
          -⟪(killedSCCS hD hD.1 hU hUb).generator f, V⟫ := by
  let P := killedSCCS hD hD.1 hU hUb
  let F : Lp ℝ 2 ((weightedMeasure rho).restrict U) := (f : Lp ℝ 2 _) - P.generator f
  have hres : P.resolvent ⟨1, by norm_num⟩ = killedResolventLp hD hU hUb 1 (by norm_num) := by
    simpa [P] using (resolvent_killedSCCS (hD := hD) (hSM := hD.1)
      (hU := hU) (hUb := hUb) (s := 1) (hs := by norm_num))
  have hRF : killedResolventLp hD hU hUb 1 (by norm_num) F = (f : Lp ℝ 2 _) := by
    rw [← hres]
    simpa [F] using P.resolvent_smul_sub_generator ⟨1, by norm_num⟩ f
  obtain ⟨u, hueq, hu⟩ := hD.2.2 U hU hUb 1 (by norm_num) (F : Vec d → ℝ) (Lp.memLp F)
  have hfu : ((f : Lp ℝ 2 ((weightedMeasure rho).restrict U)) : Vec d → ℝ)
      =ᵐ[(weightedMeasure rho).restrict U] u.toH1Function.toFun := by
    have hraw := killedResolventLp_coeFn (hD := hD) (hU := hU) (hUb := hUb)
      (s := 1) (hs := by norm_num) F
    rw [hRF] at hraw
    filter_upwards [hraw, hueq] with x hx hux
    exact hx.trans hux.symm
  refine ⟨u, hfu, ?_⟩
  intro v V hV
  have hr : CoefficientOn U rho := coefficientOn_mono subset_closure
    (hD.2.1 (closure U) hUb.isCompact_closure).2
  have hac := volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU.measurableSet hr
  have hpair : ⟪(f : Lp ℝ 2 ((weightedMeasure rho).restrict U)), V⟫ =
      ∫ x in U, rho x * u.toH1Function.toFun x * v.toH1Function.toFun x := by
    rw [inner_eq_integral, integral_weightedMeasure_restrict_eq hU.measurableSet rho _ hr]
    apply integral_congr_ae
    filter_upwards [hfu.filter_mono hac.ae_le, hV.filter_mono hac.ae_le] with x hux hvx
    rw [hux, hvx]
    ring
  have hpairF : ⟪F, V⟫ =
      ∫ x in U, rho x * F x * v.toH1Function.toFun x := by
    rw [inner_eq_integral, integral_weightedMeasure_restrict_eq hU.measurableSet rho _ hr]
    apply integral_congr_ae
    filter_upwards [hV.filter_mono hac.ae_le] with x hvx
    rw [hvx]
    ring
  have hweak := hu v
  simp only [inv_one, one_mul, vecDot_smul_left] at hweak
  rw [← dirichletBilin_apply hEll, ← hpair, ← hpairF] at hweak
  change ⟪(f : Lp ℝ 2 _), V⟫ + dirichletBilin hEll u.toH1Function v.toH1Function =
    ⟪(f : Lp ℝ 2 _) - P.generator f, V⟫ at hweak
  rw [inner_sub_left] at hweak
  change dirichletBilin hEll u.toH1Function v.toH1Function = -⟪P.generator f, V⟫
  linarith

/-- The positive-time pairing derivative, for the actual form and killed semigroup. -/
theorem exists_killed_form_derivative {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c))
    (f : (killedSCCS hD hD.1 hU hUb).generatorDomain) :
    ∃ u : H10Function U,
      ((f : Lp ℝ 2 ((weightedMeasure rho).restrict U)) : Vec d → ℝ)
        =ᵐ[(weightedMeasure rho).restrict U] u.toH1Function.toFun ∧
      ∀ (v : H10Function U) (V : Lp ℝ 2 ((weightedMeasure rho).restrict U)),
        (V : Vec d → ℝ) =ᵐ[(weightedMeasure rho).restrict U] v.toH1Function.toFun →
        Tendsto (fun t : NNReal => (t : ℝ)⁻¹ *
          ⟪(f : Lp ℝ 2 _) - (killedSCCS hD hD.1 hU hUb) t f, V⟫)
          (𝓝[>] 0) (𝓝 (dirichletBilin hEll u.toH1Function v.toH1Function)) := by
  obtain ⟨u, hu, hform⟩ := exists_generator_form_identity hD hU hUb hEll f
  exact ⟨u, hu, fun v V hV => tendsto_form_pairing (killedSCCS hD hD.1 hU hUb)
    f V _ (hform v V hV)⟩

/-- The pointwise perturbation inequality uses `c ≤ rho` and `|grad psi|² ≤ 1`.
No upper ellipticity constant enters the exponential rate. -/
theorem davies_integrand_lower {a r g2 u2 q2 lambda : ℝ}
    (ha : 0 ≤ a) (har : a ≤ r) (hu : 0 ≤ u2) (hq : q2 ≤ 1) :
    a * (g2 - lambda ^ 2 * u2 * q2) ≥ a * g2 - lambda ^ 2 * r * u2 := by
  have h := mul_le_mul_of_nonneg_left hq ha
  have h' := mul_le_mul_of_nonneg_left (h.trans (by simpa using har))
    (mul_nonneg (sq_nonneg lambda) hu)
  nlinarith

/-- Optimization of the conjugation bound gives the printed denominator `4t`. -/
theorem davies_exponent_at_optimum {t D : ℝ} (ht : 0 < t) :
    -(D / (2 * t)) * D + (D / (2 * t)) ^ 2 * t = -(D ^ 2 / (4 * t)) := by
  field_simp
  ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.Packet455
