module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationRegularization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationGenerator
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationComparison

@[expose] public section

/-! The quadratic semigroup estimate from `mfd:in-deterministic` and `s.tightness`,
proved from the weak resolvent by bounded concave regularization. -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Homogenization hiding Vec contDiff_vecNormSq
open Filter Topology MeasureTheory MarkovProcess MarkovProcess.Semigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ZeroAtInfty

theorem coeffFluxDiv_regularizedQuadratic {d : ℕ} {c rho : Vec d → ℝ}
    (hc : Differentiable ℝ c) {eps : ℝ} (heps : 0 < eps) (x : Vec d) :
    coeffFluxDiv c (fun y ↦ (1 + vecNormSq y) / (1 + eps * (1 + vecNormSq y))) x / rho x =
      (coeffFluxDiv c (fun y ↦ 1 + euclideanNorm y ^ 2) x / rho x) *
        ((1 + eps * (1 + vecNormSq x))⁻¹) ^ 2 -
      8 * eps * vecNormSq x * (c x / rho x) * ((1 + eps * (1 + vecNormSq x))⁻¹) ^ 3 := by
  rw [coeffFluxDiv_compVecNormSq hc
    (fun _ hq ↦ hasDerivAt_regularizedQuadratic heps hq)
    (fun _ hq ↦ hasDerivAt_regularizedQuadraticD heps hq) x,
    coeffFluxDiv_one_add_norm_sq hc x]
  exact regularized_flux_algebra _ _ _ _ _ _ _

/-- The bounded concave regularization is a constant plus a generator-domain
function, with a uniform Lyapunov drift bound. -/
theorem exists_regularizedQuadratic_generator {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : IsWeakEllipticResolvent c rho D) (hcnn : ∀ x, 0 ≤ c x)
    {C Bcap eps : ℝ} (hC : 0 ≤ C) (hBcap : 0 ≤ Bcap) (heps : 0 < eps)
    (hquad : ∀ x, |coeffFluxDiv c (fun y ↦ 1 + euclideanNorm y ^ 2) x / rho x| ≤
      C * (1 + vecNormSq x))
    (hcap : ∀ x, c x / rho x ≤ Bcap * (1 + vecNormSq x)) :
    let S := (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense).c0Semigroup
    ∃ f : S.generatorDomain,
      (∀ x, eps⁻¹ + (f : C₀(Vec d, ℝ)) x =
        (1 + vecNormSq x) / (1 + eps * (1 + vecNormSq x))) ∧
      (∀ x, S.generator f x ≤ C * (eps⁻¹ + (f : C₀(Vec d, ℝ)) x)) := by
  let w : C₀(Vec d, ℝ) := -regularizedComplementC0 eps heps
  have hw : ContDiff ℝ (⊤ : ℕ∞) (w : Vec d → ℝ) :=
    (contDiff_regularizedQuadraticComplement heps).neg
  have hJ : (fun y ↦ eps⁻¹ + w y) =
      (fun y : Vec d ↦ (1 + vecNormSq y) / (1 + eps * (1 + vecNormSq y))) := by
    funext y
    exact (regularizedQuadratic_eq_const_sub heps (vecNormSq_nonneg y)).symm
  have hflux (x : Vec d) : coeffFluxDiv c w x / rho x =
      (coeffFluxDiv c (fun y ↦ 1 + euclideanNorm y ^ 2) x / rho x) *
        ((1 + eps * (1 + vecNormSq x))⁻¹) ^ 2 -
      8 * eps * vecNormSq x * (c x / rho x) * ((1 + eps * (1 + vecNormSq x))⁻¹) ^ 3 := by
    rw [← coeffFluxDiv_const_add c w eps⁻¹ x, hJ]
    exact coeffFluxDiv_regularizedQuadratic (hc.differentiable (by norm_num)) heps x
  let v : Vec d → ℝ := fun x ↦ coeffFluxDiv c w x / rho x
  have hv : Continuous v := (continuous_coeffFluxDiv hc hw).div hrho
    (fun x ↦ (B.weight_pos x).ne')
  have hvbound : ∀ x, ‖v x‖ ≤ ((C + 8 * Bcap) * (eps⁻¹) ^ 2) *
      radialBarrierC0 2 (by norm_num) x := by
    intro x
    change |coeffFluxDiv c w x / rho x| ≤ _ * radialBarrier 1 2 x
    rw [hflux, radialBarrier_two]
    exact norm_regularized_flux_decay heps (vecNormSq_nonneg x)
      (div_nonneg (hcnn x) (B.weight_pos x).le) hC hBcap (hquad x) (hcap x)
  let g := dominatedC0 v hv (radialBarrierC0 2 (by norm_num))
    ((C + 8 * Bcap) * (eps⁻¹) ^ 2) hvbound
  obtain ⟨hm, hgen⟩ := exists_generator_of_smooth_c0 B hc D hdense hD w g hw (fun _ ↦ rfl)
  refine ⟨⟨w, hm⟩, fun x ↦ congrFun hJ x, ?_⟩
  intro x
  rw [hgen]
  change coeffFluxDiv c w x / rho x ≤ C * (eps⁻¹ + w x)
  rw [hflux, congrFun hJ x]
  exact regularized_drift_le heps (vecNormSq_nonneg x)
    (div_nonneg (hcnn x) (B.weight_pos x).le) hC
    ((le_abs_self _).trans (hquad x))

/-- The quadratic Lyapunov estimate at a deterministic time, derived through
bounded generator-domain regularizations and Fatou's lemma. -/
theorem lintegral_quadratic_le_exp {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : IsWeakEllipticResolvent c rho D) (hcnn : ∀ x, 0 ≤ c x)
    (hP : (D.fellerKernelSemigroup hdense).IsConservative)
    {C Bcap : ℝ} (hC : 0 ≤ C) (hBcap : 0 ≤ Bcap)
    (hquad : ∀ x, |coeffFluxDiv c (fun y ↦ 1 + euclideanNorm y ^ 2) x / rho x| ≤
      C * (1 + vecNormSq x))
    (hcap : ∀ x, c x / rho x ≤ Bcap * (1 + vecNormSq x))
    (t : NNReal) (x : Vec d) :
    (∫⁻ y, ENNReal.ofReal (1 + vecNormSq y) ∂D.fellerKernelSemigroup hdense t x) ≤
      ENNReal.ofReal (Real.exp (C * (t : ℝ)) * (1 + vecNormSq x)) := by
  let P := D.fellerKernelSemigroup hdense
  let hF := D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  let mu := P t x
  let : IsProbabilityMeasure mu := ⟨hP t x⟩
  let eps : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have heps : ∀ n, 0 < eps n := fun n ↦ (reciprocalNatSucc_pos_le_one n).1
  have hex := fun n ↦ exists_regularizedQuadratic_generator B hc hrho D hdense hD hcnn
    hC hBcap (heps n) hquad hcap
  choose f hf hLf using hex
  let v : ℕ → Vec d → ℝ := fun n y ↦
    (1 + vecNormSq y) / (1 + eps n * (1 + vecNormSq y))
  have hi : ∀ n, Integrable (v n) mu := by
    intro n
    have h : Integrable (fun y ↦ (eps n)⁻¹ + (f n : C₀(Vec d, ℝ)) y) mu :=
      (integrable_const _).add ((f n : C₀(Vec d, ℝ)).toBCF.integrable mu)
    exact h.congr (Eventually.of_forall (hf n))
  apply lintegral_ofReal_le_of_approximation mu v _ _ hi
  · intro n y
    exact (regularizedQuadratic_nonneg_le (heps n) (vecNormSq_nonneg y)).1
  · intro y
    exact tendsto_regularizedQuadratic (vecNormSq y)
  · intro n
    have hcomp := affine_c0Semigroup_le_exp P hP hF (f n) (eps n)⁻¹ C (hLf n) t x
    have hI : (∫ y, v n y ∂mu) = (eps n)⁻¹ + hF.c0Semigroup t (f n) x := by
      calc (∫ y, v n y ∂mu)
          = ∫ y, (eps n)⁻¹ + (f n : C₀(Vec d, ℝ)) y ∂mu :=
            integral_congr_ae (Eventually.of_forall fun y ↦ (hf n y).symm)
        _ = (eps n)⁻¹ + ∫ y, (f n : C₀(Vec d, ℝ)) y ∂mu := by
          simpa only [one_mul] using integral_affine_c0 mu (f n) (eps n)⁻¹ 1
        _ = _ := rfl
    rw [hI]
    refine hcomp.trans ?_
    rw [hf n x]
    exact mul_le_mul_of_nonneg_left
      (regularizedQuadratic_nonneg_le (heps n) (vecNormSq_nonneg x)).2
      (Real.exp_pos _).le

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
