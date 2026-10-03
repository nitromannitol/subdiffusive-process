module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszExtension
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

/-- The integral of the pointwise squared norm of an `L²` representative is
the squared norm of its `Lp` class. -/
theorem integral_norm_sq_coe_eq_norm_sq
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (h : Lp ℂ 2 mu) :
    ∫ x, ‖h x‖ ^ 2 ∂mu = ‖h‖ ^ 2 := by
  have hint : Integrable (fun x ↦ inner ℂ (h x) (h x)) mu :=
    L2.integrable_inner h h
  calc
    ∫ x, ‖h x‖ ^ 2 ∂mu = ∫ x, (inner ℂ (h x) (h x)).re ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (h x)).symm
    _ = (∫ x, inner ℂ (h x) (h x) ∂mu).re := integral_re hint
    _ = (inner ℂ h h).re := congrArg Complex.re (L2.inner_def h h).symm
    _ = ‖h‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) h

/-- Absorbing a strictly positive density into the Riesz representative turns
the inverse-density energy back into the Hilbert norm. -/
theorem integral_inv_density_mul_norm_sq_representative_eq_norm_sq
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (rho : X → NNReal) (hrho : Measurable rho) (hrhoPos : ∀ x, 0 < rho x)
    (h : Lp ℂ 2 (mu.withDensity fun x ↦ rho x)) :
    ∫ x, (rho x : ℝ)⁻¹ * ‖conj (h x) * (rho x : ℂ)‖ ^ 2 ∂mu = ‖h‖ ^ 2 := by
  calc
    ∫ x, (rho x : ℝ)⁻¹ * ‖conj (h x) * (rho x : ℂ)‖ ^ 2 ∂mu =
        ∫ x, (rho x : ℝ) * ‖h x‖ ^ 2 ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      have hnormRho : ‖(rho x : ℂ)‖ = (rho x : ℝ) := by simp
      rw [norm_mul, RCLike.norm_conj, hnormRho, mul_pow]
      have hrhoNe : (rho x : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr (hrhoPos x).ne'
      field_simp
    _ = ∫ x, ‖h x‖ ^ 2 ∂(mu.withDensity fun x ↦ rho x) := by
      rw [integral_withDensity_eq_integral_smul hrho]
      apply integral_congr_ae
      filter_upwards with x
      rfl
    _ = ‖h‖ ^ 2 := integral_norm_sq_coe_eq_norm_sq _ h

/-- The inverse-density energy of the density-absorbed representative is
integrable. -/
theorem integrable_inv_density_mul_norm_sq_representative
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (rho : X → NNReal) (hrho : Measurable rho) (hrhoPos : ∀ x, 0 < rho x)
    (h : Lp ℂ 2 (mu.withDensity fun x ↦ rho x)) :
    Integrable (fun x ↦
      (rho x : ℝ)⁻¹ * ‖conj (h x) * (rho x : ℂ)‖ ^ 2) mu := by
  have hsquare : Integrable (fun x ↦ ‖h x‖ ^ 2)
      (mu.withDensity fun x ↦ rho x) :=
    (Lp.memLp h).integrable_norm_pow (by norm_num)
  have hbase : Integrable (fun x ↦ (rho x : ℝ) • ‖h x‖ ^ 2) mu :=
    (integrable_withDensity_iff_integrable_smul hrho).mp hsquare
  apply hbase.congr
  filter_upwards with x
  have hnormRho : ‖(rho x : ℂ)‖ = (rho x : ℝ) := by simp
  rw [norm_mul, RCLike.norm_conj, hnormRho, mul_pow]
  rw [smul_eq_mul]
  have hrhoNe : (rho x : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr (hrhoPos x).ne'
  field_simp

/-- The linear map from an algebraic test space into its weighted `L²`
classes. -/
def fluxRowWeightedTestToLp
    {X S : Type*} [MeasurableSpace X] [AddCommGroup S] [Module ℂ S]
    (mu : Measure X) (rho : X → NNReal) (test : S →ₗ[ℂ] X → ℂ)
    (htest : ∀ s, MemLp (test s) 2 (mu.withDensity fun x ↦ rho x)) :
    S →ₗ[ℂ] Lp ℂ 2 (mu.withDensity fun x ↦ rho x) :=
  { toFun := fun s ↦ (htest s).toLp (test s)
    map_add' := by
      intro x y
      rw [← (htest x).toLp_add (htest y)]
      exact (htest (x + y)).toLp_congr ((htest x).add (htest y)) <|
        Filter.Eventually.of_forall fun z ↦ congrFun (map_add test x y) z
    map_smul' := by
      intro c x
      change (htest (c • x)).toLp (test (c • x)) =
        c • (htest x).toLp (test x)
      rw [← (htest x).toLp_const_smul c]
      exact (htest (c • x)).toLp_congr ((htest x).const_smul c) <|
        Filter.Eventually.of_forall fun z ↦ congrFun (map_smul test c x) z }

/-- A functional bounded by a weighted `L²` test norm has a base-measure
representative.  The returned function is the conjugate of the Riesz vector
times the density. -/
theorem exists_weighted_riesz_density_representative
    {X S : Type*} [MeasurableSpace X] [AddCommGroup S] [Module ℂ S]
    (mu : Measure X) (rho : X → NNReal) (hrho : Measurable rho)
    (test : S →ₗ[ℂ] X → ℂ)
    (htest : ∀ s, MemLp (test s) 2 (mu.withDensity fun x ↦ rho x))
    (L : S →ₗ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s, ‖L s‖ ≤
      C * ‖fluxRowWeightedTestToLp mu rho test htest s‖) :
    ∃ h : Lp ℂ 2 (mu.withDensity fun x ↦ rho x), ‖h‖ ≤ C ∧
      let representative : X → ℂ := fun x ↦ conj (h x) * (rho x : ℂ)
      ∀ s, Integrable (fun x ↦ representative x * test s x) mu ∧
        L s = ∫ x, representative x * test s x ∂mu := by
  obtain ⟨h, hh, hrepr⟩ := exists_riesz_representative_of_norm_le
    (fluxRowWeightedTestToLp mu rho test htest) L C hC hbound
  refine ⟨h, hh, ?_⟩
  dsimp only
  intro s
  let T := fluxRowWeightedTestToLp mu rho test htest
  have hinner : Integrable (fun x ↦ inner ℂ (h x) (T s x))
      (mu.withDensity fun x ↦ rho x) := L2.integrable_inner h (T s)
  have htestAE : (fun x ↦ T s x) =ᵐ[mu.withDensity fun x ↦ rho x] test s :=
    (htest s).coeFn_toLp
  have hprod : Integrable (fun x ↦ conj (h x) * test s x)
      (mu.withDensity fun x ↦ rho x) := by
    apply hinner.congr
    filter_upwards [htestAE] with x hx
    simpa only [RCLike.inner_apply, hx] using mul_comm (test s x) (conj (h x))
  have hbase : Integrable
      (fun x ↦ (rho x : ℝ) • (conj (h x) * test s x)) mu :=
    (integrable_withDensity_iff_integrable_smul hrho).mp hprod
  constructor
  · exact hbase.congr <| Filter.Eventually.of_forall fun x ↦ by
      change (rho x : ℂ) * (conj (h x) * test s x) =
        (conj (h x) * (rho x : ℂ)) * test s x
      ring
  · calc
      L s = inner ℂ h (T s) := hrepr s
      _ = ∫ x, inner ℂ (h x) (T s x) ∂(mu.withDensity fun x ↦ rho x) :=
        L2.inner_def h (T s)
      _ = ∫ x, conj (h x) * test s x ∂(mu.withDensity fun x ↦ rho x) := by
        apply integral_congr_ae
        filter_upwards [htestAE] with x hx
        simpa only [RCLike.inner_apply, hx] using mul_comm (test s x) (conj (h x))
      _ = ∫ x, (rho x : ℝ) • (conj (h x) * test s x) ∂mu :=
        integral_withDensity_eq_integral_smul hrho _
      _ = ∫ x, (conj (h x) * (rho x : ℝ)) * test s x ∂mu := by
        apply integral_congr_ae
        filter_upwards with x
        change (rho x : ℂ) * (conj (h x) * test s x) =
          (conj (h x) * (rho x : ℂ)) * test s x
        ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
