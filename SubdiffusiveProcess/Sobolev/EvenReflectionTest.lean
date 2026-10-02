import SubdiffusiveProcess.Sobolev.EvenReflectionDomain
import SubdiffusiveProcess.Sobolev.EvenReflectionCutoff
import SubdiffusiveProcess.Sobolev.WeakGradient
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The interface test lemma for the weak gradient on a half domain

Let `D` be an `EvenReflectionDomain` with lower half `Ω` and doubled domain
`U`, and let `(u, g)` be a weak-gradient pair on `Ω`. The distributional
identity `∫_Ω χ g_j + ∫_Ω ∂_j χ u = 0` is imposed by definition only for
tests compactly supported in `Ω`. This file extends it to tests `χ`
compactly supported in `U` under the single condition

* for the normal coordinate `j = i`: `χ` vanishes on the plane `{x i = z i}`;
* for tangential coordinates `j ≠ i`: no condition at all.

Argument. Multiply `χ` by the one-sided cutoff `η_n(x) = η(x i - z i)` of
`EvenReflectionCutoff`, which vanishes within distance `ε_n = 1/(n+1)` of the
plane and equals one at distance `2 ε_n`. Then `χ η_n` is compactly supported
in `Ω`, so the weak identity holds for it. Its derivative is
`∂_j χ · η_n + χ · ∂_j η_n`, where `∂_j η_n = 0` for `j ≠ i`. The terms
`χ η_n g_j` and `∂_j χ η_n u` converge by dominated convergence (dominated by
`|χ g_j|` and `|∂_j χ u|`, since `0 ≤ η_n ≤ 1`). For `j = i`, the error term
`χ ∂_i η_n u` is dominated by `2 L C · 1_{tsupport χ} |u|`, where `L` bounds
`‖fderiv χ‖`, `C` bounds `|η'|`, because `|χ(x)| ≤ L |x i - z i|` (mean value
inequality from the vanishing on the plane) and `|∂_i η_n| ≤ C / ε_n` is
supported where `|x i - z i| ≤ 2 ε_n`. It tends to zero pointwise on `Ω`.

No trace of `u` on the plane is defined or used.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Continuous compactly supported functions pair integrably with domain L2 classes. -/
theorem integrable_mul_domainL2 {f : SpatialCoordinates d → ℝ} (hf : Continuous f)
    (hK : HasCompactSupport f) (u : DomainL2 Ω) :
    Integrable (fun x => f x * u x) (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
  (hf.memLp_of_hasCompactSupport (μ := volume.restrict (Ω : Set (SpatialCoordinates d)))
    (p := 2) hK).integrable_mul (Lp.memLp u)

/-- The classical coordinate derivative of a smooth function is continuous. -/
theorem continuous_fderiv_single {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ ∞ f)
    (j : Fin d) : Continuous fun x => fderiv ℝ f x (Pi.single j 1) :=
  (hf.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)

/-- Dominated convergence for pairings against a fixed domain L2 class. -/
theorem tendsto_integral_mul_domainL2 {F : ℕ → SpatialCoordinates d → ℝ}
    {f g : SpatialCoordinates d → ℝ} (hF : ∀ n, Continuous (F n))
    (hg : MemLp g 2 (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hbound : ∀ n x, ‖F n x‖ ≤ ‖g x‖)
    (hlim : ∀ x ∈ Ω, Tendsto (fun n => F n x) atTop (𝓝 (f x))) (u : DomainL2 Ω) :
    Tendsto (fun n => ∫ x in (Ω : Set (SpatialCoordinates d)), F n x * u x) atTop
      (𝓝 (∫ x in (Ω : Set (SpatialCoordinates d)), f x * u x)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖ * ‖u x‖)
    (fun n => (hF n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
    (hg.norm.integrable_mul (Lp.memLp u).norm) (fun n => ae_of_all _ fun x => ?_) ?_
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound n x) (norm_nonneg _)
  · filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
    exact (hlim x hx).mul_const _

namespace EvenReflectionDomain
variable (D : EvenReflectionDomain d)

/-- A test on the doubled domain, truncated by the `n`-th cutoff, is a test on the lower half. -/
def truncate (χ : 𝓓(D.U, ℝ)) (n : ℕ) : 𝓓(D.Ω, ℝ) where
  toFun := fun x => χ x * evenReflectionSpatialCutoff D.z D.i (evenReflectionScale n) x
  contDiff' := χ.contDiff.mul (evenReflectionSpatialCutoff_contDiff _ _ _)
  hasCompactSupport' := χ.hasCompactSupport.mul_right
  tsupport_subset' := by
    intro x hx
    have h1 : x ∈ tsupport χ := tsupport_mul_subset_left hx
    have h2 : x ∈ tsupport (evenReflectionSpatialCutoff D.z D.i (evenReflectionScale n)) :=
      tsupport_mul_subset_right hx
    have hcl : tsupport (evenReflectionSpatialCutoff D.z D.i (evenReflectionScale n)) ⊆
        {y | y D.i ≤ D.z D.i - evenReflectionScale n} := by
      apply closure_minimal _ (isClosed_le (continuous_apply D.i) continuous_const)
      intro y hy
      by_contra hlt
      exact hy (evenReflectionSpatialCutoff_eq_zero D.z D.i (evenReflectionScale_pos n)
        (le_of_lt (not_le.mp hlt)))
    have h3 : x D.i ≤ D.z D.i - evenReflectionScale n := hcl h2
    exact (D.mem_iff x).mpr ⟨χ.tsupport_subset h1, by linarith [evenReflectionScale_pos n]⟩

theorem truncate_apply (χ : 𝓓(D.U, ℝ)) (n : ℕ) (x : SpatialCoordinates d) :
    D.truncate χ n x = χ x * evenReflectionSpatialCutoff D.z D.i (evenReflectionScale n) x := rfl

/-- Product rule for the truncated test. -/
theorem fderiv_truncate (χ : 𝓓(D.U, ℝ)) (n : ℕ) (x : SpatialCoordinates d) (j : Fin d) :
    fderiv ℝ (D.truncate χ n) x (Pi.single j 1) =
      fderiv ℝ χ x (Pi.single j 1) * evenReflectionSpatialCutoff D.z D.i (evenReflectionScale n) x +
      χ x * fderiv ℝ (evenReflectionSpatialCutoff D.z D.i (evenReflectionScale n)) x
        (Pi.single j 1) := by
  have h := (χ.contDiff.differentiable (by simp) x).hasFDerivAt.fun_mul
    ((evenReflectionSpatialCutoff_contDiff D.z D.i (evenReflectionScale n)).differentiable
      (by simp) x).hasFDerivAt
  change fderiv ℝ (fun y => χ y * evenReflectionSpatialCutoff D.z D.i (evenReflectionScale n) y)
    x (Pi.single j 1) = _
  rw [h.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- A test vanishing on the plane is bounded by its Lipschitz constant times the distance. -/
theorem abs_test_le_of_vanishes (χ : 𝓓(D.U, ℝ)) (hχ : ∀ x, x D.i = D.z D.i → χ x = 0)
    {L : ℝ} (hL : ∀ x, ‖fderiv ℝ χ x‖ ≤ L) (x : SpatialCoordinates d) :
    |χ x| ≤ L * |x D.i - D.z D.i| := by
  set x' : SpatialCoordinates d := x + Pi.single D.i (D.z D.i - x D.i) with hx'
  have hx'i : x' D.i = D.z D.i := by simp [hx']
  have hmvt := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => χ.contDiff.differentiable (by simp) y) (fun y _ => hL y) (mem_univ x') (mem_univ x)
  rw [hχ x' hx'i, sub_zero, Real.norm_eq_abs] at hmvt
  have hn : ‖x - x'‖ = |x D.i - D.z D.i| := by
    rw [hx', show x - (x + Pi.single D.i (D.z D.i - x D.i)) = -Pi.single D.i (D.z D.i - x D.i) by
      abel, norm_neg, Pi.norm_single, Real.norm_eq_abs, abs_sub_comm]
  rwa [hn] at hmvt

/-- The interface error integrand is uniformly bounded. -/
theorem abs_mul_deriv_cutoff_le (χ : 𝓓(D.U, ℝ)) (hχ : ∀ x, x D.i = D.z D.i → χ x = 0)
    {L : ℝ} (hL : ∀ x, ‖fderiv ℝ χ x‖ ≤ L) {C : ℝ} (hC : ∀ s, |deriv evenReflectionStep s| ≤ C)
    {ε : ℝ} (hε : 0 < ε) (x : SpatialCoordinates d) :
    |χ x * deriv (evenReflectionCutoff ε) (x D.i - D.z D.i)| ≤ 2 * L * C := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL x)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  by_cases hd : deriv (evenReflectionCutoff ε) (x D.i - D.z D.i) = 0
  · rw [hd, mul_zero, abs_zero]
    positivity
  · have ht : -(2 * ε) ≤ x D.i - D.z D.i ∧ x D.i - D.z D.i ≤ -ε := by
      by_contra h
      rw [not_and_or, not_le, not_le] at h
      exact hd (deriv_evenReflectionCutoff_eq_zero hε h)
    have habs : |x D.i - D.z D.i| ≤ 2 * ε :=
      abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h1 := D.abs_test_le_of_vanishes χ hχ hL x
    have h2 := abs_deriv_evenReflectionCutoff_le hε hC (x D.i - D.z D.i)
    calc |χ x * deriv (evenReflectionCutoff ε) (x D.i - D.z D.i)|
        = |χ x| * |deriv (evenReflectionCutoff ε) (x D.i - D.z D.i)| := abs_mul _ _
      _ ≤ (L * (2 * ε)) * (C / ε) :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left habs hL0)) h2 (abs_nonneg _)
          (by positivity)
      _ = 2 * L * C := by
        field_simp

/-- **Interface test lemma.** The weak-gradient identity on the lower half extends to
tests compactly supported in the doubled domain; for the normal derivative the test
must vanish on the reflection plane, for tangential derivatives nothing is required. -/
theorem weakGradient_identity {u : SobolevData D.Ω} (hu : u ∈ weakSobolevGraph D.Ω)
    (χ : 𝓓(D.U, ℝ)) (j : Fin d) (hχ : j = D.i → ∀ x, x D.i = D.z D.i → χ x = 0) :
    (∫ x in (D.Ω : Set (SpatialCoordinates d)), χ x * u.2 j x) +
      (∫ x in (D.Ω : Set (SpatialCoordinates d)), fderiv ℝ χ x (Pi.single j 1) * u.1 x) = 0 := by
  rw [mem_weakSobolevGraph_iff] at hu
  set c : ℕ → SpatialCoordinates d → ℝ :=
    fun n => evenReflectionSpatialCutoff D.z D.i (evenReflectionScale n) with hc
  have hcc : ∀ n, Continuous (c n) := fun n =>
    (evenReflectionSpatialCutoff_contDiff _ _ _).continuous
  have hdc : ∀ n, Continuous fun x => fderiv ℝ (c n) x (Pi.single j 1) := fun n =>
    continuous_fderiv_single (evenReflectionSpatialCutoff_contDiff _ _ _) j
  have hχc : Continuous χ := χ.contDiff.continuous
  have hdχ : Continuous fun x => fderiv ℝ χ x (Pi.single j 1) :=
    continuous_fderiv_single χ.contDiff j
  have hc0 : ∀ n x, 0 ≤ c n x := fun n x => evenReflectionSpatialCutoff_nonneg _ _ _ x
  have hc1 : ∀ n x, c n x ≤ 1 := fun n x => evenReflectionSpatialCutoff_le_one _ _ _ x
  have hcn : ∀ n x, ‖c n x‖ ≤ 1 := fun n x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hc0 n x)]
    exact hc1 n x
  -- the truncated identity along the sequence
  have hn : ∀ n, (∫ x in (D.Ω : Set (SpatialCoordinates d)), χ x * c n x * u.2 j x) +
      ((∫ x in (D.Ω : Set (SpatialCoordinates d)),
        fderiv ℝ χ x (Pi.single j 1) * c n x * u.1 x) +
       (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        χ x * fderiv ℝ (c n) x (Pi.single j 1) * u.1 x)) = 0 := by
    intro n
    have h := hu (D.truncate χ n) j
    have h1 : (∫ x in (D.Ω : Set (SpatialCoordinates d)), D.truncate χ n x * u.2 j x) =
        ∫ x in (D.Ω : Set (SpatialCoordinates d)), χ x * c n x * u.2 j x := rfl
    have h2 : (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        fderiv ℝ (D.truncate χ n) x (Pi.single j 1) * u.1 x) =
        ∫ x in (D.Ω : Set (SpatialCoordinates d)),
          (fderiv ℝ χ x (Pi.single j 1) * c n x * u.1 x +
            χ x * fderiv ℝ (c n) x (Pi.single j 1) * u.1 x) := by
      congr 1
      funext x
      rw [fderiv_truncate]
      ring
    rw [h1, h2, integral_add
      (integrable_mul_domainL2 (hdχ.mul (hcc n))
        ((χ.hasCompactSupport.fderiv_apply ℝ (Pi.single j 1)).mul_right) u.1)
      (integrable_mul_domainL2 (hχc.mul (hdc n)) χ.hasCompactSupport.mul_right u.1)] at h
    exact h
  -- limits of the three terms
  have hA : Tendsto (fun n => ∫ x in (D.Ω : Set (SpatialCoordinates d)), χ x * c n x * u.2 j x)
      atTop (𝓝 (∫ x in (D.Ω : Set (SpatialCoordinates d)), χ x * u.2 j x)) := by
    refine tendsto_integral_mul_domainL2 (F := fun n x => χ x * c n x) (fun n => hχc.mul (hcc n))
      (hχc.memLp_of_hasCompactSupport χ.hasCompactSupport) (fun n x => ?_) (fun x hx => ?_) (u.2 j)
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hcn n x)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_evenReflectionSpatialCutoff_eq_one D.z D.i
        ((D.mem_iff x).mp hx).2] with n hn
      show χ x = χ x * evenReflectionSpatialCutoff D.z D.i (evenReflectionScale n) x
      rw [hn, mul_one]
  have hB : Tendsto (fun n => ∫ x in (D.Ω : Set (SpatialCoordinates d)),
      fderiv ℝ χ x (Pi.single j 1) * c n x * u.1 x) atTop
      (𝓝 (∫ x in (D.Ω : Set (SpatialCoordinates d)), fderiv ℝ χ x (Pi.single j 1) * u.1 x)) := by
    refine tendsto_integral_mul_domainL2 (F := fun n x => fderiv ℝ χ x (Pi.single j 1) * c n x)
      (fun n => hdχ.mul (hcc n))
      (hdχ.memLp_of_hasCompactSupport (χ.hasCompactSupport.fderiv_apply ℝ (Pi.single j 1)))
      (fun n x => ?_) (fun x hx => ?_) u.1
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hcn n x)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_evenReflectionSpatialCutoff_eq_one D.z D.i
        ((D.mem_iff x).mp hx).2] with n hn
      show fderiv ℝ χ x (Pi.single j 1) =
        fderiv ℝ χ x (Pi.single j 1) * evenReflectionSpatialCutoff D.z D.i (evenReflectionScale n) x
      rw [hn, mul_one]
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_evenReflectionStep
  obtain ⟨L, hL⟩ := (χ.hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (χ.contDiff.continuous_fderiv (by simp))
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hE : Tendsto (fun n => ∫ x in (D.Ω : Set (SpatialCoordinates d)),
      χ x * fderiv ℝ (c n) x (Pi.single j 1) * u.1 x) atTop
      (𝓝 (∫ x in (D.Ω : Set (SpatialCoordinates d)), (0 : ℝ) * u.1 x)) := by
    refine tendsto_integral_mul_domainL2
      (F := fun n x => χ x * fderiv ℝ (c n) x (Pi.single j 1)) (f := fun _ => 0)
      (g := (tsupport χ).indicator fun _ => 2 * L * C) (fun n => hχc.mul (hdc n))
      (memLp_indicator_const 2 (isClosed_tsupport χ).measurableSet _
        (Or.inr χ.hasCompactSupport.isCompact.measure_lt_top.ne))
      (fun n x => ?_) (fun x hx => ?_) u.1
    · beta_reduce
      simp only [hc]
      by_cases hxs : x ∈ tsupport χ
      · rw [Set.indicator_of_mem hxs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (show (0 : ℝ) ≤ 2 * L * C by positivity),
          fderiv_evenReflectionSpatialCutoff_single]
        by_cases hj : j = D.i
        · rw [if_pos hj]
          exact D.abs_mul_deriv_cutoff_le χ (hχ hj) hL hC (evenReflectionScale_pos n) x
        · rw [if_neg hj, mul_zero, abs_zero]
          positivity
      · rw [image_eq_zero_of_notMem_tsupport hxs, zero_mul, norm_zero]
        exact norm_nonneg _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_deriv_evenReflectionCutoff_eq_zero D.z D.i
        ((D.mem_iff x).mp hx).2] with n hn
      simp only [hc]
      rw [fderiv_evenReflectionSpatialCutoff_single, hn]
      simp
  -- pass to the limit in the truncated identity
  have hsum := hA.add (hB.add hE)
  have h0 := tendsto_nhds_unique hsum (tendsto_const_nhds.congr fun n => (hn n).symm)
  have hz : (∫ x in (D.Ω : Set (SpatialCoordinates d)), (0 : ℝ) * u.1 x) = 0 := by simp
  rw [hz, add_zero] at h0
  exact h0

end EvenReflectionDomain
end SubdiffusiveProcess
end
