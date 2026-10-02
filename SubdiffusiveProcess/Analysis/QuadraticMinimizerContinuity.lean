import SubdiffusiveProcess.Analysis.QuadraticMinimizerStability
import Mathlib.Topology.Sequences
import Mathlib.Data.Real.Sqrt

open Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.Analysis

theorem trace_norm_le_of_minimizer_compared_zero
    {V W : Type*} [Zero V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (E : V → ℝ) (A : V → W) (lam : ℝ) (hlam : 0 < lam) (g : W) (u : V)
    (hE0 : E 0 = 0) (hA0 : A 0 = 0) (hEu : 0 ≤ E u)
    (hu : E u + lam * ‖A u‖ ^ 2 - 2 * ⟪g, A u⟫_ℝ ≤
      E 0 + lam * ‖A 0‖ ^ 2 - 2 * ⟪g, A 0⟫_ℝ) :
    ‖A u‖ ≤ 2 * ‖g‖ / lam := by
  rw [hE0, hA0, norm_zero, inner_zero_right] at hu
  have hip : ⟪g, A u⟫_ℝ ≤ ‖g‖ * ‖A u‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  apply (le_div_iff₀ hlam).mpr
  by_cases hz : ‖A u‖ = 0
  · rw [hz, zero_mul]
    positivity
  have hp : 0 < ‖A u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith

/-- The strict quadratic midpoint gap gives joint shift/source continuity of
the actual minimizer. No continuity of the trace map is assumed here. -/
theorem continuous_minimizer_of_quadratic_gap
    {X V W : Type*} [TopologicalSpace X] [SequentialSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (E : V → ℝ) (A : V → W) (D : Set V)
    (lam : X → ℝ) (g : X → W) (u : X → V) (mid : X → X → V)
    (κ : ℝ) (hκ : 0 < κ)
    (hlam : ∀ x, 0 < lam x) (hlamc : Continuous lam) (hgc : Continuous g)
    (hzero : (0 : V) ∈ D) (hE0 : E 0 = 0) (hA0 : A 0 = 0)
    (hEpos : ∀ v ∈ D, 0 ≤ E v) (huD : ∀ x, u x ∈ D)
    (hmidD : ∀ x y, mid x y ∈ D)
    (humin : ∀ x v, v ∈ D →
      E (u x) + lam x * ‖A (u x)‖ ^ 2 - 2 * ⟪g x, A (u x)⟫_ℝ ≤
        E v + lam x * ‖A v‖ ^ 2 - 2 * ⟪g x, A v⟫_ℝ)
    (hgap : ∀ x y, κ * ‖u x - u y‖ ^ 2 ≤
      ((E (u x) + lam x * ‖A (u x)‖ ^ 2 - 2 * ⟪g x, A (u x)⟫_ℝ) +
        (E (u y) + lam x * ‖A (u y)‖ ^ 2 - 2 * ⟪g x, A (u y)⟫_ℝ)) / 2 -
        (E (mid x y) + lam x * ‖A (mid x y)‖ ^ 2 -
          2 * ⟪g x, A (mid x y)⟫_ℝ)) : Continuous u := by
  have htrace (x : X) : ‖A (u x)‖ ≤ 2 * ‖g x‖ / lam x :=
    trace_norm_le_of_minimizer_compared_zero E A (lam x) (hlam x) (g x) (u x)
      hE0 hA0 (hEpos _ (huD x)) (humin x 0 hzero)
  apply continuous_iff_seqContinuous.mpr
  intro xs x hxs
  have hls : Tendsto (fun n => lam (xs n)) atTop (𝓝 (lam x)) :=
    (hlamc.tendsto x).comp hxs
  have hgs : Tendsto (fun n => g (xs n)) atTop (𝓝 (g x)) := (hgc.tendsto x).comp hxs
  let C := max ‖A (u x)‖ (4 * (‖g x‖ + 1) / lam x)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (le_max_left _ _)
  have hCx : ‖A (u x)‖ ≤ C := le_max_left _ _
  have hbound : ∀ᶠ n in atTop, ‖A (u (xs n))‖ ≤ C := by
    have hnear : ∀ᶠ n in atTop, lam x / 2 < lam (xs n) ∧ ‖g (xs n)‖ < ‖g x‖ + 1 :=
      (hls.eventually (eventually_gt_nhds (by linarith [hlam x]))).and
        (hgs.norm.eventually (eventually_lt_nhds (lt_add_one _)))
    filter_upwards [hnear] with n hn
    apply (htrace _).trans
    apply le_trans _ (le_max_right _ _)
    calc
      2 * ‖g (xs n)‖ / lam (xs n) ≤ 2 * (‖g x‖ + 1) / (lam x / 2) := by
        gcongr
        · exact half_pos (hlam x)
        · exact hn.2.le
        · exact hn.1.le
      _ = 4 * (‖g x‖ + 1) / lam x := by ring
  let b : ℕ → ℝ := fun n =>
    (|lam x - lam (xs n)| * (2 * C ^ 2) + 2 * ‖g x - g (xs n)‖ * (2 * C)) / 2
  have hb : Tendsto b atTop (𝓝 0) := by
    have hl0 : Tendsto (fun n => |lam x - lam (xs n)|) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => lam x) atTop (𝓝 (lam x))).sub hls).abs
    have hg0 : Tendsto (fun n => ‖g x - g (xs n)‖) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => g x) atTop (𝓝 (g x))).sub hgs).norm
    simpa only [b, zero_mul, mul_zero, zero_add, zero_div] using
      ((hl0.mul_const (2 * C ^ 2)).add ((hg0.const_mul 2).mul_const (2 * C))).div_const 2
  have hsmall : ∀ᶠ n in atTop, κ * ‖u x - u (xs n)‖ ^ 2 ≤ b n := by
    filter_upwards [hbound] with n hn
    apply (quadratic_minimizer_stability E A (lam x) (lam (xs n)) (g x) (g (xs n))
      (u x) (u (xs n)) (mid x (xs n)) κ (humin x _ (hmidD x (xs n)))
      (humin (xs n) _ (huD x)) (hgap x (xs n))).trans
    dsimp only [b]
    have hsqx : ‖A (u x)‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg (A (u x))]
    have hsqn : ‖A (u (xs n))‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg (A (u (xs n)))]
    gcongr
    · linarith
    · linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqr : Tendsto (fun n => κ * ‖u x - u (xs n)‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun n => mul_nonneg hκ.le (sq_nonneg _)) hsmall hb
  have hsq : Tendsto (fun n => ‖u x - u (xs n)‖ ^ 2) atTop (𝓝 0) := by
    simpa [hκ.ne'] using hsqr.div_const κ
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    norm_sub_rev] using hnorm

end SubdiffusiveProcess.Analysis
