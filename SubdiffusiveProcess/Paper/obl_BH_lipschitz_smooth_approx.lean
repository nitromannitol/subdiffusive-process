module

public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import SubdiffusiveProcess.DirichletForm.All

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff Convolution

namespace SubdiffusiveProcess.Paper

lemma aux_obl_BH_lipschitz_smooth_approx_lineDeriv_one
    (f f' : ℝ → ℝ) (x : ℝ) (h : HasDerivAt f (f' x) x) :
    lineDeriv ℝ f x 1 = f' x := by
  have hinner : HasDerivAt (fun t : ℝ => x + t * 1) (1 : ℝ) 0 := by
    simpa [Pi.add_def] using (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id' (0 : ℝ)).mul_const (1 : ℝ))
  have hx : HasDerivAt f (f' x) ((fun t : ℝ => x + t * 1) 0) := by
    simpa using h
  have hpath : HasDerivAt (fun t : ℝ => f (x + t * 1)) (f' x) 0 := by
    simpa [Function.comp_def] using HasDerivAt.comp 0 hx hinner
  simpa [lineDeriv] using hpath.deriv

lemma aux_obl_BH_lipschitz_smooth_approx_lineDeriv_sub
    (f f' : ℝ → ℝ) (a x : ℝ) (h : ∀ y : ℝ, HasDerivAt f (f' y) y) :
    lineDeriv ℝ (fun t => f (a - t)) x (-1) = f' (a - x) := by
  have hsub : HasDerivAt (fun t : ℝ => a - t) (-1 : ℝ) x := by
    simpa [Pi.sub_def] using (hasDerivAt_const x a).sub (hasDerivAt_id x)
  have hq : HasDerivAt (fun t : ℝ => f (a - t)) (f' (a - x) * (-1)) x := by
    convert (h (a - x)).comp x hsub using 1 ; simp [Function.comp_def]
  have hinner : HasDerivAt (fun t : ℝ => x + t * (-1)) (-1 : ℝ) 0 := by
    convert (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id' (0 : ℝ)).mul_const (-1 : ℝ))
      using 1 ; ring
  have hx : HasDerivAt (fun t : ℝ => f (a - t)) (f' (a - x) * (-1))
      ((fun t : ℝ => x + t * (-1)) 0) := by
    simpa using hq
  have hpath : HasDerivAt
      (fun t : ℝ => (fun u => f (a - u)) (x + t * (-1))) (f' (a - x)) 0 := by
    simpa [Function.comp_def] using HasDerivAt.comp 0 hx hinner
  simpa [lineDeriv] using hpath.deriv

lemma aux_obl_BH_lipschitz_smooth_approx_lsmul_flip :
    (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
  ext
  simp



theorem obl_BH_lipschitz_smooth_approx
    (T : ℝ → ℝ)
    (hLip : ∃ K : ℝ≥0, LipschitzWith K T)
    (hT0 : T 0 = 0)
    (Tderiv : ℝ → ℝ)
    (hderiv_meas : Measurable Tderiv)
    (hderiv : ∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s) :
    ∃ (Tk : ℕ → ℝ → ℝ) (Dk : ℕ → ℝ → ℝ) (C : ℝ),
      0 ≤ C ∧
      (∀ k : ℕ,
        ContDiff ℝ ∞ (Tk k) ∧ Tk k 0 = 0 ∧ Measurable (Dk k) ∧
          (∀ s : ℝ, HasDerivAt (Tk k) (Dk k s) s) ∧
          (∀ s : ℝ, |Dk k s| ≤ C)) ∧
      (∀ s : ℝ, Tendsto (fun k : ℕ => Tk k s) atTop (𝓝 (T s))) ∧
      (∀ᵐ s : ℝ, Tendsto (fun k : ℕ => Dk k s) atTop (𝓝 (Tderiv s))) := by
  rcases hLip with ⟨K, hK⟩
  let C : ℝ := K
  have hC : 0 ≤ C := by
    exact NNReal.coe_nonneg K
  let g : ℝ → ℝ := fun s => max (-C) (min C (Tderiv s))
  have hg_meas : Measurable g := by
    dsimp [g]
    exact (measurable_const.max (measurable_const.min hderiv_meas))
  have hTderiv_bound : ∀ᵐ s : ℝ, |Tderiv s| ≤ C := by
    filter_upwards [hderiv] with s hs
    simpa [C, Real.norm_eq_abs] using hs.le_of_lipschitz hK
  have hg_eq : ∀ᵐ s : ℝ, g s = Tderiv s := by
    filter_upwards [hTderiv_bound] with s hs
    have hlow : -C ≤ Tderiv s := (abs_le.mp hs).1
    have hupp : Tderiv s ≤ C := (abs_le.mp hs).2
    dsimp [g]
    rw [min_eq_right hupp, max_eq_right hlow]
  have hg_bound : ∀ s : ℝ, |g s| ≤ C := by
    intro s
    apply abs_le.2
    constructor
    · exact le_max_left _ _
    · exact max_le (neg_le_self hC) (min_le_left _ _)
  have hg_loc : LocallyIntegrable g := by
    rw [locallyIntegrable_iff]
    intro S hS
    apply Measure.integrableOn_of_bounded
      (MeasureTheory.IsFiniteMeasureOnCompacts.lt_top_of_isCompact hS).ne
      hg_meas.aestronglyMeasurable
    exact Eventually.of_forall (fun s => by
      simpa [Real.norm_eq_abs] using hg_bound s)
  have hT_loc : LocallyIntegrable T := hK.continuous.locallyIntegrable
  have hlineT : ∀ᵐ s : ℝ, lineDeriv ℝ T s 1 = Tderiv s := by
    filter_upwards [hderiv] with s hs
    exact aux_obl_BH_lipschitz_smooth_approx_lineDeriv_one T Tderiv s hs

  let eps : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ)
  have heps : ∀ k : ℕ, 0 < eps k := by
    intro k
    dsimp [eps]
    positivity
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun k =>
    ⟨eps k / 2, eps k, half_pos (heps k), half_lt_self (heps k)⟩
  have hφ_out : Tendsto (fun k : ℕ => (φ k).rOut) atTop (𝓝 0) := by
    have hnat : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_mono (fun k => by linarith)
        tendsto_natCast_atTop_atTop
    have hinv := tendsto_inv_atTop_zero.comp hnat
    simpa [φ, eps, one_div, Function.comp_def] using hinv
  have hφ_ratio : ∀ᶠ k : ℕ in atTop, (φ k).rOut ≤ 2 * (φ k).rIn := by
    filter_upwards with k
    dsimp [φ]
    rw [show 2 * (eps k / 2) = eps k by ring]

  let A : ℕ → ℝ → ℝ := fun k => (φ k).normed volume
  let F : ℕ → ℝ → ℝ := fun k => T ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] A k
  let Tk : ℕ → ℝ → ℝ := fun k s => F k s - F k 0
  let Dk : ℕ → ℝ → ℝ := fun k s => deriv (Tk k) s
  have hA_cont : ∀ k : ℕ, ContDiff ℝ ∞ (A k) := by
    intro k
    dsimp [A]
    exact (φ k).contDiff_normed
  have hA_cont_one : ∀ k : ℕ, ContDiff ℝ 1 (A k) := by
    intro k
    exact (hA_cont k).of_le (by norm_num)
  have hA_support : ∀ k : ℕ, HasCompactSupport (A k) := by
    intro k
    dsimp [A]
    exact (φ k).hasCompactSupport_normed
  have hA_nonneg : ∀ k : ℕ, ∀ s : ℝ, 0 ≤ A k s := by
    intro k s
    dsimp [A]
    exact (φ k).nonneg_normed s
  have hF_cont : ∀ k : ℕ, ContDiff ℝ ∞ (F k) := by
    intro k
    dsimp [F]
    exact (hA_support k).contDiff_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hT_loc (hA_cont k)
  have hTk_cont : ∀ k : ℕ, ContDiff ℝ ∞ (Tk k) := by
    intro k
    dsimp [Tk]
    exact (hF_cont k).sub contDiff_const
  have hTk_zero : ∀ k : ℕ, Tk k 0 = 0 := by
    intro k
    simp [Tk]
  have hD_meas : ∀ k : ℕ, Measurable (Dk k) := by
    intro k
    dsimp [Dk]
    exact measurable_deriv (Tk k)
  have hD_eq : ∀ k : ℕ, ∀ s : ℝ,
      Dk k s = (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] A k) s := by
    intro k s
    have hF_deriv : HasDerivAt (F k)
        ((T ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] deriv (A k)) s) s := by
      dsimp [F]
      exact (hA_support k).hasDerivAt_convolution_right
        (ContinuousLinearMap.lsmul ℝ ℝ) hT_loc (hA_cont_one k) s
    have hTk_deriv : Dk k s =
        (T ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] deriv (A k)) s := by
      have hsub := hF_deriv.sub (hasDerivAt_const s (F k 0))
      change deriv (fun x => F k x - F k 0) s = _
      simpa only [Pi.sub_apply, sub_zero, Pi.sub_def] using hsub.deriv
    obtain ⟨Lk, hLk⟩ :=
      ContDiff.lipschitzWith_of_hasCompactSupport (hA_support k) (hA_cont k) (by norm_num)
    have hsub_lip : LipschitzWith 1 (fun t : ℝ => s - t) := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      rw [show s - x - (s - y) = -(x - y) by ring, abs_neg]
    have hq_lip : LipschitzWith (Lk * 1) (fun t : ℝ => A k (s - t)) := by
      simpa [Function.comp_def] using hLk.comp hsub_lip
    have hq_support : HasCompactSupport (fun t : ℝ => A k (s - t)) := by
      simpa [Function.comp_def] using
        (hA_support k).comp_homeomorph (Homeomorph.subLeft s)
    have hA_deriv : ∀ y : ℝ, HasDerivAt (A k) (deriv (A k) y) y := by
      intro y
      exact ((hA_cont_one k).differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hparts := hK.integral_lineDeriv_mul_eq (μ := volume) hq_lip hq_support (1 : ℝ)
    have hparts' :
        (∫ t : ℝ, Tderiv t * A k (s - t)) =
          ∫ t : ℝ, deriv (A k) (s - t) * T t := by
      calc
        (∫ t : ℝ, Tderiv t * A k (s - t)) =
            ∫ t : ℝ, lineDeriv ℝ T t 1 * A k (s - t) := by
              apply integral_congr_ae
              filter_upwards [hlineT] with t ht
              rw [← ht]
        _ = ∫ t : ℝ, lineDeriv ℝ (fun u => A k (s - u)) t (-1) * T t := hparts
        _ = ∫ t : ℝ, deriv (A k) (s - t) * T t := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall (fun t => by
                change lineDeriv ℝ (fun u => A k (s - u)) t (-1) * T t = _
                rw [aux_obl_BH_lipschitz_smooth_approx_lineDeriv_sub
                  (A k) (deriv (A k)) s t hA_deriv])
    calc
      Dk k s = (T ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] deriv (A k)) s := hTk_deriv
      _ = ∫ t : ℝ, T t * deriv (A k) (s - t) := by
        simp [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      _ = ∫ t : ℝ, deriv (A k) (s - t) * T t := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by ring)
      _ = ∫ t : ℝ, Tderiv t * A k (s - t) := hparts'.symm
      _ = ∫ t : ℝ, g t * A k (s - t) := by
        apply integral_congr_ae
        filter_upwards [hg_eq] with t ht
        rw [ht]
      _ = (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] A k) s := by
        simp [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hD_bound : ∀ k : ℕ, ∀ s : ℝ, |Dk k s| ≤ C := by
    intro k s
    have hconv :=
      ((hA_support k).convolutionExists_right
        (ContinuousLinearMap.lsmul ℝ ℝ) hg_loc (hA_cont k).continuous s).integrable
    have hq_cont : Continuous (fun t : ℝ => A k (s - t)) := by
      simpa only [Function.comp_def, Pi.sub_apply, id_eq] using
        (hA_cont k).continuous.comp (continuous_const.sub continuous_id)
    have hq_int : Integrable (fun t : ℝ => C * A k (s - t)) := by
      exact (hq_cont.integrable_of_hasCompactSupport (by
        simpa [Function.comp_def] using
          (hA_support k).comp_homeomorph (Homeomorph.subLeft s))).const_mul C
    rw [hD_eq k s, convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    calc
      |∫ t : ℝ, g t * A k (s - t)| =
          ‖∫ t : ℝ, g t * A k (s - t)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ t : ℝ, ‖g t * A k (s - t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, C * A k (s - t) := by
        apply integral_mono_ae hconv.norm hq_int
        exact Filter.Eventually.of_forall (fun t => by
          simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.norm_eq_abs,
            abs_of_nonneg (hA_nonneg k (s - t))] using
            mul_le_mul_of_nonneg_right (hg_bound t) (hA_nonneg k (s - t)))
      _ = C := by
        rw [integral_const_mul, integral_sub_left_eq_self (A k) volume s,
          (φ k).integral_normed, mul_one]
  have hF_tendsto : ∀ s : ℝ,
      Tendsto (fun k : ℕ => F k s) atTop (𝓝 (T s)) := by
    intro s
    have hlim := ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := volume) (φ := φ) hφ_out hK.continuous s
    have hflip : ∀ k : ℕ,
        F k = (A k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] T) := by
      intro k
      dsimp [F]
      rw [← MeasureTheory.convolution_flip (ContinuousLinearMap.lsmul ℝ ℝ),
        aux_obl_BH_lipschitz_smooth_approx_lsmul_flip]
    have heq : (fun k : ℕ => F k s) =
        (fun k : ℕ => (A k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] T) s) := by
      funext k
      exact congrFun (hflip k) s
    rw [heq]
    exact hlim
  have hTk_tendsto : ∀ s : ℝ,
      Tendsto (fun k : ℕ => Tk k s) atTop (𝓝 (T s)) := by
    intro s
    have hsub := (hF_tendsto s).sub (hF_tendsto 0)
    simpa [Tk, hT0] using hsub
  have hD_tendsto : ∀ᵐ s : ℝ,
      Tendsto (fun k : ℕ => Dk k s) atTop (𝓝 (Tderiv s)) := by
    have hlim := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := volume) (φ := φ) hφ_out hφ_ratio hg_loc
    filter_upwards [hlim, hg_eq] with s hs hgs
    have heq : ∀ k : ℕ, Dk k s =
        (A k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) s := by
      intro k
      calc
        Dk k s = (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] A k) s := hD_eq k s
        _ = (A k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) s := by
          rw [← MeasureTheory.convolution_flip (ContinuousLinearMap.lsmul ℝ ℝ),
            aux_obl_BH_lipschitz_smooth_approx_lsmul_flip]
    have hconv : Tendsto
        (fun k : ℕ => (A k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) s)
        atTop (𝓝 (g s)) := hs
    have hconv' := hconv.congr (fun k => (heq k).symm)
    simpa [hgs] using hconv'
  refine ⟨Tk, Dk, C, hC, ?_, hTk_tendsto, hD_tendsto⟩
  intro k
  exact ⟨hTk_cont k, hTk_zero k, hD_meas k,
    fun s => by
      have h := (hTk_cont k).differentiable (by norm_num)
      change HasDerivAt (Tk k) (deriv (Tk k) s) s
      exact h.differentiableAt.hasDerivAt,
    hD_bound k⟩

end SubdiffusiveProcess.Paper
