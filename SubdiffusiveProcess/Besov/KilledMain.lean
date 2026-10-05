module

public import SubdiffusiveProcess.Besov.DetachMain
public import SubdiffusiveProcess.Besov.KilledIBP
public import SubdiffusiveProcess.Besov.KilledMoment

@[expose] public section

/-!
# `\eqref{e.CG.Poincare.trace.zero}`: the killed Poincaré inequality at the endpoint

For every `u ∈ H¹₀((-1/2,1/2)^d)`, `‖u‖_{L²(Q)} ≤ K [∇u]_{B^{-1}_{2,1}(Q)}` with `K = Cd d + 1`
(`killed_endpoint_main`).  The oscillation `‖u - (u)_Q‖` is bounded by the depth bound of the detach inequality
(`depth_bound` at depth `0`, where the only overlap centre is the middle child of `Q`); the mean `(u)_Q` is bounded by
the first-moment duality with the affine field `x_i` (`killed_ibp`, `first_moment_le`), which replaces the paper's
torsion function.
-/

open MeasureTheory
open Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.Besov.Detach

noncomputable section

theorem cubeAverage_unit {d : ℕ} (f : Vec d → ℝ) :
    cubeAverage (originCube d 0) f = ∫ x in openCubeSet (originCube d 0), f x := by
  unfold cubeAverage
  have hv : cubeVolume (originCube d 0) = 1 := by
    simp [cubeVolume, cubeScaleFactor, originCube]
  rw [hv, inv_one, one_mul]
  exact setIntegral_congr_set (cubeSet_ae_eq_openCubeSet _)

theorem memLp_normalized_of_h1 {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) :
    MemLp H.toFun 2 (normalizedCubeMeasure (originCube d 0)) := by
  have h1 : MemLp H.toFun 2 (volume.restrict (openCubeSet (originCube d 0))) := H.memL2
  have h2 : volume.restrict (cubeSet (originCube d 0)) =
      volume.restrict (openCubeSet (originCube d 0)) :=
    Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet _)
  unfold normalizedCubeMeasure cubeMeasure
  rw [h2]
  exact h1.smul_measure ENNReal.ofReal_ne_top

theorem cubeLpNorm_two_le {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    cubeLpNorm Q 2 f ≤ cubeBesovOscillation Q 2 f + |cubeAverage Q f| := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩
  set μ := normalizedCubeMeasure Q
  set c := cubeAverage Q f with hc
  have hcm : MemLp (fun _ : Vec d => c) 2 μ := memLp_const c
  have hfc : MemLp (fun x => f x - c) 2 μ := hf.sub hcm
  have h1 : eLpNorm f 2 μ ≤ eLpNorm (fun x => f x - c) 2 μ + eLpNorm (fun _ : Vec d => c) 2 μ := by
    have := eLpNorm_add_le (μ := μ) (f := fun x => f x - c) (g := fun _ : Vec d => c) (by norm_num : (1 : ENNReal) ≤ 2)
    have hfe : f = (fun x => f x - c) + fun _ : Vec d => c := by
      funext x; simp
    rw [hfe]
    simpa using this
  have h2 : eLpNorm (fun _ : Vec d => c) 2 μ = ENNReal.ofReal |c| := by
    rw [eLpNorm_const c (by norm_num) (IsProbabilityMeasure.ne_zero μ)]
    rw [← ofReal_norm, Real.norm_eq_abs]
    simp
  unfold cubeLpNorm cubeBesovOscillation cubeFluctuation
  have h3 := ENNReal.toReal_mono (by
    exact ENNReal.add_ne_top.mpr ⟨hfc.eLpNorm_ne_top, by rw [h2]; exact ENNReal.ofReal_ne_top⟩) h1
  rw [ENNReal.toReal_add hfc.eLpNorm_ne_top (by rw [h2]; exact ENNReal.ofReal_ne_top), h2,
    ENNReal.toReal_ofReal (abs_nonneg c)] at h3
  exact h3

/-- The `q = 1`, `s = 1` negative Besov norm of the gradient of `H`, as a scaled supremum. -/
theorem paperNorm_one_eq {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm (originCube d 0) 1
        (.finite 1) H.grad =
      sSup (Set.range fun N : ℕ =>
        ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ (-1 * (m : ℝ)) * gradX H m) := by
  rw [paperNorm_eq, one_mul]

theorem y_nonneg {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (m : ℕ) :
    0 ≤ (3 : ℝ) ^ (-1 * (m : ℝ)) * gradX H m :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _) (gradX_nonneg H m)

theorem y_summable {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) :
    Summable (fun m : ℕ => (3 : ℝ) ^ (-1 * (m : ℝ)) * gradX H m) := by
  obtain ⟨G, hG⟩ := gradX_bdd H
  exact summable_weighted 1 one_pos (gradX H) (gradX_nonneg H) G hG

theorem y_shift_eq (m : ℕ) : (3 : ℝ) ^ (-1 * ((m + 1 : ℕ) : ℝ)) = ((3 : ℝ) ^ (m + 1))⁻¹ := by
  rw [show (-1 * ((m + 1 : ℕ) : ℝ)) = -((m + 1 : ℕ) : ℝ) by ring, Real.rpow_neg (by norm_num),
    Real.rpow_natCast]

theorem partial_shift_le_sSup {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (J : ℕ) :
    ∑ m ∈ Finset.range J, ((3 : ℝ) ^ (m + 1))⁻¹ * gradX H (m + 1) ≤
      sSup (Set.range fun N : ℕ =>
        ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ (-1 * (m : ℝ)) * gradX H m) := by
  have hbdd : BddAbove (Set.range fun N : ℕ =>
      ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ (-1 * (m : ℝ)) * gradX H m) := by
    refine ⟨∑' m : ℕ, (3 : ℝ) ^ (-1 * (m : ℝ)) * gradX H m, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact (y_summable H).sum_le_tsum _ (fun i _ => y_nonneg H i)
  have h1 := Finset.sum_range_succ' (fun m : ℕ => (3 : ℝ) ^ (-1 * (m : ℝ)) * gradX H m) J
  have h2 : ∑ m ∈ Finset.range J, ((3 : ℝ) ^ (m + 1))⁻¹ * gradX H (m + 1) =
      ∑ m ∈ Finset.range J, (3 : ℝ) ^ (-1 * ((m + 1 : ℕ) : ℝ)) * gradX H (m + 1) :=
    Finset.sum_congr rfl fun m _ => by rw [y_shift_eq]
  rw [h2]
  have h3 := le_csSup hbdd ⟨J, rfl⟩
  have h4 := y_nonneg H 0
  linarith


/-- The mean of an `H¹₀` function of the unit cube is bounded by the negative Besov norm of its gradient. -/
theorem killed_mean_le {d : ℕ} [NeZero d] (u : H10Function (openCubeSet (originCube d 0))) :
    |cubeAverage (originCube d 0) u.toH1Function.toFun| ≤
      SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm (originCube d 0) 1
        (.finite 1) u.toH1Function.grad := by
  set H := u.toH1Function with hH
  set i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ with hi
  set Sup1 := sSup (Set.range fun N : ℕ =>
        ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ (-1 * (m : ℝ)) * gradX H m) with hSup
  rw [paperNorm_one_eq]
  have hibp := killed_ibp u i
  have havg : cubeAverage (originCube d 0) H.toFun =
      - cubeAverage (originCube d 0) (fun x => H.grad x i * x i) := by
    rw [cubeAverage_unit, cubeAverage_unit]
    exact hibp
  have hgI := integrableOn_grad_cube H i
  have hJ : ∀ J : ℕ, |cubeAverage (originCube d 0) H.toFun| ≤
      Sup1 + ((3 : ℝ) ^ J)⁻¹ / 2 * cubeAverage (originCube d 0) (fun x => |H.grad x i|) := by
    intro J
    rw [havg, abs_neg]
    have h1 := first_moment_le (fun x => H.grad x i) hgI i J
    have h2 : ∑ m ∈ Finset.range J, ((3 : ℝ) ^ (m + 1))⁻¹ *
        Real.sqrt (theta (originCube d 0) (m + 1) (fun x => H.grad x i)) ≤
        ∑ m ∈ Finset.range J, ((3 : ℝ) ^ (m + 1))⁻¹ * gradX H (m + 1) :=
      Finset.sum_le_sum fun m _ =>
        mul_le_mul_of_nonneg_left (sqrt_theta_le_gradX H i (m + 1)) (inv_nonneg.mpr (by positivity))
    have h3 := partial_shift_le_sSup H J
    linarith
  set M := cubeAverage (originCube d 0) (fun x => |H.grad x i|)
  have hlim : Filter.Tendsto (fun J : ℕ => Sup1 + ((3 : ℝ) ^ J)⁻¹ / 2 * M) Filter.atTop
      (nhds (Sup1 + 0 / 2 * M)) := by
    have h0 : Filter.Tendsto (fun J : ℕ => ((3 : ℝ) ^ J)⁻¹) Filter.atTop (nhds 0) := by
      simp_rw [← inv_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact tendsto_const_nhds.add ((h0.div_const 2).mul_const M)
  have h5 := ge_of_tendsto' hlim hJ
  have h6 : Sup1 + 0 / 2 * M = Sup1 := by simp
  rw [h6] at h5
  exact h5


/-- The `L²` oscillation on the unit cube is bounded by the negative Besov norm of the gradient. -/
theorem killed_osc_le {d : ℕ} [NeZero d] (H : H1Function (openCubeSet (originCube d 0))) :
    cubeBesovOscillation (originCube d 0) 2 H.toFun ≤
      Cd d * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm (originCube d 0) 1
        (.finite 1) H.grad := by
  rw [paperNorm_one_eq]
  have hD := depth_bound H 0
  have hL : Real.sqrt (ScalarOverlap.centersAverage (originCube d 0) 0
      (fun S => (cubeBesovOverlapOscillation S 2 H.toFun) ^ 2)) =
      cubeBesovOscillation (originCube d 0) 2 H.toFun := by
    unfold ScalarOverlap.centersAverage
    simp only [ScalarOverlap.centersAtDepth_zero, Finset.card_singleton, Finset.sum_singleton,
      cubeBesovOverlapOscillation_middleChildCube]
    rw [Nat.cast_one, inv_one, one_mul, Real.sqrt_sq (cubeBesovOscillation_nonneg _ _ _)]
  rw [hL] at hD
  refine hD.trans (mul_le_mul_of_nonneg_left ?_ (Cd_nonneg d))
  have hy := y_summable H
  have h1 : ∑' k : ℕ, ((3 : ℝ) ^ (0 + 1 + k))⁻¹ * gradX H (0 + 1 + k) =
      ∑' k : ℕ, (3 : ℝ) ^ (-1 * ((k + 1 : ℕ) : ℝ)) * gradX H (k + 1) := by
    refine tsum_congr fun k => ?_
    rw [y_shift_eq k, show 0 + 1 + k = k + 1 by ring]
  have h2 := hy.sum_add_tsum_nat_add 1
  have h3 := y_nonneg H 0
  simp only [Finset.range_one, Finset.sum_singleton] at h2
  have h4 := tsum_le_sSup_partial _ (y_nonneg H) hy
  rw [h1]
  linarith

theorem killed_endpoint_main {d : ℕ} [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ u : H10Function (openCubeSet (originCube d 0)),
        cubeLpNorm (originCube d 0) (2 : ℝ≥0∞) u.toH1Function.toFun ≤
          K * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
            (originCube d 0) 1 (.finite 1) u.toH1Function.grad := by
  refine ⟨Cd d + 1, by linarith [Cd_nonneg d], fun u => ?_⟩
  have h1 := cubeLpNorm_two_le (originCube d 0) u.toH1Function.toFun
    (memLp_normalized_of_h1 u.toH1Function)
  have h2 := killed_osc_le u.toH1Function
  have h3 := killed_mean_le u
  linarith


end

end SubdiffusiveProcess.Besov.Detach
