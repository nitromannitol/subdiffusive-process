module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Sobolev.NativeH1
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import Homogenization.Sobolev.CubeEmbedding.Extension
public import SubdiffusiveProcess.Analysis.RadialKernel

@[expose] public section

/-! Proof of `cubeFractionalL2Seminorm_lt_top_of_weakSobolevGraph` : every H^1 function on a cube
has finite Gagliardo seminorm at every order `s ∈ (0,1)`.
(1) smooth case: `∫∫_{Q×Q} (φx-φy)^2/|x-y|^{d+2s} ≤ C ∫_Q |∇φ|^2`, by the fundamental theorem of calculus
along segments (the cube is convex), Tonelli, the substitution `h = y - x`, and integrability of
`|h|^{2-d-2s}` on bounded balls (`2 - 2s > 0`);
(2) smooth approximation in H^1(Q) (`convexApproxSmoothH1`);
(3) Fatou along an a.e.-convergent subsequence. -/

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess Filter
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess
namespace CubeFractionalH1Internal

variable {d : ℕ}

/-- The scalar Gagliardo integrand (Euclidean distance, exponent `d + 2s`). -/
def aux_f5_gq (s : ℝ) (g : SpatialCoordinates d → ℝ) (x y : SpatialCoordinates d) : ℝ≥0∞ :=
  ENNReal.ofReal ((g x - g y) ^ 2) /
    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * s)

/-- Squared Euclidean gradient of a differentiable function. -/
def aux_f5_gradSq (φ : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∑ i : Fin d, (fderiv ℝ φ x (Pi.single i 1)) ^ 2

/-- Squared Euclidean norm. -/
def aux_f5_esq (h : SpatialCoordinates d) : ℝ := ∑ j : Fin d, h j ^ 2

/-- (1a) Along a segment: `(φ y - φ x)^2 ≤ |y-x|^2 ∫_0^1 |∇φ(x+t(y-x))|^2 dt`. -/
theorem aux_f5_sq_diff_le_segment (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ 1 φ)
    (x y : SpatialCoordinates d) :
    (φ y - φ x) ^ 2 ≤ aux_f5_esq (y - x) * ∫ t in (0 : ℝ)..1, aux_f5_gradSq φ (x + t • (y - x)) := by
  set v : SpatialCoordinates d := y - x with hv
  set F : ℝ → ℝ := fun t => fderiv ℝ φ (x + t • v) v with hF
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => φ (x + t • v)) (F t) t := fun t =>
    (hdiff (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hγ t)
  have hFc : Continuous F := by
    have h1 : Continuous fun t : ℝ => fderiv ℝ φ (x + t • v) :=
      (hφ.continuous_fderiv (by norm_num)).comp (continuous_const.add (continuous_id.smul continuous_const))
    exact h1.clm_apply continuous_const
  -- fundamental theorem of calculus along the segment
  have hFTC : φ y - φ x = ∫ t in (0 : ℝ)..1, F t := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hFc.intervalIntegrable 0 1)
    rw [this]; simp [hv]
  -- pointwise Cauchy–Schwarz: F t ^ 2 ≤ aux_f5_esq v * aux_f5_gradSq φ (x + t • v)
  have hCS : ∀ t : ℝ, F t ^ 2 ≤ aux_f5_esq v * aux_f5_gradSq φ (x + t • v) := by
    intro t
    have hvsum : v = ∑ i : Fin d, v i • (Pi.single i (1 : ℝ) : SpatialCoordinates d) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have hlin : F t = ∑ i : Fin d, v i * fderiv ℝ φ (x + t • v) (Pi.single i 1) := by
      simp only [hF]
      set L := fderiv ℝ φ (x + t • v) with hL
      calc L v = L (∑ i : Fin d, v i • (Pi.single i (1 : ℝ) : SpatialCoordinates d)) := by
            rw [← hvsum]
        _ = ∑ i : Fin d, v i * L (Pi.single i 1) := by simp [map_sum, map_smul, smul_eq_mul]
    rw [hlin, aux_f5_esq, aux_f5_gradSq]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  -- (∫ F)^2 ≤ ∫ F^2 on [0,1], since 0 ≤ ∫ (F - c)^2 = ∫ F^2 - c^2
  have hF2i : IntervalIntegrable (fun t => F t ^ 2) volume 0 1 := (hFc.pow 2).intervalIntegrable 0 1
  have hJ : (∫ t in (0 : ℝ)..1, F t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, F t ^ 2 := by
    set c := ∫ t in (0 : ℝ)..1, F t with hc
    have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (F t - c) ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
    have hexp : ∫ t in (0 : ℝ)..1, (F t - c) ^ 2 = (∫ t in (0 : ℝ)..1, F t ^ 2) - c ^ 2 := by
      have e : ∀ t, (F t - c) ^ 2 = F t ^ 2 - 2 * c * F t + c ^ 2 := fun t => by ring
      simp_rw [e]
      rw [intervalIntegral.integral_add (hF2i.sub ((hFc.intervalIntegrable 0 1).const_mul _))
          intervalIntegrable_const,
        intervalIntegral.integral_sub hF2i ((hFc.intervalIntegrable 0 1).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp [hc]; ring
    linarith
  have hG : Continuous fun t : ℝ => aux_f5_gradSq φ (x + t • v) := by
    unfold aux_f5_gradSq
    have h1 : Continuous fun t : ℝ => fderiv ℝ φ (x + t • v) :=
      (hφ.continuous_fderiv (by norm_num)).comp (continuous_const.add (continuous_id.smul continuous_const))
    exact continuous_finsetSum _ fun i _ => (h1.clm_apply continuous_const).pow 2
  calc (φ y - φ x) ^ 2 = (∫ t in (0 : ℝ)..1, F t) ^ 2 := by rw [hFTC]
    _ ≤ ∫ t in (0 : ℝ)..1, F t ^ 2 := hJ
    _ ≤ ∫ t in (0 : ℝ)..1, aux_f5_esq v * aux_f5_gradSq φ (x + t • v) :=
        intervalIntegral.integral_mono_on (by norm_num) hF2i
          ((continuous_const.mul hG).intervalIntegrable 0 1) fun t _ => hCS t
    _ = aux_f5_esq v * ∫ t in (0 : ℝ)..1, aux_f5_gradSq φ (x + t • v) := intervalIntegral.integral_const_mul _ _

/-- (1b) The kernel `|h|^{2-d-2s}` (Euclidean norm) is integrable on every ball. -/
theorem aux_f5_kernel_lintegral_lt_top (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (R : ℝ) :
    ∫⁻ h in Metric.ball (0 : SpatialCoordinates d) R,
      ENNReal.ofReal (aux_f5_esq h) / (ENNReal.ofReal (Real.sqrt (aux_f5_esq h))) ^ ((d : ℝ) + 2 * s) < ⊤ := by
  classical
  have hq : -(d : ℝ) < 2 - d - 2 * s := by linarith
  have hint := integrableOn_norm_rpow_ball (by omega : 0 < d) (2 - d - 2 * s) R hq
  refine lt_of_le_of_lt ?_ hint.lintegral_lt_top
  refine lintegral_mono fun h => ?_
  by_cases h0 : aux_f5_esq h = 0
  · simp [h0]
  · have hpos : 0 < aux_f5_esq h := lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg (h j)) (Ne.symm h0)
    set e := Real.sqrt (aux_f5_esq h) with he
    have hepos : 0 < e := Real.sqrt_pos.mpr hpos
    have hesq : aux_f5_esq h = e ^ 2 := (Real.sq_sqrt hpos.le).symm
    -- sup norm ≤ Euclidean norm
    have hnorm : ‖h‖ ≤ e := by
      refine (pi_norm_le_iff_of_nonneg hepos.le).mpr fun j => ?_
      rw [Real.norm_eq_abs, he]
      refine Real.abs_le_sqrt ?_
      exact Finset.single_le_sum (f := fun j => h j ^ 2) (fun j _ => sq_nonneg (h j)) (Finset.mem_univ j)
    have hnpos : 0 < ‖h‖ := by
      rw [norm_pos_iff]; intro hz; apply h0; simp [aux_f5_esq, hz]
    rw [ENNReal.ofReal_rpow_of_pos hepos, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hepos _)]
    apply ENNReal.ofReal_le_ofReal
    rw [hesq, ← Real.rpow_natCast, ← Real.rpow_sub hepos]
    have hexp : (↑(2 : ℕ) : ℝ) - ((d : ℝ) + 2 * s) = 2 - d - 2 * s := by push_cast; ring
    rw [hexp]
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    exact Real.rpow_le_rpow_of_nonpos hnpos hnorm (by linarith)

/-- Generic Tonelli/substitution bound. -/
theorem aux_f5_segment_integral_le_gen (Q B : Set (SpatialCoordinates d)) (hQm : MeasurableSet Q)
    (hBm : MeasurableSet B) (hconv : Convex ℝ Q) (hQB : ∀ x ∈ Q, ∀ y ∈ Q, y - x ∈ B) (s : ℝ)
    (G : SpatialCoordinates d → ℝ) (hG0 : ∀ x, 0 ≤ G x) (hGm : Measurable G) :
    ∫⁻ x in Q, ∫⁻ y in Q,
        ENNReal.ofReal (aux_f5_esq (y - x)) / (ENNReal.ofReal (Real.sqrt (aux_f5_esq (y - x)))) ^ ((d : ℝ) + 2 * s) *
          ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • (y - x))) ≤
      (∫⁻ h in B, ENNReal.ofReal (aux_f5_esq h) / (ENNReal.ofReal (Real.sqrt (aux_f5_esq h))) ^ ((d : ℝ) + 2 * s)) *
        ∫⁻ x in Q, ENNReal.ofReal (G x) := by
  classical
  set K : SpatialCoordinates d → ℝ≥0∞ := fun h =>
    ENNReal.ofReal (aux_f5_esq h) / (ENNReal.ofReal (Real.sqrt (aux_f5_esq h))) ^ ((d : ℝ) + 2 * s) with hK
  have hKm : Measurable K := by simp only [hK, aux_f5_esq]; fun_prop
  set g : SpatialCoordinates d → ℝ≥0∞ := fun w => ENNReal.ofReal (G w) with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp hGm
  -- (1) the t-integral is at most the lower integral over [0,1]
  have h1 : ∀ x y : SpatialCoordinates d,
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • (y - x))) ≤
        ∫⁻ t in Icc (0 : ℝ) 1, g (x + t • (y - x)) := by
    intro x y
    rw [intervalIntegral.integral_of_le zero_le_one]
    have hmeas : AEStronglyMeasurable (fun t : ℝ => G (x + t • (y - x))) (volume.restrict (Ioc 0 1)) :=
      (hGm.comp (by fun_prop)).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t => hG0 _) hmeas]
    exact ENNReal.ofReal_toReal_le.trans (lintegral_mono_set Ioc_subset_Icc_self)
  -- (2) substitute y = x + h and use convexity
  have h2 : ∀ x ∈ Q, ∫⁻ y in Q, K (y - x) * ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • (y - x))) ≤
      ∫⁻ h, B.indicator (fun h => ∫⁻ t in Icc (0 : ℝ) 1, K h * Q.indicator g (x + t • h)) h := by
    intro x hx
    rw [← lintegral_indicator hQm, ← lintegral_add_left_eq_self _ x]
    refine lintegral_mono fun h => ?_
    by_cases hy : x + h ∈ Q
    · have hhB : h ∈ B := by simpa using hQB x hx (x + h) hy
      have hgi : Measurable fun t : ℝ => Q.indicator g (x + t • h) := (hgm.indicator hQm).comp (by fun_prop)
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hhB, add_sub_cancel_left, lintegral_const_mul _ hgi]
      gcongr
      calc ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • h))
          ≤ ∫⁻ t in Icc (0 : ℝ) 1, g (x + t • h) := by simpa using h1 x (x + h)
        _ = ∫⁻ t in Icc (0 : ℝ) 1, Q.indicator g (x + t • h) := by
            refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
            rw [Set.indicator_of_mem (hconv.add_smul_mem hx hy ht)]
    · rw [Set.indicator_of_notMem hy]; exact zero_le
  -- (3) Tonelli and translation invariance
  have hF : Measurable (fun p : (SpatialCoordinates d × SpatialCoordinates d) × ℝ =>
      K p.1.2 * Q.indicator g (p.1.1 + p.2 • p.1.2)) :=
    (hKm.comp (by fun_prop)).mul ((hgm.indicator hQm).comp (by fun_prop))
  have hinner : ∀ t : ℝ, ∀ h : SpatialCoordinates d,
      ∫⁻ x, Q.indicator g (x + t • h) = ∫⁻ x in Q, g x := by
    intro t h
    rw [lintegral_add_right_eq_self (fun x => Q.indicator g x) (t • h), lintegral_indicator hQm]
  calc ∫⁻ x in Q, ∫⁻ y in Q, K (y - x) * ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • (y - x)))
      ≤ ∫⁻ x in Q, ∫⁻ h, B.indicator (fun h => ∫⁻ t in Icc (0 : ℝ) 1, K h * Q.indicator g (x + t • h)) h :=
        setLIntegral_mono' hQm h2
    _ ≤ ∫⁻ x, ∫⁻ h, B.indicator (fun h => ∫⁻ t in Icc (0 : ℝ) 1, K h * Q.indicator g (x + t • h)) h :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ h, ∫⁻ x, B.indicator (fun h => ∫⁻ t in Icc (0 : ℝ) 1, K h * Q.indicator g (x + t • h)) h := by
        apply lintegral_lintegral_swap
        refine Measurable.aemeasurable ?_
        refine Measurable.indicator ?_ (hBm.preimage measurable_snd)
        exact hF.lintegral_prod_right'
    _ = ∫⁻ h, B.indicator (fun h => ∫⁻ t in Icc (0 : ℝ) 1, K h * ∫⁻ x in Q, g x) h := by
        refine lintegral_congr fun h => ?_
        by_cases hh : h ∈ B
        · simp only [Set.indicator_of_mem hh]
          have hm2 : Measurable (Function.uncurry fun (x : SpatialCoordinates d) (t : ℝ) =>
              K h * Q.indicator g (x + t • h)) :=
            measurable_const.mul ((hgm.indicator hQm).comp
              (by fun_prop : Measurable fun q : SpatialCoordinates d × ℝ => q.1 + q.2 • h))
          rw [lintegral_lintegral_swap hm2.aemeasurable]
          refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
          have hmx : Measurable fun x : SpatialCoordinates d => Q.indicator g (x + t • h) :=
            (hgm.indicator hQm).comp (by fun_prop)
          rw [lintegral_const_mul _ hmx, hinner t h]
        · simp [Set.indicator_of_notMem hh]
    _ = (∫⁻ h in B, K h) * ∫⁻ x in Q, g x := by
        rw [lintegral_indicator hBm]
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc,
          sub_zero, ENNReal.ofReal_one, mul_one]
        rw [lintegral_mul_const _ hKm]


/-- (1c) Tonelli + substitution `y = x + h` + translation invariance, for a nonnegative `G`
vanishing off the convex cube. -/
theorem aux_f5_segment_integral_le (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (s : ℝ)
    (G : SpatialCoordinates d → ℝ) (hG0 : ∀ x, 0 ≤ G x) (hGm : Measurable G) :
    ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (aux_f5_esq (y - x)) / (ENNReal.ofReal (Real.sqrt (aux_f5_esq (y - x)))) ^ ((d : ℝ) + 2 * s) *
            ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • (y - x))) ≤
      (∫⁻ h in Metric.ball (0 : SpatialCoordinates d) (r + 1),
          ENNReal.ofReal (aux_f5_esq h) / (ENNReal.ofReal (Real.sqrt (aux_f5_esq h))) ^ ((d : ℝ) + 2 * s)) *
        ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal (G x) := by
  refine aux_f5_segment_integral_le_gen _ _ (centeredCube z r hr).isOpen.measurableSet
    Metric.isOpen_ball.measurableSet (convex_ball z (r / 2)) ?_ s G hG0 hGm
  intro x hx y hy
  have hx' : dist x z < r / 2 := hx
  have hy' : dist y z < r / 2 := hy
  rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm]
  calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
    _ < r / 2 + r / 2 := by rw [dist_comm z x]; linarith
    _ < r + 1 := by linarith

/-- (1) Smooth case. -/
theorem aux_f5_smooth_bound (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ φ : SpatialCoordinates d → ℝ, ContDiff ℝ 1 φ →
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_f5_gq s φ x y ≤
        C * ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal (aux_f5_gradSq φ x) := by
  refine ⟨∫⁻ h in Metric.ball (0 : SpatialCoordinates d) (r + 1),
      ENNReal.ofReal (aux_f5_esq h) / (ENNReal.ofReal (Real.sqrt (aux_f5_esq h))) ^ ((d : ℝ) + 2 * s),
    aux_f5_kernel_lintegral_lt_top hd s hs0 hs1 (r + 1), fun φ hφ => ?_⟩
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQ
  have hQm : MeasurableSet Q := (centeredCube z r hr).isOpen.measurableSet
  -- G = |∇φ|^2 on Q, 0 off Q (the segment between two points of Q stays in Q)
  set G : SpatialCoordinates d → ℝ := Q.indicator (aux_f5_gradSq φ) with hG
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ hQm
    have hc := hφ.continuous_fderiv (by norm_num)
    unfold aux_f5_gradSq; fun_prop
  have hconv : Convex ℝ Q := convex_ball z (r / 2)
  calc ∫⁻ x in Q, ∫⁻ y in Q, aux_f5_gq s φ x y
      ≤ ∫⁻ x in Q, ∫⁻ y in Q,
          ENNReal.ofReal (aux_f5_esq (y - x)) / (ENNReal.ofReal (Real.sqrt (aux_f5_esq (y - x)))) ^ ((d : ℝ) + 2 * s) *
            ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • (y - x))) := by
        refine setLIntegral_mono' hQm fun x hx => setLIntegral_mono' hQm fun y hy => ?_
        -- the segment stays in the convex cube, so G = aux_f5_gradSq φ along it
        have hseg : ∫ t in (0 : ℝ)..1, G (x + t • (y - x)) = ∫ t in (0 : ℝ)..1, aux_f5_gradSq φ (x + t • (y - x)) := by
          refine intervalIntegral.integral_congr fun t ht => ?_
          rw [Set.uIcc_of_le zero_le_one] at ht
          have hmem : x + t • (y - x) ∈ Q := by
            have := hconv.add_smul_sub_mem hx hy ⟨ht.1, ht.2⟩
            simpa using this
          simp [hG, Set.indicator_of_mem hmem]
        have hesym : aux_f5_esq (y - x) = ∑ j : Fin d, (x j - y j) ^ 2 := by
          unfold aux_f5_esq; refine Finset.sum_congr rfl fun j _ => ?_; simp only [Pi.sub_apply]; ring
        have hsq := aux_f5_sq_diff_le_segment φ hφ x y
        have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, aux_f5_gradSq φ (x + t • (y - x)) :=
          intervalIntegral.integral_nonneg zero_le_one fun t _ => Finset.sum_nonneg fun i _ => sq_nonneg _
        rw [hseg]
        unfold aux_f5_gq
        rw [← hesym, div_eq_mul_inv, div_eq_mul_inv, mul_right_comm,
          ← ENNReal.ofReal_mul (by unfold aux_f5_esq; positivity)]
        gcongr
        calc (φ x - φ y) ^ 2 = (φ y - φ x) ^ 2 := by ring
          _ ≤ _ := hsq
    _ ≤ _ := aux_f5_segment_integral_le z hr s G (fun x => Set.indicator_nonneg (fun x _ => by
          unfold aux_f5_gradSq; positivity) x) hGm
    _ = _ := by
        congr 1
        rw [hG]
        refine setLIntegral_congr_fun hQm (fun x hx => ?_)
        exact congrArg ENNReal.ofReal (Set.indicator_of_mem hx _)

/-- (2) Smooth approximation of an H^1 function on the cube, in values and in gradient. -/
theorem aux_f5_smooth_approx (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr)) :
    ∃ φ : ℕ → SpatialCoordinates d → ℝ, (∀ n, ContDiff ℝ 1 (φ n)) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - (u : SobolevData (centeredCube z r hr)).1 x) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) atTop (𝓝 0) ∧
      ∀ i : Fin d, Tendsto (fun n => eLpNorm
          (fun x => fderiv ℝ (φ n) x (Pi.single i 1) - (u : SobolevData (centeredCube z r hr)).2 i x) 2
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) atTop (𝓝 0) := by
  classical
  obtain ⟨v, hv1, hv2⟩ := exists_nativeH1Function_of_weakSobolevGraph u
  have hU := lane2_isOpenBoundedConvexDomain_centeredCube z hr
  have hρ : (0 : ℝ) < r / 4 := by positivity
  have hball : Metric.closedBall z (r / 4) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro x hx
    change x ∈ Metric.ball z (r / 2)
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith))
  refine ⟨fun n => (Homogenization.H1Function.convexApproxSmoothH1 hU v z hρ n).toFun,
    fun n => ?_, ?_, fun i => ?_⟩
  · dsimp only
    rw [Homogenization.H1Function.convexApproxSmoothH1_toFun]
    exact (Homogenization.contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet
      Homogenization.isConvexApproxKernel_unitConvexApproxKernel (by norm_num) v.memL2 hρ
      (by dsimp [Homogenization.unitConvexApproxScale]; positivity)).of_le (by norm_num)
  · have h := Homogenization.tendsto_eLpNorm_convexApproxSmoothH1 hU v hρ hball
    rw [hv1] at h
    exact h
  · have h := Homogenization.tendsto_eLpNorm_grad_convexApproxSmoothH1 hU v hρ hball i
    simp only [Homogenization.H1Function.convexApproxSmoothH1_grad, hv2] at h
    simp only [Homogenization.H1Function.convexApproxSmoothH1_toFun]
    exact h

/-- The gradient energies of the approximants stay bounded. -/
theorem aux_f5_gradSq_bounded (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr)) (φ : ℕ → SpatialCoordinates d → ℝ)
    (hgrad : ∀ i : Fin d, Tendsto (fun n => eLpNorm
          (fun x => fderiv ℝ (φ n) x (Pi.single i 1) - (u : SobolevData (centeredCube z r hr)).2 i x) 2
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) atTop (𝓝 0)) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ᶠ n in atTop,
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal (aux_f5_gradSq (φ n) x) ≤ B := by
  classical
  set μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) with hμ
  set U2 : Fin d → ℝ≥0∞ := fun i => eLpNorm ((u : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ) 2 μ
  have hU2 : ∀ i, U2 i < ⊤ := fun i => Lp.eLpNorm_lt_top _
  have hev : ∀ᶠ n in atTop, ∀ i : Fin d, eLpNorm
      (fun x => fderiv ℝ (φ n) x (Pi.single i 1) - (u : SobolevData (centeredCube z r hr)).2 i x) 2 μ ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    exact (hgrad i).eventually (Iic_mem_nhds (by norm_num))
  refine ⟨∑ i : Fin d, (1 + U2 i) ^ 2, ?_, ?_⟩
  · exact ENNReal.sum_lt_top.mpr fun i _ =>
      ENNReal.pow_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hU2 i⟩)
  · filter_upwards [hev] with n hn
    -- each coordinate: ∫⁻ ofReal(f^2) = (eLpNorm f 2)^2 ≤ (1 + U2 i)^2
    have hcoord : ∀ i : Fin d, ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal ((fderiv ℝ (φ n) x (Pi.single i 1)) ^ 2) ≤ (1 + U2 i) ^ 2 := by
      intro i
      set f : SpatialCoordinates d → ℝ := fun x => fderiv ℝ (φ n) x (Pi.single i 1) with hf
      set w : SpatialCoordinates d → ℝ := ((u : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
      have hfm : AEStronglyMeasurable f μ :=
        (measurable_fderiv_apply_const ℝ (φ n) (Pi.single i 1)).aestronglyMeasurable
      have hwm : AEStronglyMeasurable w μ := Lp.aestronglyMeasurable _
      have hsq : ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal (f x ^ 2) =
          eLpNorm f 2 μ ^ 2 := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hfm]
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
        refine lintegral_congr fun x => ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      have htri : eLpNorm f 2 μ ≤ 1 + U2 i := by
        calc eLpNorm f 2 μ = eLpNorm ((fun x => f x - w x) + w) 2 μ := by congr 1; funext x; simp
          _ ≤ eLpNorm (fun x => f x - w x) 2 μ + eLpNorm w 2 μ :=
              eLpNorm_add_le (by norm_num)
          _ ≤ 1 + U2 i := add_le_add (hn i) le_rfl
      rw [hsq]
      exact pow_le_pow_left₀ (zero_le) htri 2
    calc ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal (aux_f5_gradSq (φ n) x)
        = ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∑ i : Fin d, ENNReal.ofReal ((fderiv ℝ (φ n) x (Pi.single i 1)) ^ 2) := by
          refine lintegral_congr fun x => ?_
          rw [aux_f5_gradSq, ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
      _ ≤ ∑ i : Fin d, ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal ((fderiv ℝ (φ n) x (Pi.single i 1)) ^ 2) :=
          (lintegral_finsetSum _ fun i _ =>
            ((measurable_fderiv_apply_const ℝ (φ n) (Pi.single i 1)).pow_const 2).ennreal_ofReal).le
      _ ≤ ∑ i : Fin d, (1 + U2 i) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i

/-- (3) Fatou: a Gagliardo bound along approximants that converge in L2 passes to the limit. -/
theorem aux_f5_fatou_limit (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (s : ℝ)
    (g : SpatialCoordinates d → ℝ) (φ : ℕ → SpatialCoordinates d → ℝ)
    (_hgm : AEStronglyMeasurable g (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hφc : ∀ n, Continuous (φ n))
    (hconv : Tendsto (fun n => eLpNorm (fun x => φ n x - g x) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) atTop (𝓝 0))
    (M : ℝ≥0∞) (hM : ∀ᶠ n in atTop, ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_f5_gq s (φ n) x y ≤ M) :
    ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_f5_gq s g x y ≤ M := by
  classical
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQ
  set μ := volume.restrict Q with hμ
  have hQm : MeasurableSet Q := (centeredCube z r hr).isOpen.measurableSet
  -- a.e.-convergent subsequence
  have hTIM : TendstoInMeasure μ φ atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      hconv
  obtain ⟨ns, hns, hae⟩ := hTIM.exists_seq_tendsto_ae
  -- pointwise convergence of the integrand for a.e. x and a.e. y
  have hptw : ∀ x y, Tendsto (fun k => φ (ns k) x) atTop (𝓝 (g x)) →
      Tendsto (fun k => φ (ns k) y) atTop (𝓝 (g y)) →
      Tendsto (fun k => aux_f5_gq s (φ (ns k)) x y) atTop (𝓝 (aux_f5_gq s g x y)) := by
    intro x y hx hy
    unfold aux_f5_gq
    have hnum : Tendsto (fun k => ENNReal.ofReal ((φ (ns k) x - φ (ns k) y) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((g x - g y) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (((hx.sub hy).pow 2))
    by_cases hxy : x = y
    · subst hxy; simp only [sub_self]; exact tendsto_const_nhds
    · refine ENNReal.Tendsto.div_const hnum (Or.inr ?_)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
      have hpos : 0 < ∑ i : Fin d, (x i - y i) ^ 2 :=
        Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ _,
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hj)))⟩
      exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hpos))
        ENNReal.ofReal_ne_top).ne'
  have hgqm : ∀ k, Measurable (Function.uncurry (aux_f5_gq s (φ (ns k)))) := by
    intro k
    have hm := (hφc (ns k)).measurable
    unfold aux_f5_gq Function.uncurry; fun_prop
  -- Fatou in both variables
  have hM' : ∀ᶠ k in atTop, ∫⁻ x in Q, ∫⁻ y in Q, aux_f5_gq s (φ (ns k)) x y ≤ M :=
    (hns.tendsto_atTop.eventually hM)
  calc ∫⁻ x in Q, ∫⁻ y in Q, aux_f5_gq s g x y
      ≤ ∫⁻ x in Q, liminf (fun k => ∫⁻ y in Q, aux_f5_gq s (φ (ns k)) x y) atTop := by
        refine setLIntegral_mono_ae ?_ ?_
        · exact (Measurable.liminf fun k => (hgqm k).lintegral_prod_right).aemeasurable
        · filter_upwards [(ae_restrict_iff' hQm).mp hae] with x hx hxQ
          replace hx := hx hxQ
          calc ∫⁻ y in Q, aux_f5_gq s g x y
              = ∫⁻ y in Q, liminf (fun k => aux_f5_gq s (φ (ns k)) x y) atTop := by
                refine setLIntegral_congr_fun_ae hQm ?_
                filter_upwards [(ae_restrict_iff' hQm).mp hae] with y hy hyQ
                exact ((hptw x y hx (hy hyQ)).liminf_eq).symm
            _ ≤ liminf (fun k => ∫⁻ y in Q, aux_f5_gq s (φ (ns k)) x y) atTop := by
                apply lintegral_liminf_le
                intro k
                exact (hgqm k).of_uncurry_left
    _ ≤ liminf (fun k => ∫⁻ x in Q, ∫⁻ y in Q, aux_f5_gq s (φ (ns k)) x y) atTop := by
        apply lintegral_liminf_le
        intro k
        exact (hgqm k).lintegral_prod_right
    _ ≤ M := liminf_le_of_frequently_le' (hM'.frequently)

/-- The Gagliardo double integral of an H^1 function on the cube is finite. -/
theorem aux_f5_double_integral_lt_top (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (u : weakSobolevGraph (centeredCube z r hr)) :
    ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          aux_f5_gq s ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) x y < ⊤ := by
  obtain ⟨C, hC, hsm⟩ := aux_f5_smooth_bound hd z hr s hs0 hs1
  obtain ⟨φ, hφ, hval, hgrad⟩ := aux_f5_smooth_approx z hr u
  obtain ⟨B, hB, hBev⟩ := aux_f5_gradSq_bounded z hr u φ hgrad
  have hM : ∀ᶠ n in atTop, ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_f5_gq s (φ n) x y ≤ C * B := by
    filter_upwards [hBev] with n hn
    exact (hsm (φ n) (hφ n)).trans (mul_le_mul_right hn C)
  exact (aux_f5_fatou_limit z hr s _ φ (Lp.aestronglyMeasurable _) (fun n => (hφ n).continuous) hval (C * B) hM).trans_lt
    (ENNReal.mul_lt_top hC hB)

end CubeFractionalH1Internal

open CubeFractionalH1Internal in
theorem cubeFractionalL2Seminorm_lt_top_of_weakSobolevGraph (d : ℕ) (hd : 2 ≤ d)
    (s : Set.Ioo (0 : ℝ) 1) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr)) :
    cubeFractionalL2Seminorm hd z r hr s
      (fun _ : Fin 1 => (u : SobolevData (centeredCube z r hr)).1) < ⊤ := by
  have hI := aux_f5_double_integral_lt_top hd z hr s s.2.1 s.2.2 u
  unfold cubeFractionalL2Seminorm
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  refine (ENNReal.mul_lt_top ?_ ?_).ne
  · exact ENNReal.div_lt_top ENNReal.ofReal_ne_top
      (by rw [centeredCube_volume]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne')
  · simpa only [Fin.sum_univ_one, aux_f5_gq] using hI

end SubdiffusiveProcess
