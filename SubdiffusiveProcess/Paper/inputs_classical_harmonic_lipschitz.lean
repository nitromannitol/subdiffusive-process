module

public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Interior
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.EvenBoundHessian
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Reproducing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.InteriorGrad
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Kernel
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Bridge

@[expose] public section

/-! Classical interior Lipschitz estimate for harmonic functions, stated in the normalized
`L²` seminorm of a coordinate cube.  PROVED from the library's reproducing identity for radial kernels
(`SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.reproducing_of_radial`): a harmonic function reproduces itself against
the scaled radial mollifier `K_ε`, so differences `V x - V y` are integrals of `(K_ε(· - x) - K_ε(· - y)) V`, bounded by the
Lipschitz constant of `K_ε` and Cauchy–Schwarz on the cube.  (Evans, PDE, §2.2.3 Theorem 7; Gilbarg–Trudinger,
Theorem 2.10 are the classical sources.) -/

open MeasureTheory Set
open SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section
namespace Paper

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

/-- A harmonic function reproduces itself against `K_ε` on a ball of radius `2ε` contained in the harmonicity set. -/
theorem aux_inputs_classical_harmonic_lipschitz_reproducing {d : ℕ} [NeZero d]
    {S : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u S) {a : EuclideanSpace ℝ (Fin d)} {ε : ℝ} (hε : 0 < ε)
    (hcl : Metric.closedBall a (2 * ε) ⊆ S) :
    Integrable (fun t => radialKernelScaled d ε (t - a) * u t) ∧
      ∫ t, radialKernelScaled d ε (t - a) * u t = u a := by
  classical
  let χ : ContDiffBump a := ⟨ε, 2 * ε, hε, by linarith⟩
  have hχrIn : χ.rIn = ε := rfl
  have hχrOut : χ.rOut = 2 * ε := rfl
  set ũ : EuclideanSpace ℝ (Fin d) → ℝ := fun t => χ t * u t with hũdef
  have hcl' : tsupport (χ : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ S := by
    rw [χ.tsupport_eq, hχrOut]; exact hcl
  have hũ : ContDiff ℝ 2 ũ := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t ∈ tsupport (χ : EuclideanSpace ℝ (Fin d) → ℝ)
    · exact (χ.contDiff.contDiffAt).mul (hu t (hcl' ht)).1
    · have hz : (χ : EuclideanSpace ℝ (Fin d) → ℝ) =ᶠ[nhds t] 0 := notMem_tsupport_iff_eventuallyEq.1 ht
      have : ũ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
        filter_upwards [hz] with s hs
        simp [ũ, hs]
      exact contDiffAt_const.congr_of_eventuallyEq this
  have hball_sub : Metric.ball a ε ⊆ S :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))).trans hcl
  have hharm : InnerProductSpace.HarmonicOnNhd ũ (Metric.ball a ε) := by
    intro t ht
    have hev : ũ =ᶠ[nhds t] u := by
      filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
      have : χ s = 1 := χ.one_of_mem_closedBall (by rw [hχrIn]; exact Metric.ball_subset_closedBall hs)
      simp [ũ, this]
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).2 (hu t (hball_sub ht))
  have hrep := reproducing_of_radial hũ (x := a) (R := ε) hharm (radialKernelScaled_continuous d)
    (radialKernelScaled_hasCompactSupport d hε) (fun h => radialKernelScaled_radial d h)
    (ρ := ε) le_rfl (fun z hz => radialKernelScaled_eq_zero_of_le_norm d hε hz)
    (radialKernelScaled_integral_eq_one d hε)
  have hpt : ∀ t, radialKernelScaled d ε (t - a) * ũ t = radialKernelScaled d ε (t - a) * u t := by
    intro t
    by_cases ht : t ∈ Metric.ball a ε
    · have : χ t = 1 := χ.one_of_mem_closedBall (by rw [hχrIn]; exact Metric.ball_subset_closedBall ht)
      simp [ũ, this]
    · have hle : ε ≤ ‖t - a‖ := by
        rw [Metric.mem_ball, dist_eq_norm, not_lt] at ht; exact ht
      rw [radialKernelScaled_eq_zero_of_le_norm d hε hle]; simp
  have hũa : ũ a = u a := by
    have : χ a = 1 := χ.one_of_mem_closedBall (by rw [hχrIn]; exact Metric.mem_closedBall_self hε.le)
    simp [ũ, this]
  have hcont : Continuous fun t => radialKernelScaled d ε (t - a) * ũ t :=
    ((radialKernelScaled_continuous d).comp (continuous_id.sub continuous_const)).mul hũ.continuous
  have hsupp : HasCompactSupport fun t => radialKernelScaled d ε (t - a) * ũ t := by
    have : HasCompactSupport fun t => radialKernelScaled d ε (t - a) :=
      (radialKernelScaled_hasCompactSupport d hε).comp_homeomorph (Homeomorph.subRight a)
    exact this.mul_right
  have hint : Integrable fun t => radialKernelScaled d ε (t - a) * ũ t :=
    hcont.integrable_of_hasCompactSupport hsupp
  have heq : (fun t => radialKernelScaled d ε (t - a) * u t) =
      fun t => radialKernelScaled d ε (t - a) * ũ t := by
    funext t; exact (hpt t).symm
  refine ⟨by rw [heq]; exact hint, ?_⟩
  rw [heq, hrep, hũa]


/-- The scaled radial mollifier is Lipschitz with constant `G * ε^{-d} * ε^{-1}`. -/
theorem aux_inputs_classical_harmonic_lipschitz_kernel_lip (d : ℕ) [NeZero d] :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (ε : ℝ), 0 < ε → ∀ a b : EuclideanSpace ℝ (Fin d),
      |radialKernelScaled d ε a - radialKernelScaled d ε b| ≤ G * (ε ^ d)⁻¹ * ε⁻¹ * ‖a - b‖ := by
  obtain ⟨G, hG⟩ := (radialKernel_contDiff d (n := 1)).lipschitzWith_of_hasCompactSupport
    (radialKernel_hasCompactSupport d) (by norm_num)
  refine ⟨(G : ℝ), G.2, ?_⟩
  intro ε hε a b
  have h1 := hG.dist_le_mul (ε⁻¹ • a) (ε⁻¹ • b)
  rw [Real.dist_eq, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_pos.2 hε).le] at h1
  have hε' : 0 < (ε ^ d)⁻¹ := by positivity
  simp only [radialKernelScaled_apply]
  rw [← mul_sub, abs_mul, abs_of_pos hε']
  calc (ε ^ d)⁻¹ * |radialKernel d (ε⁻¹ • a) - radialKernel d (ε⁻¹ • b)|
      ≤ (ε ^ d)⁻¹ * ((G : ℝ) * (ε⁻¹ * ‖a - b‖)) := mul_le_mul_of_nonneg_left h1 hε'.le
    _ = (G : ℝ) * (ε ^ d)⁻¹ * ε⁻¹ * ‖a - b‖ := by ring

/-- The sup norm is at most the Euclidean norm. -/
theorem aux_inputs_classical_harmonic_lipschitz_sup_le {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) :
    ‖(toEuc.symm w : SpatialCoordinates d)‖ ≤ ‖w‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  exact PiLp.norm_apply_le w i

/-- The Euclidean norm is at most `√d` times the sup norm. -/
theorem aux_inputs_classical_harmonic_lipschitz_euc_le {d : ℕ} (w : SpatialCoordinates d) :
    ‖(toEuc w : EuclideanSpace ℝ (Fin d))‖ ≤ Real.sqrt d * ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin d, ‖(toEuc w) i‖ ^ 2 ≤ ∑ _i : Fin d, ‖w‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => by
      have : ‖w i‖ ≤ ‖w‖ := norm_le_pi_norm w i
      simpa using pow_le_pow_left₀ (norm_nonneg _) this 2
  calc Real.sqrt (∑ i : Fin d, ‖(toEuc w) i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin d, ‖w‖ ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * ‖w‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- Cauchy–Schwarz on a finite-measure set for an `L²` function. -/
theorem aux_inputs_classical_harmonic_lipschitz_cs {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : MeasurableSet W) (hWfin : volume W ≠ ⊤) {V : SpatialCoordinates d → ℝ}
    (hV : MemLp V 2 (volume.restrict W)) :
    (∫ x in W, |V x|) ^ 2 ≤ (volume W).toReal * ∫ x in W, (V x) ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hWfin.lt_top⟩
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; constructor <;> norm_num
  have hmem_f : MemLp (fun y => |V y|) (ENNReal.ofReal 2) (volume.restrict W) := by
    have := hV.norm
    simpa [ENNReal.ofReal_ofNat] using this
  have hmem_1 : MemLp (fun _ : SpatialCoordinates d => (1 : ℝ)) (ENNReal.ofReal 2)
      (volume.restrict W) := memLp_const 1
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall (fun y => abs_nonneg (V y)))
    (Filter.Eventually.of_forall (fun _ => (zero_le_one : (0 : ℝ) ≤ 1))) hmem_f hmem_1
  have e1 : ∫ y in W, |V y| * (1 : ℝ) = ∫ y in W, |V y| := by simp
  have e2 : ∫ _y in W, ((1 : ℝ)) ^ (2 : ℝ) = (volume W).toReal := by
    simp only [Real.one_rpow, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  have e3 : ∫ y in W, |V y| ^ (2 : ℝ) = ∫ y in W, (V y) ^ 2 := by
    refine setIntegral_congr_fun hW (fun y _ => ?_)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [e1, e3, e2] at hCS
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
  have hf2nonneg : 0 ≤ ∫ y in W, (V y) ^ 2 := setIntegral_nonneg hW (fun y _ => sq_nonneg _)
  have habs_nonneg : 0 ≤ ∫ y in W, |V y| := setIntegral_nonneg hW (fun y _ => abs_nonneg _)
  calc (∫ y in W, |V y|) ^ 2
      ≤ (Real.sqrt (∫ y in W, (V y) ^ 2) * Real.sqrt (volume W).toReal) ^ 2 :=
        pow_le_pow_left₀ habs_nonneg hCS 2
    _ = (volume W).toReal * ∫ y in W, (V y) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hf2nonneg, Real.sq_sqrt ENNReal.toReal_nonneg]; ring


/-- CLASSICAL (Evans §2.2.3 Thm 7; Gilbarg–Trudinger Thm 2.10): a harmonic function on a
coordinate cube of side `R` is Lipschitz on the concentric cube of half the side, with
constant `C / R` times its normalized `L²` norm on the whole cube. -/
theorem inputs_classical_harmonic_lipschitz (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (z : SpatialCoordinates d) (R : ℝ) (V : SpatialCoordinates d → ℝ), 0 < R →
        InnerProductSpace.HarmonicOnNhd
          (V ∘ (Section6Schauder.toEuc.symm :
            EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
          ((Section6Schauder.toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) ''
            Metric.ball z (R / 2)) →
        MemLp V 2 (volume.restrict (Metric.ball z (R / 2))) →
        ∀ x ∈ Metric.ball z (R / 4), ∀ y ∈ Metric.ball z (R / 4),
          |V x - V y| ≤ C * (dist x y / R) * normalizedL2On (Metric.ball z (R / 2)) V := by
  obtain ⟨G, hG0, hGlip⟩ := aux_inputs_classical_harmonic_lipschitz_kernel_lip d
  refine ⟨8 ^ (d + 1) * G * Real.sqrt d, by positivity, ?_⟩
  intro z R V hR hharm hV x hx y hy
  set ε : ℝ := R / 8 with hεdef
  have hε : 0 < ε := by positivity
  set W : Set (SpatialCoordinates d) := Metric.ball z (R / 2) with hW
  set S : Set (EuclideanSpace ℝ (Fin d)) :=
    (toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) '' W with hS
  set u : EuclideanSpace ℝ (Fin d) → ℝ :=
    V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → SpatialCoordinates d) with hu
  have hcl : ∀ p ∈ Metric.ball z (R / 4),
      Metric.closedBall (toEuc p : EuclideanSpace ℝ (Fin d)) (2 * ε) ⊆ S := by
    intro p hp t ht
    have h1 : ‖t - toEuc p‖ ≤ 2 * ε := by rwa [Metric.mem_closedBall, dist_eq_norm] at ht
    have h2 : dist (toEuc.symm t : SpatialCoordinates d) p ≤ R / 4 := by
      rw [dist_eq_norm]
      have : (toEuc.symm t : SpatialCoordinates d) - p = toEuc.symm (t - toEuc p) := by
        simp [map_sub]
      rw [this]
      exact (aux_inputs_classical_harmonic_lipschitz_sup_le _).trans (by rw [hεdef] at h1; linarith)
    refine ⟨toEuc.symm t, ?_, by simp⟩
    rw [hW, Metric.mem_ball]
    have h3 : dist p z < R / 4 := Metric.mem_ball.1 hp
    have := dist_triangle (toEuc.symm t : SpatialCoordinates d) p z
    linarith
  have hKS : ∀ p ∈ Metric.ball z (R / 4), ∀ t, t ∉ S →
      radialKernelScaled d ε (t - toEuc p) = 0 := by
    intro p hp t ht
    apply radialKernelScaled_eq_zero_of_le_norm d hε
    by_contra hlt
    push_neg at hlt
    apply ht
    apply hcl p hp
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith
  obtain ⟨hIa, hra⟩ := aux_inputs_classical_harmonic_lipschitz_reproducing hharm hε (hcl x hx)
  obtain ⟨hIb, hrb⟩ := aux_inputs_classical_harmonic_lipschitz_reproducing hharm hε (hcl y hy)
  have hVx : u (toEuc x) = V x := by simp [hu]
  have hVy : u (toEuc y) = V y := by simp [hu]
  have hdiff : V x - V y = ∫ t, (radialKernelScaled d ε (t - toEuc x) -
      radialKernelScaled d ε (t - toEuc y)) * u t := by
    rw [← hVx, ← hVy, ← hra, ← hrb, ← integral_sub hIa hIb]
    congr 1
    funext t
    ring
  set M : ℝ := G * (ε ^ d)⁻¹ * ε⁻¹ * ‖(toEuc x : EuclideanSpace ℝ (Fin d)) - toEuc y‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hpt : ∀ t, |(radialKernelScaled d ε (t - toEuc x) - radialKernelScaled d ε (t - toEuc y)) *
      u t| ≤ S.indicator (fun t => M * |u t|) t := by
    intro t
    by_cases htS : t ∈ S
    · rw [Set.indicator_of_mem htS, abs_mul]
      have h := hGlip ε hε (t - toEuc x) (t - toEuc y)
      have hn : ‖(t - toEuc x) - (t - toEuc y)‖ = ‖(toEuc x : EuclideanSpace ℝ (Fin d)) - toEuc y‖ := by
        rw [sub_sub_sub_cancel_left, norm_sub_rev]
      rw [hn] at h
      exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
    · rw [Set.indicator_of_notMem htS, hKS x hx t htS, hKS y hy t htS]
      simp
  haveI : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ, hW]; exact measure_ball_lt_top⟩
  have hSmeas : MeasurableSet S := (measurableEmbedding_toEuc d).measurableSet_image.2 measurableSet_ball
  have hpre : (toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) ⁻¹' S = W :=
    Set.preimage_image_eq W toEuc.injective
  have hVint : IntegrableOn (fun x => |V x|) W volume := (hV.integrable (by norm_num)).abs
  have huint : IntegrableOn (fun t => |u t|) S volume := by
    have hcomp : ((fun t => |u t|) ∘
        (toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d))) = fun x => |V x| := by
      funext x
      simp [hu]
    rw [← (measurePreserving_toEuc d).integrableOn_comp_preimage (measurableEmbedding_toEuc d),
      hpre, hcomp]
    exact hVint
  have hind : Integrable (S.indicator (fun t => M * |u t|)) volume :=
    IntegrableOn.integrable_indicator
      (show IntegrableOn (fun t => M * |u t|) S volume from huint.const_mul M) hSmeas
  have htransfer : ∫ t in S, |u t| = ∫ x in W, |V x| := by
    have h := (measurePreserving_toEuc d).setIntegral_preimage_emb (measurableEmbedding_toEuc d)
      (fun t => |u t|) S
    rw [hpre] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_ball ?_
    intro x _
    simp [hu]
  have hWvol : (volume W).toReal = R ^ d := by
    rw [hW, Real.volume_pi_ball z (by positivity : 0 < R / 2), ENNReal.toReal_ofReal (by positivity),
      Fintype.card_fin]
    congr 1
    ring
  have hCS := aux_inputs_classical_harmonic_lipschitz_cs (W := W) measurableSet_ball
    (by rw [hW]; exact measure_ball_lt_top.ne) hV
  set N : ℝ := normalizedL2On W V with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hRd : 0 < R ^ d := by positivity
  have hVsq : ∫ x in W, (V x) ^ 2 = R ^ d * N ^ 2 := by
    have hN2 : N ^ 2 = (R ^ d)⁻¹ * ∫ x in W, (V x) ^ 2 := by
      rw [hN]
      unfold normalizedL2On Homogenization.volumeAverage
      rw [Real.sq_sqrt (mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
        (setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _)), hWvol]
    rw [hN2]
    field_simp
  have habsV : ∫ x in W, |V x| ≤ R ^ d * N := by
    have h0 : 0 ≤ ∫ x in W, |V x| := setIntegral_nonneg measurableSet_ball fun _ _ => abs_nonneg _
    have h1 : (∫ x in W, |V x|) ^ 2 ≤ (R ^ d * N) ^ 2 := by
      calc (∫ x in W, |V x|) ^ 2 ≤ (volume W).toReal * ∫ x in W, (V x) ^ 2 := hCS
        _ = (R ^ d * N) ^ 2 := by rw [hWvol, hVsq]; ring
    exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 h1
  have hmain : |V x - V y| ≤ M * (R ^ d * N) := by
    calc |V x - V y| = |∫ t, (radialKernelScaled d ε (t - toEuc x) -
          radialKernelScaled d ε (t - toEuc y)) * u t| := by rw [hdiff]
      _ ≤ ∫ t, |(radialKernelScaled d ε (t - toEuc x) - radialKernelScaled d ε (t - toEuc y)) *
          u t| := abs_integral_le_integral_abs
      _ ≤ ∫ t, S.indicator (fun t => M * |u t|) t :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) hind
            (Filter.Eventually.of_forall hpt)
      _ = M * ∫ t in S, |u t| := by
          rw [integral_indicator hSmeas, integral_const_mul]
      _ = M * ∫ x in W, |V x| := by rw [htransfer]
      _ ≤ M * (R ^ d * N) := mul_le_mul_of_nonneg_left habsV hM0
  have hfin : M * (R ^ d * N) =
      8 ^ (d + 1) * G * (‖(toEuc x : EuclideanSpace ℝ (Fin d)) - toEuc y‖ / R) * N := by
    have h8 : ((R / 8) ^ d)⁻¹ = 8 ^ d * (R ^ d)⁻¹ := by rw [div_pow, inv_div, div_eq_mul_inv]
    have h8' : (R / 8)⁻¹ = 8 * R⁻¹ := by rw [inv_div, div_eq_mul_inv]
    rw [hM, hεdef, h8, h8']
    field_simp
    ring
  have hxy : ‖(toEuc x : EuclideanSpace ℝ (Fin d)) - toEuc y‖ ≤ Real.sqrt d * dist x y := by
    have := aux_inputs_classical_harmonic_lipschitz_euc_le (x - y)
    rw [dist_eq_norm]
    simpa [map_sub] using this
  calc |V x - V y| ≤ M * (R ^ d * N) := hmain
    _ = 8 ^ (d + 1) * G * (‖(toEuc x : EuclideanSpace ℝ (Fin d)) - toEuc y‖ / R) * N := hfin
    _ ≤ 8 ^ (d + 1) * G * (Real.sqrt d * dist x y / R) * N := by
        apply mul_le_mul_of_nonneg_right _ hN0
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_of_nonneg_right hxy hR.le
    _ = 8 ^ (d + 1) * G * Real.sqrt d * (dist x y / R) * N := by ring

end Paper
