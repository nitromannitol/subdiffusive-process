module

public import SubdiffusiveProcess.Paper.tight_subharmonic
public import SubdiffusiveProcess.Paper.tight_lem_static
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Dyadic bracketing of a rational interval `[q, q'] ⊆ [1/2, 1]`: at some level `N` the grid
`1/2 + k/2^(N+1)` has consecutive points `q ≤ 1/2 + k/2^(N+1) < 1/2 + (k+1)/2^(N+1) ≤ q'`, with grid
spacing at least a quarter of `q' - q`. -/
lemma aux_tight_lem_subharmonic_bracket (q q' : ℚ) (hq : (1 : ℝ) / 2 ≤ q) (hqq' : (q : ℝ) < q')
    (hq' : (q' : ℝ) ≤ 1) :
    ∃ N k : ℕ, k < 2 ^ N ∧ (q : ℝ) ≤ 1 / 2 + (k : ℝ) / 2 ^ (N + 1) ∧
      1 / 2 + ((k : ℝ) + 1) / 2 ^ (N + 1) ≤ q' ∧ ((q' : ℝ) - q) / 4 ≤ 1 / 2 ^ (N + 1) := by
  set Δ : ℝ := (q' : ℝ) - q with hΔ
  have hΔpos : 0 < Δ := by rw [hΔ]; linarith
  have hΔle : Δ ≤ 1 / 2 := by rw [hΔ]; linarith
  have h1 : (1 : ℝ) ≤ 1 / Δ := by
    rw [le_div_iff₀ hΔpos]; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hΔ1 : Δ * 2 ^ n ≤ 1 := by
    rw [le_div_iff₀ hΔpos] at hn1; linarith
  have hΔ2 : 1 < Δ * 2 ^ (n + 1) := by
    rw [div_lt_iff₀ hΔpos] at hn2; linarith
  have hS : (2 : ℝ) ^ (n + 1 + 1) = 4 * 2 ^ n := by ring
  have hp : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
  have hΔ2' : 1 < ((q' : ℝ) - q) * (2 * 2 ^ n) := by rw [← hp, ← hΔ]; exact hΔ2
  have hSpos : (0 : ℝ) < 2 ^ (n + 1 + 1) := by positivity
  set k : ℕ := ⌈((q : ℝ) - 1 / 2) * 2 ^ (n + 1 + 1)⌉₊ with hk
  have hk_le : ((q : ℝ) - 1 / 2) * 2 ^ (n + 1 + 1) ≤ k := Nat.le_ceil _
  have hk_lt : (k : ℝ) < ((q : ℝ) - 1 / 2) * 2 ^ (n + 1 + 1) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (by linarith) hSpos.le)
  have h3 : 1 / 2 + ((k : ℝ) + 1) / 2 ^ (n + 1 + 1) ≤ q' := by
    have : ((k : ℝ) + 1) / 2 ^ (n + 1 + 1) < (q' : ℝ) - 1 / 2 := by
      rw [div_lt_iff₀ hSpos]
      rw [hS] at hk_lt ⊢
      linarith
    linarith
  refine ⟨n + 1, k, ?_, ?_, h3, ?_⟩
  · have h4 : ((k : ℝ) + 1) / 2 ^ (n + 1 + 1) ≤ 1 / 2 := by linarith
    rw [div_le_iff₀ hSpos] at h4
    have h5 : ((k : ℝ) + 1) ≤ 2 ^ (n + 1) := by
      rw [hS] at h4; linarith
    have h6 : (k : ℝ) < 2 ^ (n + 1) := by linarith
    exact_mod_cast h6
  · have : ((q : ℝ) - 1 / 2) ≤ (k : ℝ) / 2 ^ (n + 1 + 1) := by
      rw [le_div_iff₀ hSpos]; exact hk_le
    linarith
  · rw [div_le_div_iff₀ (by norm_num) hSpos]
    rw [hS]
    nlinarith [h2n]

/-- Gap comparison: a grid spacing `σ ≥ Δ/4` costs at most a factor `4^B`. -/
lemma aux_tight_lem_subharmonic_gap_const {δ σ Δ B K : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hσ : Δ / 4 ≤ σ) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    K * (δ * σ) ^ (-B) ≤ 4 ^ B * K * (δ * Δ) ^ (-B) := by
  have hx : 0 < δ * Δ / 4 := by positivity
  have hxy : δ * Δ / 4 ≤ δ * σ := by
    have := mul_le_mul_of_nonneg_left hσ hδ.le
    calc δ * Δ / 4 = δ * (Δ / 4) := by ring
      _ ≤ δ * σ := this
  have h1 : (δ * σ) ^ (-B) ≤ (δ * Δ / 4) ^ (-B) :=
    Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)
  have h2 : (δ * Δ / 4) ^ (-B) = 4 ^ B * (δ * Δ) ^ (-B) := by
    have : δ * Δ / 4 = (δ * Δ) * 4⁻¹ := by ring
    rw [this, Real.mul_rpow (by positivity : 0 ≤ δ * Δ) (by norm_num : (0 : ℝ) ≤ 4⁻¹),
      Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4) B,
      inv_inv, mul_comm]
  calc K * (δ * σ) ^ (-B) ≤ K * (4 ^ B * (δ * Δ) ^ (-B)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hK
    _ = 4 ^ B * K * (δ * Δ) ^ (-B) := by ring

section shift
variable {d : ℕ}

/-- `x + z ∈ ball z R ↔ x ∈ ball 0 R`. -/
lemma aux_tight_lem_subharmonic_preimage_ball (z : Fin d → ℝ) (R : ℝ) :
    (fun x : Fin d → ℝ => x + z) ⁻¹' Metric.ball z R = Metric.ball 0 R := by
  ext x
  simp [Metric.mem_ball, dist_eq_norm]

/-- Change of variables `x ↦ x + z` in a set lintegral over a ball. -/
lemma aux_tight_lem_subharmonic_lintegral_ball_shift (z : Fin d → ℝ) (R : ℝ)
    (f : (Fin d → ℝ) → ℝ≥0∞) :
    ∫⁻ x in Metric.ball z R, f x = ∫⁻ x in Metric.ball 0 R, f (x + z) := by
  have h := (measurePreserving_add_right (volume : Measure (Fin d → ℝ)) z).setLIntegral_comp_preimage_emb
    (Homeomorph.addRight z).measurableEmbedding f (Metric.ball z R)
  rw [aux_tight_lem_subharmonic_preimage_ball] at h
  exact h.symm

/-- The `H^{3/4}`-type energy is translation covariant on balls. -/
lemma aux_tight_lem_subharmonic_fE_shift (g : (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) (R : ℝ) :
    aux_tight_subharmonic_fE (fun x => g (x + z)) (Metric.ball 0 R) =
      aux_tight_subharmonic_fE g (Metric.ball z R) := by
  unfold aux_tight_subharmonic_fE aux_tight_subharmonic_gag
  rw [aux_tight_lem_subharmonic_lintegral_ball_shift z R
      (fun y => ENNReal.ofReal (g y ^ 2)),
    aux_tight_lem_subharmonic_lintegral_ball_shift z R]
  congr 1
  · refine lintegral_congr fun y => ?_
    rw [aux_tight_lem_subharmonic_lintegral_ball_shift z R]
    refine lintegral_congr fun y' => ?_
    rw [add_sub_add_right_eq_sub]

end shift

section cutfam
variable {d : ℕ}

lemma aux_tight_lem_subharmonic_map_sub (z : Fin d → ℝ) :
    Measure.map (fun x : Fin d → ℝ => x - z) (volume : Measure (Fin d → ℝ)) = volume := by
  have := Measure.IsAddRightInvariant.map_add_right_eq_self (μ := (volume : Measure (Fin d → ℝ))) (-z)
  simpa [sub_eq_add_neg] using this

end cutfam

section cutfam
variable {d : ℕ}

/-- The cutoff family of the Moser iteration at the centre `z` of a concentric pair of cubes of
radii `δ/2 ⋐ δ` inside the cube `ball cB rB` on which the subsolution lives: the dyadic family
`hcut` between consecutive radii `δ(1/2 + k/2^{n+1})` is bracketed between any two rationals of
`[1/2, 1]`, at the price `4^B` in the constant, and the Caccioppoli–coercivity inequality is
obtained from the coercivity on the whole cube `ball cB rB`.  The result is stated after the
translation `x ↦ x + z` to the origin, as required by `aux_tight_subharmonic_moser_iter`
(`ρ0 = 2δ`, `q₁ = 1/2`, `q₂ = 1`). -/
lemma aux_tight_lem_subharmonic_cutfam
    {A : SpatialCoordinates d → ℝ} (hA : Continuous A) (hApos : ∀ x, 0 < A x)
    {cB : SpatialCoordinates d} {rB : ℝ} (hrB : 0 < rB)
    {z : SpatialCoordinates d} {δ : ℝ} (hδ : 0 < δ)
    (hzV : Metric.ball z δ ⊆ Metric.ball cB rB) {K B : ℝ} (hK : 1 ≤ K) (hB : 0 ≤ B)
    (hcoer : ∀ v : Homogenization.H10Function (Metric.ball cB rB),
        (∫⁻ x in Metric.ball cB rB, ∫⁻ y in Metric.ball cB rB,
            ENNReal.ofReal ((v.toFun x - v.toFun y) ^ 2) /
              ENNReal.ofReal (‖x - y‖ ^ ((d : ℝ) + 3 / 2))) +
          ∫⁻ x in Metric.ball cB rB, ENNReal.ofReal (v.toFun x ^ 2) ≤
        ENNReal.ofReal K *
          ∫⁻ x in Metric.ball cB rB,
            ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)))
    (hcut : ∀ n k : ℕ, k < 2 ^ n → ∀ R1 R2 : ℝ, R1 = δ * (1 / 2 + (k : ℝ) / 2 ^ (n + 1)) →
        R2 = δ * (1 / 2 + ((k : ℝ) + 1) / 2 ^ (n + 1)) →
        ∃ chi : Homogenization.H10Function (Metric.ball z R2),
          (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
          (∀ x ∈ Metric.ball z R1, chi.toFun x = 1) ∧
          tsupport chi.toFun ⊆ Metric.ball z R2 ∧
          ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
            ∫⁻ y in Metric.ball x r ∩ Metric.ball z R2,
                ENNReal.ofReal (A y * Homogenization.vecDot (chi.grad y) (chi.grad y)) ≤
              ENNReal.ofReal (K * (δ / 2 ^ (n + 1)) ^ (-B) * r ^ ((d : ℝ) - 1 / 2)))
    (w : Homogenization.H1Function (Metric.ball cB rB)) (hw0 : ∀ x, 0 ≤ w.toFun x) {Mw : ℝ}
    (hwM : ∀ x, w.toFun x ≤ Mw)
    (hsub : SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn A (Metric.ball cB rB) w)
    (W : SpatialCoordinates d → ℝ) (hWm : Measurable W)
    (hWae : W =ᵐ[volume.restrict (Metric.ball cB rB)] w.toFun) (s : ℝ) (hs : 1 ≤ s) :
    aux_tight_subharmonic_CutFam (fun x => W (x + z) ^ s) ((4 : ℝ) ^ B * K) B (2 * δ)
      (K * (8 * s ^ 2 + 2)) (1 / 2) 1 := by
  intro q q' hq hqq' hq'
  have hq_r : (1 : ℝ) / 2 ≤ q := by
    have h := (Rat.cast_le (K := ℝ)).2 hq
    push_cast at h
    exact h
  have hqq_r : (q : ℝ) < q' := by exact_mod_cast hqq'
  have hq'_r : (q' : ℝ) ≤ 1 := by exact_mod_cast hq'
  obtain ⟨N, k, hk, hk1, hk2, hσ⟩ := aux_tight_lem_subharmonic_bracket q q' hq_r hqq_r hq'_r
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, R1 = δ * (1 / 2 + (k : ℝ) / 2 ^ (N + 1)) := ⟨_, rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℝ, R2 = δ * (1 / 2 + ((k : ℝ) + 1) / 2 ^ (N + 1)) := ⟨_, rfl⟩
  obtain ⟨chi, hchi01, hchi1, hchisupp, hchien⟩ := hcut N k hk R1 R2 hR1 hR2
  have hR2q : R2 ≤ δ * q' := by rw [hR2]; exact mul_le_mul_of_nonneg_left hk2 hδ.le
  have hR2δ : R2 ≤ δ := hR2q.trans (by nlinarith)
  have hR1q : δ * q ≤ R1 := by rw [hR1]; exact mul_le_mul_of_nonneg_left hk1 hδ.le
  have hUV : Metric.ball z R2 ⊆ Metric.ball cB rB := (Metric.ball_subset_ball hR2δ).trans hzV
  have hqδ : δ * q ≤ δ := by nlinarith
  have hVq : Metric.ball z (δ * q) ⊆ Metric.ball cB rB := (Metric.ball_subset_ball hqδ).trans hzV
  have hmsub : Measurable (fun x : SpatialCoordinates d => x - z) := measurable_sub_const z
  have hdm := aux_tight_subharmonic_dens_aemeas (U := Metric.ball z R2) hA chi.toH1Function
  set Γz : Measure (SpatialCoordinates d) :=
    (volume.restrict (Metric.ball z R2)).withDensity
      (fun y => ENNReal.ofReal (A y * Homogenization.vecDot (chi.grad y) (chi.grad y))) with hΓz
  have hΓac : Γz ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hpre : ∀ (x : SpatialCoordinates d) (ρ : ℝ),
      (fun y : SpatialCoordinates d => y - z) ⁻¹' Metric.ball x ρ = Metric.ball (x + z) ρ := by
    intro x ρ; ext y
    have e : y - z - x = y - (x + z) := by abel
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, e]
  refine ⟨Γz.map (fun y => y - z), ?_, ?_, ?_, ?_⟩
  · have := hΓac.map hmsub
    rwa [aux_tight_lem_subharmonic_map_sub] at this
  · rw [Measure.map_apply hmsub Metric.isOpen_ball.measurableSet.compl]
    have h1 : (fun y : SpatialCoordinates d => y - z) ⁻¹' (Metric.ball 0 (2 * δ * (q' : ℝ) / 2))ᶜ
        ⊆ (Metric.ball z R2)ᶜ := by
      intro y hy hy2
      apply hy
      have : y - z ∈ Metric.ball (0 : SpatialCoordinates d) R2 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hy2
      exact Metric.ball_subset_ball (by nlinarith) this
    refine measure_mono_null h1 ?_
    rw [hΓz, withDensity_apply _ Metric.isOpen_ball.measurableSet.compl,
      Measure.restrict_restrict Metric.isOpen_ball.measurableSet.compl, Set.compl_inter_self,
      Measure.restrict_empty, lintegral_zero_measure]
  · intro x ρ' hρ' hρ'1
    rw [Measure.map_apply hmsub Metric.isOpen_ball.measurableSet, hpre, hΓz,
      withDensity_apply _ Metric.isOpen_ball.measurableSet,
      Measure.restrict_restrict Metric.isOpen_ball.measurableSet]
    refine (hchien (x + z) ρ' hρ' hρ'1).trans (ENNReal.ofReal_le_ofReal ?_)
    have hΔ : 0 < (q' : ℝ) - q := by linarith
    have hnum := aux_tight_lem_subharmonic_gap_const (K := K) (B := B) (σ := 1 / 2 ^ (N + 1))
      hδ hΔ hσ hB (by linarith)
    have e1 : δ / 2 ^ (N + 1) = δ * (1 / 2 ^ (N + 1)) := by ring
    have e2 : 2 * δ * ((q' : ℝ) - q) / 2 = δ * ((q' : ℝ) - q) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hnum (Real.rpow_nonneg hρ'.le _)
  · have hCC := aux_tight_subharmonic_cutoff_coercive
      (Homogenization.isOpenBoundedConvexDomain_ball cB hrB) hUV hA hApos w hw0 hwM hsub hs
      (Kc := K) (by linarith) hcoer chi hchisupp
    have hL : aux_tight_subharmonic_fE (fun x => W (x + z) ^ s)
          (Metric.ball (0 : SpatialCoordinates d) (2 * δ * (q : ℝ) / 2)) =
        aux_tight_subharmonic_fE (fun x => chi.toFun x * w.toFun x ^ s)
          (Metric.ball z (δ * q)) := by
      have h := aux_tight_lem_subharmonic_fE_shift (fun y => W y ^ s) z (2 * δ * (q : ℝ) / 2)
      rw [show 2 * δ * (q : ℝ) / 2 = δ * q by ring] at h ⊢
      refine h.trans ?_
      refine aux_tight_subharmonic_gag_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hVq hWae,
        ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxm
      simp only [hx, hchi1 x (Metric.ball_subset_ball hR1q hxm), one_mul]
    have hR : ∫⁻ x, ENNReal.ofReal ((W (x + z) ^ s) ^ 2) ∂(Γz.map (fun y => y - z)) =
        ∫⁻ x in Metric.ball z R2, ENNReal.ofReal
          (w.toFun x ^ (2 * s) * (A x * Homogenization.vecDot (chi.grad x) (chi.grad x))) := by
      have hfm : Measurable (fun x : SpatialCoordinates d => ENNReal.ofReal ((W (x + z) ^ s) ^ 2)) :=
        ENNReal.measurable_ofReal.comp (((hWm.comp (measurable_add_const z)).pow_const s).pow_const 2)
      rw [lintegral_map hfm hmsub]
      simp only [sub_add_cancel]
      have hgm : AEMeasurable (fun x => ENNReal.ofReal ((W x ^ s) ^ 2))
          (volume.restrict (Metric.ball z R2)) :=
        (ENNReal.measurable_ofReal.comp ((hWm.pow_const s).pow_const 2)).aemeasurable
      rw [hΓz, lintegral_withDensity_eq_lintegral_mul₀ hdm hgm]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hUV hWae] with x hx
      have hvd : 0 ≤ A x * Homogenization.vecDot (chi.grad x) (chi.grad x) :=
        mul_nonneg (hApos x).le (Homogenization.vecNormSq_nonneg _)
      simp only [Pi.mul_apply, hx]
      rw [← ENNReal.ofReal_mul hvd, ← Real.rpow_natCast, ← Real.rpow_mul (hw0 x), mul_comm s,
        mul_comm]
      norm_num
    rw [hL, hR]
    exact (aux_tight_subharmonic_fE_mono _ hVq).trans hCC

end cutfam

section det
variable {d : ℕ}

/-- The translated speed measure is absolutely continuous, and dominates Lebesgue measure when the
density is positive. -/
lemma aux_tight_lem_subharmonic_speed_ac {b : SpatialCoordinates d → ℝ} (hb : Continuous b)
    (hbpos : ∀ x, 0 < b x) (z : SpatialCoordinates d) :
    (volume.withDensity (fun y => ENNReal.ofReal (b y))).map (fun y : SpatialCoordinates d => y - z) ≪
        volume ∧
      (volume : Measure (SpatialCoordinates d)) ≪
        (volume.withDensity (fun y => ENNReal.ofReal (b y))).map
          (fun y : SpatialCoordinates d => y - z) := by
  have hmsub : Measurable (fun x : SpatialCoordinates d => x - z) := measurable_sub_const z
  have hbm : Measurable fun y => ENNReal.ofReal (b y) := ENNReal.measurable_ofReal.comp hb.measurable
  constructor
  · have := (withDensity_absolutelyContinuous (volume : Measure (SpatialCoordinates d))
      (fun y => ENNReal.ofReal (b y))).map hmsub
    rwa [aux_tight_lem_subharmonic_map_sub] at this
  · have h1 : (volume : Measure (SpatialCoordinates d)) ≪
        volume.withDensity (fun y => ENNReal.ofReal (b y)) :=
      withDensity_absolutelyContinuous' hbm.aemeasurable
        (Eventually.of_forall fun x => (ENNReal.ofReal_pos.2 (hbpos x)).ne')
    have h2 := h1.map hmsub
    rwa [aux_tight_lem_subharmonic_map_sub] at h2

end det

section det
variable {d : ℕ}

lemma aux_tight_lem_subharmonic_preimage_ball_sub (x z : SpatialCoordinates d) (ρ : ℝ) :
    (fun y : SpatialCoordinates d => y - z) ⁻¹' Metric.ball x ρ = Metric.ball (x + z) ρ := by
  ext y
  have e : y - z - x = y - (x + z) := by abel
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, e]

/-- **Deterministic core of `tight:lem-subharmonic` in the local normalization.** -/
lemma aux_tight_lem_subharmonic_det (hd : 1 ≤ d) (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ) :
    ∃ C Bm : ℝ, 0 < C ∧ 0 < Bm ∧
      ∀ (b A : SpatialCoordinates d → ℝ) (K : ℝ) (cB : SpatialCoordinates d) (rB : ℝ)
        (z : SpatialCoordinates d),
        Continuous b → Continuous A → (∀ x, 0 < b x) → (∀ x, 0 < A x) → 1 ≤ K → 0 < rB →
        Metric.ball z δ ⊆ Metric.ball cB rB →
        (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          Metric.ball x r ⊆ Metric.ball cB rB →
            ENNReal.ofReal (K⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
                volume.withDensity (fun y => ENNReal.ofReal (b y)) (Metric.ball x r) ∧
              volume.withDensity (fun y => ENNReal.ofReal (b y)) (Metric.ball x r) ≤
                ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2))) →
        (∀ v : Homogenization.H10Function (Metric.ball cB rB),
          (∫⁻ x in Metric.ball cB rB, ∫⁻ y in Metric.ball cB rB,
              ENNReal.ofReal ((v.toFun x - v.toFun y) ^ 2) /
                ENNReal.ofReal (‖x - y‖ ^ ((d : ℝ) + 3 / 2))) +
            ∫⁻ x in Metric.ball cB rB, ENNReal.ofReal (v.toFun x ^ 2) ≤
          ENNReal.ofReal K *
            ∫⁻ x in Metric.ball cB rB,
              ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x))) →
        (∀ n k : ℕ, k < 2 ^ n → ∀ R1 R2 : ℝ, R1 = δ * (1 / 2 + (k : ℝ) / 2 ^ (n + 1)) →
          R2 = δ * (1 / 2 + ((k : ℝ) + 1) / 2 ^ (n + 1)) →
          ∃ chi : Homogenization.H10Function (Metric.ball z R2),
            (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
            (∀ x ∈ Metric.ball z R1, chi.toFun x = 1) ∧
            tsupport chi.toFun ⊆ Metric.ball z R2 ∧
            ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              ∫⁻ y in Metric.ball x r ∩ Metric.ball z R2,
                  ENNReal.ofReal (A y * Homogenization.vecDot (chi.grad y) (chi.grad y)) ≤
                ENNReal.ofReal (K * (δ / 2 ^ (n + 1)) ^ (-B) * r ^ ((d : ℝ) - 1 / 2))) →
        ∀ w : Homogenization.H1Function (Metric.ball cB rB),
          (∀ x, 0 ≤ w.toFun x) → (∃ Mw : ℝ, ∀ x, w.toFun x ≤ Mw) →
          SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn A (Metric.ball cB rB) w →
          ∀ᵐ x ∂(volume.restrict (Metric.ball z (δ / 2))),
            ENNReal.ofReal (w.toFun x) ≤ ENNReal.ofReal (C * K ^ Bm) *
              (∫⁻ y in Metric.ball cB rB, ENNReal.ofReal (w.toFun y ^ 2 * b y)) ^ (1 / 2 : ℝ) := by
  obtain ⟨C0, Bm0, hC0, hBm0, hiter⟩ := aux_tight_subharmonic_moser_iter (d := d) hd B (2 * δ) hB
    (by positivity) (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C0 * ((4 : ℝ) ^ B) ^ Bm0, 2 * Bm0, by positivity, by positivity, ?_⟩
  intro b A K cB rB z hb hA hbpos hApos hK hrB hzV hmass hcoer hcut w hw0 hwbdd hsub
  obtain ⟨Mw, hwM⟩ := hwbdd
  obtain ⟨W, hWm, hW0, hWM, hWae⟩ :=
    aux_tight_subharmonic_meas_mod w.toFun w.memL2.aestronglyMeasurable hw0 hwM
  have hK0 : 0 ≤ K := by linarith
  have h4B : (1 : ℝ) ≤ (4 : ℝ) ^ B := Real.one_le_rpow (by norm_num) hB.le
  set K1 : ℝ := (4 : ℝ) ^ B * K with hK1def
  have hK1 : 1 ≤ K1 := one_le_mul_of_one_le_of_one_le h4B hK
  have hKK1 : K ≤ K1 := le_mul_of_one_le_left hK0 h4B
  have hmsub : Measurable (fun x : SpatialCoordinates d => x - z) := measurable_sub_const z
  have hbm : Measurable fun y => ENNReal.ofReal (b y) :=
    ENNReal.measurable_ofReal.comp hb.measurable
  set μb : Measure (SpatialCoordinates d) := volume.withDensity (fun y => ENNReal.ofReal (b y))
    with hμb
  set μz : Measure (SpatialCoordinates d) := μb.map (fun y : SpatialCoordinates d => y - z)
    with hμz
  obtain ⟨hac, hac'⟩ := aux_tight_lem_subharmonic_speed_ac hb hbpos z
  have hcutW : ∀ s : ℝ, 1 ≤ s → aux_tight_subharmonic_CutFam (fun x => W (x + z) ^ s) K1 B (2 * δ)
      (K * (8 * s ^ 2 + 2)) (1 / 2) 1 := fun s hs =>
    aux_tight_lem_subharmonic_cutfam hA hApos hrB hδ hzV hK hB.le hcoer hcut w hw0 hwM hsub W hWm
      hWae s hs
  have hmassW : aux_tight_subharmonic_MassBd μz K1 (2 * δ / 2) := by
    intro x ρ' hρ' hρ'1 hxsub
    have hpre := aux_tight_lem_subharmonic_preimage_ball_sub x z ρ'
    have hpre0 := aux_tight_lem_subharmonic_preimage_ball_sub (0 : SpatialCoordinates d) z (2 * δ / 2)
    have hball : Metric.ball (x + z) ρ' ⊆ Metric.ball cB rB := by
      have h1 : Metric.ball (x + z) ρ' ⊆ Metric.ball ((0 : SpatialCoordinates d) + z) (2 * δ / 2) := by
        rw [← hpre, ← hpre0]
        exact Set.preimage_mono hxsub
      refine h1.trans (Set.Subset.trans ?_ hzV)
      rw [zero_add, show 2 * δ / 2 = δ by ring]
    have hmz : μz (Metric.ball x ρ') = μb (Metric.ball (x + z) ρ') := by
      rw [hμz, Measure.map_apply hmsub Metric.isOpen_ball.measurableSet, hpre]
    rw [hmz]
    obtain ⟨hlo, hhi⟩ := hmass (x + z) ρ' hρ' hρ'1 hball
    refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) hlo, hhi.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    · exact mul_le_mul_of_nonneg_right (inv_anti₀ (by linarith) hKK1)
        (Real.rpow_nonneg hρ'.le _)
    · exact mul_le_mul_of_nonneg_right hKK1 (Real.rpow_nonneg hρ'.le _)
  have hWz : Measurable (fun x : SpatialCoordinates d => W (x + z)) :=
    hWm.comp (measurable_add_const z)
  have hh := hiter μz (fun x => W (x + z)) Mw K1 K hWz (fun x => hW0 _) (fun x => hWM _) hK1 hK
    hac hmassW hcutW
  clear hiter hcutW
  have e1 : (2 * δ * (((1 / 2 : ℚ)) : ℝ) / 2) = δ / 2 := by push_cast; ring
  have e2 : (2 * δ * (((1 : ℚ)) : ℝ) / 2) = δ := by push_cast; ring
  rw [e1, e2] at hh
  have hgm2 : Measurable (fun y : SpatialCoordinates d => ENNReal.ofReal (W y ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hWm.pow_const 2)
  have hI : (∫⁻ x in Metric.ball (0 : SpatialCoordinates d) δ, ENNReal.ofReal (W (x + z) ^ 2) ∂μz) ≤
      ∫⁻ y in Metric.ball cB rB, ENNReal.ofReal (w.toFun y ^ 2 * b y) := by
    have hfm : Measurable (fun x : SpatialCoordinates d => ENNReal.ofReal (W (x + z) ^ 2)) :=
      ENNReal.measurable_ofReal.comp (hWz.pow_const 2)
    rw [hμz, setLIntegral_map Metric.isOpen_ball.measurableSet hfm hmsub]
    have hpre0 := aux_tight_lem_subharmonic_preimage_ball_sub (0 : SpatialCoordinates d) z δ
    rw [hpre0, zero_add]
    simp only [sub_add_cancel]
    rw [hμb, setLIntegral_withDensity_eq_setLIntegral_mul volume hbm hgm2
      Metric.isOpen_ball.measurableSet]
    calc _ = ∫⁻ y in Metric.ball z δ, ENNReal.ofReal (w.toFun y ^ 2 * b y) := by
            refine lintegral_congr_ae ?_
            filter_upwards [ae_restrict_of_ae_restrict_of_subset hzV hWae] with y hy
            simp only [Pi.mul_apply, hy]
            rw [← ENNReal.ofReal_mul (hbpos y).le, mul_comm]
      _ ≤ _ := lintegral_mono_set hzV
  have hac0 : (volume.restrict (Metric.ball (0 : SpatialCoordinates d) (δ / 2))) ≪
      μz.restrict (Metric.ball (0 : SpatialCoordinates d) (δ / 2)) := hac'.restrict _
  have h1 := hac0.ae_le hh
  have hmp : MeasurePreserving (fun y : SpatialCoordinates d => y - z) volume volume :=
    measurePreserving_sub_right volume z
  have hme : MeasurableEmbedding (fun y : SpatialCoordinates d => y - z) :=
    (Homeomorph.subRight z).measurableEmbedding
  have hmp' := hmp.restrict_preimage_emb hme (Metric.ball (0 : SpatialCoordinates d) (δ / 2))
  have hpre1 := aux_tight_lem_subharmonic_preimage_ball_sub (0 : SpatialCoordinates d) z (δ / 2)
  rw [hpre1, zero_add] at hmp'
  have h2 := hmp'.quasiMeasurePreserving.ae h1
  have hsubz : Metric.ball z (δ / 2) ⊆ Metric.ball cB rB :=
    (Metric.ball_subset_ball (by linarith)).trans hzV
  have hconst : C0 * (K1 * K) ^ Bm0 = C0 * ((4 : ℝ) ^ B) ^ Bm0 * K ^ (2 * Bm0) := by
    have h : K1 * K = (4 : ℝ) ^ B * K ^ (2 : ℝ) := by
      rw [hK1def, Real.rpow_two]; ring
    rw [h, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hK0]
    ring
  filter_upwards [h2, ae_restrict_of_ae_restrict_of_subset hsubz hWae] with y hy hyW
  simp only [sub_add_cancel] at hy
  rw [← hyW]
  refine hy.trans ?_
  rw [hconst]
  exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hI (by norm_num))

end det

section glue
variable {d : ℕ}

/-- Weak gradients only see the class of the function almost everywhere. -/
lemma aux_tight_lem_subharmonic_hasWeakGradient_congr {U : Set (SpatialCoordinates d)}
    {u u' : SpatialCoordinates d → ℝ} {Du : SpatialCoordinates d → SpatialCoordinates d}
    (h : Homogenization.HasWeakGradientOn U u Du) (huu' : u' =ᵐ[volume.restrict U] u) :
    Homogenization.HasWeakGradientOn U u' Du := by
  intro i φ hφ hc hs
  rw [← h i φ hφ hc hs]
  exact integral_congr_ae (huu'.mono fun x hx => by simp only [hx])

/-- A nonnegative bounded `H¹` function (in the almost-everywhere sense) has an everywhere
nonnegative, everywhere bounded modification with the same gradient. -/
lemma aux_tight_lem_subharmonic_regularize {V : Set (SpatialCoordinates d)}
    (w : Homogenization.H1Function V) {Mw : ℝ}
    (hw0 : ∀ᵐ x ∂(volume.restrict V), 0 ≤ w.toFun x)
    (hwM : ∀ᵐ x ∂(volume.restrict V), w.toFun x ≤ Mw) :
    ∃ w' : Homogenization.H1Function V, w'.grad = w.grad ∧
      w'.toFun =ᵐ[volume.restrict V] w.toFun ∧ (∀ x, 0 ≤ w'.toFun x) ∧
      ∀ x, w'.toFun x ≤ max 0 Mw := by
  have hae : (fun x => max 0 (min Mw (w.toFun x))) =ᵐ[volume.restrict V] w.toFun := by
    filter_upwards [hw0, hwM] with x h0 hM
    rw [min_eq_right hM, max_eq_right h0]
  refine ⟨{ toFun := fun x => max 0 (min Mw (w.toFun x))
            grad := w.grad
            memL2 := w.memL2.ae_eq hae.symm
            gradMemL2 := w.gradMemL2
            hasWeakGradient :=
              aux_tight_lem_subharmonic_hasWeakGradient_congr w.hasWeakGradient hae }, rfl, hae,
    fun x => le_max_left _ _, fun x => max_le_max le_rfl (min_le_left _ _)⟩

/-- The `H¹` coercivity of `tight:lem-static` (level `n = 0`, `k = 2⁰`) on the outer cube of a pair. -/
lemma aux_tight_lem_subharmonic_coer_of_est {p : ℕ} {b A : SpatialCoordinates d → ℝ}
    {y0 : SpatialCoordinates d} {ρ0 : ℝ} {c : Fin p → SpatialCoordinates d} {s0 s1 : Fin p → ℝ}
    {K B : ℝ} (h : aux_tight_lem_static_estimates b A y0 ρ0 c s0 s1 K B) (i : Fin p) :
    ∀ v : Homogenization.H10Function (Metric.ball (c i) (s1 i / 2)),
      (∫⁻ x in Metric.ball (c i) (s1 i / 2), ∫⁻ y in Metric.ball (c i) (s1 i / 2),
          ENNReal.ofReal ((v.toFun x - v.toFun y) ^ 2) /
            ENNReal.ofReal (‖x - y‖ ^ ((d : ℝ) + 3 / 2))) +
        ∫⁻ x in Metric.ball (c i) (s1 i / 2), ENNReal.ofReal (v.toFun x ^ 2) ≤
      ENNReal.ofReal K *
        ∫⁻ x in Metric.ball (c i) (s1 i / 2),
          ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)) := by
  have := (h.2.1 i 0 1 (by norm_num)).2
  have e : ((1 - ((1 : ℕ) : ℝ) / 2 ^ 0) * s0 i + (((1 : ℕ) : ℝ) / 2 ^ 0) * s1 i) / 2 = s1 i / 2 := by
    norm_num
  rw [e] at this
  simpa using this

end glue

section glue
variable {d : ℕ}

/-- The harmonic cutoffs of `tight:lem-static` on a pair with sides `δ < 2δ`, in the dyadic
parametrisation used by the Moser iteration. -/
lemma aux_tight_lem_subharmonic_cut_of_est {p : ℕ} {b A : SpatialCoordinates d → ℝ}
    {y0 : SpatialCoordinates d} {ρ0 : ℝ} {c : Fin p → SpatialCoordinates d} {s0 s1 : Fin p → ℝ}
    {K B : ℝ} (h : aux_tight_lem_static_estimates b A y0 ρ0 c s0 s1 K B) (i : Fin p) {δ : ℝ}
    {z : SpatialCoordinates d} (hz : c i = z) (h0 : s0 i = δ) (h1 : s1 i = 2 * δ) :
    ∀ n k : ℕ, k < 2 ^ n → ∀ R1 R2 : ℝ, R1 = δ * (1 / 2 + (k : ℝ) / 2 ^ (n + 1)) →
      R2 = δ * (1 / 2 + ((k : ℝ) + 1) / 2 ^ (n + 1)) →
      ∃ chi : Homogenization.H10Function (Metric.ball z R2),
        (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
        (∀ x ∈ Metric.ball z R1, chi.toFun x = 1) ∧
        tsupport chi.toFun ⊆ Metric.ball z R2 ∧
        ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          ∫⁻ y in Metric.ball x r ∩ Metric.ball z R2,
              ENNReal.ofReal (A y * Homogenization.vecDot (chi.grad y) (chi.grad y)) ≤
            ENNReal.ofReal (K * (δ / 2 ^ (n + 1)) ^ (-B) * r ^ ((d : ℝ) - 1 / 2)) := by
  intro n k hk R1 R2 hR1 hR2
  have := h.2.2 i n k hk
  rw [h0, h1, hz] at this
  have e1 : ((1 - (k : ℝ) / 2 ^ n) * δ + ((k : ℝ) / 2 ^ n) * (2 * δ)) / 2 = R1 := by
    rw [hR1]; field_simp; ring
  have e2 : ((1 - ((k + 1 : ℕ) : ℝ) / 2 ^ n) * δ + (((k + 1 : ℕ) : ℝ) / 2 ^ n) * (2 * δ)) / 2 = R2 := by
    rw [hR2]; push_cast; field_simp; ring
  have e3 : (2 * δ - δ) / 2 ^ n / 2 = δ / 2 ^ (n + 1) := by
    rw [pow_succ]; field_simp; ring
  rw [e1, e2, e3] at this
  simpa using this

/-- Compactness: finitely many small balls around points of `closedBall cV' (sV'/2)` cover
`ball cV' (sV'/2)`, and their doubles stay inside `ball cV (sV/2)`. -/
lemma aux_tight_lem_subharmonic_cover {cV cV' : SpatialCoordinates d} {sV sV' : ℝ}
    (hVV' : Metric.closedBall cV' (sV' / 2) ⊆ Metric.ball cV (sV / 2)) :
    ∃ (δ : ℝ) (n : ℕ) (f : Fin n → SpatialCoordinates d), 0 < δ ∧
      (∀ i, Metric.ball (f i) δ ⊆ Metric.ball cV (sV / 2)) ∧
      Metric.ball cV' (sV' / 2) ⊆ ⋃ i, Metric.ball (f i) (δ / 2) := by
  have hK : IsCompact (Metric.closedBall cV' (sV' / 2)) := isCompact_closedBall _ _
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open Metric.isOpen_ball hVV'
  obtain ⟨t, htK, htfin, hcov⟩ := hK.finite_cover_balls (half_pos hδ)
  obtain ⟨n, f, hf⟩ := htfin.fin_embedding
  refine ⟨δ, n, f, hδ, fun i => ?_, ?_⟩
  · have hi : f i ∈ Metric.closedBall cV' (sV' / 2) := htK (hf ▸ Set.mem_range_self i)
    exact (Metric.ball_subset_thickening hi δ).trans hth
  · intro x hx
    have hx' := hcov (Metric.ball_subset_closedBall hx)
    simp only [Set.mem_iUnion] at hx' ⊢
    obtain ⟨y, hy, hxy⟩ := hx'
    rw [← hf] at hy
    obtain ⟨i, rfl⟩ := hy
    exact ⟨i, hxy⟩

end glue

section glue
variable {d : ℕ}

/-- From the static estimates on the finite family of concentric pairs (the outer cube `V` itself
and pairs `δ < 2δ` centred at the points `f i` covering `V'`) to the local bound on `V'`. -/
lemma aux_tight_lem_subharmonic_of_est (hd : 1 ≤ d) (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (cV : SpatialCoordinates d) (sV : ℝ) (hsV : 0 < sV) (n : ℕ) (f : Fin n → SpatialCoordinates d)
    (hfV : ∀ i, Metric.ball (f i) δ ⊆ Metric.ball cV (sV / 2)) :
    ∃ C Bm : ℝ, 0 < C ∧ 0 < Bm ∧
      ∀ (b A : SpatialCoordinates d → ℝ) (K : ℝ), Continuous b → Continuous A →
        (∀ x, 0 < b x) → (∀ x, 0 < A x) → 1 ≤ K →
        aux_tight_lem_static_estimates b A cV sV
          (Fin.cons cV f : Fin (n + 1) → SpatialCoordinates d)
          (Fin.cons (sV / 2) (fun _ => δ) : Fin (n + 1) → ℝ)
          (Fin.cons sV (fun _ => 2 * δ) : Fin (n + 1) → ℝ) K B →
        ∀ w : Homogenization.H1Function (Metric.ball cV (sV / 2)),
          (∀ᵐ x ∂(volume.restrict (Metric.ball cV (sV / 2))), 0 ≤ w.toFun x) →
          (∃ Mw : ℝ, ∀ᵐ x ∂(volume.restrict (Metric.ball cV (sV / 2))), w.toFun x ≤ Mw) →
          SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn A (Metric.ball cV (sV / 2)) w →
          ∀ᵐ x ∂(volume.restrict (⋃ i, Metric.ball (f i) (δ / 2))),
            ENNReal.ofReal (w.toFun x) ≤ ENNReal.ofReal (C * K ^ Bm) *
              (∫⁻ y in Metric.ball cV (sV / 2), ENNReal.ofReal (w.toFun y ^ 2 * b y)) ^
                (1 / 2 : ℝ) := by
  obtain ⟨C, Bm, hC, hBm, hdet⟩ := aux_tight_lem_subharmonic_det hd B δ hB hδ
  refine ⟨C, Bm, hC, hBm, ?_⟩
  intro b A K hb hA hbpos hApos hK hest w hw0 hwM hsub
  obtain ⟨Mw, hwM⟩ := hwM
  obtain ⟨w', hgrad, hae, hw'0, hw'M⟩ := aux_tight_lem_subharmonic_regularize w hw0 hwM
  have hsub' : SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn A (Metric.ball cV (sV / 2)) w' := by
    intro psi hpsi
    have := hsub psi hpsi
    simpa [hgrad] using this
  have hcoer := aux_tight_lem_subharmonic_coer_of_est hest 0
  simp only [Fin.cons_zero] at hcoer
  have hmass : ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
      Metric.ball x r ⊆ Metric.ball cV (sV / 2) →
        ENNReal.ofReal (K⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
            volume.withDensity (fun y => ENNReal.ofReal (b y)) (Metric.ball x r) ∧
          volume.withDensity (fun y => ENNReal.ofReal (b y)) (Metric.ball x r) ≤
            ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2)) := fun x r hr hr1 hsub =>
    hest.1 x r hr hr1 hsub
  rw [ae_restrict_iUnion_iff]
  intro i
  have hcut := aux_tight_lem_subharmonic_cut_of_est hest i.succ (δ := δ) (z := f i) (by simp) (by simp)
    (by simp)
  have h := hdet b A K cV (sV / 2) (f i) hb hA hbpos hApos hK (half_pos hsV) (hfV i) hmass hcoer
    hcut w' hw'0 ⟨_, hw'M⟩ hsub'
  have hsubz : Metric.ball (f i) (δ / 2) ⊆ Metric.ball cV (sV / 2) :=
    (Metric.ball_subset_ball (by linarith)).trans (hfV i)
  have hI : ∫⁻ y in Metric.ball cV (sV / 2), ENNReal.ofReal (w'.toFun y ^ 2 * b y) =
      ∫⁻ y in Metric.ball cV (sV / 2), ENNReal.ofReal (w.toFun y ^ 2 * b y) :=
    lintegral_congr_ae (hae.mono fun y hy => by simp only [hy])
  rw [hI] at h
  filter_upwards [h, ae_restrict_of_ae_restrict_of_subset hsubz hae] with x hx hxw
  rwa [hxw] at hx

end glue

section prob
open SubdiffusiveProcess.CoarseGrainingVocab
variable {d : ℕ}

lemma aux_tight_lem_subharmonic_coefficientAt_pos (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : WithTop ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) (x : Vec d) :
    0 < coefficientAt M L ω x := by
  induction L using WithTop.recTopCoe with
  | top => exact SubdiffusiveProcess.Frozen.Assumptions.aAnchored_pos M ω x
  | coe n => exact SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n ω.1 x

lemma aux_tight_lem_subharmonic_coefficientAt_cont (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : WithTop ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) :
    Continuous (coefficientAt M L ω) := by
  induction L using WithTop.recTopCoe with
  | top => exact SubdiffusiveProcess.Frozen.Assumptions.continuous_aAnchored M ω
  | coe n => exact SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M n ω.1

/-- The local speed density and coefficient are continuous and positive. -/
lemma aux_tight_lem_subharmonic_local_regular (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : WithTop ℕ) (m : ℕ) (z : Vec d) (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) (j : ℕ) :
    let cz : ℝ := coefficientAt M L ω z / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M j ω.1 z
    let b : Vec d → ℝ := fun x => cz⁻¹ * coefficientAt M L ω (z + (3 : ℝ) ^ m • x)
    let A : Vec d → ℝ := fun x => (ahom M j)⁻¹ * b x
    Continuous b ∧ Continuous A ∧ (∀ x, 0 < b x) ∧ (∀ x, 0 < A x) := by
  intro cz b A
  have hcz : 0 < cz := div_pos (aux_tight_lem_subharmonic_coefficientAt_pos M L ω z)
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M j ω.1 z)
  have hchart : Continuous (fun x : Vec d => z + (3 : ℝ) ^ m • x) := by fun_prop
  have hbc : Continuous b := by
    simpa only [b, Function.comp_def] using!
      (continuous_const : Continuous (fun _ : Vec d => cz⁻¹)).mul
        ((aux_tight_lem_subharmonic_coefficientAt_cont M L ω).comp hchart)
  have hbpos : ∀ x, 0 < b x := fun x =>
    mul_pos (inv_pos.2 hcz) (aux_tight_lem_subharmonic_coefficientAt_pos M L ω _)
  exact ⟨hbc, continuous_const.mul hbc, hbpos, fun x => mul_pos (inv_pos.2 (ahom_pos M j)) (hbpos x)⟩

end prob

section main
open SubdiffusiveProcess.CoarseGrainingVocab



theorem tight_lem_subharmonic (d : ℕ) (cV : Vec d) (sV : ℝ) (cV' : Vec d) (sV' : ℝ)
    (hsV' : 0 < sV') (hVV' : Metric.closedBall cV' (sV' / 2) ⊆ Metric.ball cV (sV / 2)) :
    ∀ q : ℝ, 1 ≤ q → ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ delta0 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
            ∃ K : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d → ℝ, Measurable K ∧
              (∀ ω, 1 ≤ K ω) ∧
              (∫⁻ ω, ENNReal.ofReal (K ω ^ q)
                ∂(SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M
                  (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
                  (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure) ≤
                ENNReal.ofReal C ∧
              ∀ᵐ ω ∂(SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M
                  (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
                  (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure,
                let j : ℕ := match L with
                  | ⊤ => m
                  | (n : ℕ) => min m n
                let cz : ℝ := coefficientAt M L ω z /
                  SubdiffusiveProcess.Frozen.Assumptions.aCutoff M j ω.1 z
                let b : Vec d → ℝ := fun x => cz⁻¹ * coefficientAt M L ω (z + (3 : ℝ) ^ m • x)
                let A : Vec d → ℝ := fun x => (ahom M j)⁻¹ * b x
                ∀ w : Homogenization.H1Function (Metric.ball cV (sV / 2)),
                  (∀ᵐ x ∂(volume.restrict (Metric.ball cV (sV / 2))), 0 ≤ w.toFun x) →
                  (∃ Mw : ℝ, ∀ᵐ x ∂(volume.restrict (Metric.ball cV (sV / 2))), w.toFun x ≤ Mw) →
                  SubdiffusiveProcess.CoarseGrainingVocab.Section11.IsWeakSubSolutionOn A
                    (Metric.ball cV (sV / 2)) w →
                  ∀ᵐ x ∂(volume.restrict (Metric.ball cV' (sV' / 2))),
                    ENNReal.ofReal (w.toFun x) ≤ ENNReal.ofReal (K ω) *
                      (∫⁻ y in Metric.ball cV (sV / 2), ENNReal.ofReal (w.toFun y ^ 2 * b y)) ^
                        (1 / 2 : ℝ) := by
  by_cases hd : 2 ≤ d
  swap
  · intro q hq
    exact ⟨1, one_pos, fun M _ => absurd M.shellPrefix.dimension hd⟩
  have hsV : 0 < sV := by
    have h1 : cV' ∈ Metric.ball cV (sV / 2) :=
      hVV' (Metric.mem_closedBall_self (by linarith))
    have h2 := Metric.mem_ball.1 h1
    linarith [dist_nonneg (x := cV') (y := cV)]
  obtain ⟨δ, n, f, hδ, hfV, hcov⟩ := aux_tight_lem_subharmonic_cover hVV'
  have hs : ∀ i : Fin (n + 1), 0 < (Fin.cons (sV / 2) (fun _ => δ) : Fin (n + 1) → ℝ) i ∧
      (Fin.cons (sV / 2) (fun _ => δ) : Fin (n + 1) → ℝ) i <
        (Fin.cons sV (fun _ => 2 * δ) : Fin (n + 1) → ℝ) i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]; constructor <;> linarith
    · simp only [Fin.cons_succ]; constructor <;> linarith
  have hin : ∀ i : Fin (n + 1),
      Metric.ball ((Fin.cons cV f : Fin (n + 1) → Vec d) i)
          ((Fin.cons sV (fun _ => 2 * δ) : Fin (n + 1) → ℝ) i / 2) ⊆
        Metric.ball cV (sV / 2) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]; exact subset_rfl
    · simp only [Fin.cons_succ]
      rw [show 2 * δ / 2 = δ by ring]
      exact hfV j
  obtain ⟨B, hB, hstat⟩ := tight_lem_static d cV sV hsV (n + 1) (Fin.cons cV f)
    (Fin.cons (sV / 2) fun _ => δ) (Fin.cons sV fun _ => 2 * δ) hs hin
  obtain ⟨C1, Bm1, hC1, hBm1, hcomb⟩ :=
    aux_tight_lem_subharmonic_of_est (by omega) B δ hB hδ cV sV hsV n f hfV
  intro q hq
  obtain ⟨delta0, hdelta0, hM⟩ := hstat (max 1 (Bm1 * q)) (le_max_left _ _)
  refine ⟨delta0, hdelta0, fun M hMd => ?_⟩
  obtain ⟨C0, hC0, hK⟩ := hM M hMd
  set C2 : ℝ := max C1 1 with hC2def
  have hC2 : 1 ≤ C2 := le_max_right _ _
  have hC2pos : 0 < C2 := lt_of_lt_of_le one_pos hC2
  refine ⟨C2 ^ q * C0, by positivity, fun L m z => ?_⟩
  obtain ⟨K0, hK0m, hK01, hK0int, hK0ae⟩ := hK L m z
  refine ⟨fun ω => C2 * K0 ω ^ Bm1, measurable_const.mul (hK0m.pow_const Bm1), fun ω =>
    one_le_mul_of_one_le_of_one_le hC2 (Real.one_le_rpow (hK01 ω) hBm1.le), ?_, ?_⟩
  · calc ∫⁻ ω, ENNReal.ofReal ((C2 * K0 ω ^ Bm1) ^ q)
          ∂(SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure
        ≤ ∫⁻ ω, ENNReal.ofReal (C2 ^ q) * ENNReal.ofReal (K0 ω ^ (max 1 (Bm1 * q)))
          ∂(SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure := by
          refine lintegral_mono fun ω => ?_
          have hK0pos : 0 ≤ K0 ω := by linarith [hK01 ω]
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [Real.mul_rpow hC2pos.le (Real.rpow_nonneg hK0pos _), ← Real.rpow_mul hK0pos]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (hK01 ω) (le_max_right _ _)) (by positivity)
      _ = ENNReal.ofReal (C2 ^ q) * ∫⁻ ω, ENNReal.ofReal (K0 ω ^ (max 1 (Bm1 * q)))
          ∂(SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C2 ^ q) * ENNReal.ofReal C0 := by gcongr
      _ = ENNReal.ofReal (C2 ^ q * C0) := (ENNReal.ofReal_mul (by positivity)).symm
  · filter_upwards [hK0ae] with ω hω
    intro j cz b A w hw0 hwM hsub
    have hest : aux_tight_lem_static_estimates b A cV sV
        (Fin.cons cV f : Fin (n + 1) → Vec d)
        (Fin.cons (sV / 2) (fun _ => δ) : Fin (n + 1) → ℝ)
        (Fin.cons sV (fun _ => 2 * δ) : Fin (n + 1) → ℝ) (K0 ω) B := hω
    obtain ⟨hbc, hAc, hbpos, hApos⟩ := aux_tight_lem_subharmonic_local_regular M L m z ω j
    have h := hcomb b A (K0 ω) hbc hAc hbpos hApos (hK01 ω) hest w hw0 hwM hsub
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hcov h] with x hx
    refine hx.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by linarith [hK01 ω]) _)

end main

end Paper
