module

public import SubdiffusiveProcess.Paper.lane4_reference_oscillation_moments
public import SubdiffusiveProcess.Probability.OrliczLpNorm
public import SubdiffusiveProcess.Probability.OrliczExponentialMoment

@[expose] public section

/-! Anchored oscillation of one layer on a small cell, for every layer index.

A layer `omega ℓ` of wavelength `3^ℓ` oscillates on a cell of level `k` (side `3^{-k}`) by an amount
of size `δ 3^{-(ℓ+k)}` as soon as the layer is coarser than the cell (`0 < ℓ + k`), with sub-Gaussian
tails.  The source for `-k < ℓ ≤ 0` is the existing `lane4_reference_oscillation_moments` layer estimate; here
the integer-index version (which also covers the infrared layers `ℓ ≥ 1`) is proved by the same
scaling/stationarity argument, and turned into `L^p` and exponential moment bounds. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter Metric TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators

namespace Paper

noncomputable section

theorem aux_prop_conc_layer_oscillation_moments_geometry
    {d k : ℕ} {j : ℤ} (hj : j < (k : ℤ)) (y : SpatialCoordinates d)
    (f : C(SpatialCoordinates d, ℝ)) :
    aux_lane4_reference_oscillation_moments_localA y
        ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ)))
        (layerScaling d (-j) f) ≤
      aux_lane4_reference_oscillation_moments_rootA
        ((3 : ℝ) ^ (j - (k : ℤ)))
        (aux_lane4_reference_oscillation_moments_trans
          ((3 : ℝ) ^ j • y) f) := by
  let r : ℝ := (3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))
  let c : ℝ := (3 : ℝ) ^ (j - (k : ℤ))
  let K := aux_lane4_reference_oscillation_moments_Kball y r
  let K0 := aux_lane4_reference_oscillation_moments_Kball
    (0 : SpatialCoordinates d) (3 / 2 : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    rw [show j - (k : ℤ) = -((k : ℤ) - j) by ring, zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by norm_num) (by omega))
  have hnorm : ∀ x : SpatialCoordinates d, x ∈ (K : Set (SpatialCoordinates d)) →
      (3 : ℝ) ^ (k : ℤ) • (x - y) ∈ (K0 : Set (SpatialCoordinates d)) := by
    intro x hx
    change x ∈ closedBall y r at hx
    change (3 : ℝ) ^ (k : ℤ) • (x - y) ∈ closedBall 0 (3 / 2 : ℝ)
    rw [mem_closedBall] at hx ⊢
    rw [dist_eq_norm] at hx ⊢
    have hx' : ‖x - y‖ ≤ r := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm] using! hx
    simp only [sub_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hpow : (3 : ℝ) ^ (k : ℤ) * r = 3 / 2 := by
      dsimp [r]
      calc
        (3 : ℝ) ^ (k : ℤ) * ((3 / 2 : ℝ) * 3 ^ (-(k : ℤ))) =
            (3 / 2 : ℝ) * ((3 : ℝ) ^ (k : ℤ) * 3 ^ (-(k : ℤ))) := by ring
        _ = 3 / 2 := by
          rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
          simp
    nlinarith [mul_le_mul_of_nonneg_left hx'
      (by positivity : 0 ≤ (3 : ℝ) ^ (k : ℤ))]
  have hrootnonneg : 0 ≤
      aux_lane4_reference_oscillation_moments_rootA c
        (aux_lane4_reference_oscillation_moments_trans
          ((3 : ℝ) ^ j • y) f) := norm_nonneg _
  have hnorm_le : ∀ x : SpatialCoordinates d, x ∈ (K : Set (SpatialCoordinates d)) →
      ‖(layerScaling d (-j) f) x -
          (layerScaling d (-j) f) y‖ ≤
        aux_lane4_reference_oscillation_moments_rootA c
          (aux_lane4_reference_oscillation_moments_trans
            ((3 : ℝ) ^ j • y) f) := by
    intro x hx
    let u : SpatialCoordinates d := (3 : ℝ) ^ (k : ℤ) • (x - y)
    have hu : u ∈ (K0 : Set (SpatialCoordinates d)) := hnorm x hx
    have hpoint := ContinuousMap.norm_coe_le_norm
      (((aux_lane4_reference_oscillation_moments_trans
          ((3 : ℝ) ^ j • y) f).comp
        (⟨fun v : SpatialCoordinates d => c • v,
          by fun_prop⟩ : C(SpatialCoordinates d, SpatialCoordinates d))).restrict
          (K0 : Set (SpatialCoordinates d)) -
        ContinuousMap.const K0
          (aux_lane4_reference_oscillation_moments_trans
            ((3 : ℝ) ^ j • y) f 0)) ⟨u, hu⟩
    change ‖(aux_lane4_reference_oscillation_moments_trans
          ((3 : ℝ) ^ j • y) f) (c • u) -
        (aux_lane4_reference_oscillation_moments_trans
          ((3 : ℝ) ^ j • y) f) 0‖ ≤ _ at hpoint
    calc
      ‖(layerScaling d (-j) f) x -
          (layerScaling d (-j) f) y‖ =
          ‖f ((3 : ℝ) ^ j • x) -
            f ((3 : ℝ) ^ j • y)‖ := by
            congr 2
            · simp [layerScaling]
            · simp [layerScaling]
      _ = ‖f (c • u + (3 : ℝ) ^ j • y) -
            f ((3 : ℝ) ^ j • y)‖ := by
            congr 2
            dsimp [u, c]
            simp only [smul_sub, smul_smul]
            have hck : c * (3 : ℝ) ^ (k : ℤ) = (3 : ℝ) ^ j := by
              dsimp [c]
              rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
              congr 1 <;> omega
            rw [hck]
            rw [sub_add_cancel]
      _ = ‖(aux_lane4_reference_oscillation_moments_trans
          ((3 : ℝ) ^ j • y) f) (c • u) -
            (aux_lane4_reference_oscillation_moments_trans
              ((3 : ℝ) ^ j • y) f) 0‖ := by
            simp [aux_lane4_reference_oscillation_moments_trans]
      _ ≤ _ := hpoint
  have hnormK : ‖(layerScaling d (-j) f).restrict (K : Set _) -
      ContinuousMap.const K ((layerScaling d (-j) f) y)‖ ≤
      aux_lane4_reference_oscillation_moments_rootA c
        (aux_lane4_reference_oscillation_moments_trans
          ((3 : ℝ) ^ j • y) f) := by
    apply (ContinuousMap.norm_le _ hrootnonneg).2
    intro x
    exact hnorm_le x x.property
  simpa [aux_lane4_reference_oscillation_moments_localA,
    aux_lane4_reference_oscillation_moments_rootA,
    aux_lane4_reference_oscillation_moments_trans, K, K0, r, c] using! hnormK

theorem aux_prop_conc_layer_oscillation_moments_layer_exp
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ m : ℕ, 0 < m ∧ ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (y : SpatialCoordinates d) (k : ℕ) j, j < (k : ℤ) →
      let r : ℝ := (3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))
      let c : ℝ := (3 : ℝ) ^ (j - (k : ℤ))
      let P := (chaosSampleLaw M).toMeasure
      (∫⁻ omega, ENNReal.ofReal (Real.exp
        (((2 * aux_lane4_reference_oscillation_moments_localA y r
            (omega (-j))) /
          (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2)) ∂P) ≤ 2 := by
  obtain ⟨m, hm, hmom⟩ :=
    exists_gmc_anchored_contraction_exp_square (d := d) (3 / 2 : ℝ) (by norm_num)
  refine ⟨m, hm, ?_⟩
  intro M y k j hj
  dsimp only
  let r : ℝ := (3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))
  let c : ℝ := (3 : ℝ) ^ (j - (k : ℤ))
  let K0 := aux_lane4_reference_oscillation_moments_Kball
    (0 : SpatialCoordinates d) (3 / 2 : ℝ)
  let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) := chaosRootFieldLaw M
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun n => (scaledLayerLaw d ν n : Measure C(SpatialCoordinates d, ℝ))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    rw [show j - (k : ℤ) = -((k : ℤ) - j) by ring, zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by norm_num) (by omega))
  have hK0 : ∀ x ∈ (K0 : Set (SpatialCoordinates d)), ‖x‖ ≤ (3 / 2 : ℝ) := by
    intro x hx
    change x ∈ closedBall (0 : SpatialCoordinates d) (3 / 2 : ℝ) at hx
    simpa [mem_closedBall, dist_eq_norm] using! hx
  have hroot := hmom M K0 hK0 c hc hc1
  dsimp only at hroot
  let T : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ) :=
    fun f => aux_lane4_reference_oscillation_moments_trans
      ((3 : ℝ) ^ j • y) f
  let Φ : C(SpatialCoordinates d, ℝ) → ℝ≥0∞ := fun f =>
    ENNReal.ofReal (Real.exp
      ((aux_lane4_reference_oscillation_moments_rootA c (T f) /
        (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
  have hrootAcont : Continuous
      (aux_lane4_reference_oscillation_moments_rootA c :
        C(SpatialCoordinates d, ℝ) → ℝ) := by
    let dil : C(SpatialCoordinates d, SpatialCoordinates d) :=
      ⟨fun x => c • x, by fun_prop⟩
    have hc1 : Continuous (fun f : C(SpatialCoordinates d, ℝ) => f.comp dil) :=
      ContinuousMap.continuous_precomp dil
    have hc2 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        (f.comp dil).restrict
          (aux_lane4_reference_oscillation_moments_Kball
            (0 : SpatialCoordinates d) (3 / 2 : ℝ) : Set (SpatialCoordinates d))) :=
      (ContinuousMap.continuous_restrict _).comp hc1
    have hc3 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ContinuousMap.const
          (aux_lane4_reference_oscillation_moments_Kball
            (0 : SpatialCoordinates d) (3 / 2 : ℝ)) (f 0)) :=
      ContinuousMap.continuous_const'.comp (continuous_eval_const 0)
    exact continuous_norm.comp (hc2.sub hc3)
  have hTcont : Continuous T := by
    dsimp [T, aux_lane4_reference_oscillation_moments_trans]
    exact ContinuousMap.continuous_precomp _
  have hΦ : Measurable Φ := by
    have hcΦ : Continuous Φ := by
      dsimp [Φ]
      apply ENNReal.continuous_ofReal.comp
      apply Real.continuous_exp.comp
      exact (((hrootAcont.comp hTcont).div_const _).pow 2)
    exact hcΦ.measurable
  have hstat : MeasurePreserving T (ν : Measure C(SpatialCoordinates d, ℝ))
      (ν : Measure C(SpatialCoordinates d, ℝ)) := by
    simpa [T, ν, aux_lane4_reference_oscillation_moments_trans,
      chaosRootFieldLaw] using!
      (gmc_zero_field_law_stationary M ((3 : ℝ) ^ j • y))
  have hrootT : (∫⁻ f, Φ f ∂(ν : Measure C(SpatialCoordinates d, ℝ))) ≤ 2 := by
    have hbase : Measurable (fun f : C(SpatialCoordinates d, ℝ) =>
        ENNReal.ofReal (Real.exp
          ((aux_lane4_reference_oscillation_moments_rootA c f /
            (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))) := by
      have hcbase : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
          ENNReal.ofReal (Real.exp
            ((aux_lane4_reference_oscillation_moments_rootA c f /
              (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))) := by
        apply ENNReal.continuous_ofReal.comp
        apply Real.continuous_exp.comp
        exact ((hrootAcont.div_const _).pow 2)
      exact hcbase.measurable
    calc
      (∫⁻ f, Φ f ∂(ν : Measure C(SpatialCoordinates d, ℝ))) =
          ∫⁻ f, ENNReal.ofReal (Real.exp
            ((aux_lane4_reference_oscillation_moments_rootA c f /
              (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
            ∂Measure.map T (ν : Measure C(SpatialCoordinates d, ℝ)) := by
              change (∫⁻ f, ENNReal.ofReal (Real.exp
                ((aux_lane4_reference_oscillation_moments_rootA c (T f) /
                  (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
                  ∂(ν : Measure _)) = _
              exact (lintegral_map hbase hstat.measurable).symm
      _ = ∫⁻ f, ENNReal.ofReal (Real.exp
            ((aux_lane4_reference_oscillation_moments_rootA c f /
              (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
            ∂(ν : Measure C(SpatialCoordinates d, ℝ)) := by rw [hstat.map_eq]
      _ ≤ 2 := by
        simpa [aux_lane4_reference_oscillation_moments_rootA, T,
          aux_lane4_reference_oscillation_moments_trans, K0, ν, chaosRootFieldLaw] using! hroot
  have hlocalAcont : Continuous
      (aux_lane4_reference_oscillation_moments_localA y r :
        C(SpatialCoordinates d, ℝ) → ℝ) := by
    have hc1 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        f.restrict
          (aux_lane4_reference_oscillation_moments_Kball y r : Set (SpatialCoordinates d))) :=
      ContinuousMap.continuous_restrict _
    have hc2 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ContinuousMap.const
          (aux_lane4_reference_oscillation_moments_Kball y r) (f y)) :=
      ContinuousMap.continuous_const'.comp (continuous_eval_const y)
    exact continuous_norm.comp (hc1.sub hc2)
  have htarget : Measurable (fun f : C(SpatialCoordinates d, ℝ) =>
      ENNReal.ofReal (Real.exp
        ((2 * aux_lane4_reference_oscillation_moments_localA y r f /
          (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))) := by
    have hcTarget : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ENNReal.ofReal (Real.exp
          ((2 * aux_lane4_reference_oscillation_moments_localA y r f /
            (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))) := by
      apply ENNReal.continuous_ofReal.comp
      apply Real.continuous_exp.comp
      exact (((continuous_const.mul hlocalAcont).div_const _).pow 2)
    exact hcTarget.measurable
  have hP : (chaosSampleLaw M).toMeasure = Measure.infinitePi laws := by
    rfl
  rw [hP]
  have heval := measurePreserving_eval_infinitePi laws (-j)
  calc
    (∫⁻ omega, ENNReal.ofReal (Real.exp
        ((2 * aux_lane4_reference_oscillation_moments_localA y r
            (omega (-j)) /
          (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
        ∂Measure.infinitePi laws) =
      ∫⁻ f, ENNReal.ofReal (Real.exp
        ((2 * aux_lane4_reference_oscillation_moments_localA y r f /
          (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
        ∂laws (-j) := by
          exact heval.lintegral_comp htarget
    _ = ∫⁻ f, ENNReal.ofReal (Real.exp
        ((2 * aux_lane4_reference_oscillation_moments_localA y r
            (layerScaling d (-j) f) /
          (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
        ∂(ν : Measure C(SpatialCoordinates d, ℝ)) := by
          dsimp [laws, scaledLayerLaw]
          exact (lintegral_map htarget
            (layerScaling d (-j)).continuous.measurable)
    _ ≤ ∫⁻ f, Φ f ∂(ν : Measure C(SpatialCoordinates d, ℝ)) := by
      apply lintegral_mono
      intro f
      apply ENNReal.ofReal_mono
      rw [Real.exp_le_exp]
      have hδ : 0 < M.delta := M.shellPrefix.delta_pos
      have hden : 0 < c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta) := by
        positivity
      have hleft0 : 0 ≤
          2 * aux_lane4_reference_oscillation_moments_localA y r
              ((layerScaling d (-j)) f) /
            (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) := by
        exact div_nonneg (mul_nonneg (by positivity) (norm_nonneg _)) (by positivity)
      have hright0 : 0 ≤
          aux_lane4_reference_oscillation_moments_rootA c (T f) /
            (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) := by
        exact div_nonneg (norm_nonneg _) hden.le
      apply (sq_le_sq₀ hleft0 hright0).2
      calc
        2 * aux_lane4_reference_oscillation_moments_localA y r
              ((layerScaling d (-j)) f) /
              (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) =
            aux_lane4_reference_oscillation_moments_localA y r
              ((layerScaling d (-j)) f) /
              (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) := by
                field_simp
        _ ≤ aux_lane4_reference_oscillation_moments_rootA c (T f) /
              (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) := by
                exact div_le_div_of_nonneg_right
                  (aux_prop_conc_layer_oscillation_moments_geometry hj y f) hden.le
    _ ≤ 2 := hrootT

theorem aux_prop_conc_layer_oscillation_moments_localA_continuous {d : ℕ}
    (y : SpatialCoordinates d) (r : ℝ) :
    Continuous (aux_lane4_reference_oscillation_moments_localA y r :
      C(SpatialCoordinates d, ℝ) → ℝ) := by
  change Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
    ‖f.restrict (aux_lane4_reference_oscillation_moments_Kball y r : Set (SpatialCoordinates d)) -
      ContinuousMap.const (aux_lane4_reference_oscillation_moments_Kball y r) (f y)‖)
  have hc1 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
      f.restrict
        (aux_lane4_reference_oscillation_moments_Kball y r : Set (SpatialCoordinates d))) :=
    ContinuousMap.continuous_restrict _
  have hc2 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
      ContinuousMap.const
        (aux_lane4_reference_oscillation_moments_Kball y r) (f y)) :=
    ContinuousMap.continuous_const'.comp (continuous_eval_const y)
  exact continuous_norm.comp (hc1.sub hc2)

theorem aux_prop_conc_layer_oscillation_moments_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (y : SpatialCoordinates d) (r : ℝ) (ℓ : ℤ) :
    Measurable (fun omega : BilateralField d =>
      aux_lane4_reference_oscillation_moments_localA y r (omega ℓ)) :=
  (aux_prop_conc_layer_oscillation_moments_localA_continuous y r).measurable.comp
    (measurable_pi_apply ℓ)

/-- The oscillation moments for a fixed σ-algebra instance (the constant may a priori depend on it). -/
theorem aux_prop_conc_layer_oscillation_moments_main (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C1 : ℝ, 0 < C1 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (y : SpatialCoordinates d) (k : ℕ) (ℓ : ℤ),
        0 < ℓ + (k : ℤ) →
        Measurable (fun omega : BilateralField d =>
          aux_lane4_reference_oscillation_moments_localA y
            ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (omega ℓ)) ∧
        (∀ p' : ℝ≥0∞, p' ≠ ⊤ → 2 ≤ p' →
          eLpNorm (fun omega : BilateralField d =>
            aux_lane4_reference_oscillation_moments_localA y
              ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (omega ℓ)) p'
              (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C1 * M.delta * (((3 : ℝ) ^ (ℓ + (k : ℤ)).natAbs)⁻¹) *
              Real.sqrt p'.toReal)) ∧
        ∀ lam : ℝ, 0 ≤ lam →
          ∫⁻ omega : BilateralField d, ENNReal.ofReal (Real.exp (lam *
            aux_lane4_reference_oscillation_moments_localA y
              ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (omega ℓ))) ∂(chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (2 * Real.exp
              ((C1 * M.delta * (((3 : ℝ) ^ (ℓ + (k : ℤ)).natAbs)⁻¹)) ^ 2 * lam ^ 2 / 4)) := by
  obtain ⟨m, hm, hexp⟩ := aux_prop_conc_layer_oscillation_moments_layer_exp (d := d) hd
  obtain ⟨C0, hC0, horl⟩ := SubdiffusiveProcess.exists_universal_orlicz_eLpNorm_constant
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨(C0 + 1) * (3 / 2 : ℝ) * m, by positivity, ?_⟩
  intro M y k ℓ hℓ
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  set n : ℕ := (ℓ + (k : ℤ)).natAbs with hn
  have hnℓ : ℓ + (k : ℤ) = (n : ℤ) := by omega
  set r : ℝ := (3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ)) with hr
  let X : BilateralField d → ℝ := fun omega =>
    aux_lane4_reference_oscillation_moments_localA y r (omega ℓ)
  have hXm : Measurable X := aux_prop_conc_layer_oscillation_moments_measurable y r ℓ
  have hX0 : ∀ omega, 0 ≤ X omega := fun omega => norm_nonneg _
  set a : ℝ := (3 / 2 : ℝ) * m * M.delta * (((3 : ℝ) ^ n)⁻¹) with ha
  have ha0 : 0 < a := by positivity
  have hOrl : (∫⁻ omega, ENNReal.ofReal (Real.exp ((X omega / a) ^ (2 : ℕ)))
      ∂(chaosSampleLaw M).toMeasure) ≤ 2 := by
    have h1 := hexp M y k (-ℓ) (by omega)
    dsimp only at h1
    have hc : (3 : ℝ) ^ (-ℓ - (k : ℤ)) = ((3 : ℝ) ^ n)⁻¹ := by
      have : -ℓ - (k : ℤ) = -(n : ℤ) := by omega
      rw [this, zpow_neg, zpow_natCast]
    rw [hc] at h1
    refine le_trans (le_of_eq ?_) h1
    apply lintegral_congr
    intro omega
    have hneg : -(-ℓ) = ℓ := neg_neg ℓ
    simp only [hneg]
    have hxa : X omega / a = 2 * aux_lane4_reference_oscillation_moments_localA y
        (3 / 2 * 3 ^ (-(k : ℤ))) (omega ℓ) /
        (2 * ((3 : ℝ) ^ n)⁻¹ * (3 / 2) * ((m : ℝ) * M.delta)) := by
      simp only [X, ha, hr]
      field_simp
    rw [hxa]
  refine ⟨hXm, ?_, ?_⟩
  · intro p' hp' hp2
    have h := horl (chaosSampleLaw M).toMeasure X a hXm hX0 ha0 hOrl p' hp' hp2
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq : 0 ≤ Real.sqrt p'.toReal := Real.sqrt_nonneg _
    have hdn : 0 < ((3 : ℝ) ^ n)⁻¹ := by positivity
    have : C0 * a = C0 * (3 / 2 : ℝ) * m * (M.delta * ((3 : ℝ) ^ n)⁻¹) := by rw [ha]; ring
    calc C0 * a * Real.sqrt p'.toReal
        = C0 * (3 / 2 : ℝ) * m * (M.delta * ((3 : ℝ) ^ n)⁻¹) * Real.sqrt p'.toReal := by rw [this]
      _ ≤ (C0 + 1) * (3 / 2 : ℝ) * m * (M.delta * ((3 : ℝ) ^ n)⁻¹) * Real.sqrt p'.toReal := by
          gcongr
          linarith
      _ = _ := by ring
  · intro lam hlam
    obtain ⟨hint, hle⟩ := SubdiffusiveProcess.orlicz_exp_linear_integrable_integral_le
      (chaosSampleLaw M).toMeasure X a lam hXm hX0 ha0 hlam hOrl
    have hEq := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun omega => (Real.exp_pos _).le)
    rw [← hEq]
    refine ENNReal.ofReal_le_ofReal (hle.trans ?_)
    have hdn : 0 < ((3 : ℝ) ^ n)⁻¹ := by positivity
    have hA : a ≤ ((C0 + 1) * (3 / 2 : ℝ) * m) * M.delta * ((3 : ℝ) ^ n)⁻¹ := by
      rw [ha]; gcongr; linarith
    have hsq : a ^ 2 ≤ (((C0 + 1) * (3 / 2 : ℝ) * m) * M.delta * ((3 : ℝ) ^ n)⁻¹) ^ 2 :=
      pow_le_pow_left₀ ha0.le hA 2
    gcongr


/-- The layer `omega ℓ` oscillates on the cell of level `k` by `δ 3^{-(ℓ+k)}` in every `L^p`, `2 ≤ p < ∞`
(with the `√p` sub-Gaussian growth), and has the matching exponential moments, whenever it is coarser
than the cell (`0 < ℓ + k`); this covers every layer index `ℓ : ℤ`.  The constant `C1` depends on `d` only
(it is chosen before the Borel σ-algebra instance and the model). -/
theorem prop_conc_layer_oscillation_moments (d : ℕ) (hd : 2 ≤ d) :
    ∃ C1 : ℝ, 0 < C1 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (y : SpatialCoordinates d) (k : ℕ) (ℓ : ℤ),
        0 < ℓ + (k : ℤ) →
        Measurable (fun omega : BilateralField d =>
          aux_lane4_reference_oscillation_moments_localA y
            ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (omega ℓ)) ∧
        (∀ p' : ℝ≥0∞, p' ≠ ⊤ → 2 ≤ p' →
          eLpNorm (fun omega : BilateralField d =>
            aux_lane4_reference_oscillation_moments_localA y
              ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (omega ℓ)) p'
              (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (C1 * M.delta * (((3 : ℝ) ^ (ℓ + (k : ℤ)).natAbs)⁻¹) *
              Real.sqrt p'.toReal)) ∧
        ∀ lam : ℝ, 0 ≤ lam →
          ∫⁻ omega : BilateralField d, ENNReal.ofReal (Real.exp (lam *
            aux_lane4_reference_oscillation_moments_localA y
              ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (omega ℓ))) ∂(chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (2 * Real.exp
              ((C1 * M.delta * (((3 : ℝ) ^ (ℓ + (k : ℤ)).natAbs)⁻¹)) ^ 2 * lam ^ 2 / 4)) := by
  letI : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  haveI : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  obtain ⟨C1, hC1, h⟩ := aux_prop_conc_layer_oscillation_moments_main d hd
  refine ⟨C1, hC1, ?_⟩
  intro inst1 inst2
  have hEq : inst1 = borel C(SpatialCoordinates d, ℝ) := inst2.measurable_eq
  subst hEq
  exact h


end

end Paper
