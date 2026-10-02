import SubdiffusiveProcess.Paper.lane4_reference_point_moments
import SubdiffusiveProcess.Paper.lane4_reference_oscillation_moments

open MeasureTheory Set Filter Metric ProbabilityTheory TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_lem_as_coarse_shallow_grid_centered_oscillation_moments_sup_measurable
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHmeas : Measurable H) (k : ℕ)
    (y : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Measurable (fun omega : BilateralField d =>
      sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r,
          v = |(H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
            (H omega x' + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x')|}) := by
  let g : BilateralField d → SpatialCoordinates d → ℝ :=
    fun omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
  let U : Set (SpatialCoordinates d × SpatialCoordinates d) :=
    Metric.ball y r ×ˢ Metric.ball y r
  let Kpair : Set (SpatialCoordinates d × SpatialCoordinates d) :=
    Metric.closedBall y r ×ˢ Metric.closedBall y r
  let F : BilateralField d → SpatialCoordinates d × SpatialCoordinates d → ℝ :=
    fun omega z => |g omega z.1 - g omega z.2|
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_ball.prod isOpen_ball
  have hUsub : U ⊆ Kpair := by
    intro z hz
    exact ⟨mem_ball.mp hz.1 |>.le, mem_ball.mp hz.2 |>.le⟩
  have hKsub : Kpair ⊆ closure U := by
    intro z hz
    change z ∈ closure (Metric.ball y r ×ˢ Metric.ball y r)
    rw [closure_prod_eq, closure_ball y hr.ne']
    exact ⟨hz.1, hz.2⟩
  have hKne : Kpair.Nonempty := by
    exact ⟨(y, y), ⟨Metric.mem_closedBall_self hr.le, Metric.mem_closedBall_self hr.le⟩⟩
  have hFcont : ∀ omega, Continuous (F omega) := by
    intro omega
    have hsum : Continuous (fun x : SpatialCoordinates d =>
        ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) :=
      continuous_finset_sum (Finset.range k) (by
        intro j hj
        exact (omega (-(j : ℤ))).continuous)
    have hg : Continuous (g omega) := by
      dsimp [g]
      exact (H omega).continuous.add hsum
    exact continuous_abs.comp ((hg.comp continuous_fst).sub (hg.comp continuous_snd))
  have hFmeas : ∀ z : SpatialCoordinates d × SpatialCoordinates d,
      Measurable (fun omega => F omega z) := by
    intro z
    have hH1 : Measurable (fun omega => H omega z.1) :=
      (continuous_eval_const z.1).measurable.comp hHmeas
    have hH2 : Measurable (fun omega => H omega z.2) :=
      (continuous_eval_const z.2).measurable.comp hHmeas
    have hsum1 : Measurable (fun omega : BilateralField d =>
        ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) z.1) :=
      Finset.measurable_sum (Finset.range k) (by
        intro j hj
        have heval : Measurable (fun omega : BilateralField d =>
            omega (-(j : ℤ))) := measurable_pi_apply _
        simpa only [Function.comp_apply] using
          ((continuous_eval_const z.1).measurable.comp heval))
    have hsum2 : Measurable (fun omega : BilateralField d =>
        ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) z.2) :=
      Finset.measurable_sum (Finset.range k) (by
        intro j hj
        have heval : Measurable (fun omega : BilateralField d =>
            omega (-(j : ℤ))) := measurable_pi_apply _
        simpa only [Function.comp_apply] using
          ((continuous_eval_const z.2).measurable.comp heval))
    have hsub : Measurable (fun omega => g omega z.1 - g omega z.2) := by
      exact (hH1.add hsum1).sub (hH2.add hsum2)
    exact measurable_norm.comp hsub
  have hAbdd : ∀ omega, BddAbove {v : ℝ | ∃ z ∈ Kpair, v = F omega z} := by
    intro omega
    have hcompact : IsCompact Kpair := by
      dsimp [Kpair]
      exact (isCompact_closedBall y r).prod (isCompact_closedBall y r)
    have himage := hcompact.bddAbove_image (hFcont omega).continuousOn
    apply himage.mono
    rintro v ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  have hSupOpen : Measurable (fun omega =>
      sSup {v : ℝ | ∃ z ∈ U, v = F omega z}) :=
    aux_lane4_reference_oscillation_moments_measurable_sup_open
      hUopen hFcont hFmeas (by
        intro omega
        have himage := hAbdd omega
        exact himage.mono (by
          rintro v ⟨z, hz, rfl⟩
          exact ⟨z, hUsub hz, rfl⟩))
  have hSupMeas : Measurable (fun omega =>
      sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = F omega (x, x')}) := by
    have heq : (fun omega => sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = F omega (x, x')}) =
        (fun omega => sSup {v : ℝ | ∃ z ∈ U, v = F omega z}) := by
      funext omega
      calc
        sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
            ∃ x' ∈ Metric.closedBall y r, v = F omega (x, x')} =
            sSup {v : ℝ | ∃ z ∈ Kpair, v = F omega z} := by
              apply congrArg sSup
              ext v
              constructor
              · rintro ⟨x, hx, x', hx', hv⟩
                exact ⟨(x, x'), ⟨hx, hx'⟩, hv⟩
              · rintro ⟨z, hz, hv⟩
                exact ⟨z.1, hz.1, z.2, hz.2, hv⟩
        _ = sSup {v : ℝ | ∃ z ∈ U, v = F omega z} :=
          aux_lane4_reference_oscillation_moments_sup_closed_eq_sup_open
            hUsub hKsub hKne (hFcont omega) (hAbdd omega)
    rw [heq]
    exact hSupOpen
  exact hSupMeas

theorem aux_lem_as_coarse_shallow_grid_centered_oscillation_point
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q)
    (CH : Compacts (SpatialCoordinates d) → ℝ)
    (hCH : ∀ K, 0 ≤ CH K)
    (hHmom : aux_lane4_reference_oscillation_moments_Hmom d CH)
    (m : ℕ) (hm : 0 < m)
    (hLayer : aux_lane4_reference_oscillation_moments_Layer d m)
    (Kbig : Compacts (SpatialCoordinates d))
    (E Cosc : ℝ)
    (hKbig_def : Kbig =
      aux_lane4_reference_oscillation_moments_Kball
        (0 : SpatialCoordinates d) (3 : ℝ))
    (hE : E = CH Kbig * (4 * (2 * q)) ^ 2 +
      (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2)
    (hCosc : Cosc = (2 * Real.exp E) ^ (1 / (2 * q)))
        (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (hM : M.delta ≤ delta0)
    (k : ℕ) (y : SpatialCoordinates d)
    (hy : y ∈ {x : SpatialCoordinates d | ∀ i, |x i| ≤ (1 / 2 : ℝ)}) :
      let P := (chaosSampleLaw M).toMeasure
    let r : ℝ := (3 : ℝ) * ((3 : ℝ) ^ (-(k : ℤ)) / 2)
    let g : BilateralField d → SpatialCoordinates d → ℝ :=
      fun omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
    let O : BilateralField d → ℝ := fun omega =>
      sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = |g omega x - g omega x'|}
    MemLp (fun omega => Real.exp (O omega))
        (ENNReal.ofReal (2 * q)) P ∧
      eLpNorm (fun omega => Real.exp (O omega))
        (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  classical
  dsimp only
  let r : ℝ := (3 : ℝ) * ((3 : ℝ) ^ (-(k : ℤ)) / 2)
  let g : BilateralField d → SpatialCoordinates d → ℝ :=
    fun omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
  let U : Set (SpatialCoordinates d × SpatialCoordinates d) :=
    Metric.ball y r ×ˢ Metric.ball y r
  let Kpair : Set (SpatialCoordinates d × SpatialCoordinates d) :=
    Metric.closedBall y r ×ˢ Metric.closedBall y r
  let F : BilateralField d → SpatialCoordinates d × SpatialCoordinates d → ℝ :=
    fun omega z => |g omega z.1 - g omega z.2|
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hSupMeas : Measurable (fun omega =>
      sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = F omega (x, x')}) :=
    aux_lem_as_coarse_shallow_grid_centered_oscillation_moments_sup_measurable d H hH.1 k y r hr
  let O : BilateralField d → ℝ := fun omega =>
    sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
      ∃ x' ∈ Metric.closedBall y r, v = F omega (x, x')}
  have hOmeas : Measurable O := by
    exact hSupMeas
  have hr_le : (3 : ℝ) ^ (-(k : ℤ)) ≤ 1 := by
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by norm_num) (by omega))
  have hy_norm : ‖y‖ ≤ 1 := by
    have hy' : ∀ i : Fin d, |y i| ≤ (1 / 2 : ℝ) := by
      simpa using hy
    rw [Pi.norm_def]
    have hsup : (Finset.univ.sup fun b : Fin d => ‖y b‖₊) ≤ (1 : ℝ≥0) := by
      apply Finset.sup_le
      intro i hi
      apply NNReal.coe_le_coe.mp
      have hh : |y i| ≤ (1 : ℝ) := (hy' i).trans (by norm_num)
      simpa [Real.norm_eq_abs] using hh
    exact_mod_cast hsup
  have hKbig : ∀ x ∈ Metric.closedBall y r,
      x ∈ (Kbig : Set (SpatialCoordinates d)) := by
    intro x hx
    rw [hKbig_def]
    change x ∈ Metric.closedBall (0 : SpatialCoordinates d) 3
    rw [mem_closedBall, dist_eq_norm]
    have hx' : ‖x - y‖ ≤ r := by
      simpa [mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_comm] using hx
    have hr_le' : r ≤ 3 / 2 := by
      dsimp [r]
      calc
        3 * (3 ^ (-(k : ℤ)) / 2) ≤ 3 * ((1 : ℝ) / 2) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hr_le (by norm_num)) (by norm_num)
        _ = 3 / 2 := by ring
    have hxy : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      simpa only [sub_add_cancel] using (norm_add_le (x - y) y)
    have : ‖x‖ ≤ (3 / 2 : ℝ) + 1 := hxy.trans
      (add_le_add (hx'.trans hr_le') hy_norm)
    have hx3 : ‖x‖ ≤ 3 := by nlinarith
    simpa only [sub_zero] using hx3
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let X : ℕ → BilateralField d → ℝ := fun j omega =>
    2 * aux_lane4_reference_oscillation_moments_localA y r (omega (-(j : ℤ)))
  let A : ℕ → ℝ := fun j =>
    2 * (3 : ℝ) ^ ((j : ℤ) - (k : ℤ)) * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)
  let S : BilateralField d → ℝ := fun omega => ∑ j ∈ Finset.range k, X j omega
  have hlocalAcont : Continuous
      (aux_lane4_reference_oscillation_moments_localA y r :
        C(SpatialCoordinates d, ℝ) → ℝ) := by
    dsimp [aux_lane4_reference_oscillation_moments_localA]
    have hc1 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        f.restrict
          (aux_lane4_reference_oscillation_moments_Kball y r : Set (SpatialCoordinates d))) :=
      ContinuousMap.continuous_restrict _
    have hc2 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ContinuousMap.const
          (aux_lane4_reference_oscillation_moments_Kball y r) (f y)) :=
      ContinuousMap.continuous_const'.comp (continuous_eval_const y)
    exact continuous_norm.comp (hc1.sub hc2)
  have hXmeas : ∀ j, Measurable (X j) := by
    intro j
    dsimp [X]
    have heval : Measurable (fun omega : BilateralField d => omega (-(j : ℤ))) :=
      measurable_pi_apply _
    simpa only [Function.comp_apply] using
      (measurable_const.mul (hlocalAcont.measurable.comp heval))
  have hX0 : ∀ j omega, 0 ≤ X j omega := by
    intro j omega
    dsimp [X, aux_lane4_reference_oscillation_moments_localA]
    positivity
  have hA : ∀ j, 0 < A j := by
    intro j
    dsimp [A]
    have hδ : 0 < M.delta := M.shellPrefix.delta_pos
    positivity
  have hXexp : ∀ j, j < k →
      (∫⁻ omega, ENNReal.ofReal (Real.exp ((X j omega / A j) ^ 2)) ∂P) ≤ 2 := by
    intro j hj
    have hh := hLayer M y k j hj
    dsimp only at hh
    have hr_eq : r = (3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ)) := by
      dsimp [r]
      ring
    simpa [P, X, A, hr_eq] using hh
  have hSmeas : Measurable S := by
    dsimp [S]
    exact Finset.measurable_sum (Finset.range k) (by
      intro j hj
      exact hXmeas j)
  have hS0 : ∀ omega, 0 ≤ S omega := by
    intro omega
    dsimp [S]
    exact Finset.sum_nonneg (fun j hj => hX0 j omega)
  have hsumc : (∑ j ∈ Finset.range k, (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))) ≤ 1 / 2 := by
    have hsum : (∑ j ∈ Finset.range k, (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))) =
        (1 - 3 ^ (-(k : ℤ))) / 2 := by
      calc
        (∑ j ∈ Finset.range k, (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))) =
            (∑ j ∈ Finset.range k, 3 ^ (j : ℤ)) * 3 ^ (-(k : ℤ)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j hj
              rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
              congr 1 <;> omega
        _ = (1 - 3 ^ (-(k : ℤ))) / 2 := by
              have hg := geom_sum_mul (3 : ℝ) k
              have hz : (∑ j ∈ Finset.range k, (3 : ℝ) ^ (j : ℤ)) =
                  ∑ j ∈ Finset.range k, (3 : ℝ) ^ j := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [zpow_natCast (3 : ℝ) j]
              rw [hz]
              rw [zpow_neg, zpow_natCast]
              field_simp [show (3 : ℝ) ^ k ≠ 0 by positivity]
              nlinarith [hg]
    rw [hsum]
    have hpos : 0 < (3 : ℝ) ^ (-(k : ℤ)) := by positivity
    linarith
  have hAsum_eq : (∑ j ∈ Finset.range k, A j) =
      (2 * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) *
        (∑ j ∈ Finset.range k, (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))) := by
    dsimp [A]
    calc
      (∑ j ∈ Finset.range k,
          2 * (3 : ℝ) ^ ((j : ℤ) - (k : ℤ)) * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) =
          ∑ j ∈ Finset.range k,
            (2 * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) *
              (3 : ℝ) ^ ((j : ℤ) - (k : ℤ)) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
      _ = (2 * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) *
          (∑ j ∈ Finset.range k, (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))) := by
            rw [Finset.mul_sum]
  have hAsum_bound : (∑ j ∈ Finset.range k, A j) ≤
      (3 / 2 : ℝ) * ((m : ℝ) * M.delta) := by
    rw [hAsum_eq]
    calc
      (2 * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) *
          (∑ j ∈ Finset.range k, (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))) ≤
          (2 * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) * (1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hsumc (by
              have hδ : 0 < M.delta := M.shellPrefix.delta_pos
              positivity)
      _ = (3 / 2 : ℝ) * ((m : ℝ) * M.delta) := by ring
  have hAsum_bound' : (∑ j ∈ Finset.range k, A j) ≤
      (3 / 2 : ℝ) * (m : ℝ) := by
    have hδle1' : M.delta ≤ 1 := hM.trans hdelta1
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    have hmd : (m : ℝ) * M.delta ≤ (m : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hδle1' hm0
    have hmd' : (3 / 2 : ℝ) * ((m : ℝ) * M.delta) ≤
        (3 / 2 : ℝ) * ((m : ℝ) * 1) :=
      mul_le_mul_of_nonneg_left hmd (by norm_num)
    calc
      (∑ j ∈ Finset.range k, A j) ≤
          (3 / 2 : ℝ) * ((m : ℝ) * M.delta) := hAsum_bound
      _ ≤ (3 / 2 : ℝ) * (m : ℝ) := by simpa only [mul_one] using hmd'
  have hSlin :
      Integrable (fun omega => Real.exp ((2 * (2 * q)) * S omega)) P ∧
        (∫ omega, Real.exp ((2 * (2 * q)) * S omega) ∂P) ≤
          2 * Real.exp ((((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2) := by
    by_cases hk : k = 0
    · subst k
      refine ⟨?_, ?_⟩
      · simpa [S] using (integrable_const (μ := P) (c := (1 : ℝ)))
      · simp [S]
        nlinarith [Real.one_le_exp (by positivity :
          0 ≤ ((3 / 2 : ℝ) * (m : ℝ) * (2 * q)) ^ 2)]
    · have hkne : (Finset.range k).Nonempty := by
        exact ⟨0, by simp; omega⟩
      have hOr := lintegral_exp_sq_finset_sum_le P (Finset.range k) X A hkne
        (by intro j hj; exact (hXmeas j).aestronglyMeasurable)
        (by intro j hj; exact Filter.Eventually.of_forall (fun omega => hX0 j omega))
        (by intro j hj; exact hA j)
        (by intro j hj; exact hXexp j (Finset.mem_range.mp hj))
      have hraw := orlicz_exp_linear_integrable_integral_le P S
        (∑ j ∈ Finset.range k, A j) (2 * (2 * q)) hSmeas hS0
        (Finset.sum_pos (fun j hj => hA j) hkne) (by positivity) hOr
      refine ⟨hraw.1, ?_⟩
      have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range k, A j := by
        exact Finset.sum_nonneg (fun j hj => (hA j).le)
      have hqpos : 0 ≤ 2 * q := by positivity
      have hprod :
          (∑ j ∈ Finset.range k, A j) * (2 * q) ≤
            ((3 / 2 : ℝ) * (m : ℝ)) * (2 * q) :=
        mul_le_mul_of_nonneg_right hAsum_bound' hqpos
      calc
        (∫ omega, Real.exp ((2 * (2 * q)) * S omega) ∂P) ≤
            2 * Real.exp
              ((∑ j ∈ Finset.range k, A j) ^ 2 * (2 * (2 * q)) ^ 2 / 4) := by
                simpa using hraw.2
        _ ≤ 2 * Real.exp
              ((((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2) := by
                apply mul_le_mul_of_nonneg_left
                  (Real.exp_le_exp.mpr ?_) (by positivity)
                calc
                  (∑ j ∈ Finset.range k, A j) ^ 2 * (2 * (2 * q)) ^ 2 / 4 =
                      ((∑ j ∈ Finset.range k, A j) * (2 * q)) ^ 2 := by ring
                  _ ≤ (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2 := by
                    have htarget0 : 0 ≤
                        ((3 / 2 : ℝ) * (m : ℝ)) * (2 * q) := by
                      have hm0 : 0 ≤ (m : ℝ) := by positivity
                      exact mul_nonneg
                        (mul_nonneg (by norm_num) hm0) hqpos
                    exact (sq_le_sq₀ (mul_nonneg hsum_nonneg hqpos) htarget0).2 hprod
  let YH : BilateralField d → ℝ := fun omega =>
    ‖(H omega).restrict (Kbig : Set (SpatialCoordinates d))‖
  let U : BilateralField d → ℝ := fun omega =>
    Real.exp ((2 * q) * O omega)
  have hU : U = fun omega => Real.exp ((2 * q) * O omega) := by
    rfl
  let V : BilateralField d → ℝ := fun omega =>
    (Real.exp ((4 * (2 * q)) * YH omega) +
      Real.exp ((2 * (2 * q)) * S omega)) / 2
  have hV : V = fun omega =>
      (Real.exp ((4 * (2 * q)) * YH omega) +
        Real.exp ((2 * (2 * q)) * S omega)) / 2 := by
    rfl
  have hYHmeas : Measurable YH := by
    have hcont : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ‖f.restrict (Kbig : Set (SpatialCoordinates d))‖) :=
      continuous_norm.comp (ContinuousMap.continuous_restrict _)
    simpa [YH, Function.comp_apply] using hcont.measurable.comp hH.1
  have hHraw := hHmom M H hH Kbig (4 * (2 * q)) (by positivity)
  have hHint : Integrable (fun omega => Real.exp ((4 * (2 * q)) * YH omega)) P := by
    simpa [P, YH] using hHraw.1
  have hδle1 : M.delta ≤ 1 := hM.trans hdelta1
  have hδsq : M.delta ^ 2 ≤ 1 := by
    have hδ0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
    have hh := mul_self_le_mul_self hδ0 hδle1
    simpa [pow_two] using hh
  have hHbound :
      (∫ omega, Real.exp ((4 * (2 * q)) * YH omega) ∂P) ≤
        2 * Real.exp (CH Kbig * (4 * (2 * q)) ^ 2) := by
    have hcoef : 0 ≤ CH Kbig * (4 * (2 * q)) ^ 2 := by
      exact mul_nonneg (hCH Kbig) (sq_nonneg _)
    have hexp : CH Kbig * (4 * (2 * q)) ^ 2 * M.delta ^ 2 ≤
        CH Kbig * (4 * (2 * q)) ^ 2 := by
      calc
        CH Kbig * (4 * (2 * q)) ^ 2 * M.delta ^ 2 ≤
            CH Kbig * (4 * (2 * q)) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hδsq hcoef
        _ = CH Kbig * (4 * (2 * q)) ^ 2 := by ring
    calc
      (∫ omega, Real.exp ((4 * (2 * q)) * YH omega) ∂P) ≤
          2 * Real.exp (CH Kbig * (4 * (2 * q)) ^ 2 * M.delta ^ 2) := by
            simpa [P, YH] using hHraw.2
      _ ≤ 2 * Real.exp (CH Kbig * (4 * (2 * q)) ^ 2) := by
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
  have hlocal_pair : ∀ (f : C(SpatialCoordinates d, ℝ))
      (x : SpatialCoordinates d) (x' : SpatialCoordinates d),
      x ∈ Metric.closedBall y r → x' ∈ Metric.closedBall y r →
      |f x - f x'| ≤
        2 * aux_lane4_reference_oscillation_moments_localA y r f := by
    intro f x x' hx hx'
    have hxA := ContinuousMap.norm_coe_le_norm
      (f.restrict (aux_lane4_reference_oscillation_moments_Kball y r :
        Set (SpatialCoordinates d)) -
        ContinuousMap.const (aux_lane4_reference_oscillation_moments_Kball y r) (f y))
      ⟨x, hx⟩
    have hxA2 := ContinuousMap.norm_coe_le_norm
      (f.restrict (aux_lane4_reference_oscillation_moments_Kball y r :
        Set (SpatialCoordinates d)) -
        ContinuousMap.const (aux_lane4_reference_oscillation_moments_Kball y r) (f y))
      ⟨x', hx'⟩
    have hx1 : |f x - f y| ≤
        aux_lane4_reference_oscillation_moments_localA y r f := by
      change ‖f x - f y‖ ≤
        aux_lane4_reference_oscillation_moments_localA y r f at hxA
      simpa only [Real.norm_eq_abs] using hxA
    have hx2 : |f x' - f y| ≤
        aux_lane4_reference_oscillation_moments_localA y r f := by
      change ‖f x' - f y‖ ≤
        aux_lane4_reference_oscillation_moments_localA y r f at hxA2
      simpa only [Real.norm_eq_abs] using hxA2
    calc
      |f x - f x'| = |(f x - f y) - (f x' - f y)| := by congr 1 <;> ring
      _ ≤ |f x - f y| + |f x' - f y| := by
        exact abs_sub _ _
      _ ≤ 2 * aux_lane4_reference_oscillation_moments_localA y r f := by
        calc
          |f x - f y| + |f x' - f y| ≤
              aux_lane4_reference_oscillation_moments_localA y r f +
                aux_lane4_reference_oscillation_moments_localA y r f :=
            add_le_add hx1 hx2
          _ = 2 * aux_lane4_reference_oscillation_moments_localA y r f := by ring
  have hHpair : ∀ omega x, x ∈ Metric.closedBall y r →
      ∀ x', x' ∈ Metric.closedBall y r →
      |H omega x - H omega x'| ≤ 2 * YH omega := by
    intro omega x hx x' hx'
    have hxH := ContinuousMap.norm_coe_le_norm
      ((H omega).restrict (Kbig : Set (SpatialCoordinates d)))
      ⟨x, hKbig x hx⟩
    have hxH' := ContinuousMap.norm_coe_le_norm
      ((H omega).restrict (Kbig : Set (SpatialCoordinates d)))
      ⟨x', hKbig x' hx'
      ⟩
    calc
      |H omega x - H omega x'| ≤ |H omega x| + |H omega x'| := abs_sub _ _
      _ ≤ YH omega + YH omega := by
        exact add_le_add hxH hxH'
      _ = 2 * YH omega := by ring
  have hsum_pair : ∀ omega x, x ∈ Metric.closedBall y r →
      ∀ x', x' ∈ Metric.closedBall y r →
      |(∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
        (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x')| ≤ S omega := by
    intro omega x hx x' hx'
    calc
      |(∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
          (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x')| =
          ‖∑ j ∈ Finset.range k,
            ((omega (-(j : ℤ))) x - (omega (-(j : ℤ))) x')‖ := by
              rw [Finset.sum_sub_distrib, Real.norm_eq_abs]
      _ ≤ ∑ j ∈ Finset.range k,
          ‖(omega (-(j : ℤ))) x - (omega (-(j : ℤ))) x'‖ :=
            norm_sum_le _ _
      _ = ∑ j ∈ Finset.range k,
          |(omega (-(j : ℤ))) x - (omega (-(j : ℤ))) x'| := by
            simp only [Real.norm_eq_abs]
      _ ≤ ∑ j ∈ Finset.range k, X j omega := by
            apply Finset.sum_le_sum
            intro j hj
            have hh := hlocal_pair (omega (-(j : ℤ))) x x' hx hx'
            simpa [X] using hh
      _ = S omega := by rfl
  have hO_le : ∀ omega, O omega ≤ 2 * YH omega + S omega := by
    intro omega
    dsimp [O]
    have hne : {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = F omega (x, x')}.Nonempty := by
      refine ⟨F omega (y, y), y, Metric.mem_closedBall_self hr.le,
        y, Metric.mem_closedBall_self hr.le, rfl⟩
    refine csSup_le hne ?_
    rintro v ⟨x, hx, x', hx', rfl⟩
    calc
      F omega (x, x') =
          |(H omega x - H omega x') +
            ((∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
              (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x'))| := by
            congr 1
            change |(H omega x +
                ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
              (H omega x' +
                ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x')| = _
            congr 1
            ring
      _ ≤ |H omega x - H omega x'| +
          |(∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
            (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x')| := by
            exact abs_add_le _ _
      _ ≤ 2 * YH omega + S omega :=
            add_le_add (hHpair omega x hx x' hx') (hsum_pair omega x hx x' hx')
  have hpoint : ∀ omega,
      Real.exp ((2 * q) * O omega) ≤
        (Real.exp ((4 * (2 * q)) * YH omega) +
          Real.exp ((2 * (2 * q)) * S omega)) / 2 := by
    intro omega
    have hq0 : 0 ≤ 2 * q := by positivity
    exact aux_lane4_reference_oscillation_moments_exp_osc_envelope q
      (O omega) (YH omega) (S omega) (hO_le omega) hq0
  have hdom : Integrable V P := by
    rw [hV]
    exact aux_lane4_reference_oscillation_moments_integrable_add_div_two
      hHint hSlin.1
  rw [hV] at hdom
  have hOexp_meas' : Measurable (fun omega => Real.exp ((2 * q) * O omega)) := by
    exact aux_lane4_reference_oscillation_moments_measurable_exp_mul
      (2 * q) hOmeas
  have hOexp_int :=
    aux_lane4_reference_oscillation_moments_integrable_exp_of_le
      (f := O)
      (g := fun omega =>
        (Real.exp ((4 * (2 * q)) * YH omega) +
          Real.exp ((2 * (2 * q)) * S omega)) / 2)
      (2 * q) hOmeas hdom hpoint
  /-
  have hOexp_bound :
      (∫ omega, Real.exp ((2 * q) * O omega) ∂P) ≤ 2 * Real.exp E := by
    have hmono :
        (fun omega => Real.exp ((2 * q) * O omega)) ≤
          (fun omega =>
            (Real.exp ((4 * (2 * q)) * YH omega) +
              Real.exp ((2 * (2 * q)) * S omega)) / 2) := by
      intro omega
      exact hpoint omega
    have hmono_ae :
        (fun omega => Real.exp ((2 * q) * O omega)) ≤ᵐ[P]
          (fun omega =>
            (Real.exp ((4 * (2 * q)) * YH omega) +
              Real.exp ((2 * (2 * q)) * S omega)) / 2) :=
      Filter.Eventually.of_forall hmono
    have hIntMono' :
        (∫ omega, Real.exp ((2 * q) * O omega) ∂P) ≤
          ∫ omega, (Real.exp ((4 * (2 * q)) * YH omega) +
            Real.exp ((2 * (2 * q)) * S omega)) / 2 ∂P := by
      exact aux_lane4_reference_oscillation_moments_integral_mono_ae
        hOexp_int hdom hmono_ae
    have hA : 0 ≤ CH Kbig * (4 * (2 * q)) ^ 2 :=
      mul_nonneg (hCH Kbig) (sq_nonneg _)
    have hB : 0 ≤ (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2 :=
      sq_nonneg _
    have hAvgToE :
        (∫ omega, (Real.exp ((4 * (2 * q)) * YH omega) +
          Real.exp ((2 * (2 * q)) * S omega)) / 2 ∂P) ≤ 2 * Real.exp E := by
      exact aux_lane4_reference_oscillation_moments_integral_add_div_two_exp_le
        (μ := P)
        (f := fun omega => Real.exp ((4 * (2 * q)) * YH omega))
        (g := fun omega => Real.exp ((2 * (2 * q)) * S omega))
        (a := CH Kbig * (4 * (2 * q)) ^ 2)
        (b := (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2)
        (e := E) hHint hSlin.1 hHbound hSlin.2 hE hA hB
    exact hIntMono'.trans hAvgToE
  have hconvert :
      MemLp (fun omega => Real.exp (O omega))
          (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (O omega))
          (ENNReal.ofReal (2 * q)) P ≤
          ENNReal.ofReal ((2 * Real.exp E) ^ (1 / (2 * q))) := by
    have hp : 0 < 2 * q := by linarith
    have hp0 : ENNReal.ofReal (2 * q) ≠ 0 :=
      (ENNReal.ofReal_eq_zero.not).2 (not_le.mpr hp)
    have hptop : ENNReal.ofReal (2 * q) ≠ ∞ := ENNReal.ofReal_ne_top
    have heq : ∀ omega, ‖Real.exp (O omega)‖ ^
        (ENNReal.ofReal (2 * q)).toReal =
          Real.exp ((2 * q) * O omega) := by
      intro omega
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ENNReal.toReal_ofReal hp.le]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    have hpow : Integrable (fun omega =>
        ‖Real.exp (O omega)‖ ^
          (ENNReal.ofReal (2 * q)).toReal) P := by
      simpa only [heq] using hOexp_int
    have hexpm : Measurable (fun omega => Real.exp (O omega)) := hOmeas.exp
    have hmem :=
      (integrable_norm_rpow_iff hexpm.aestronglyMeasurable hp0 hptop).mp hpow
    refine ⟨hmem, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hptop]
    have hlin :
        ∫⁻ omega, ‖Real.exp (O omega)‖ₑ ^
            (ENNReal.ofReal (2 * q)).toReal ∂P =
          ENNReal.ofReal (∫ omega, Real.exp ((2 * q) * O omega) ∂P) := by
      rw [ofReal_integral_eq_lintegral_ofReal hOexp_int
        (Filter.Eventually.of_forall fun omega => (Real.exp_pos _).le)]
      apply lintegral_congr_ae
      filter_upwards [] with omega
      rw [← ofReal_norm_eq_enorm]
      rw [ENNReal.ofReal_rpow_of_nonneg
        (norm_nonneg (Real.exp (O omega)))
        ENNReal.toReal_nonneg]
      rw [heq]
    rw [hlin]
    calc
      (ENNReal.ofReal
        (∫ omega, Real.exp ((2 * q) * O omega) ∂P)) ^
          (1 / (ENNReal.ofReal (2 * q)).toReal) ≤
          (ENNReal.ofReal (2 * Real.exp E)) ^ (1 / (2 * q)) := by
            rw [ENNReal.toReal_ofReal hp.le]
            exact ENNReal.rpow_le_rpow
              ((ENNReal.ofReal_le_ofReal_iff (by positivity)).2 hOexp_bound)
              (by positivity)
      _ = ENNReal.ofReal ((2 * Real.exp E) ^ (1 / (2 * q))) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  change MemLp (fun omega => Real.exp (O omega)) (ENNReal.ofReal (2 * q)) P ∧
    eLpNorm (fun omega => Real.exp (O omega)) (ENNReal.ofReal (2 * q)) P ≤
      ENNReal.ofReal Cosc
  rw [hCosc]
  exact hconvert
  -/
  exact aux_lane4_reference_oscillation_moments_final
    P q hq O YH S
    (CH Kbig * (4 * (2 * q)) ^ 2)
    ((((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2) E Cosc
    hOmeas hOexp_int hHint hSlin.1 hHbound hSlin.2
    (mul_nonneg (hCH Kbig) (sq_nonneg _)) (sq_nonneg _)
    hO_le hE hCosc







theorem aux_lem_as_coarse_shallow_grid_centered_oscillation_delta
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q)
    (CH : Compacts (SpatialCoordinates d) → ℝ)
    (hCH : ∀ K, 0 ≤ CH K)
    (hHmom : aux_lane4_reference_oscillation_moments_Hmom d CH)
    (m : ℕ) (hm : 0 < m)
    (hLayer : aux_lane4_reference_oscillation_moments_Layer d m)
    (Kbig : Compacts (SpatialCoordinates d))
    (E Cosc : ℝ)
    (hKbig_def : Kbig =
      aux_lane4_reference_oscillation_moments_Kball
        (0 : SpatialCoordinates d) (3 : ℝ))
    (hE : E = CH Kbig * (4 * (2 * q)) ^ 2 +
      (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2)
    (hCosc : Cosc = (2 * Real.exp E) ^ (1 / (2 * q)))
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (hM : M.delta ≤ delta0) :
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, |x i| ≤ (1 / 2 : ℝ)}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        ∀ (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          MemLp (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  classical
  dsimp only
  intro k y hy
  exact aux_lem_as_coarse_shallow_grid_centered_oscillation_point
    d hd q hq CH hCH hHmom m hm hLayer Kbig E Cosc
    hKbig_def hE hCosc delta0 hdelta0 hdelta1 M H hH hM k y hy

theorem aux_lem_as_coarse_shallow_grid_centered_oscillation_inner
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q)
    (CH : Compacts (SpatialCoordinates d) → ℝ)
    (hCH : ∀ K, 0 ≤ CH K)
    (hHmom : aux_lane4_reference_oscillation_moments_Hmom d CH)
    (m : ℕ) (hm : 0 < m)
    (hLayer : aux_lane4_reference_oscillation_moments_Layer d m)
    (Kbig : Compacts (SpatialCoordinates d))
    (E Cosc : ℝ)
    (hKbig_def : Kbig =
      aux_lane4_reference_oscillation_moments_Kball
        (0 : SpatialCoordinates d) (3 : ℝ))
    (hE : E = CH Kbig * (4 * (2 * q)) ^ 2 +
      (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2)
    (hCosc : Cosc = (2 * Real.exp E) ^ (1 / (2 * q))) :
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, |x i| ≤ (1 / 2 : ℝ)}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        ∀ (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          MemLp (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  classical
  intro delta0 hdelta0 hdelta1 M H hH hM
  exact aux_lem_as_coarse_shallow_grid_centered_oscillation_delta
    d hd q hq CH hCH hHmom m hm hLayer Kbig E Cosc
    hKbig_def hE hCosc delta0 hdelta0 hdelta1 M H hH hM

theorem aux_lem_as_coarse_shallow_grid_centered_oscillation_core
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q)
    (CH : Compacts (SpatialCoordinates d) → ℝ)
    (hCH : ∀ K, 0 ≤ CH K)
    (hHmom : aux_lane4_reference_oscillation_moments_Hmom d CH)
    (m : ℕ) (hm : 0 < m)
    (hLayer : aux_lane4_reference_oscillation_moments_Layer d m) :
    ∃ Cosc : ℝ, 0 < Cosc ∧
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, |x i| ≤ (1 / 2 : ℝ)}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        ∀ (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          MemLp (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  classical
  let Kbig := aux_lane4_reference_oscillation_moments_Kball
    (0 : SpatialCoordinates d) (3 : ℝ)
  let E : ℝ := CH Kbig * (4 * (2 * q)) ^ 2 +
    (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2
  let Cosc : ℝ := (2 * Real.exp E) ^ (1 / (2 * q))
  have hKbig_def : Kbig =
      aux_lane4_reference_oscillation_moments_Kball
        (0 : SpatialCoordinates d) (3 : ℝ) := by
    rfl
  have hE : E = CH Kbig * (4 * (2 * q)) ^ 2 +
      (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2 := by
    rfl
  have hCosc : Cosc = (2 * Real.exp E) ^ (1 / (2 * q)) := by
    rfl
  refine ⟨Cosc, by
    dsimp [Cosc]
    positivity, ?_⟩
  exact aux_lem_as_coarse_shallow_grid_centered_oscillation_inner
    d hd q hq CH hCH hHmom m hm hLayer Kbig E Cosc
    hKbig_def hE hCosc

theorem lem_as_coarse_shallow_grid_centered_oscillation_moments
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cosc : ℝ, 0 < Cosc ∧
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, |x i| ≤ (1 / 2 : ℝ)}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        ∀ (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          MemLp (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  classical
  obtain ⟨CH, hCH, hHmom⟩ :=
    exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  obtain ⟨m, hm, hLayer⟩ :=
    aux_lane4_reference_oscillation_moments_layer_exp hd
  exact aux_lem_as_coarse_shallow_grid_centered_oscillation_core
    d hd q hq CH hCH hHmom m hm hLayer

end Paper

