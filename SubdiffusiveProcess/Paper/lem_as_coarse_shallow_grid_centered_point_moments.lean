module

public import SubdiffusiveProcess.Paper.lane4_reference_point_moments
public import SubdiffusiveProcess.Paper.lane4_reference_oscillation_moments

@[expose] public section

open MeasureTheory Set Filter Metric ProbabilityTheory TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem lem_as_coarse_shallow_grid_centered_point_moments
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cmom Crate : ℝ,
      0 < Cmom ∧ 0 < Crate ∧
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, |x i| ≤ (1 / 2 : ℝ)}
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let s : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k omega x =>
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              Real.exp (G k omega x - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
        ∀ aexp : ℝ, aexp ∈ Set.Icc 1 (2 * q) →
          ∀ (N k : ℕ), k ≤ N → ∀ y ∈ K,
            Integrable (fun omega => (s N k omega y)^aexp +
              (s N k omega y)^(-aexp)) P ∧
            (∫ omega, (s N k omega y)^aexp +
              (s N k omega y)^(-aexp) ∂P) ≤
              Cmom * Real.exp (Crate * (aexp + aexp^2) * M.delta^2 * (k : ℝ)) ∧
            MemLp (fun omega => s N k omega y) (ENNReal.ofReal aexp) P ∧
              MemLp (fun omega => (s N k omega y)⁻¹)
              (ENNReal.ofReal aexp) P := by
  obtain ⟨CH, hCH, hHmom⟩ :=
    SubdiffusiveProcess.exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  let Kc : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall (0 : SpatialCoordinates d) 1,
      ProperSpace.isCompact_closedBall (0 : SpatialCoordinates d) 1⟩
  let c0 : ℝ := 3 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2
  let Cmom : ℝ := 4 * Real.exp (16 * CH Kc * q^2)
  let Crate : ℝ := 4 * (4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) + 2
  refine ⟨Cmom, Crate, ?_, ?_, ?_⟩
  · dsimp [Cmom]
    positivity
  · dsimp [Crate]
    have hbase : 0 ≤ ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2 := sq_nonneg _
    linarith
  · intro delta0 hdelta0pos hdelta0le M Rm H hH hMd
    dsimp
    intro a ha N k hkn y hy
    have ha1 : 0 < a := lt_of_lt_of_le zero_lt_one ha.1
    have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
    have haUpper : a ≤ 2 * q := ha.2
    have hyK : y ∈ (Kc : Set (SpatialCoordinates d)) := by
      change y ∈ Metric.closedBall (0 : SpatialCoordinates d) 1
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro i
      rw [Real.norm_eq_abs]
      exact (hy i).trans (by norm_num)
    have hHexp (t : ℝ) :
        Integrable (fun omega => Real.exp (t * H omega y))
          (chaosSampleLaw M).toMeasure ∧
        (∫ omega, Real.exp (t * H omega y)
          ∂(chaosSampleLaw M).toMeasure) ≤
          2 * Real.exp (CH Kc * t^2 * M.delta^2) := by
      have hnorm := hHmom M H hH Kc |t| (abs_nonneg t)
      have htarget : Measurable (fun omega => Real.exp (t * H omega y)) := by
        exact (measurable_const.mul
          ((continuous_eval_const y).measurable.comp hH.1)).exp
      have hdom : ∀ omega, t * H omega y ≤
          |t| * ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖ := by
        intro omega
        have hb := ((H omega).restrict (Kc : Set (SpatialCoordinates d))).norm_coe_le_norm
          ⟨y, hyK⟩
        calc
          t * H omega y ≤ |t * H omega y| := le_abs_self _
          _ = |t| * |H omega y| := abs_mul _ _
          _ ≤ |t| * ‖(H omega).restrict (Kc : Set (SpatialCoordinates d))‖ := by
            rw [← Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left hb (abs_nonneg t)
      have hint : Integrable (fun omega => Real.exp (t * H omega y))
          (chaosSampleLaw M).toMeasure := by
        refine hnorm.1.mono' htarget.aestronglyMeasurable ?_
        filter_upwards [] with omega
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (hdom omega)
      constructor
      · exact hint
      · calc
          (∫ omega, Real.exp (t * H omega y)
            ∂(chaosSampleLaw M).toMeasure) ≤
              ∫ omega, Real.exp (|t| * ‖(H omega).restrict
                (Kc : Set (SpatialCoordinates d))‖)
                ∂(chaosSampleLaw M).toMeasure :=
            integral_mono hint hnorm.1 (fun omega =>
              Real.exp_le_exp.mpr (hdom omega))
          _ ≤ 2 * Real.exp (CH Kc * |t|^2 * M.delta^2) := hnorm.2
          _ = 2 * Real.exp (CH Kc * t^2 * M.delta^2) := by
            rw [sq_abs]
    let r : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
    have hahompos (m : ℕ) :
        0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M m := by
      exact lt_of_lt_of_le (Real.exp_pos _) (Rm.ahom_lower m)
    have hrpos : 0 < r := by
      dsimp [r]
      exact div_pos (hahompos _) (hahompos _)
    have hratio : r ≤ Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
        (k : ℝ)) := by
      by_cases hk0 : k = 0
      · subst k
        dsimp [r]
        rw [div_self (ne_of_gt (hahompos N))]
        simp
      · have hsub : N - k < N := by omega
        have hord := Rm.ahom_ordering (N - k) N hsub
        apply (div_le_iff₀ (hahompos N)).2
        calc
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) ≤
              Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
                ((N : ℝ) - (N - k : ℕ))) *
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := hord.2
          _ = Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) *
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := by
            congr 2
            rw [Nat.cast_sub hkn]
            ring
    have hratioInv : r⁻¹ ≤ 1 := by
      by_cases hk0 : k = 0
      · subst k
        dsimp [r]
        rw [div_self (ne_of_gt (hahompos N))]
        simp
      · apply inv_le_one_of_one_le₀
        apply (le_div_iff₀ (hahompos N)).2
        simpa using (Rm.ahom_ordering (N - k) N (by omega)).1
    have hsumPos := aux_lane4_reference_point_moments_sum M k y (2 * a)
    have hsumNeg := aux_lane4_reference_point_moments_sum M k y (-2 * a)
    have hHPos := hHexp (2 * a)
    have hHNeg := hHexp (-2 * a)
    let center : BilateralField d → ℝ := fun omega =>
      (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
    have hsrepr (omega : BilateralField d) :
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (H omega y +
            ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
            (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
        r * Real.exp (H omega y + center omega) := by
      dsimp [r, center]
      rw [show H omega y +
          ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
          H omega y +
            (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
            (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) by ring]
    let A : ℝ := 4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2
    have hsumPosA :
        (∫ omega, Real.exp (2 * a * center omega)
            ∂(chaosSampleLaw M).toMeasure) ≤
          Real.exp (A * (|2 * a| + (2 * a)^2) * M.delta^2 * (k : ℝ)) := by
      simpa only [A] using hsumPos.2
    have hsumNegA :
        (∫ omega, Real.exp (-2 * a * center omega)
            ∂(chaosSampleLaw M).toMeasure) ≤
          Real.exp (A * (|-2 * a| + (-2 * a)^2) * M.delta^2 * (k : ℝ)) := by
      simpa only [A] using hsumNeg.2
    have hpointPos (omega : BilateralField d) :
        (r * Real.exp (H omega y + center omega))^a ≤
          (r^a / 2) * (Real.exp (2 * a * H omega y) +
            Real.exp (2 * a * center omega)) := by
      exact aux_lane4_reference_point_moments_amgm r (H omega y)
        (center omega) a hrpos
    have hHpointMeas : Measurable (fun omega : BilateralField d => H omega y) :=
      (continuous_eval_const y).measurable.comp hH.1
    have hsumMeas : Measurable (fun omega : BilateralField d =>
        ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y) := by
      apply Finset.measurable_sum
      intro j hj
      exact (continuous_eval_const y).measurable.comp
        (measurable_pi_apply (-(j : ℤ)))
    let F : BilateralField d → ℝ := fun omega =>
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        Real.exp (H omega y +
          ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
    have hFmeas : Measurable F := by
      dsimp [F]
      have hratioMeas : Measurable (fun _ : BilateralField d =>
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) := measurable_const
      exact hratioMeas.mul
        (((hHpointMeas.add hsumMeas).sub measurable_const).exp)
    have hFpos (omega : BilateralField d) : 0 < F omega := by
      dsimp [F]
      exact mul_pos (div_pos (hahompos _) (hahompos _)) (Real.exp_pos _)
    have hplusMeas : Measurable (fun omega : BilateralField d =>
        (F omega)^a) := by
      dsimp [F]
      fun_prop
    have hplusDom : Integrable (fun omega : BilateralField d =>
        (r^a / 2) * (Real.exp (2 * a * H omega y) +
          Real.exp (2 * a * center omega)))
        (chaosSampleLaw M).toMeasure := by
      have hA := hHPos.1.add hsumPos.1
      exact hA.const_mul (r^a / 2)
    have hplusInt : Integrable (fun omega : BilateralField d => (F omega)^a)
        (chaosSampleLaw M).toMeasure := by
      refine hplusDom.mono' hplusMeas.aestronglyMeasurable ?_
      filter_upwards [] with omega
      dsimp [F]
      rw [hsrepr omega]
      rw [abs_of_nonneg
        (Real.rpow_nonneg (mul_nonneg hrpos.le (Real.exp_pos _).le) _)]
      exact hpointPos omega
    have hinvrepr (omega : BilateralField d) :
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (H omega y +
            ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
            (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))^(-a) =
          (r⁻¹ * Real.exp (-(H omega y) - center omega))^a := by
      rw [hsrepr omega]
      rw [Real.rpow_neg (mul_nonneg hrpos.le (Real.exp_pos _).le)]
      rw [← Real.inv_rpow (mul_nonneg hrpos.le (Real.exp_pos _).le)]
      congr 1
      rw [mul_inv_rev, ← Real.exp_neg]
      ring
    have hpointNeg (omega : BilateralField d) :
        (r⁻¹ * Real.exp (-(H omega y) - center omega))^a ≤
          ((r⁻¹)^a / 2) * (Real.exp (-2 * a * H omega y) +
            Real.exp (-2 * a * center omega)) := by
      convert aux_lane4_reference_point_moments_amgm (r⁻¹) (-(H omega y))
        (-center omega) a (inv_pos.mpr hrpos) using 1 ; ring
    have hminusMeas : Measurable (fun omega : BilateralField d =>
        (F omega)^(-a)) := by
      dsimp [F]
      fun_prop
    have hminusDom : Integrable (fun omega : BilateralField d =>
        ((r⁻¹)^a / 2) * (Real.exp (-2 * a * H omega y) +
          Real.exp (-2 * a * center omega)))
        (chaosSampleLaw M).toMeasure := by
      have hA := hHNeg.1.add hsumNeg.1
      exact hA.const_mul ((r⁻¹)^a / 2)
    have hminusInt : Integrable (fun omega : BilateralField d => (F omega)^(-a))
        (chaosSampleLaw M).toMeasure := by
      refine hminusDom.mono' hminusMeas.aestronglyMeasurable ?_
      filter_upwards [] with omega
      dsimp [F]
      rw [hinvrepr omega]
      rw [abs_of_nonneg
        (Real.rpow_nonneg (mul_nonneg (inv_pos.mpr hrpos).le
          (Real.exp_pos _).le) _)]
      exact hpointNeg omega
    have hplusIntegral :
        (∫ omega, (F omega)^a
          ∂(chaosSampleLaw M).toMeasure) ≤
          (r^a / 2) *
            ((∫ omega, Real.exp (2 * a * H omega y)
                ∂(chaosSampleLaw M).toMeasure) +
              (∫ omega, Real.exp (2 * a * center omega)
                ∂(chaosSampleLaw M).toMeasure)) := by
      calc
        _ ≤ ∫ omega, (r^a / 2) *
            (Real.exp (2 * a * H omega y) +
              Real.exp (2 * a * center omega))
            ∂(chaosSampleLaw M).toMeasure := by
              apply integral_mono hplusInt hplusDom
              intro omega
              change (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
                  Real.exp (H omega y +
                    ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
                    (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))^a ≤ _
              rw [hsrepr omega]
              simpa using hpointPos omega
        _ = _ := by
          rw [integral_const_mul, integral_add hHPos.1 hsumPos.1]
    have hminusIntegral :
        (∫ omega, (F omega)^(-a)
          ∂(chaosSampleLaw M).toMeasure) ≤
          ((r⁻¹)^a / 2) *
            ((∫ omega, Real.exp (-2 * a * H omega y)
                ∂(chaosSampleLaw M).toMeasure) +
              (∫ omega, Real.exp (-2 * a * center omega)
                ∂(chaosSampleLaw M).toMeasure)) := by
      calc
        _ ≤ ∫ omega, ((r⁻¹)^a / 2) *
            (Real.exp (-2 * a * H omega y) +
              Real.exp (-2 * a * center omega))
            ∂(chaosSampleLaw M).toMeasure := by
              apply integral_mono hminusInt hminusDom
              intro omega
              change (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
                  Real.exp (H omega y +
                    ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
                    (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))^(-a) ≤ _
              rw [hinvrepr omega]
              simpa using hpointNeg omega
        _ = _ := by
          rw [integral_const_mul, integral_add hHNeg.1 hsumNeg.1]
    let T : ℝ := (a + a^2) * M.delta^2 * (k : ℝ)
    let E0 : ℝ := 16 * CH Kc * q^2
    have hTdef : T = (a + a^2) * M.delta^2 * (k : ℝ) := rfl
    have hA : 0 ≤ A := by
      dsimp [A]
      positivity
    have hδ : 0 ≤ M.delta := by
      exact M.shellPrefix.delta_pos.le
    have hδle : M.delta ≤ 1 := le_trans hMd hdelta0le
    have hδ2le : M.delta^2 ≤ 1 := by
      nlinarith [sq_nonneg M.delta, sq_nonneg (1 - M.delta)]
    have hT : 0 ≤ T := by
      dsimp [T]
      positivity
    have hE0 : 0 ≤ E0 := by
      dsimp [E0]
      exact mul_nonneg (mul_nonneg (by norm_num) (hCH Kc)) (sq_nonneg q)
    have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta^2 := by
      have hh := SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
      have hlog : Real.log 2 / 2 ≤ 1 := by
        have hlog' := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      have hprod := mul_le_mul_of_nonneg_right hlog (sq_nonneg M.delta)
      simpa using le_trans hh hprod
    have hsumAbsPos : |2 * a| = 2 * a := by
      rw [abs_of_nonneg]
      linarith
    have hsumAbsNeg : |-2 * a| = 2 * a := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    have hsumSq : (-2 * a)^2 = (2 * a)^2 := by ring
    have hsumBudgetPosNorm :
      A * (2 * a + (2 * a)^2) * M.delta^2 * (k : ℝ) ≤ 4 * A * T := by
      have hlin : 2 * a + (2 * a)^2 ≤ 4 * (a + a^2) :=
        aux_lane4_reference_point_moments_quadratic a ha1.le
      have hfac : 0 ≤ M.delta^2 * (k : ℝ) :=
        mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
      have hmul :
          (2 * a + (2 * a)^2) * (M.delta^2 * (k : ℝ)) ≤
            4 * (a + a^2) * (M.delta^2 * (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hlin hfac
      calc
        A * (2 * a + (2 * a)^2) * M.delta^2 * (k : ℝ) =
            A * ((2 * a + (2 * a)^2) * (M.delta^2 * (k : ℝ))) :=
              by simp only [mul_assoc]
        _ ≤ A * (4 * (a + a^2) * (M.delta^2 * (k : ℝ))) :=
          mul_le_mul_of_nonneg_left hmul hA
        _ = 4 * A * T := by
          rw [hTdef]
          simp only [mul_assoc, mul_left_comm, mul_comm]
    have hsumBudgetPos :
        A * (|2 * a| + (2 * a)^2) * M.delta^2 * (k : ℝ) ≤ 4 * A * T := by
      rw [hsumAbsPos]
      exact hsumBudgetPosNorm
    have hsumBudgetNeg :
        A * (|-2 * a| + (-2 * a)^2) * M.delta^2 * (k : ℝ) ≤ 4 * A * T := by
      rw [hsumAbsNeg, hsumSq]
      exact hsumBudgetPosNorm
    have hHbudgetPos : CH Kc * (2 * a)^2 * M.delta^2 ≤ E0 := by
      have hCH0 : 0 ≤ CH Kc := hCH Kc
      have haSq : (2 * a)^2 ≤ (4 * q)^2 := by
        apply (sq_le_sq₀ (by positivity) (by positivity)).2
        linarith
      dsimp [E0]
      calc
        CH Kc * (2 * a)^2 * M.delta^2 ≤ CH Kc * (2 * a)^2 * 1 :=
          mul_le_mul_of_nonneg_left hδ2le
            (mul_nonneg hCH0 (sq_nonneg _))
        _ ≤ CH Kc * (4 * q)^2 * 1 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left haSq hCH0
        _ = 16 * CH Kc * q^2 := by ring
    have hHbudgetNeg : CH Kc * (-2 * a)^2 * M.delta^2 ≤ E0 := by
      rw [hsumSq]
      exact hHbudgetPos
    have hdetBudget : 2 * a * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ) ≤ 2 * T := by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
      have h2a : 0 ≤ 2 * a := by positivity
      have h1 : 2 * a * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ) ≤
          2 * a * M.delta^2 * (k : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htau h2a) hk
      dsimp [T]
      have hlin : 2 * a ≤ 2 * (a + a^2) := by
        linarith [sq_nonneg a]
      have h2 := mul_le_mul_of_nonneg_right hlin
        (mul_nonneg (sq_nonneg M.delta) hk)
      calc
        2 * a * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ) ≤
            2 * a * M.delta^2 * (k : ℝ) := h1
        _ ≤ 2 * ((a + a^2) * M.delta^2 * (k : ℝ)) := by
          calc
            2 * a * M.delta^2 * (k : ℝ) =
                2 * a * (M.delta^2 * (k : ℝ)) := by ring
            _ ≤ 2 * (a + a^2) * (M.delta^2 * (k : ℝ)) := h2
            _ = 2 * ((a + a^2) * M.delta^2 * (k : ℝ)) := by ring
    have hrrpow : r^a ≤ Real.exp (2 * T) := by
      have hpow := Real.rpow_le_rpow hrpos.le hratio ha1.le
      have hpow' : r^a ≤ (Real.exp
          (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)))^a := hpow
      calc
        r^a ≤ (Real.exp
            (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)))^a := hpow'
        _ = Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ) * a) := by
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        _ = Real.exp (2 * a * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) := by
          congr 1
          ring
        _ ≤ Real.exp (2 * T) := by
          exact Real.exp_le_exp.mpr hdetBudget
    have hrrpowInv : (r⁻¹)^a ≤ 1 := by
      have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ r⁻¹) hratioInv ha1.le
      simpa using hpow
    have hbudget : 2 * T + 4 * A * T = Crate * T := by
      dsimp [Crate]
      ring
    have hbudget_le : 2 * T ≤ Crate * T := by
      have hnonneg : 0 ≤ 4 * A * T :=
        mul_nonneg (mul_nonneg (by norm_num) hA) hT
      rw [← hbudget]
      exact le_add_of_nonneg_right hnonneg
    have hplusExpBudget :
        2 * T + CH Kc * (2 * a)^2 * M.delta^2 ≤ Crate * T + E0 := by
      calc
        2 * T + CH Kc * (2 * a)^2 * M.delta^2 ≤ 2 * T + E0 :=
          add_le_add_right hHbudgetPos (2 * T)
        _ ≤ Crate * T + E0 := add_le_add_left hbudget_le E0
    have hplusSumExpBudget :
        2 * T + A * (|2 * a| + (2 * a)^2) * M.delta^2 * (k : ℝ) ≤
          Crate * T := by
      calc
        2 * T + A * (|2 * a| + (2 * a)^2) * M.delta^2 * (k : ℝ) ≤
            2 * T + 4 * A * T := add_le_add_right hsumBudgetPos (2 * T)
        _ = Crate * T := hbudget
    have hminusSumExpBudget :
        A * (|-2 * a| + (-2 * a)^2) * M.delta^2 * (k : ℝ) ≤
          Crate * T := by
      calc
        A * (|-2 * a| + (-2 * a)^2) * M.delta^2 * (k : ℝ) ≤
            4 * A * T := hsumBudgetNeg
        _ ≤ 2 * T + 4 * A * T :=
          le_add_of_nonneg_left (mul_nonneg (by norm_num) hT)
        _ = Crate * T := hbudget
    let Ep : ℝ := CH Kc * (2 * a)^2 * M.delta^2
    let En : ℝ := CH Kc * (-2 * a)^2 * M.delta^2
    let Sp : ℝ := A * (|2 * a| + (2 * a)^2) * M.delta^2 * (k : ℝ)
    let Sn : ℝ := A * (|-2 * a| + (-2 * a)^2) * M.delta^2 * (k : ℝ)
    have hEp : Ep ≤ E0 := by simpa [Ep] using hHbudgetPos
    have hEn : En ≤ E0 := by simpa [En] using hHbudgetNeg
    have hSp :
        (∫ omega, Real.exp (2 * a * center omega)
            ∂(chaosSampleLaw M).toMeasure) ≤ Real.exp Sp := by
      simpa [Sp] using hsumPosA
    have hSn :
        (∫ omega, Real.exp (-2 * a * center omega)
            ∂(chaosSampleLaw M).toMeasure) ≤ Real.exp Sn := by
      simpa [Sn] using hsumNegA
    have hplusRaw :
        (∫ omega, (F omega)^a ∂(chaosSampleLaw M).toMeasure) ≤
          (r^a / 2) *
            (2 * Real.exp Ep + Real.exp Sp) := by
      calc
        _ ≤ (r^a / 2) *
            ((∫ omega, Real.exp (2 * a * H omega y)
                ∂(chaosSampleLaw M).toMeasure) +
              (∫ omega, Real.exp (2 * a * center omega)
                ∂(chaosSampleLaw M).toMeasure)) := hplusIntegral
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add hHPos.2 hSp
          · positivity
    have hplusTerm1 :
        (r^a / 2) * (2 * Real.exp Ep) ≤
          Real.exp E0 * Real.exp (Crate * T) := by
      calc
        (r^a / 2) * (2 * Real.exp Ep) =
            r^a * Real.exp Ep :=
          aux_lane4_reference_point_moments_half_two _ _
        _ ≤ Real.exp (2 * T) *
            Real.exp Ep := by
              exact mul_le_mul_of_nonneg_right hrrpow (Real.exp_pos _).le
        _ = Real.exp (2 * T + Ep) := by
              exact (Real.exp_add _ _).symm
        _ ≤ Real.exp (Crate * T + E0) := by
              exact Real.exp_le_exp.mpr hplusExpBudget
        _ = Real.exp E0 * Real.exp (Crate * T) := by
              rw [show Crate * T + E0 = E0 + Crate * T by ring,
                Real.exp_add]
    have hplusTerm2 :
        (r^a / 2) * Real.exp Sp ≤ Real.exp E0 * Real.exp (Crate * T) := by
      have hnonneg : 0 ≤ r^a * Real.exp Sp := by positivity
      calc
        (r^a / 2) * Real.exp Sp ≤ r^a * Real.exp Sp := by
                calc
                  (r^a / 2) * Real.exp Sp =
                      (1 / 2 : ℝ) * (r^a * Real.exp Sp) :=
                    aux_lane4_reference_point_moments_half_mul _ _
                  _ ≤ 1 * (r^a * Real.exp Sp) := by
                    exact mul_le_mul_of_nonneg_right (by norm_num)
                      hnonneg
                  _ = _ := by ring
        _ ≤ Real.exp (2 * T) * Real.exp Sp := by
                exact mul_le_mul_of_nonneg_right hrrpow (Real.exp_pos _).le
        _ = Real.exp (2 * T + Sp) := by
                exact (Real.exp_add _ _).symm
        _ ≤ Real.exp (Crate * T) := by
              exact Real.exp_le_exp.mpr hplusSumExpBudget
        _ ≤ Real.exp E0 * Real.exp (Crate * T) := by
              calc
                Real.exp (Crate * T) = 1 * Real.exp (Crate * T) := by ring
                _ ≤ _ := by
                  exact mul_le_mul_of_nonneg_right (Real.one_le_exp hE0)
                    (Real.exp_pos _).le
    have hminusTerm1 :
        ((r⁻¹)^a / 2) * (2 * Real.exp En) ≤
          Real.exp E0 * Real.exp (Crate * T) := by
      calc
        ((r⁻¹)^a / 2) * (2 * Real.exp En) =
            (r⁻¹)^a * Real.exp En :=
          aux_lane4_reference_point_moments_half_two _ _
        _ ≤ Real.exp En := by
              calc
                (r⁻¹)^a * Real.exp En ≤ 1 * Real.exp En :=
                  mul_le_mul_of_nonneg_right hrrpowInv (Real.exp_pos En).le
                _ = Real.exp En := one_mul _
        _ ≤ Real.exp E0 := Real.exp_le_exp.mpr hEn
        _ ≤ Real.exp E0 * Real.exp (Crate * T) := by
              calc
                Real.exp E0 = Real.exp E0 * 1 := by ring
                _ ≤ _ := by
                  exact mul_le_mul_of_nonneg_left
                    (Real.one_le_exp (by
                      dsimp [Crate]
                      positivity)) (Real.exp_pos _).le
    have hminusTerm2 :
        ((r⁻¹)^a / 2) * Real.exp Sn ≤ Real.exp E0 * Real.exp (Crate * T) := by
      calc
        ((r⁻¹)^a / 2) * Real.exp Sn ≤ 1 * Real.exp Sn := by
                have hcoef : (r⁻¹)^a / 2 ≤ 1 :=
                  aux_lane4_reference_point_moments_half_le_one _ hrrpowInv
                exact mul_le_mul_of_nonneg_right hcoef (Real.exp_pos Sn).le
        _ = Real.exp Sn := one_mul _
        _ ≤ Real.exp (Crate * T) := by
              apply Real.exp_le_exp.mpr
              change A * (|-2 * a| + (-2 * a)^2) * M.delta^2 * (k : ℝ) ≤
                Crate * T
              exact hminusSumExpBudget
        _ ≤ Real.exp E0 * Real.exp (Crate * T) := by
              calc
                Real.exp (Crate * T) = 1 * Real.exp (Crate * T) := by ring
                _ ≤ _ := by
                  exact mul_le_mul_of_nonneg_right (Real.one_le_exp hE0)
                    (Real.exp_pos _).le
    let Iplus : ℝ := ∫ omega, (F omega)^a ∂(chaosSampleLaw M).toMeasure
    let Iminus : ℝ := ∫ omega, (F omega)^(-a) ∂(chaosSampleLaw M).toMeasure
    have hplusRawF : Iplus ≤
        (r^a / 2) * (2 * Real.exp Ep + Real.exp Sp) := by
      change (∫ omega, (F omega)^a ∂(chaosSampleLaw M).toMeasure) ≤ _
      exact hplusRaw
    have hminusRawF : Iminus ≤
        ((r⁻¹)^a / 2) * (2 * Real.exp En + Real.exp Sn) := by
      apply le_trans (show Iminus ≤
        ((r⁻¹)^a / 2) *
        ((∫ omega, Real.exp (-2 * a * H omega y)
              ∂(chaosSampleLaw M).toMeasure) +
            (∫ omega, Real.exp (-2 * a * center omega)
              ∂(chaosSampleLaw M).toMeasure)) by
        change (∫ omega, (F omega)^(-a) ∂(chaosSampleLaw M).toMeasure) ≤ _
        exact hminusIntegral)
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add hHNeg.2 hSn
      · exact div_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hrpos.le) _)
          (by norm_num)
    have hplusCore : Iplus ≤
        2 * (Real.exp E0 * Real.exp (Crate * T)) := by
      exact aux_lane4_reference_point_moments_combine_two
        Iplus (r^a / 2) (Real.exp Ep) (Real.exp Sp)
        (Real.exp E0 * Real.exp (Crate * T)) hplusRawF hplusTerm1 hplusTerm2
    have hminusCore : Iminus ≤
        2 * (Real.exp E0 * Real.exp (Crate * T)) := by
      exact aux_lane4_reference_point_moments_combine_two
        Iminus ((r⁻¹)^a / 2) (Real.exp En) (Real.exp Sn)
        (Real.exp E0 * Real.exp (Crate * T)) hminusRawF
        hminusTerm1 hminusTerm2
    have hplusBoundF : Iplus ≤ Cmom * Real.exp (Crate * T) := by
      calc
        _ ≤ 2 * (Real.exp E0 * Real.exp (Crate * T)) := hplusCore
        _ ≤ Cmom * Real.exp (Crate * T) := by
          simpa only [Cmom, E0] using
            aux_lane4_reference_point_moments_two_le_four
              (Real.exp (16 * CH Kc * q^2)) (Real.exp (Crate * T))
              (Real.exp_pos _).le (Real.exp_pos _).le
    have hminusBoundF : Iminus ≤ Cmom * Real.exp (Crate * T) := by
      calc
        _ ≤ 2 * (Real.exp E0 * Real.exp (Crate * T)) := hminusCore
        _ ≤ Cmom * Real.exp (Crate * T) := by
          simpa only [Cmom, E0] using
            aux_lane4_reference_point_moments_two_le_four
              (Real.exp (16 * CH Kc * q^2)) (Real.exp (Crate * T))
              (Real.exp_pos _).le (Real.exp_pos _).le

    have hp0 : ENNReal.ofReal a ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr ha1)
    have hptop : ENNReal.ofReal a ≠ ∞ := ENNReal.ofReal_ne_top
    have hplusNormInt :
        Integrable (fun omega : BilateralField d =>
          ‖F omega‖ ^ (ENNReal.ofReal a).toReal)
          (chaosSampleLaw M).toMeasure := by
      refine hplusInt.congr (Filter.Eventually.of_forall ?_)
      intro omega
      change (F omega)^a = ‖F omega‖ ^ (ENNReal.ofReal a).toReal
      rw [Real.norm_eq_abs, abs_of_pos (hFpos omega),
        ENNReal.toReal_ofReal ha1.le]
    have hminusNormInt :
        Integrable (fun omega : BilateralField d =>
          ‖(F omega)⁻¹‖ ^ (ENNReal.ofReal a).toReal)
          (chaosSampleLaw M).toMeasure := by
      refine hminusInt.congr (Filter.Eventually.of_forall ?_)
      intro omega
      change (F omega)^(-a) = ‖(F omega)⁻¹‖ ^ (ENNReal.ofReal a).toReal
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hFpos omega)),
        ENNReal.toReal_ofReal ha1.le, Real.inv_rpow (hFpos omega).le,
        ← Real.rpow_neg (hFpos omega).le]
    have hmemBase :
        MemLp F
          (ENNReal.ofReal a) (chaosSampleLaw M).toMeasure :=
      (integrable_norm_rpow_iff hFmeas.aestronglyMeasurable hp0 hptop).mp
        hplusNormInt
    have hmemInv :
        MemLp (fun omega : BilateralField d => (F omega)⁻¹)
          (ENNReal.ofReal a) (chaosSampleLaw M).toMeasure :=
      (integrable_norm_rpow_iff hFmeas.inv.aestronglyMeasurable hp0 hptop).mp
        hminusNormInt
    have hsumInt :
        Integrable (fun omega : BilateralField d =>
          (F omega)^a + (F omega)^(-a))
          (chaosSampleLaw M).toMeasure :=
      hplusInt.add hminusInt
    have hsumBound :
        (∫ omega : BilateralField d,
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
            Real.exp (H omega y +
              ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
              (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))^a +
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
            Real.exp (H omega y +
              ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) y -
              (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))^(-a)
            ∂(chaosSampleLaw M).toMeasure) ≤
          Cmom * Real.exp (Crate * (a + a^2) * M.delta^2 * (k : ℝ)) := by
      have hrawF :
          (∫ omega, (F omega)^a + (F omega)^(-a)
            ∂(chaosSampleLaw M).toMeasure) ≤
            Cmom * Real.exp (Crate * T) := by
        rw [integral_add hplusInt hminusInt]
        have hcore : Iplus + Iminus ≤
            Cmom * Real.exp (Crate * T) := by
          calc
            Iplus + Iminus ≤
                2 * (Real.exp E0 * Real.exp (Crate * T)) +
                  2 * (Real.exp E0 * Real.exp (Crate * T)) :=
              add_le_add hplusCore hminusCore
            _ = Cmom * Real.exp (Crate * T) := by
              dsimp [Cmom]
              ring
        simpa only [Iplus, Iminus] using hcore
      have hExpEq : Crate * T =
          Crate * (a + a^2) * M.delta^2 * (k : ℝ) := by
        rw [hTdef]
        ring
      calc
        _ = (∫ omega, (F omega)^a + (F omega)^(-a)
              ∂(chaosSampleLaw M).toMeasure) := by
          simp only [F]
        _ ≤ Cmom * Real.exp (Crate * T) := hrawF
        _ = _ := by rw [hExpEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [F] using hsumInt
    · exact hsumBound
    · simpa only [F] using hmemBase
    · simpa only [F] using hmemInv

end SubdiffusiveProcess.Paper


