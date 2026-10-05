module

public import SubdiffusiveProcess.Paper.lem_branch
public import SubdiffusiveProcess.Paper.lem_rare_tests_dyadic_condExp_ae_limit
public import SubdiffusiveProcess.Paper.lem_rare_tests_band_increment_bound
public import SubdiffusiveProcess.ResponseMoments.BandFiltration
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

theorem aux_dyadic_exp_sum_le (n : ℕ) :
    ∑ k ∈ Finset.range n, (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ) - 3) ≤ 1 / 8 := by
  have hrew : ∀ k : ℕ, (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ) - 3) = (1 / 2 : ℝ) ^ (k + 4) := by
    intro k
    have hexp : -((k + 1 : ℕ) : ℤ) - 3 = -(((k + 4 : ℕ) : ℤ)) := by
      push_cast; ring
    rw [hexp, zpow_neg, zpow_natCast, one_div, inv_pow]
  calc ∑ k ∈ Finset.range n, (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ) - 3)
      = ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 4) := by
        apply Finset.sum_congr rfl
        intro k _
        exact hrew k
    _ = (1 / 16 : ℝ) * ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [show k + 4 = 4 + k from Nat.add_comm k 4, pow_add]
        norm_num
    _ ≤ (1 / 16 : ℝ) * 2 := by
        have hsumm : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
          summable_geometric_of_norm_lt_one (by norm_num)
        have hle := Summable.sum_le_tsum (Finset.range n) (fun k _ => by positivity) hsumm
        rw [tsum_geometric_of_norm_lt_one (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)] at hle
        have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
        rw [h2] at hle
        exact mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = 1 / 8 := by norm_num

theorem aux_lem_rare_tests_dyadic_cover_pigeonhole (X : ℝ) (M : ℕ → ℝ)
    (hX : 1 / 2 < X) (hM0 : M 0 ≤ 3 / 8) (hlim : Tendsto M atTop (𝓝 X)) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ (2 : ℝ) ^ (-(ℓ : ℤ) - 3 : ℤ) ≤ M ℓ - M (ℓ - 1) := by
  by_contra h
  push Not at h
  have hb : ∀ n, M n ≤ 1 / 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      linarith
    · have hstep : ∀ k ∈ Finset.range n,
          M (k + 1) - M k < (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ) - 3) := by
        intro k _
        have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
        have hk := h (k + 1) hk1
        simpa [Nat.add_sub_cancel] using hk
      have hsum : M n - M 0 ≤ 1 / 8 := by
        rw [← Finset.sum_range_sub M n]
        calc ∑ k ∈ Finset.range n, (M (k + 1) - M k)
            ≤ ∑ k ∈ Finset.range n, (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ) - 3) :=
              Finset.sum_le_sum (fun k hk => le_of_lt (hstep k hk))
          _ ≤ 1 / 8 := aux_dyadic_exp_sum_le n
      linarith
  have hXle : X ≤ 1 / 2 := le_of_tendsto' hlim hb
  linarith

theorem aux_lem_rare_tests_dyadic_cover_window_mono (d : ℕ) (center : ℤ) {K h : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (h1 : center - 2 * (h : ℤ) ≤ center - (K : ℤ)) (h2 : center + (K : ℤ) ≤ center + (h : ℤ))
    (msK : MeasurableSpace (BilateralField d)) (msH : MeasurableSpace (BilateralField d))
    (hmsK : msK = MeasurableSpace.comap
        ((Set.Icc (center - (K : ℤ)) (center + (K : ℤ))).domRestrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (center - (K : ℤ)) (center + (K : ℤ))) → C(SpatialCoordinates d, ℝ))))
    (hmsH : msH = MeasurableSpace.comap
        ((Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))).domRestrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))) → C(SpatialCoordinates d, ℝ)))) :
    msK ≤ msH := by
  rw [hmsK, hmsH]
  have hmem : ∀ i : Set.Icc (center - (K : ℤ)) (center + (K : ℤ)),
      (i : ℤ) ∈ Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ)) :=
    fun i => ⟨le_trans h1 i.2.1, le_trans i.2.2 h2⟩
  let R_K : BilateralField d →
      ((i : Set.Icc (center - (K : ℤ)) (center + (K : ℤ))) → C(SpatialCoordinates d, ℝ)) :=
    fun x i => x i.1
  let R_H : BilateralField d →
      ((j : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))) → C(SpatialCoordinates d, ℝ)) :=
    fun x j => x j.1
  change MeasurableSpace.comap R_K inferInstance ≤ MeasurableSpace.comap R_H inferInstance
  let g : ((j : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))) → C(SpatialCoordinates d, ℝ)) →
      ((i : Set.Icc (center - (K : ℤ)) (center + (K : ℤ))) → C(SpatialCoordinates d, ℝ)) :=
    fun φ i => φ (⟨(i : ℤ), hmem i⟩ : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ)))
  have heq : R_K = g ∘ R_H := by
    funext x i; rfl
  have hg : Measurable g := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (a := (⟨(i : ℤ), hmem i⟩ : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))))
  rw [heq, ← MeasurableSpace.comap_comp]
  apply MeasurableSpace.comap_mono
  exact measurable_iff_comap_le.mp hg

theorem aux_lem_rare_tests_dyadic_cover_condExp_meas (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) (center : ℤ) (X : BilateralField d → ℝ) (H : ℕ) :
    let Bsym := MeasurableSpace.comap
      ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
      (inferInstance : MeasurableSpace
        ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) → C(SpatialCoordinates d, ℝ)))
    Measurable[Bsym] (fun ω => (P[X | Bsym]) ω) := by
  dsimp only
  exact stronglyMeasurable_condExp.measurable

theorem aux_lem_rare_tests_dyadic_cover_markov_lp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (p C ε : ℝ)
    (hp : 1 ≤ p) (hε : 0 < ε) (hC : 0 < C)
    (_hfmeas : AEStronglyMeasurable f μ)
    (hlp : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C)
    (_hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ 1) :
    μ {ω | ε < |f ω|} ≤ ENNReal.ofReal (C ^ p * (ε⁻¹) ^ p) := by
  have hp_pos : (0:ℝ) < p := lt_of_lt_of_le one_pos hp
  have hpnn : 0 ≤ p := le_of_lt hp_pos
  have hεnn : 0 ≤ ε := le_of_lt hε
  have hCnn : 0 ≤ C := le_of_lt hC
  have hsub : {ω : α | ε < |f ω|} ⊆ {x : α | ENNReal.ofReal ε ≤ ‖f x‖ₑ} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hω)
  have hmarkov : μ {x : α | ENNReal.ofReal ε ≤ ‖f x‖ₑ} ≤
      (ENNReal.ofReal ε)⁻¹ ^ (ENNReal.ofReal p).toReal *
        eLpNorm f (ENNReal.ofReal p) μ ^ (ENNReal.ofReal p).toReal :=
    meas_ge_le_mul_pow_eLpNorm_enorm μ (ENNReal.ofReal_ne_zero_iff.mpr hp_pos)
      ENNReal.ofReal_ne_top (ENNReal.ofReal_ne_zero_iff.mpr hε)
      (fun h => absurd h ENNReal.ofReal_ne_top)
  rw [ENNReal.toReal_ofReal hpnn] at hmarkov
  refine ((measure_mono hsub).trans hmarkov).trans ?_
  have hB : eLpNorm f (ENNReal.ofReal p) μ ^ p ≤ ENNReal.ofReal (C ^ p) := by
    refine (ENNReal.rpow_le_rpow hlp hpnn).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg hCnn hpnn]
  have hA : (ENNReal.ofReal ε)⁻¹ ^ p = ENNReal.ofReal (ε⁻¹ ^ p) := by
    rw [← ENNReal.ofReal_inv_of_pos hε,
      ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hεnn) hpnn]
  rw [hA]
  calc ENNReal.ofReal (ε⁻¹ ^ p) * eLpNorm f (ENNReal.ofReal p) μ ^ p
      ≤ ENNReal.ofReal (ε⁻¹ ^ p) * ENNReal.ofReal (C ^ p) := mul_le_mul_right hB _
    _ = ENNReal.ofReal (C ^ p * ε⁻¹ ^ p) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hεnn) p), mul_comm]

theorem aux_geom_rpow_eq (Cstar a p x : ℝ) (hC : 0 ≤ Cstar) :
    (16 / 3 : ℝ) ^ p * (Cstar * (3 : ℝ) ^ (-(a * x))) ^ p
      = ((16 / 3) * Cstar) ^ p * Real.exp (-(a * p * Real.log 3 * x)) := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h3pos : (0 : ℝ) < 3 := by norm_num
  calc
    (16 / 3 : ℝ) ^ p * (Cstar * (3 : ℝ) ^ (-(a * x))) ^ p
        = (16 / 3 : ℝ) ^ p * (Cstar ^ p * ((3 : ℝ) ^ (-(a * x))) ^ p) := by
          rw [Real.mul_rpow hC (Real.rpow_nonneg h3 _)]
      _ = ((16 / 3 : ℝ) ^ p * Cstar ^ p) * ((3 : ℝ) ^ (-(a * x))) ^ p := by ring
      _ = (((16 / 3) * Cstar) ^ p) * ((3 : ℝ) ^ (-(a * x))) ^ p := by
          rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16/3) hC]
      _ = (((16 / 3) * Cstar) ^ p) * (3 : ℝ) ^ ((-(a * x)) * p) := by
          rw [Real.rpow_mul h3 (-(a * x)) p]
      _ = (((16 / 3) * Cstar) ^ p) * Real.exp (Real.log 3 * ((-(a * x)) * p)) := by
          rw [Real.rpow_def_of_pos h3pos]
      _ = ((16 / 3) * Cstar) ^ p * Real.exp (-(a * p * Real.log 3 * x)) := by
          congr 1
          ring

theorem aux_geom_exp_eq (B a p x : ℝ) :
    Real.exp (-(B * x)) / 2
      = Real.exp ((a * p * Real.log 3 - B) * x) * Real.exp (-(a * p * Real.log 3 * x)) / 2 := by
  have h : (a * p * Real.log 3 - B) * x + (-(a * p * Real.log 3 * x)) = -(B * x) := by ring
  rw [← Real.exp_add, h]

theorem aux_lem_rare_tests_dyadic_cover_geom_H0 (Cstar a p B : ℝ)
    (hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p) (hB : 0 < B)
    (hBab : 4 * B < a * p * Real.log 3) :
    ∃ H0 : ℕ, 0 < H0 ∧
      (16 / 3 : ℝ) ^ p * (Cstar * (3 : ℝ) ^ (-(a * (H0 : ℝ)))) ^ p ≤
        Real.exp (-(B * (H0 : ℝ))) / 2 := by
  set R : ℝ := Real.log (2 * ((16 / 3) * Cstar) ^ p) / (a * p * Real.log 3 - B) with hR
  refine ⟨max 1 (Nat.ceil R + 1), ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (le_max_left _ _)
  · set H0 : ℕ := max 1 (Nat.ceil R + 1) with hH0
    have hD : 0 < a * p * Real.log 3 - B := by nlinarith [hBab, hB]
    have hceil : Nat.ceil R ≤ H0 := by
      rw [hH0]
      exact le_trans (Nat.le_succ _) (le_max_right _ _)
    have hcast : (Nat.ceil R : ℝ) ≤ (H0 : ℝ) := by exact_mod_cast hceil
    have hH0geR : R ≤ (H0 : ℝ) := le_trans (Nat.le_ceil R) hcast
    have hlogbound : Real.log (2 * ((16 / 3) * Cstar) ^ p) ≤ (a * p * Real.log 3 - B) * (H0 : ℝ) := by
      have hRle : Real.log (2 * ((16 / 3) * Cstar) ^ p) / (a * p * Real.log 3 - B) ≤ (H0 : ℝ) := by
        rw [← hR]; exact hH0geR
      calc Real.log (2 * ((16 / 3) * Cstar) ^ p)
          ≤ (H0 : ℝ) * (a * p * Real.log 3 - B) := (div_le_iff₀ hD).mp hRle
        _ = (a * p * Real.log 3 - B) * (H0 : ℝ) := by ring
    have hCpos : (0 : ℝ) < (16 / 3) * Cstar := by positivity
    have hKpos : (0 : ℝ) < ((16 / 3) * Cstar) ^ p := Real.rpow_pos_of_pos hCpos p
    have hpos_arg : (0 : ℝ) < 2 * ((16 / 3) * Cstar) ^ p := by linarith
    have hexpD : Real.exp (Real.log (2 * ((16 / 3) * Cstar) ^ p))
        ≤ Real.exp ((a * p * Real.log 3 - B) * (H0 : ℝ)) := Real.exp_le_exp.mpr hlogbound
    have htwoK : 2 * ((16 / 3) * Cstar) ^ p
        ≤ Real.exp ((a * p * Real.log 3 - B) * (H0 : ℝ)) := by
      rwa [Real.exp_log hpos_arg] at hexpD
    have hLHS := aux_geom_rpow_eq Cstar a p (H0 : ℝ) hCstar.le
    have hRHS := aux_geom_exp_eq B a p (H0 : ℝ)
    rw [hLHS, hRHS]
    have h2 : 2 * ((16 / 3) * Cstar) ^ p * (Real.exp (-(a * p * Real.log 3 * (H0 : ℝ))) / 2)
        ≤ Real.exp ((a * p * Real.log 3 - B) * (H0 : ℝ)) * (Real.exp (-(a * p * Real.log 3 * (H0 : ℝ))) / 2) :=
      mul_le_mul_of_nonneg_right htwoK (by positivity)
    have heq : ((16 / 3) * Cstar) ^ p * Real.exp (-(a * p * Real.log 3 * (H0 : ℝ)))
        = 2 * ((16 / 3) * Cstar) ^ p * (Real.exp (-(a * p * Real.log 3 * (H0 : ℝ))) / 2) := by ring
    rw [heq, mul_div_assoc]
    exact h2

theorem aux_lem_rare_tests_dyadic_cover_aesm (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) (center : ℤ) (H : ℕ) (f : BilateralField d → ℝ)
    (hf : AEStronglyMeasurable f P) :
    AEStronglyMeasurable (fun ω => f ω -
      (P[f | MeasurableSpace.comap
        ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) →
            C(SpatialCoordinates d, ℝ)))]) ω) P := by
    have hmeas : Measurable (domRestrict (Set.Icc (center - (H : ℤ)) (center + (H : ℤ)))
        : BilateralField d → ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) → C(SpatialCoordinates d, ℝ))) := by
      simpa using! (Measurable.of_eval fun i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ)) => measurable_pi_apply (i : ℤ))
    have hle : MeasurableSpace.comap ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) → C(SpatialCoordinates d, ℝ)))
        ≤ (inferInstance : MeasurableSpace (BilateralField d)) := Measurable.comap_le hmeas
    exact hf.sub (AEStronglyMeasurable.mono hle
      ((MeasureTheory.stronglyMeasurable_condExp (μ := P) (f := f)).aestronglyMeasurable))

theorem aux_lem_rare_tests_dyadic_cover_pow_inj {H0 l l' : ℕ} (hH0 : 0 < H0) (h : 2 ^ l * H0 = 2 ^ l' * H0) : l = l' := by
  have h2 : 2 ^ l = 2 ^ l' := Nat.eq_of_mul_eq_mul_right hH0 h
  exact Nat.pow_right_injective (by norm_num) h2

theorem aux_lem_rare_tests_dyadic_cover_geom_exp_eq (Cstar a p H : ℝ) (hCstar : 0 < Cstar) :
    (Cstar * (3 : ℝ) ^ (-(a * H))) ^ p = Cstar ^ p * Real.exp (-(a * p * Real.log 3 * H)) := by
  rw [Real.mul_rpow hCstar.le (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (-(a * H)) p]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3) (-(a * H) * p)]
  rw [show Real.log 3 * (-(a * H) * p) = -(a * p * Real.log 3 * H) by ring]

theorem aux_lem_rare_tests_dyadic_cover_geom_transfer_all (Cstar a p B : ℝ)
    (hCstar : 0 ≤ Cstar) (_ha : 0 < a) (_hp : 0 < p) (_hB : 0 < B)
    (hBab : B < a * p * Real.log 3) {H0g H0 : ℕ} (h : H0g ≤ H0)
    (hG : (16 / 3 : ℝ) ^ p * (Cstar * (3 : ℝ) ^ (-(a * (H0g : ℝ)))) ^ p ≤
      Real.exp (-(B * (H0g : ℝ))) / 2) :
    (16 / 3 : ℝ) ^ p * (Cstar * (3 : ℝ) ^ (-(a * (H0 : ℝ)))) ^ p ≤
      Real.exp (-(B * (H0 : ℝ))) / 2 := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hD : 0 < a * p * Real.log 3 - B := by linarith
  have hcast : ((H0g : ℕ) : ℝ) ≤ ((H0 : ℕ) : ℝ) := by exact_mod_cast h
  have eq_L : ∀ H : ℕ, (Cstar * (3:ℝ)^(-(a*↑H)))^p = Cstar^p * Real.exp (-(a*p*Real.log 3 * ↑H)) := by
    intro H
    have h3 : (0:ℝ) ≤ 3 := by norm_num
    have hstep : (Cstar * (3:ℝ)^(-(a*↑H)))^p = Cstar^p * ((3:ℝ)^(-(a*↑H)))^p :=
      Real.mul_rpow hCstar (Real.rpow_nonneg h3 _)
    rw [hstep]
    congr 1
    rw [← Real.rpow_mul h3]
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
    congr 1
    ring
  have hG' : (16/3:ℝ)^p * (Cstar^p * Real.exp (-(a*p*Real.log 3 * ↑H0g))) ≤ Real.exp (-(B*↑H0g))/2 := by
    rw [eq_L H0g] at hG
    exact hG
  have step1 : 2 * ((16/3:ℝ)^p * (Cstar^p * Real.exp (-(a*p*Real.log 3 * ↑H0g)))) ≤ Real.exp (-(B*↑H0g)) := by
    have hm := mul_le_mul_of_nonneg_left hG' (by norm_num : (0:ℝ) ≤ 2)
    have h2 : 2 * (Real.exp (-(B*↑H0g))/2) = Real.exp (-(B*↑H0g)) := by ring
    rwa [h2] at hm
  have hBg : 2*(16/3:ℝ)^p*Cstar^p ≤ Real.exp ((a*p*Real.log 3 - B)*↑H0g) := by
    have hBexp : Real.exp (-(B*↑H0g)) = Real.exp (-(a*p*Real.log 3 * ↑H0g)) * Real.exp ((a*p*Real.log 3 - B)*↑H0g) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hBexp] at step1
    have hL : 2 * ((16/3:ℝ)^p * (Cstar^p * Real.exp (-(a*p*Real.log 3 * ↑H0g)))) = Real.exp (-(a*p*Real.log 3 * ↑H0g)) * (2*(16/3:ℝ)^p*Cstar^p) := by ring
    rw [hL] at step1
    exact le_of_mul_le_mul_left step1 (Real.exp_pos _)
  have hA : 2*(16/3:ℝ)^p*Cstar^p ≤ Real.exp ((a*p*Real.log 3 - B)*↑H0) := by
    calc 2*(16/3:ℝ)^p*Cstar^p ≤ Real.exp ((a*p*Real.log 3 - B)*↑H0g) := hBg
      _ ≤ Real.exp ((a*p*Real.log 3 - B)*↑H0) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcast (le_of_lt hD))
  have hmid : (2*(16/3:ℝ)^p*Cstar^p) * Real.exp (-(a*p*Real.log 3*↑H0)) ≤ Real.exp (-(B*↑H0)) := by
    have hm := mul_le_mul_of_nonneg_right hA (le_of_lt (Real.exp_pos (-(a*p*Real.log 3*↑H0))))
    have hR : Real.exp ((a*p*Real.log 3 - B)*↑H0) * Real.exp (-(a*p*Real.log 3*↑H0)) = Real.exp (-(B*↑H0)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [hR] at hm
  rw [eq_L H0]
  have hY : (16/3:ℝ)^p * (Cstar^p * Real.exp (-(a*p*Real.log 3 * ↑H0))) = ((2*(16/3:ℝ)^p*Cstar^p) * Real.exp (-(a*p*Real.log 3*↑H0))) / 2 := by ring
  rw [hY]
  exact div_le_div_of_nonneg_right hmid (by norm_num : (0:ℝ) ≤ 2)

theorem aux_lem_rare_tests_dyadic_cover_clause_empty (Cgeom : ℝ) (_hCgeom : 4 ≤ Cgeom) (d : ℕ) (_hd : 1 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (P : Measure (BilateralField d)) [IsProbabilityMeasure P] (center : ℤ) (X : ℕ → BilateralField d → ℝ) (_hX01 : ∀ (m : ℕ) (ω : BilateralField d), X m ω ∈ Icc 0 1) (_hmeas : ∀ (m : ℕ), Measurable (X m)) (_hprob : TendstoInMeasure P X atTop fun (_x : BilateralField d) => 0) (Cstar a p : ℝ) (_hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p) (Bsym0 : ℕ → MeasurableSpace (BilateralField d)) (_Bsym0_def : Bsym0 = fun (H : ℕ) => MeasurableSpace.comap (Icc (center - ↑H) (center + ↑H)).domRestrict inferInstance) (_hE : ∀ (m H : ℕ), eLpNorm (fun (ω : BilateralField d) => X m ω - P[X m|Bsym0 H] ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (H : ℝ))))) (_hD : ∀ (m H0 : ℕ), 0 < H0 → ∀ᵐ (ω : BilateralField d) ∂P, Tendsto (fun (ell : ℕ) => P[X m|Bsym0 (2 ^ ell * H0)] ω) atTop (𝓝 (X m ω))) (_hI : ∀ (B : ℝ), 0 < B → Cgeom * B < a * p * Real.log 3 → ∃ (Hinc : ℕ), 0 < Hinc ∧ ∀ (H0 : ℕ), Hinc ≤ H0 → ∀ (m ell : ℕ), 1 ≤ ell → P {ω : BilateralField d | (2 : ℝ) ^ (-((ell : ℤ)) - 3) ≤ P[X m|Bsym0 (2 ^ ell * H0)] ω - P[X m|Bsym0 (2 ^ (ell - 1) * H0)] ω} ≤ ENNReal.ofReal (Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))))) (B : ℝ) (_hB : 0 < B) (_hBab : Cgeom * B < a * p * Real.log 3) (Hinc : ℕ) (_hHinc0 : 0 < Hinc) (_hHinc : ∀ (H0 : ℕ), Hinc ≤ H0 → ∀ (m ell : ℕ), 1 ≤ ell → P {ω : BilateralField d | (2 : ℝ) ^ (-((ell : ℤ)) - 3) ≤ P[X m|Bsym0 (2 ^ ell * H0)] ω - P[X m|Bsym0 (2 ^ (ell - 1) * H0)] ω} ≤ ENNReal.ofReal (Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))))) (H0g : ℕ) (_hH0g0 : 0 < H0g) (_hH0g_geom : (16 / 3) ^ p * (Cstar * (3 : ℝ) ^ (-(a * (H0g : ℝ)))) ^ p ≤ Real.exp (-(B * (H0g : ℝ))) / 2) (H0 : ℕ) (H0_def : H0 = max Hinc (max H0g 1)) (_hK : Hinc ≤ H0) (_hK0 : 1 ≤ H0) (_hH00 : 0 < H0) (_hgeomH0 : (16 / 3) ^ p * (Cstar * (3 : ℝ) ^ (-(a * (H0 : ℝ)))) ^ p ≤ Real.exp (-(B * (H0 : ℝ))) / 2) (m : ℕ) (_hm : H0 ≤ m) (W : ℕ+ → Set (BilateralField d)) (W_def : W = fun (h : ℕ+) => (if (h : ℕ) = H0 then (fun (ω : BilateralField d) => X m ω - P[X m|Bsym0 H0] ω) ⁻¹' Set.Ici (1 / 4 : ℝ) else ∅) ∪ ⋃ (l : { l : ℕ // 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ) }), {ω : BilateralField d | (2 : ℝ) ^ (-(((l : ℕ) : ℤ)) - 3) ≤ P[X m|Bsym0 (2 ^ (l : ℕ) * H0)] ω - P[X m|Bsym0 (2 ^ ((l : ℕ) - 1) * H0)] ω}) :
    ∀ (h : ℕ+), (h : ℕ) < H0 → W h = ∅ := by
  intro h hlt
  simp only [W_def]
  have hne : (h : ℕ) ≠ H0 := by omega
  rw [ite_eq_right hne]
  have : IsEmpty { l : ℕ // 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ) } :=
    ⟨fun l => by
      have hl1 : 1 ≤ (l : ℕ) := l.2.1
      have h2l : 2 ≤ 2 ^ (l : ℕ) := by
        have h := Nat.pow_le_pow_right (show 0 < (2 : ℕ) by norm_num) hl1
        simpa using h
      have hle : 2 * H0 ≤ 2 ^ (l : ℕ) * H0 := Nat.mul_le_mul_right H0 h2l
      omega⟩
  rw [iUnion_of_empty, empty_union]

theorem aux_lem_rare_tests_dyadic_cover_clause_meas (Cgeom : ℝ) (_hCgeom : 4 ≤ Cgeom) (d : ℕ) (_hd : 1 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (P : Measure (BilateralField d)) [IsProbabilityMeasure P] (center : ℤ) (X : ℕ → BilateralField d → ℝ) (_hX01 : ∀ (m : ℕ) (ω : BilateralField d), X m ω ∈ Icc 0 1) (hmeas : ∀ (m : ℕ), Measurable (X m)) (_hprob : TendstoInMeasure P X atTop fun (_x : BilateralField d) => 0) (Cstar a p : ℝ) (_hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p) (Bsym0 : ℕ → MeasurableSpace (BilateralField d)) (Bsym0_def : Bsym0 = fun (H : ℕ) => MeasurableSpace.comap (Icc (center - ↑H) (center + ↑H)).domRestrict inferInstance) (_hE : ∀ (m H : ℕ), eLpNorm (fun (ω : BilateralField d) => X m ω - P[X m|Bsym0 H] ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (H : ℝ))))) (_hD : ∀ (m H0 : ℕ), 0 < H0 → ∀ᵐ (ω : BilateralField d) ∂P, Tendsto (fun (ell : ℕ) => P[X m|Bsym0 (2 ^ ell * H0)] ω) atTop (𝓝 (X m ω))) (_hI : ∀ (B : ℝ), 0 < B → Cgeom * B < a * p * Real.log 3 → ∃ (Hinc : ℕ), 0 < Hinc ∧ ∀ (H0 : ℕ), Hinc ≤ H0 → ∀ (m ell : ℕ), 1 ≤ ell → P {ω : BilateralField d | (2 : ℝ) ^ (-((ell : ℤ)) - 3) ≤ P[X m|Bsym0 (2 ^ ell * H0)] ω - P[X m|Bsym0 (2 ^ (ell - 1) * H0)] ω} ≤ ENNReal.ofReal (Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))))) (B : ℝ) (_hB : 0 < B) (_hBab : Cgeom * B < a * p * Real.log 3) (Hinc : ℕ) (_hHinc0 : 0 < Hinc) (_hHinc : ∀ (H0 : ℕ), Hinc ≤ H0 → ∀ (m ell : ℕ), 1 ≤ ell → P {ω : BilateralField d | (2 : ℝ) ^ (-((ell : ℤ)) - 3) ≤ P[X m|Bsym0 (2 ^ ell * H0)] ω - P[X m|Bsym0 (2 ^ (ell - 1) * H0)] ω} ≤ ENNReal.ofReal (Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))))) (H0g : ℕ) (_hH0g0 : 0 < H0g) (_hH0g_geom : (16 / 3) ^ p * (Cstar * (3 : ℝ) ^ (-(a * (H0g : ℝ)))) ^ p ≤ Real.exp (-(B * (H0g : ℝ))) / 2) (H0 : ℕ) (_H0_def : H0 = max Hinc (max H0g 1)) (_hK : Hinc ≤ H0) (_hK0 : 1 ≤ H0) (_hH00 : 0 < H0) (_hgeomH0 : (16 / 3) ^ p * (Cstar * (3 : ℝ) ^ (-(a * (H0 : ℝ)))) ^ p ≤ Real.exp (-(B * (H0 : ℝ))) / 2) (m : ℕ) (_hm : H0 ≤ m) (W : ℕ+ → Set (BilateralField d)) (W_def : W = fun (h : ℕ+) => (if (h : ℕ) = H0 then (fun (ω : BilateralField d) => X m ω - P[X m|Bsym0 H0] ω) ⁻¹' Set.Ici (1 / 4 : ℝ) else ∅) ∪ ⋃ (l : { l : ℕ // 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ) }), {ω : BilateralField d | (2 : ℝ) ^ (-(((l : ℕ) : ℤ)) - 3) ≤ P[X m|Bsym0 (2 ^ (l : ℕ) * H0)] ω - P[X m|Bsym0 (2 ^ ((l : ℕ) - 1) * H0)] ω}) :
    ∀ (h : ℕ+), MeasurableSet (W h) := by
  intro h
  rw [W_def]
  have hc : ∀ H : ℕ, Measurable (fun ω : BilateralField d => P[X m|Bsym0 H] ω) := fun H => by
    have hle : Bsym0 H ≤ (inferInstance : MeasurableSpace (BilateralField d)) := by
      rw [Bsym0_def]
      exact (Set.measurable_restrict _).comap_le
    exact ((stronglyMeasurable_condExp (m := Bsym0 H) (μ := P) (f := X m)).measurable).mono hle le_rfl
  refine MeasurableSet.union ?_ ?_
  · by_cases hh : (h : ℕ) = H0
    · rw [ite_eq_left hh]
      exact MeasurableSet.preimage measurableSet_Ici ((hmeas m).sub (hc H0))
    · rw [ite_eq_right hh]
      exact MeasurableSet.empty
  · apply MeasurableSet.iUnion
    intro l
    exact MeasurableSet.preimage measurableSet_Ici ((hc (2 ^ (l : ℕ) * H0)).sub (hc (2 ^ ((l : ℕ) - 1) * H0)))

theorem aux_lem_rare_tests_dyadic_cover_1 (Cgeom : ℝ) (hCgeom : 4 ≤ Cgeom) (d : ℕ) (_hd : 1 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (P : Measure (BilateralField d)) [IsProbabilityMeasure P] (center : ℤ) (X : ℕ → BilateralField d → ℝ) (_hX01 : ∀ (m : ℕ) (ω : BilateralField d), X m ω ∈ Icc 0 1) (_hmeas : ∀ (m : ℕ), Measurable (X m)) (_hprob : TendstoInMeasure P X atTop fun (_x : BilateralField d) => 0) (Cstar a p : ℝ) (hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p) (Bsym0 : ℕ → MeasurableSpace (BilateralField d)) (_Bsym0_def : Bsym0 = fun (H : ℕ) => MeasurableSpace.comap (Icc (center - ↑H) (center + ↑H)).domRestrict inferInstance) (_hE : ∀ (m H : ℕ), eLpNorm (fun (ω : BilateralField d) => X m ω - P[X m|Bsym0 H] ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cstar * 3 ^ (-(a * ↑H)))) (_hD : ∀ (m H0 : ℕ), 0 < H0 → ∀ᵐ (ω : BilateralField d) ∂P, Tendsto (fun (ell : ℕ) => P[X m|Bsym0 (2 ^ ell * H0)] ω) atTop (𝓝 (X m ω))) (_hI : ∀ (B : ℝ), 0 < B → Cgeom * B < a * p * Real.log 3 → ∃ (Hinc : ℕ), 0 < Hinc ∧ ∀ (H0 : ℕ), Hinc ≤ H0 → ∀ (m ell : ℕ), 1 ≤ ell → P {ω : BilateralField d | (2 : ℝ) ^ (-(↑ell : ℝ) - 3) ≤ P[X m|Bsym0 (2 ^ ell * H0)] ω - P[X m|Bsym0 (2 ^ (ell - 1) * H0)] ω} ≤ ENNReal.ofReal (Real.exp (-(B * ↑(2 ^ ell * H0))))) (B : ℝ) (hB : 0 < B) (hBab : Cgeom * B < a * p * Real.log 3) (Hinc : ℕ) (_hHinc0 : 0 < Hinc) (_hHinc : ∀ (H0 : ℕ), Hinc ≤ H0 → ∀ (m ell : ℕ), 1 ≤ ell → P {ω : BilateralField d | (2 : ℝ) ^ (-(↑ell : ℝ) - 3) ≤ P[X m|Bsym0 (2 ^ ell * H0)] ω - P[X m|Bsym0 (2 ^ (ell - 1) * H0)] ω} ≤ ENNReal.ofReal (Real.exp (-(B * ↑(2 ^ ell * H0))))) : ∃ (H0 : ℕ), 0 < H0 ∧ (16 / 3) ^ p * (Cstar * 3 ^ (-(a * ↑H0))) ^ p ≤ Real.exp (-(B * ↑H0)) / 2 := by
  have h3 : (0:ℝ) < 3 := by norm_num
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set c : ℝ := a * p * Real.log 3 with hc
  have hcB : 0 < c - B := by
    have h2 : Cgeom * B < c := by rw [hc]; exact hBab
    have h1 : (4:ℝ) * B ≤ Cgeom * B := by nlinarith [hB, hCgeom]
    linarith [hB, h1, h2]
  have hid : ∀ H0 : ℕ, (Cstar * 3 ^ (-(a * ↑H0)))^p = Cstar^p * Real.exp (-(c * ↑H0)) := by
    intro H0
    rw [Real.mul_rpow (le_of_lt hCstar) (Real.rpow_nonneg (le_of_lt h3) _),
        ← Real.rpow_mul (le_of_lt h3), Real.rpow_def_of_pos h3]
    have harg : Real.log 3 * ((-(a * ↑H0)) * p) = -(c * ↑H0) := by rw [hc]; ring
    rw [harg]
  set K : ℝ := 2 * (16/3)^p * Cstar^p with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.log K / (c - B))
  refine ⟨max N 1, by omega, ?_⟩
  have hNle : (N:ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by
    exact_mod_cast (le_max_left N 1 : N ≤ max N 1)
  have hlogK : Real.log K ≤ (c - B) * ((max N 1 : ℕ) : ℝ) := by
    have h := le_trans hN hNle
    rw [div_le_iff₀ hcB] at h
    rw [mul_comm] at h
    exact h
  have hexp : K ≤ Real.exp ((c - B) * ((max N 1 : ℕ) : ℝ)) := by
    rw [← Real.exp_log hKpos]
    exact Real.exp_le_exp.mpr hlogK
  have hstep : K * Real.exp (-(c * ((max N 1 : ℕ) : ℝ))) ≤
      Real.exp (-(B * ((max N 1 : ℕ) : ℝ))) := by
    have hmul := mul_le_mul_of_nonneg_right hexp
      (Real.exp_pos (-(c * ((max N 1 : ℕ) : ℝ)))).le
    rw [← Real.exp_add] at hmul
    have harg : (c - B) * ((max N 1 : ℕ) : ℝ) + -(c * ((max N 1 : ℕ) : ℝ))
        = -(B * ((max N 1 : ℕ) : ℝ)) := by ring
    rwa [harg] at hmul
  rw [hid (max N 1), le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  have heq : (16 / 3) ^ p * (Cstar ^ p * Real.exp (-(c * ((max N 1 : ℕ) : ℝ)))) * 2
      = K * Real.exp (-(c * ((max N 1 : ℕ) : ℝ))) := by
    rw [hK]; ring
  rw [heq]
  exact hstep

theorem aux_cover_2_base (Cstar a p : ℝ) (hCstar : 0 < Cstar) (H : ℝ) :
    (16 / 3) ^ p * (Cstar * 3 ^ (-(a * H))) ^ p
      = ((16 / 3) ^ p * Cstar ^ p) * Real.exp (-(a * p * Real.log 3 * H)) := by
  have hCstar_nonneg : 0 ≤ Cstar := le_of_lt hCstar
  have h3nonneg : (0 : ℝ) ≤ 3 := by norm_num
  rw [Real.mul_rpow hCstar_nonneg (Real.rpow_nonneg h3nonneg (-(a * H)))]
  rw [← Real.rpow_mul h3nonneg]
  rw [Real.rpow_def_of_pos (show (0 : ℝ) < 3 by norm_num)]
  rw [show Real.log 3 * (-(a * H) * p) = -(a * p * Real.log 3 * H) by ring]
  ring

theorem aux_lem_rare_tests_dyadic_cover_2 (Cgeom : ℝ) (hCgeom : 4 ≤ Cgeom) (d : ℕ) (_hd : 1 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (P : Measure (BilateralField d)) [IsProbabilityMeasure P] (center : ℤ) (X : ℕ → BilateralField d → ℝ) (_hX01 : ∀ (m : ℕ) (ω : BilateralField d), X m ω ∈ Icc 0 1) (_hmeas : ∀ (m : ℕ), Measurable (X m)) (_hprob : TendstoInMeasure P X atTop fun (_x : BilateralField d) => 0) (Cstar a p : ℝ) (hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p) (Bsym0 : ℕ → MeasurableSpace (BilateralField d)) (_Bsym0_def : Bsym0 = fun (H : ℕ) => MeasurableSpace.comap (Icc (center - ↑H) (center + ↑H)).domRestrict inferInstance) (_hE : ∀ (m H : ℕ), eLpNorm (fun (ω : BilateralField d) => X m ω - P[X m|Bsym0 H] ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cstar * 3 ^ (-(a * ↑H)))) (_hD : ∀ (m H0 : ℕ), 0 < H0 → ∀ᵐ (ω : BilateralField d) ∂P, Tendsto (fun (ell : ℕ) => P[X m|Bsym0 (2 ^ ell * H0)] ω) atTop (𝓝 (X m ω))) (_hI : ∀ (B : ℝ), 0 < B → Cgeom * B < a * p * Real.log 3 → ∃ (Hinc : ℕ), 0 < Hinc ∧ ∀ (H0 : ℕ), Hinc ≤ H0 → ∀ (m ell : ℕ), 1 ≤ ell → P {ω : BilateralField d | (2 : ℝ) ^ (-(↑ell : ℝ) - 3) ≤ P[X m|Bsym0 (2 ^ ell * H0)] ω - P[X m|Bsym0 (2 ^ (ell - 1) * H0)] ω} ≤ ENNReal.ofReal (Real.exp (-(B * ↑(2 ^ ell * H0))))) (B : ℝ) (hB : 0 < B) (hBab : Cgeom * B < a * p * Real.log 3) (Hinc : ℕ) (_hHinc0 : 0 < Hinc) (_hHinc : ∀ (H0 : ℕ), Hinc ≤ H0 → ∀ (m ell : ℕ), 1 ≤ ell → P {ω : BilateralField d | (2 : ℝ) ^ (-(↑ell : ℝ) - 3) ≤ P[X m|Bsym0 (2 ^ ell * H0)] ω - P[X m|Bsym0 (2 ^ (ell - 1) * H0)] ω} ≤ ENNReal.ofReal (Real.exp (-(B * ↑(2 ^ ell * H0))))) (H0g : ℕ) (_hH0g0 : 0 < H0g) (hH0g_geom : (16 / 3) ^ p * (Cstar * 3 ^ (-(a * ↑H0g))) ^ p ≤ Real.exp (-(B * ↑H0g)) / 2) (H0 : ℕ) (_H0_def : H0 = max Hinc (max H0g 1)) (_hK : Hinc ≤ H0) (_hK0 : 1 ≤ H0) (_hH00 : 0 < H0) (hKgg : H0g ≤ H0) : (16 / 3) ^ p * (Cstar * 3 ^ (-(a * ↑H0))) ^ p ≤ Real.exp (-(B * ↑H0)) / 2 := by
  have hΔ : 0 ≤ (↑H0 : ℝ) - ↑H0g := by
    have : (H0g : ℝ) ≤ (H0 : ℝ) := by exact_mod_cast hKgg
    linarith
  have hcB : B ≤ a * p * Real.log 3 := by
    nlinarith [hBab, hCgeom, hB]
  have hL0 : (16 / 3) ^ p * (Cstar * 3 ^ (-(a * ↑H0))) ^ p
      = ((16 / 3) ^ p * Cstar ^ p) * Real.exp (-(a * p * Real.log 3 * ↑H0)) :=
    aux_cover_2_base Cstar a p hCstar (↑H0)
  have hLg : (16 / 3) ^ p * (Cstar * 3 ^ (-(a * ↑H0g))) ^ p
      = ((16 / 3) ^ p * Cstar ^ p) * Real.exp (-(a * p * Real.log 3 * ↑H0g)) :=
    aux_cover_2_base Cstar a p hCstar (↑H0g)
  have hg' : ((16 / 3) ^ p * Cstar ^ p) * Real.exp (-(a * p * Real.log 3 * ↑H0g))
      ≤ Real.exp (-(B * ↑H0g)) / 2 := by
    rw [← hLg]; exact hH0g_geom
  have hexp1 : Real.exp (-(a * p * Real.log 3 * ↑H0))
      = Real.exp (-(a * p * Real.log 3 * ↑H0g))
        * Real.exp (-(a * p * Real.log 3 * ((↑H0 : ℝ) - ↑H0g))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hBmul : Real.exp (-(B * ↑H0g)) * Real.exp (-(B * ((↑H0 : ℝ) - ↑H0g)))
      = Real.exp (-(B * ↑H0)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp3 : Real.exp (-(B * ↑H0g)) / 2 * Real.exp (-(B * ((↑H0 : ℝ) - ↑H0g)))
      = Real.exp (-(B * ↑H0)) / 2 := by
    rw [← hBmul]; ring
  have hexp2 : Real.exp (-(a * p * Real.log 3 * ((↑H0 : ℝ) - ↑H0g)))
      ≤ Real.exp (-(B * ((↑H0 : ℝ) - ↑H0g))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hcB, hΔ]
  have hDnn : 0 ≤ (16 / 3) ^ p * Cstar ^ p :=
    mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 16 / 3) p)
      (Real.rpow_nonneg (le_of_lt hCstar) p)
  rw [hL0]
  calc
    ((16 / 3) ^ p * Cstar ^ p) * Real.exp (-(a * p * Real.log 3 * ↑H0))
        = ((16 / 3) ^ p * Cstar ^ p)
            * (Real.exp (-(a * p * Real.log 3 * ↑H0g))
              * Real.exp (-(a * p * Real.log 3 * ((↑H0 : ℝ) - ↑H0g)))) := by rw [hexp1]
    _ ≤ ((16 / 3) ^ p * Cstar ^ p)
            * (Real.exp (-(a * p * Real.log 3 * ↑H0g))
              * Real.exp (-(B * ((↑H0 : ℝ) - ↑H0g)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp2 (Real.exp_nonneg _)) hDnn
    _ = (((16 / 3) ^ p * Cstar ^ p) * Real.exp (-(a * p * Real.log 3 * ↑H0g)))
            * Real.exp (-(B * ((↑H0 : ℝ) - ↑H0g))) := by ring
    _ ≤ (Real.exp (-(B * ↑H0g)) / 2) * Real.exp (-(B * ((↑H0 : ℝ) - ↑H0g))) :=
          mul_le_mul_of_nonneg_right hg' (Real.exp_nonneg _)
    _ = Real.exp (-(B * ↑H0)) / 2 := hexp3

theorem aux_lem_rare_tests_dyadic_cover_3 (Cgeom : ℝ) (_hCgeom : 4 ≤ Cgeom) (d : ℕ) (_hd : 1 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (P : Measure (BilateralField d)) [IsProbabilityMeasure P] (center : ℤ) (X : ℕ → BilateralField d → ℝ) (hX01 : ∀ (m : ℕ) (ω : BilateralField d), X m ω ∈ Icc 0 1) (hmeas : ∀ (m : ℕ), Measurable (X m)) (hprob : TendstoInMeasure P X atTop fun (_x : BilateralField d) => 0) (Cstar a p : ℝ) (_hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p) (Bsym0 : ℕ → MeasurableSpace (BilateralField d)) (_Bsym0_def : Bsym0 = fun (H : ℕ) => MeasurableSpace.comap (Icc (center - ↑H) (center + ↑H)).domRestrict inferInstance) (_hE : ∀ (m H : ℕ), eLpNorm (fun (ω : BilateralField d) => X m ω - P[X m|Bsym0 H] ω) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cstar * 3 ^ (-(a * ↑H)))) (_hD : ∀ (m H0 : ℕ), 0 < H0 → ∀ᵐ (ω : BilateralField d) ∂P, Tendsto (fun (ell : ℕ) => P[X m|Bsym0 (2 ^ ell * H0)] ω) atTop (𝓝 (X m ω))) (_hI : ∀ (B : ℝ), 0 < B → Cgeom * B < a * p * Real.log 3 → ∃ (Hinc : ℕ), 0 < Hinc ∧ ∀ (H0 : ℕ), Hinc ≤ H0 → ∀ (m ell : ℕ), 1 ≤ ell → P {ω : BilateralField d | (2 : ℝ) ^ (-(↑ell : ℝ) - 3) ≤ P[X m|Bsym0 (2 ^ ell * H0)] ω - P[X m|Bsym0 (2 ^ (ell - 1) * H0)] ω} ≤ ENNReal.ofReal (Real.exp (-(B * ↑(2 ^ ell * H0))))) (B : ℝ) (_hB : 0 < B) (_hBab : Cgeom * B < a * p * Real.log 3) (Hinc : ℕ) (_hHinc0 : 0 < Hinc) (_hHinc : ∀ (H0 : ℕ), Hinc ≤ H0 → ∀ (m ell : ℕ), 1 ≤ ell → P {ω : BilateralField d | (2 : ℝ) ^ (-(↑ell : ℝ) - 3) ≤ P[X m|Bsym0 (2 ^ ell * H0)] ω - P[X m|Bsym0 (2 ^ (ell - 1) * H0)] ω} ≤ ENNReal.ofReal (Real.exp (-(B * ↑(2 ^ ell * H0))))) (H0g : ℕ) (_hH0g0 : 0 < H0g) (_hH0g_geom : (16 / 3) ^ p * (Cstar * 3 ^ (-(a * ↑H0g))) ^ p ≤ Real.exp (-(B * ↑H0g)) / 2) (H0 : ℕ) (_H0_def : H0 = max Hinc (max H0g 1)) (_hK : Hinc ≤ H0) (_hK0 : 1 ≤ H0) (_hH00 : 0 < H0) (_hKgg : H0g ≤ H0) (_hgeomH0 : (16 / 3) ^ p * (Cstar * 3 ^ (-(a * ↑H0))) ^ p ≤ Real.exp (-(B * ↑H0)) / 2) : ∃ (m0 : ℕ), ∀ (m : ℕ), m0 ≤ m → 8 * ∫ (x : BilateralField d), X m x ∂P ≤ Real.exp (-(B * ↑H0)) / 2 := by
  set θ : ℝ := Real.exp (-(B * ↑H0)) / 32 with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hconv := (tendstoInMeasure_iff_norm.mp hprob) θ hθpos
  have hev := hconv.eventually (isOpen_Iio.mem_nhds (ENNReal.ofReal_pos.mpr hθpos))
  obtain ⟨m0, hm0⟩ := eventually_atTop.mp hev
  refine ⟨m0, fun m hm => ?_⟩
  set A : Set (BilateralField d) := {x | θ ≤ ‖X m x‖} with hAdef
  have hPle : P A ≤ ENNReal.ofReal θ := by
    rw [hAdef]
    simpa only [sub_zero] using (hm0 m hm).le
  have hPA_le : P.real A ≤ θ := by
    rw [measureReal_def, ← ENNReal.toReal_ofReal (le_of_lt hθpos)]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hPle
  have hAmeas : MeasurableSet A := by
    rw [hAdef]
    exact MeasurableSet.preimage measurableSet_Ici (hmeas m).norm
  have hfint : Integrable (X m) P := by
    refine Integrable.of_bound (hmeas m).aestronglyMeasurable 1 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hX01 m x).1]
    exact (hX01 m x).2
  have hgmeas : Measurable (fun x : BilateralField d => θ + A.indicator (fun _ => (1:ℝ)) x) :=
    measurable_const.add (measurable_const.indicator hAmeas)
  have hgint : Integrable (fun x : BilateralField d => θ + A.indicator (fun _ => (1:ℝ)) x) P := by
    refine Integrable.of_bound hgmeas.aestronglyMeasurable (θ + 1) ?_
    filter_upwards with x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hθpos])]
    · rw [Set.indicator_of_notMem hx]
      simp only [add_zero]
      rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hθpos)]
      linarith
  have hpoint : X m ≤ fun x : BilateralField d => θ + A.indicator (fun _ => (1:ℝ)) x := by
    intro x
    dsimp only
    by_cases hxA : x ∈ A
    · have hθx : θ ≤ X m x := by
        have h := hxA
        rw [hAdef] at h
        simp only [mem_ofPred_eq, Real.norm_eq_abs, abs_of_nonneg (hX01 m x).1] at h
        exact h
      rw [Set.indicator_of_mem hxA]
      linarith [(hX01 m x).2, hθpos]
    · have hxθ : X m x ≤ θ := by
        have h := hxA
        rw [hAdef] at h
        simp only [mem_ofPred_eq, Real.norm_eq_abs, abs_of_nonneg (hX01 m x).1] at h
        exact le_of_lt (not_le.mp h)
      rw [Set.indicator_of_notMem hxA]
      simp only [add_zero]
      linarith
  have hmono := integral_mono hfint hgint hpoint
  have hind_int : Integrable (A.indicator (fun _ : BilateralField d => (1:ℝ))) P :=
    (integrable_const (1:ℝ)).indicator hAmeas
  have hgval : ∫ x, (θ + A.indicator (fun _ => (1:ℝ)) x) ∂P = θ + P.real A := by
    rw [integral_add (f := fun _ : BilateralField d => θ)
        (g := A.indicator (fun _ => (1:ℝ))) (integrable_const θ) hind_int]
    rw [integral_const, integral_indicator_const (1:ℝ) hAmeas]
    rw [smul_eq_mul, smul_eq_mul, mul_one]
    rw [measureReal_def, measure_univ, ENNReal.toReal_one, one_mul]
  rw [hgval] at hmono
  have hfin : 8 * ∫ x, X m x ∂P ≤ 8 * (2 * θ) := by nlinarith [hmono, hPA_le]
  rw [hθdef] at hfin
  linarith [hfin]

theorem aux_rare_geom_H0 (Cstar a p B Cgeom : ℝ) (hCstar : 0 < Cstar) (_ha : 0 < a)
    (_hp : 1 ≤ p) (hB : 0 < B) (hCgeom : 4 ≤ Cgeom)
    (hBab : Cgeom * B < a * p * Real.log 3) :
    ∃ H0 : ℕ, 0 < H0 ∧ ∀ h : ℕ, H0 ≤ h →
      (4 : ℝ) ^ p * (Cstar * (3 : ℝ) ^ (-(a * (h : ℝ)))) ^ p ≤
        Real.exp (-(B * (h : ℝ))) / 2 := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hBlt : B < a * p * Real.log 3 := by nlinarith [hBab, hCgeom, hB]
  set mu : ℝ := a * p * Real.log 3 - B with hmudef
  have hmu_pos : 0 < mu := by rw [hmudef]; linarith
  obtain ⟨H0, hH0⟩ := Filter.eventually_atTop.1
    ((Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hmu_pos)).eventually
      (eventually_ge_atTop (2 * (4*Cstar)^p)))
  refine ⟨max H0 1, Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right H0 1), ?_⟩
  intro h hh
  have h1 : 1 ≤ h := le_trans (le_max_right H0 1) hh
  have hhh : (0:ℝ) < (h:ℝ) := by exact_mod_cast h1
  have hge : 2 * (4*Cstar)^p ≤ Real.exp (mu * (h:ℝ)) :=
    hH0 h (le_trans (le_max_left H0 1) hh)
  have h4pos : (0:ℝ) < 4 := by norm_num
  have h3pos : (0:ℝ) < 3 := by norm_num
  have hCsnn : 0 ≤ Cstar := le_of_lt hCstar
  have hA : (4:ℝ)^p * (Cstar * (3:ℝ)^(-(a*(h:ℝ))))^p
      = (4*Cstar)^p * Real.exp (-(a*p*Real.log 3*(h:ℝ))) := by
    have h1' : (Cstar * (3:ℝ)^(-(a*(h:ℝ))))^p
        = Cstar^p * (3:ℝ)^((-(a*(h:ℝ)))*p) := by
      rw [Real.mul_rpow hCsnn (Real.rpow_nonneg h3pos.le _), ← Real.rpow_mul h3pos.le]
    have h2' : (4:ℝ)^p * (Cstar^p * (3:ℝ)^((-(a*(h:ℝ)))*p))
        = (4^p * Cstar^p) * (3:ℝ)^((-(a*(h:ℝ)))*p) := by ring
    rw [h1', h2', ← Real.mul_rpow h4pos.le hCsnn,
        Real.rpow_def_of_pos h3pos ((-(a*(h:ℝ)))*p)]
    congr 1
    ring
  have hexp : Real.exp (-(B*(h:ℝ)))
      = Real.exp (mu*(h:ℝ)) * Real.exp (-(a*p*Real.log 3*(h:ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    rw [hmudef]; ring
  have hmain : 2 * ((4*Cstar)^p * Real.exp (-(a*p*Real.log 3*(h:ℝ))))
      ≤ Real.exp (-(B*(h:ℝ))) := by
    rw [hexp]
    calc 2 * ((4*Cstar)^p * Real.exp (-(a*p*Real.log 3*(h:ℝ))))
        = (2*(4*Cstar)^p) * Real.exp (-(a*p*Real.log 3*(h:ℝ))) := by ring
      _ ≤ Real.exp (mu*(h:ℝ)) * Real.exp (-(a*p*Real.log 3*(h:ℝ))) :=
            mul_le_mul_of_nonneg_right hge (Real.exp_pos _).le
  rw [hA]
  rw [le_div_iff₀ (show (0:ℝ) < 2 by norm_num)]
  linarith [hmain]

theorem aux_rare_markov (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (P : Measure (BilateralField d))
    [IsProbabilityMeasure P] (X : ℕ → BilateralField d → ℝ)
    (_hX01 : ∀ (m : ℕ) (ω : BilateralField d), X m ω ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ m : ℕ, Measurable (X m))
    (Cstar a p : ℝ) (_hCstar : 0 < Cstar) (_ha : 0 < a) (hp : 1 ≤ p)
    (Bsym0 : ℕ → MeasurableSpace (BilateralField d))
    (hE : ∀ (m H : ℕ), eLpNorm (fun ω : BilateralField d => X m ω - (P[X m | Bsym0 H]) ω)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (H : ℝ)))))
    (m h : ℕ) :
    P {ω : BilateralField d | (1 / 2 : ℝ) < (P[X m | Bsym0 h]) ω} ≤
      ENNReal.ofReal ((4 : ℝ) ^ p) *
          (ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (h : ℝ))))) ^ p +
        4 * ∫⁻ ω, ENNReal.ofReal (X m ω) ∂P := by
  have hp0 : (0:ℝ) ≤ p := le_trans zero_le_one hp
  have h4of : ENNReal.ofReal (1/4) = (4:ℝ≥0∞)⁻¹ := by
    have h14 : (1/4:ℝ) = (4:ℝ)⁻¹ := by norm_num
    rw [h14, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 4), ENNReal.ofReal_ofNat]
  have h4inv : (4:ℝ≥0∞) * ENNReal.ofReal (1/4) = 1 := by
    rw [h4of, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hsub : {ω : BilateralField d | (1/2:ℝ) < (P[X m | Bsym0 h]) ω} ⊆
      {ω : BilateralField d | (1/4:ℝ) < (P[X m | Bsym0 h]) ω - X m ω} ∪
        {ω : BilateralField d | (1/4:ℝ) < X m ω} := by
    intro ω hω
    simp only [Set.mem_union, mem_ofPred_eq] at hω ⊢
    by_cases hX : (1/4:ℝ) < X m ω
    · exact Or.inr hX
    · push Not at hX
      exact Or.inl (by linarith)
  have hC : P {ω : BilateralField d | (1/4:ℝ) < X m ω} ≤
      4 * ∫⁻ ω, ENNReal.ofReal (X m ω) ∂P := by
    have hsub2 : {ω : BilateralField d | (1/4:ℝ) < X m ω} ⊆
        {ω : BilateralField d | ENNReal.ofReal (1/4) ≤ ENNReal.ofReal (X m ω)} := by
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      exact ENNReal.ofReal_le_ofReal (le_of_lt hω)
    have hfmeas : Measurable (fun ω : BilateralField d => ENNReal.ofReal (X m ω)) :=
      (hmeas m).ennreal_ofReal
    have h1 := mul_meas_ge_le_lintegral (μ := P) hfmeas (ENNReal.ofReal (1/4))
    calc P {ω : BilateralField d | (1/4:ℝ) < X m ω}
        = (4:ℝ≥0∞) * (ENNReal.ofReal (1/4) * P {ω : BilateralField d | (1/4:ℝ) < X m ω}) := by
          rw [← mul_assoc, h4inv, one_mul]
      _ ≤ (4:ℝ≥0∞) * (ENNReal.ofReal (1/4) * P {ω : BilateralField d | ENNReal.ofReal (1/4) ≤ ENNReal.ofReal (X m ω)}) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (measure_mono hsub2) zero_le) zero_le
      _ ≤ (4:ℝ≥0∞) * ∫⁻ ω, ENNReal.ofReal (X m ω) ∂P := mul_le_mul_of_nonneg_left h1 zero_le
  have hB : P {ω : BilateralField d | (1/4:ℝ) < (P[X m | Bsym0 h]) ω - X m ω} ≤
      ENNReal.ofReal ((4:ℝ)^p) * (ENNReal.ofReal (Cstar * (3:ℝ)^(-(a*(h:ℝ)))))^p := by
    have hof4p : ENNReal.ofReal ((4:ℝ)^p) = (4:ℝ≥0∞)^p := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0:ℝ) ≤ 4) hp0, ENNReal.ofReal_ofNat]
    have h4p : ENNReal.ofReal ((4:ℝ)^p) * (ENNReal.ofReal (1/4))^p = 1 := by
      have hrp0 : (4:ℝ≥0∞)^p ≠ 0 := by
        rw [← hof4p]
        exact ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 4) p)
      have hrpt : (4:ℝ≥0∞)^p ≠ ⊤ := by
        rw [← hof4p]; exact ENNReal.ofReal_ne_top
      rw [hof4p, h4of, ENNReal.inv_rpow, ENNReal.mul_inv_cancel hrp0 hrpt]
    have hq0 : (ENNReal.ofReal p) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
    have hqtop : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hcondAE : AEStronglyMeasurable (fun ω : BilateralField d => (P[X m | Bsym0 h]) ω) P := by
      by_cases hle : Bsym0 h ≤ (inferInstance : MeasurableSpace (BilateralField d))
      · exact ((stronglyMeasurable_condExp (μ := P) (m := Bsym0 h) (f := X m)).mono hle).aestronglyMeasurable
      · rw [condExp_of_not_le hle]
        exact aestronglyMeasurable_zero
    have hfAE : AEStronglyMeasurable (fun ω : BilateralField d => (P[X m | Bsym0 h]) ω - X m ω) P :=
      hcondAE.sub (hmeas m).aestronglyMeasurable
    have hcheb := mul_meas_ge_le_pow_eLpNorm' (p := ENNReal.ofReal p) (f := fun ω : BilateralField d => (P[X m | Bsym0 h]) ω - X m ω) P hq0 hqtop (ENNReal.ofReal (1/4))
    rw [ENNReal.toReal_ofReal hp0] at hcheb
    have hsubB : {ω : BilateralField d | (1/4:ℝ) < (P[X m | Bsym0 h]) ω - X m ω} ⊆
        {ω : BilateralField d | ENNReal.ofReal (1/4) ≤ ‖(P[X m | Bsym0 h]) ω - X m ω‖ₑ} := by
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      rw [← ofReal_norm, Real.norm_of_nonneg (le_of_lt (by linarith))]
      exact ENNReal.ofReal_le_ofReal (le_of_lt hω)
    have hEeLp : eLpNorm (fun ω : BilateralField d => (P[X m | Bsym0 h]) ω - X m ω) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cstar * (3:ℝ)^(-(a*(h:ℝ)))) := by
      have hg : (fun ω : BilateralField d => (P[X m | Bsym0 h]) ω - X m ω)
          = -(fun ω : BilateralField d => X m ω - (P[X m | Bsym0 h]) ω) := by
        funext ω; simp only [Pi.neg_apply]; ring
      rw [hg, eLpNorm_neg]
      exact hE m h
    have hmain : P {ω : BilateralField d | (1/4:ℝ) < (P[X m | Bsym0 h]) ω - X m ω} ≤
        ENNReal.ofReal ((4:ℝ)^p) * (eLpNorm (fun ω : BilateralField d => (P[X m | Bsym0 h]) ω - X m ω) (ENNReal.ofReal p) P)^p := by
      have hpT : P {ω : BilateralField d | (1/4:ℝ) < (P[X m | Bsym0 h]) ω - X m ω}
          ≤ P {ω : BilateralField d | ENNReal.ofReal (1/4) ≤ ‖(P[X m | Bsym0 h]) ω - X m ω‖ₑ} := measure_mono hsubB
      have h2 : (ENNReal.ofReal (1/4))^p * P {ω : BilateralField d | (1/4:ℝ) < (P[X m | Bsym0 h]) ω - X m ω}
          ≤ (eLpNorm (fun ω : BilateralField d => (P[X m | Bsym0 h]) ω - X m ω) (ENNReal.ofReal p) P)^p :=
        le_trans (mul_le_mul_of_nonneg_left hpT zero_le) hcheb
      calc P {ω : BilateralField d | (1/4:ℝ) < (P[X m | Bsym0 h]) ω - X m ω}
          = ENNReal.ofReal ((4:ℝ)^p) * ((ENNReal.ofReal (1/4))^p * P {ω : BilateralField d | (1/4:ℝ) < (P[X m | Bsym0 h]) ω - X m ω}) := by
            rw [← mul_assoc, h4p, one_mul]
        _ ≤ ENNReal.ofReal ((4:ℝ)^p) * (eLpNorm (fun ω : BilateralField d => (P[X m | Bsym0 h]) ω - X m ω) (ENNReal.ofReal p) P)^p :=
            mul_le_mul_of_nonneg_left h2 zero_le
    calc P {ω : BilateralField d | (1/4:ℝ) < (P[X m | Bsym0 h]) ω - X m ω}
        ≤ ENNReal.ofReal ((4:ℝ)^p) * (eLpNorm (fun ω : BilateralField d => (P[X m | Bsym0 h]) ω - X m ω) (ENNReal.ofReal p) P)^p := hmain
      _ ≤ ENNReal.ofReal ((4:ℝ)^p) * (ENNReal.ofReal (Cstar * (3:ℝ)^(-(a*(h:ℝ)))))^p :=
          mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hEeLp hp0) zero_le
  calc P {ω : BilateralField d | (1/2:ℝ) < (P[X m | Bsym0 h]) ω}
      ≤ P ({ω : BilateralField d | (1/4:ℝ) < (P[X m | Bsym0 h]) ω - X m ω} ∪
          {ω : BilateralField d | (1/4:ℝ) < X m ω}) := measure_mono hsub
    _ ≤ P {ω : BilateralField d | (1/4:ℝ) < (P[X m | Bsym0 h]) ω - X m ω} +
          P {ω : BilateralField d | (1/4:ℝ) < X m ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((4:ℝ)^p) * (ENNReal.ofReal (Cstar * (3:ℝ)^(-(a*(h:ℝ)))))^p +
          4 * ∫⁻ ω, ENNReal.ofReal (X m ω) ∂P := add_le_add hB hC

theorem aux_rare_clause_meas3_window_mono (d : ℕ) (center : ℤ) {K h : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (h1 : center - 2 * (h : ℤ) ≤ center - (K : ℤ)) (h2 : center + (K : ℤ) ≤ center + (h : ℤ))
    (msK : MeasurableSpace (BilateralField d)) (msH : MeasurableSpace (BilateralField d))
    (hmsK : msK = MeasurableSpace.comap
        ((Set.Icc (center - (K : ℤ)) (center + (K : ℤ))).domRestrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (center - (K : ℤ)) (center + (K : ℤ))) → C(SpatialCoordinates d, ℝ))))
    (hmsH : msH = MeasurableSpace.comap
        ((Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))).domRestrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))) → C(SpatialCoordinates d, ℝ)))) :
    msK ≤ msH := by
  rw [hmsK, hmsH]
  have hmem : ∀ i : Set.Icc (center - (K : ℤ)) (center + (K : ℤ)),
      (i : ℤ) ∈ Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ)) :=
    fun i => ⟨le_trans h1 i.2.1, le_trans i.2.2 h2⟩
  let R_K : BilateralField d →
      ((i : Set.Icc (center - (K : ℤ)) (center + (K : ℤ))) → C(SpatialCoordinates d, ℝ)) :=
    fun x i => x i.1
  let R_H : BilateralField d →
      ((j : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))) → C(SpatialCoordinates d, ℝ)) :=
    fun x j => x j.1
  change MeasurableSpace.comap R_K inferInstance ≤ MeasurableSpace.comap R_H inferInstance
  let g : ((j : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))) → C(SpatialCoordinates d, ℝ)) →
      ((i : Set.Icc (center - (K : ℤ)) (center + (K : ℤ))) → C(SpatialCoordinates d, ℝ)) :=
    fun φ i => φ (⟨(i : ℤ), hmem i⟩ : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ)))
  have heq : R_K = g ∘ R_H := by
    funext x i; rfl
  have hg : Measurable g := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (a := (⟨(i : ℤ), hmem i⟩ : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))))
  rw [heq, ← MeasurableSpace.comap_comp]
  apply MeasurableSpace.comap_mono
  exact measurable_iff_comap_le.mp hg

theorem aux_rare_m0 (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (P : Measure (BilateralField d))
    [IsProbabilityMeasure P] (X : ℕ → BilateralField d → ℝ)
    (hX01 : ∀ (m : ℕ) (ω : BilateralField d), X m ω ∈ Set.Icc (0 : ℝ) 1)
    (hmeas : ∀ m : ℕ, Measurable (X m))
    (hprob : TendstoInMeasure P X atTop (fun _ => (0 : ℝ)))
    (B : ℝ) (_hB : 0 < B) (H0 : ℕ) (_hH00 : 0 < H0) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
      ∫⁻ ω, ENNReal.ofReal (X m ω) ∂P ≤
        ENNReal.ofReal (Real.exp (-(B * (H0 : ℝ))) / 8) := by
  set δ : ℝ := Real.exp (-(B * (H0 : ℝ))) / 8 with hδ
  have hδ2pos : 0 < δ / 2 := by rw [hδ]; positivity
  have hεpos : 0 < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.mpr hδ2pos
  rw [MeasureTheory.tendstoInMeasure_iff_enorm] at hprob
  have htend := hprob (ENNReal.ofReal (δ / 2)) hεpos ENNReal.ofReal_ne_top
  have hev : ∀ᶠ m in atTop,
      P {ω | ENNReal.ofReal (δ / 2) ≤ ‖X m ω - (0 : ℝ)‖ₑ} < ENNReal.ofReal (δ / 2) :=
    htend.eventually (Iio_mem_nhds hεpos)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨m0, hm0⟩ := hev
  refine ⟨m0, fun m hm => ?_⟩
  have hAmeas : MeasurableSet {ω : BilateralField d | δ / 2 ≤ X m ω} :=
    measurableSet_le measurable_const (hmeas m)
  have hPA : P {ω : BilateralField d | δ / 2 ≤ X m ω} ≤ ENNReal.ofReal (δ / 2) := by
    have hsub : {ω : BilateralField d | δ / 2 ≤ X m ω} ⊆
        {ω | ENNReal.ofReal (δ / 2) ≤ ‖X m ω - (0 : ℝ)‖ₑ} := by
      intro ω hω
      simp only [mem_ofPred_eq] at hω ⊢
      rw [sub_zero, Real.enorm_eq_ofReal (le_trans hδ2pos.le hω)]
      exact ENNReal.ofReal_le_ofReal hω
    exact le_trans (measure_mono hsub) (le_of_lt (hm0 m hm))
  have hsplit := MeasureTheory.lintegral_add_compl (μ := P)
    (fun ω => ENNReal.ofReal (X m ω)) hAmeas
  rw [← hsplit]
  calc ∫⁻ ω in {ω : BilateralField d | δ / 2 ≤ X m ω}, ENNReal.ofReal (X m ω) ∂P
        + ∫⁻ ω in {ω : BilateralField d | δ / 2 ≤ X m ω}ᶜ, ENNReal.ofReal (X m ω) ∂P
      ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := by
        apply add_le_add
        · calc ∫⁻ ω in {ω : BilateralField d | δ / 2 ≤ X m ω}, ENNReal.ofReal (X m ω) ∂P
              ≤ ∫⁻ _ω in {ω : BilateralField d | δ / 2 ≤ X m ω}, (1 : ℝ≥0∞) ∂P := by
                refine MeasureTheory.setLIntegral_mono (g := fun _ => (1 : ℝ≥0∞)) measurable_const ?_
                intro ω _
                exact ENNReal.ofReal_le_one.mpr (hX01 m ω).2
            _ = P {ω : BilateralField d | δ / 2 ≤ X m ω} := by
                rw [MeasureTheory.setLIntegral_const, one_mul]
            _ ≤ ENNReal.ofReal (δ / 2) := hPA
        · calc ∫⁻ ω in {ω : BilateralField d | δ / 2 ≤ X m ω}ᶜ, ENNReal.ofReal (X m ω) ∂P
              ≤ ∫⁻ _ω in {ω : BilateralField d | δ / 2 ≤ X m ω}ᶜ, ENNReal.ofReal (δ / 2) ∂P := by
                refine MeasureTheory.setLIntegral_mono
                  (g := fun _ => ENNReal.ofReal (δ / 2)) measurable_const ?_
                intro ω hω
                simp only [Set.mem_compl_iff, mem_ofPred_eq, not_le] at hω
                exact ENNReal.ofReal_le_ofReal hω.le
            _ = ENNReal.ofReal (δ / 2) * P {ω : BilateralField d | δ / 2 ≤ X m ω}ᶜ := by
                rw [MeasureTheory.setLIntegral_const]
            _ ≤ ENNReal.ofReal (δ / 2) * 1 := mul_le_mul_right prob_le_one _
            _ = ENNReal.ofReal (δ / 2) := mul_one _
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add hδ2pos.le hδ2pos.le]
        congr 1
        ring

theorem aux_rare_clause_empty3 (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (P : Measure (BilateralField d)) (center : ℤ) (X : ℕ → BilateralField d → ℝ) (Bsym0 : ℕ → MeasurableSpace (BilateralField d)) (_hBsym0 : ∀ H : ℕ, Bsym0 H = MeasurableSpace.comap ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict) (inferInstance : MeasurableSpace ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) → C(SpatialCoordinates d, ℝ)))) (H0 m : ℕ) (hH00 : 0 < H0) (W : ℕ+ → Set (BilateralField d)) (W_def : W = fun h : ℕ+ => (if (h : ℕ) = H0 then {ω : BilateralField d | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω} else ∅) ∪ ⋃ (l : { l : ℕ // 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ) }), {ω : BilateralField d | (2 : ℝ) ^ (-(((l : ℕ) : ℤ)) - 3) ≤ (P[X m | Bsym0 (2 ^ (l : ℕ) * H0)]) ω - (P[X m | Bsym0 (2 ^ ((l : ℕ) - 1) * H0)]) ω}) : ∀ h : ℕ+, (h : ℕ) < H0 → W h = ∅ := by
  intro h hh
  have hempty : IsEmpty { l : ℕ // 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ) } :=
    ⟨fun l => by
      obtain ⟨hl1, hl2⟩ := l.2
      have h2l : 2 ≤ 2 ^ (l : ℕ) := by
        calc 2 = 2 ^ (1 : ℕ) := by norm_num
          _ ≤ 2 ^ (l : ℕ) := Nat.pow_le_pow_right (by norm_num) hl1
      have hmul : 2 * H0 ≤ 2 ^ (l : ℕ) * H0 := Nat.mul_le_mul_right H0 h2l
      rw [hl2] at hmul
      have hlt : H0 < 2 * H0 := by omega
      omega⟩
  rw [W_def]
  dsimp only
  rw [ite_eq_right (ne_of_lt hh)]
  have := hempty
  simp only [Set.empty_union, Set.iUnion_of_empty]

theorem aux_rare_h0_level_prob (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (P : Measure (BilateralField d)) [IsProbabilityMeasure P] (_center : ℤ) (X : ℕ → BilateralField d → ℝ) (hmeas : ∀ m : ℕ, Measurable (X m)) (hX01 : ∀ (m : ℕ) (ω : BilateralField d), X m ω ∈ Set.Icc (0 : ℝ) 1) (Bsym0 : ℕ → MeasurableSpace (BilateralField d)) (H0 m : ℕ) (B : ℝ) (hbound : ∫⁻ ω, ENNReal.ofReal (X m ω) ∂P ≤ ENNReal.ofReal (Real.exp (-(B * (H0 : ℝ))) / 8)) : P {ω | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω} ≤ ENNReal.ofReal (Real.exp (-(B * (H0 : ℝ)))) := by
  by_cases hle : Bsym0 H0 ≤ (inferInstance : MeasurableSpace (BilateralField d))
  · have hσ : SigmaFinite (P.trim hle) := inferInstance
    have hIntX : Integrable (X m) P := by
      refine MeasureTheory.Integrable.of_bound ((hmeas m).aestronglyMeasurable) 1 ?_
      filter_upwards with ω
      have h := hX01 m ω
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]
      exact h.2
    have hXnn : 0 ≤ᵐ[P] X m := by
      filter_upwards with ω
      exact (hX01 m ω).1
    have hcondnn : 0 ≤ᵐ[P] (P[X m | Bsym0 H0]) := MeasureTheory.condExp_nonneg hXnn
    have hcondint : Integrable (P[X m | Bsym0 H0]) P := MeasureTheory.integrable_condExp
    have heq : ∫⁻ ω, ENNReal.ofReal ((P[X m | Bsym0 H0]) ω) ∂P
             = ∫⁻ ω, ENNReal.ofReal (X m ω) ∂P := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hcondint hcondnn,
          ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntX hXnn,
          MeasureTheory.integral_condExp hle]
    have hFmeas : Measurable (fun ω => ENNReal.ofReal ((P[X m | Bsym0 H0]) ω)) :=
      ENNReal.measurable_ofReal.comp ((MeasureTheory.stronglyMeasurable_condExp.mono hle).measurable)
    have hmarkov : ENNReal.ofReal (3 / 8 : ℝ)
        * P {ω : BilateralField d | ENNReal.ofReal (3 / 8 : ℝ) ≤ ENNReal.ofReal ((P[X m | Bsym0 H0]) ω)}
        ≤ ∫⁻ ω, ENNReal.ofReal ((P[X m | Bsym0 H0]) ω) ∂P :=
      MeasureTheory.mul_meas_ge_le_lintegral hFmeas (ENNReal.ofReal (3 / 8 : ℝ))
    have hseteq : {ω : BilateralField d | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω}
        = {ω : BilateralField d | ENNReal.ofReal (3 / 8 : ℝ) ≤ ENNReal.ofReal ((P[X m | Bsym0 H0]) ω)} := by
      ext ω
      simp only [mem_ofPred_eq]
      constructor
      · intro h
        exact ENNReal.ofReal_le_ofReal h
      · intro h
        by_cases hz : (0 : ℝ) ≤ (P[X m | Bsym0 H0]) ω
        · exact (ENNReal.ofReal_le_ofReal_iff hz).mp h
        · exfalso
          have h0 : ENNReal.ofReal ((P[X m | Bsym0 H0]) ω) = 0 :=
            ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hz)
          rw [h0] at h
          exact not_le_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 3 / 8)) h
    rw [← hseteq] at hmarkov
    have hchain : ENNReal.ofReal (3 / 8 : ℝ) * P {ω : BilateralField d | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω}
        ≤ ENNReal.ofReal (Real.exp (-(B * (H0 : ℝ))) / 8) := by
      calc ENNReal.ofReal (3 / 8 : ℝ) * P {ω : BilateralField d | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω}
          ≤ ∫⁻ ω, ENNReal.ofReal ((P[X m | Bsym0 H0]) ω) ∂P := hmarkov
        _ = ∫⁻ ω, ENNReal.ofReal (X m ω) ∂P := heq
        _ ≤ ENNReal.ofReal (Real.exp (-(B * (H0 : ℝ))) / 8) := hbound
    have hmul : ENNReal.ofReal (3 / 8 : ℝ) * ENNReal.ofReal (Real.exp (-(B * (H0 : ℝ))) / 3)
        = ENNReal.ofReal (Real.exp (-(B * (H0 : ℝ))) / 8) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 8)]
      congr 1
      ring
    have hne0 : ENNReal.ofReal (3 / 8 : ℝ) ≠ 0 := by
      intro h
      have h' : (3 / 8 : ℝ) ≤ 0 := ENNReal.ofReal_eq_zero.mp h
      norm_num at h'
    have hnetop : ENNReal.ofReal (3 / 8 : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h1 : P {ω : BilateralField d | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω}
        ≤ ENNReal.ofReal (Real.exp (-(B * (H0 : ℝ))) / 3) := by
      have hle' : ENNReal.ofReal (3 / 8 : ℝ) * P {ω : BilateralField d | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω}
          ≤ ENNReal.ofReal (3 / 8 : ℝ) * ENNReal.ofReal (Real.exp (-(B * (H0 : ℝ))) / 3) := by
        rw [hmul]; exact hchain
      exact (ENNReal.mul_le_mul_iff_right hne0 hnetop).mp hle'
    calc P {ω : BilateralField d | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω}
        ≤ ENNReal.ofReal (Real.exp (-(B * (H0 : ℝ))) / 3) := h1
      _ ≤ ENNReal.ofReal (Real.exp (-(B * (H0 : ℝ)))) := by
          apply ENNReal.ofReal_le_ofReal
          exact div_le_self (Real.exp_pos _).le (by norm_num)
  · rw [MeasureTheory.condExp_of_not_le hle]
    have hnull : P {ω : BilateralField d | (3 / 8 : ℝ) ≤ (0 : BilateralField d → ℝ) ω} = 0 :=
      measure_mono_null (fun ω h => by
        simp only [mem_ofPred_eq, Pi.zero_apply] at h
        exact absurd h (by norm_num : ¬ ((3 : ℝ) / 8 ≤ 0))) measure_empty
    rw [hnull]
    exact zero_le

theorem aux_rare_cover_telescope (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (P : Measure (BilateralField d)) (_center : ℤ) (X : ℕ → BilateralField d → ℝ) (Bsym0 : ℕ → MeasurableSpace (BilateralField d)) (H0 : ℕ) (_hH0 : 0 < H0) (m : ℕ) (ω : BilateralField d) (hlim : Tendsto (fun ell : ℕ => (P[X m | Bsym0 (2 ^ ell * H0)]) ω) atTop (𝓝 (X m ω))) (h0 : (P[X m | Bsym0 H0]) ω < 3 / 8) (hΔ : ∀ l : ℕ, 1 ≤ l → (P[X m | Bsym0 (2 ^ l * H0)]) ω - (P[X m | Bsym0 (2 ^ (l - 1) * H0)]) ω < (2 : ℝ) ^ (-(l : ℤ) - 3)) : X m ω ≤ 1 / 2 := by
  have hf0 : (P[X m | Bsym0 (2 ^ 0 * H0)]) ω = (P[X m | Bsym0 H0]) ω := by
    simp only [pow_zero, one_mul]
  have hvle : ∀ L : ℕ,
      Finset.sum (Finset.range L) (fun i : ℕ => (2 : ℝ) ^ (-((i + 1 : ℕ) : ℤ) - 3)) ≤ 1 / 8 := by
    intro L
    have hz : ∀ n : ℕ, (2 : ℝ) ^ (-(n : ℤ)) = (1 / 2 : ℝ) ^ n := by
      intro n
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      rw [show (2 : ℝ)⁻¹ = 1 / 2 from by norm_num]
    have hpt : ∀ i : ℕ, (2 : ℝ) ^ (-((i + 1 : ℕ) : ℤ) - 3)
        = (1 / 2 : ℝ) ^ (i + 1) * (1 / 8) := by
      intro i
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      have e1 : -((i + 1 : ℕ) : ℤ) - 3 = (-((i + 1 : ℕ) : ℤ)) + (-3) := by ring
      rw [e1, zpow_add₀ h2, hz (i + 1)]
      have e3 : (2 : ℝ) ^ (-3 : ℤ) = (1 / 8 : ℝ) := by
        rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) from by norm_num, hz 3]
        norm_num
      rw [e3]
    have hv : Finset.sum (Finset.range L) (fun i : ℕ => (2 : ℝ) ^ (-((i + 1 : ℕ) : ℤ) - 3))
        = (1 / 8) * Finset.sum (Finset.range L) (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hpt i]
      ring
    have hs : Finset.sum (Finset.range L) (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1)) ≤ 1 := by
      have hsub := Finset.sum_range_sub' (fun i : ℕ => (1 / 2 : ℝ) ^ i) L
      have heq : Finset.sum (Finset.range L) (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1))
          = Finset.sum (Finset.range L) (fun i : ℕ => (1 / 2 : ℝ) ^ i - (1 / 2 : ℝ) ^ (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_succ]
        ring
      rw [heq, hsub, pow_zero]
      have hp : (0 : ℝ) ≤ (1 / 2) ^ L := pow_nonneg (by norm_num) L
      linarith
    rw [hv]
    calc (1 / 8) * Finset.sum (Finset.range L) (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1))
        ≤ (1 / 8) * 1 := mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = 1 / 8 := by ring
  have hbound : ∀ L : ℕ, (P[X m | Bsym0 (2 ^ L * H0)]) ω < 1 / 2 := by
    intro L
    have htel : (P[X m | Bsym0 (2 ^ L * H0)]) ω
        = (P[X m | Bsym0 (2 ^ 0 * H0)]) ω
          + Finset.sum (Finset.range L) (fun i : ℕ =>
              (P[X m | Bsym0 (2 ^ (i + 1) * H0)]) ω - (P[X m | Bsym0 (2 ^ i * H0)]) ω) := by
      have h := Finset.sum_range_sub (fun L : ℕ => (P[X m | Bsym0 (2 ^ L * H0)]) ω) L
      linarith [h]
    have hinc : ∀ i : ℕ,
        (P[X m | Bsym0 (2 ^ (i + 1) * H0)]) ω - (P[X m | Bsym0 (2 ^ i * H0)]) ω
          < (2 : ℝ) ^ (-((i + 1 : ℕ) : ℤ) - 3) := by
      intro i
      have h := hΔ (i + 1) (by omega)
      have hidx : i + 1 - 1 = i := by omega
      rw [hidx] at h
      exact h
    have hSum : Finset.sum (Finset.range L) (fun i : ℕ =>
              (P[X m | Bsym0 (2 ^ (i + 1) * H0)]) ω - (P[X m | Bsym0 (2 ^ i * H0)]) ω)
        ≤ Finset.sum (Finset.range L) (fun i : ℕ => (2 : ℝ) ^ (-((i + 1 : ℕ) : ℤ) - 3)) :=
      Finset.sum_le_sum (fun i _ => le_of_lt (hinc i))
    calc (P[X m | Bsym0 (2 ^ L * H0)]) ω
        = (P[X m | Bsym0 (2 ^ 0 * H0)]) ω
            + Finset.sum (Finset.range L) (fun i : ℕ =>
                (P[X m | Bsym0 (2 ^ (i + 1) * H0)]) ω - (P[X m | Bsym0 (2 ^ i * H0)]) ω) := htel
      _ = (P[X m | Bsym0 H0]) ω
            + Finset.sum (Finset.range L) (fun i : ℕ =>
                (P[X m | Bsym0 (2 ^ (i + 1) * H0)]) ω - (P[X m | Bsym0 (2 ^ i * H0)]) ω) := by rw [hf0]
      _ ≤ (P[X m | Bsym0 H0]) ω
            + Finset.sum (Finset.range L) (fun i : ℕ => (2 : ℝ) ^ (-((i + 1 : ℕ) : ℤ) - 3)) :=
          add_le_add (le_refl _) hSum
      _ < 3 / 8 + Finset.sum (Finset.range L) (fun i : ℕ => (2 : ℝ) ^ (-((i + 1 : ℕ) : ℤ) - 3)) :=
          add_lt_add_of_lt_of_le h0 (le_refl _)
      _ ≤ 3 / 8 + 1 / 8 := add_le_add (le_refl _) (hvle L)
      _ = 1 / 2 := by norm_num
  exact le_of_tendsto hlim (Filter.Eventually.of_forall (fun ell => le_of_lt (hbound ell)))

theorem aux_rare_clause_meas3 (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (P : Measure (BilateralField d)) (center : ℤ) (X : ℕ → BilateralField d → ℝ) (Bsym0 : ℕ → MeasurableSpace (BilateralField d)) (hBsym0 : ∀ H : ℕ, Bsym0 H = MeasurableSpace.comap ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict) (inferInstance : MeasurableSpace ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) → C(SpatialCoordinates d, ℝ)))) (H0 m : ℕ) (W : ℕ+ → Set (BilateralField d)) (W_def : W = fun h : ℕ+ => (if (h : ℕ) = H0 then {ω : BilateralField d | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω} else ∅) ∪ ⋃ (l : { l : ℕ // 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ) }), {ω : BilateralField d | (2 : ℝ) ^ (-(((l : ℕ) : ℤ)) - 3) ≤ (P[X m | Bsym0 (2 ^ (l : ℕ) * H0)]) ω - (P[X m | Bsym0 (2 ^ ((l : ℕ) - 1) * H0)]) ω}) : ∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap ((Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))).domRestrict) (inferInstance : MeasurableSpace ((i : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))) → C(SpatialCoordinates d, ℝ)))] (W h) := by
  intro h
  rw [W_def]
  let T : MeasurableSpace (BilateralField d) :=
    MeasurableSpace.comap ((Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))).domRestrict)
      (inferInstance : MeasurableSpace ((i : Set.Icc (center - 2 * (h : ℤ)) (center + (h : ℤ))) → C(SpatialCoordinates d, ℝ)))
  change MeasurableSet[T] _
  have hle : ∀ (H : ℕ), center - 2 * (h : ℤ) ≤ center - (H : ℤ) →
      center + (H : ℤ) ≤ center + (h : ℤ) → Bsym0 H ≤ T :=
    fun H h1 h2 => aux_rare_clause_meas3_window_mono d center h1 h2 (Bsym0 H) T (hBsym0 H) rfl
  refine MeasurableSet.union ?_ ?_
  · by_cases hh : (h : ℕ) = H0
    · rw [ite_eq_left hh]
      have h1 : center - 2 * (h : ℤ) ≤ center - (H0 : ℤ) := by omega
      have h2 : center + (H0 : ℤ) ≤ center + (h : ℤ) := by omega
      have hc : Measurable[T] (fun ω : BilateralField d => (P[X m|Bsym0 H0]) ω) :=
        ((stronglyMeasurable_condExp (m := Bsym0 H0) (μ := P) (f := X m)).measurable).mono (hle H0 h1 h2) le_rfl
      show MeasurableSet[T] ((fun ω : BilateralField d => (P[X m|Bsym0 H0]) ω) ⁻¹' Set.Ici ((3 : ℝ) / 8))
      exact MeasurableSet.preimage measurableSet_Ici hc
    · rw [ite_eq_right hh]
      exact @MeasurableSet.empty (BilateralField d) T
  · apply MeasurableSet.iUnion
    intro l
    have hpow : 2 ^ ((l : ℕ) - 1) * H0 ≤ 2 ^ (l : ℕ) * H0 :=
      Nat.mul_le_mul_right H0 (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le (l : ℕ) 1))
    have hN1 : 2 ^ (l : ℕ) * H0 ≤ (h : ℕ) := le_of_eq l.2.2
    have hN2 : 2 ^ ((l : ℕ) - 1) * H0 ≤ (h : ℕ) := le_trans hpow hN1
    have h1a : center - 2 * (h : ℤ) ≤ center - ((2 ^ (l : ℕ) * H0 : ℕ) : ℤ) := by omega
    have h2a : center + ((2 ^ (l : ℕ) * H0 : ℕ) : ℤ) ≤ center + (h : ℤ) := by omega
    have h1b : center - 2 * (h : ℤ) ≤ center - ((2 ^ ((l : ℕ) - 1) * H0 : ℕ) : ℤ) := by omega
    have h2b : center + ((2 ^ ((l : ℕ) - 1) * H0 : ℕ) : ℤ) ≤ center + (h : ℤ) := by omega
    have hc1 : Measurable[T] (fun ω : BilateralField d => (P[X m|Bsym0 (2 ^ (l : ℕ) * H0)]) ω) :=
      ((stronglyMeasurable_condExp (m := Bsym0 (2 ^ (l : ℕ) * H0)) (μ := P) (f := X m)).measurable).mono (hle (2 ^ (l : ℕ) * H0) h1a h2a) le_rfl
    have hc2 : Measurable[T] (fun ω : BilateralField d => (P[X m|Bsym0 (2 ^ ((l : ℕ) - 1) * H0)]) ω) :=
      ((stronglyMeasurable_condExp (m := Bsym0 (2 ^ ((l : ℕ) - 1) * H0)) (μ := P) (f := X m)).measurable).mono (hle (2 ^ ((l : ℕ) - 1) * H0) h1b h2b) le_rfl
    show MeasurableSet[T] ((fun ω : BilateralField d => (P[X m|Bsym0 (2 ^ (l : ℕ) * H0)]) ω - (P[X m|Bsym0 (2 ^ ((l : ℕ) - 1) * H0)]) ω) ⁻¹' Set.Ici ((2 : ℝ) ^ (-(((l : ℕ) : ℤ)) - 3)))
    exact MeasurableSet.preimage measurableSet_Ici (hc1.sub hc2)

theorem aux_lem_rare_tests_dyadic_cover_assembly :
    ∀ (Cgeom : ℝ), 4 ≤ Cgeom →
    ∀ (d : ℕ) (_hd : 1 ≤ d)
      [MeasurableSpace C(SpatialCoordinates d, ℝ)]
      [BorelSpace C(SpatialCoordinates d, ℝ)]
      (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
      (center : ℤ)
      (X : ℕ → BilateralField d → ℝ)
      (_hX01 : ∀ m ω, X m ω ∈ Set.Icc (0 : ℝ) 1)
      (_hmeas : ∀ m, Measurable (X m))
      (_hprob : TendstoInMeasure P X atTop (fun _ => (0 : ℝ)))
      (Cstar a p : ℝ) (_hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p),
      let Bsym : ℕ → MeasurableSpace (BilateralField d) := fun H =>
          MeasurableSpace.comap
            ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) →
                C(SpatialCoordinates d, ℝ)));
        (∀ m H : ℕ,
          eLpNorm (fun ω => X m ω - (P[X m | Bsym H]) ω)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
        (∀ (m H0 : ℕ), 0 < H0 →
          ∀ᵐ ω ∂P, Tendsto
            (fun ell : ℕ => (P[X m | Bsym (2 ^ ell * H0)]) ω)
            atTop (𝓝 (X m ω))) →
        (∀ B : ℝ, 0 < B → Cgeom * B < a * p * Real.log 3 →
          ∃ Hinc : ℕ, 0 < Hinc ∧
            ∀ H0 : ℕ, Hinc ≤ H0 →
              ∀ (m ell : ℕ), 1 ≤ ell →
                P {ω |
                    2 ^ (-(ell : ℤ) - 3 : ℤ) ≤
                      (P[X m | Bsym (2 ^ ell * H0)]) ω -
                        (P[X m | Bsym (2 ^ (ell - 1) * H0)]) ω} ≤
                  ENNReal.ofReal
                    (Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))))) →
        ∀ B : ℝ, 0 < B → Cgeom * B < a * p * Real.log 3 →
          ∃ H0 m0 : ℕ, 0 < H0 ∧
            ∀ m : ℕ, m0 ≤ m →
              ∃ W : ℕ+ → Set (BilateralField d),
                (∀ h : ℕ+,
                  MeasurableSet[
                    MeasurableSpace.comap
                      ((Set.Icc (center - 2 * (h : ℤ))
                        (center + (h : ℤ))).domRestrict)
                      (inferInstance : MeasurableSpace
                        ((i : Set.Icc (center - 2 * (h : ℤ))
                          (center + (h : ℤ))) →
                          C(SpatialCoordinates d, ℝ)))] (W h)) ∧
                (∀ h : ℕ+,
                  P (W h) ≤
                    ENNReal.ofReal (Real.exp (-(B * (h : ℝ))))) ∧
                (∀ h : ℕ+, (h : ℕ) < H0 → W h = ∅) ∧
                (∀ᵐ ω ∂P, 1 / 2 < X m ω →
                  ω ∈ ⋃ h : ℕ+, W h) := by
  intro Cgeom hCgeom d hd instM instB P instP center X hX01 hmeas hprob Cstar a p hCstar ha hp Bsym hE hD hI B hB hBab0
  obtain ⟨Hinc, hHinc0, hHinc⟩ := hI B hB hBab0
  let H0 : ℕ := max Hinc 1
  have hH0ge : Hinc ≤ H0 := le_max_left _ _
  have hH01 : 1 ≤ H0 := le_max_right _ _
  have hH00 : 0 < H0 := lt_of_lt_of_le Nat.zero_lt_one hH01
  obtain ⟨m0, hm0⟩ := aux_rare_m0 d P X hX01 hmeas hprob B hB H0 hH00
  refine ⟨H0, m0, hH00, fun m hm => ?_⟩
  let Bsym0 : ℕ → MeasurableSpace (BilateralField d) := fun H =>
    MeasurableSpace.comap ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
      (inferInstance : MeasurableSpace ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) → C(SpatialCoordinates d, ℝ)))
  have hBsym0 : ∀ H : ℕ, Bsym0 H = MeasurableSpace.comap ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
      (inferInstance : MeasurableSpace ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) → C(SpatialCoordinates d, ℝ))) := fun H => rfl
  have hlevel := aux_rare_h0_level_prob d P center X hmeas hX01 Bsym0 H0 m B (hm0 m hm)
  let W : ℕ+ → Set (BilateralField d) := fun h => (if (h : ℕ) = H0 then {ω : BilateralField d | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω} else ∅) ∪ ⋃ (l : { l : ℕ // 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ) }), {ω : BilateralField d | (2 : ℝ) ^ (-(((l : ℕ) : ℤ)) - 3) ≤ (P[X m | Bsym0 (2 ^ (l : ℕ) * H0)]) ω - (P[X m | Bsym0 (2 ^ ((l : ℕ) - 1) * H0)]) ω}
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact aux_rare_clause_meas3 d P center X Bsym0 hBsym0 H0 m W rfl
  · intro h
    by_cases hh : (h : ℕ) = H0
    · have hWeq : W h = {ω : BilateralField d | (3 / 8 : ℝ) ≤ (P[X m | Bsym0 H0]) ω} := by
        dsimp only [W]
        rw [ite_eq_left hh]
        have : IsEmpty { l : ℕ // 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ) } :=
          ⟨fun l => by
            have h2l : 2 ≤ 2 ^ (l : ℕ) := by
              calc 2 = 2 ^ (1 : ℕ) := by norm_num
                _ ≤ 2 ^ (l : ℕ) := Nat.pow_le_pow_right (by norm_num) l.2.1
            have hmul : 2 * H0 ≤ 2 ^ (l : ℕ) * H0 := Nat.mul_le_mul_right H0 h2l
            rw [l.2.2, hh] at hmul
            omega⟩
        rw [iUnion_of_empty, Set.union_empty]
      rw [hWeq]
      refine le_trans hlevel (le_of_eq ?_)
      rw [show (h : ℝ) = (H0 : ℝ) from by rw [hh]]
    · by_cases hex : ∃ l : ℕ, 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ)
      · obtain ⟨l, hl1, hl2⟩ := hex
        have hsub : W h ⊆ {ω : BilateralField d | (2 : ℝ) ^ (-(((l : ℕ) : ℤ)) - 3) ≤ (P[X m | Bsym0 (2 ^ (l : ℕ) * H0)]) ω - (P[X m | Bsym0 (2 ^ ((l : ℕ) - 1) * H0)]) ω} := by
          intro ω hω
          dsimp only [W] at hω
          rw [ite_eq_right hh, Set.empty_union] at hω
          simp only [Set.mem_iUnion, mem_ofPred_eq] at hω
          obtain ⟨l', hl'mem⟩ := hω
          have hl'eq : (l' : ℕ) = l := by
            have h2 : 2 ^ l = 2 ^ (l' : ℕ) := Nat.eq_of_mul_eq_mul_right hH00 (hl2.trans l'.2.2.symm)
            exact (Nat.pow_right_injective (by norm_num) h2).symm
          rw [hl'eq] at hl'mem
          exact hl'mem
        refine le_trans (measure_mono hsub) ?_
        have hcast : ((2 ^ l * H0 : ℕ) : ℝ) = ((h : ℕ) : ℝ) := by exact_mod_cast hl2
        have hmono := hHinc H0 hH0ge m l hl1
        rw [hcast] at hmono
        exact hmono
      · have hWeq : W h = ∅ := by
          dsimp only [W]
          rw [ite_eq_right hh, Set.empty_union]
          have : IsEmpty { l : ℕ // 1 ≤ l ∧ 2 ^ l * H0 = (h : ℕ) } := ⟨fun l => hex ⟨l, l.2.1, l.2.2⟩⟩
          rw [iUnion_of_empty]
        rw [hWeq, measure_empty]
        exact zero_le
  · exact aux_rare_clause_empty3 d P center X Bsym0 hBsym0 H0 m hH00 W rfl
  · filter_upwards [hD m H0 hH00] with ω hlim
    intro hlt
    by_cases h0 : (P[X m | Bsym0 H0]) ω < 3 / 8
    · have hfail : ¬ (∀ l : ℕ, 1 ≤ l → (P[X m | Bsym0 (2 ^ l * H0)]) ω - (P[X m | Bsym0 (2 ^ (l - 1) * H0)]) ω < (2 : ℝ) ^ (-(l : ℤ) - 3)) := by
        intro hΔ
        exact absurd (aux_rare_cover_telescope d P center X Bsym0 H0 hH00 m ω hlim h0 hΔ) (not_le.mpr hlt)
      push Not at hfail
      obtain ⟨l, hl1, hl2⟩ := hfail
      refine Set.mem_iUnion.mpr ⟨⟨2 ^ l * H0, Nat.mul_pos (Nat.pow_pos (by norm_num)) hH00⟩, ?_⟩
      dsimp only [W]
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨l, hl1, rfl⟩, hl2⟩)
    · push Not at h0
      refine Set.mem_iUnion.mpr ⟨⟨H0, hH00⟩, ?_⟩
      dsimp only [W]
      split_ifs with hc
      · exact Or.inl h0
      · exfalso; exact absurd rfl hc



theorem lem_rare_tests_dyadic_cover :
    ∀ (Cgeom : ℝ), 4 ≤ Cgeom →
    ∀ (d : ℕ) (_hd : 1 ≤ d)
      [MeasurableSpace C(SpatialCoordinates d, ℝ)]
      [BorelSpace C(SpatialCoordinates d, ℝ)]
      (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
      (center : ℤ)
      (X : ℕ → BilateralField d → ℝ)
      (_hX01 : ∀ m ω, X m ω ∈ Set.Icc (0 : ℝ) 1)
      (_hmeas : ∀ m, Measurable (X m))
      (_hprob : TendstoInMeasure P X atTop (fun _ => (0 : ℝ)))
      (Cstar a p : ℝ) (_hCstar : 0 < Cstar) (_ha : 0 < a) (_hp : 1 ≤ p),
      let Bsym : ℕ → MeasurableSpace (BilateralField d) := fun H =>
          MeasurableSpace.comap
            ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).domRestrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) →
                C(SpatialCoordinates d, ℝ)));
        (∀ m H : ℕ,
          eLpNorm (fun ω => X m ω - (P[X m | Bsym H]) ω)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
        (∀ (m H0 : ℕ), 0 < H0 →
          ∀ᵐ ω ∂P, Tendsto
            (fun ell : ℕ => (P[X m | Bsym (2 ^ ell * H0)]) ω)
            atTop (𝓝 (X m ω))) →
        (∀ B : ℝ, 0 < B → Cgeom * B < a * p * Real.log 3 →
          ∃ Hinc : ℕ, 0 < Hinc ∧
            ∀ H0 : ℕ, Hinc ≤ H0 →
              ∀ (m ell : ℕ), 1 ≤ ell →
                P {ω |
                    2 ^ (-(ell : ℤ) - 3 : ℤ) ≤
                      (P[X m | Bsym (2 ^ ell * H0)]) ω -
                        (P[X m | Bsym (2 ^ (ell - 1) * H0)]) ω} ≤
                  ENNReal.ofReal
                    (Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))))) →
        ∀ B : ℝ, 0 < B → Cgeom * B < a * p * Real.log 3 →
          ∃ H0 m0 : ℕ, 0 < H0 ∧
            ∀ m : ℕ, m0 ≤ m →
              ∃ W : ℕ+ → Set (BilateralField d),
                (∀ h : ℕ+,
                  MeasurableSet[
                    MeasurableSpace.comap
                      ((Set.Icc (center - 2 * (h : ℤ))
                        (center + (h : ℤ))).domRestrict)
                      (inferInstance : MeasurableSpace
                        ((i : Set.Icc (center - 2 * (h : ℤ))
                          (center + (h : ℤ))) →
                          C(SpatialCoordinates d, ℝ)))] (W h)) ∧
                (∀ h : ℕ+,
                  P (W h) ≤
                    ENNReal.ofReal (Real.exp (-(B * (h : ℝ))))) ∧
                (∀ h : ℕ+, (h : ℕ) < H0 → W h = ∅) ∧
                (∀ᵐ ω ∂P, 1 / 2 < X m ω →
                  ω ∈ ⋃ h : ℕ+, W h) := by
  intro Cgeom hCgeom d hd instM instB P instP center X hX01 hmeas hprob Cstar a p hCstar ha hp
  exact aux_lem_rare_tests_dyadic_cover_assembly Cgeom hCgeom d hd P center X hX01 hmeas hprob Cstar a p hCstar ha hp


end SubdiffusiveProcess.Paper
