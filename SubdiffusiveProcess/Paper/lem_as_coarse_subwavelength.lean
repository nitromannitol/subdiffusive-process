import SubdiffusiveProcess.Paper.lem_extremes
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import Mathlib.Tactic

open MeasureTheory Set Filter Topology SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_as_coarse_subwavelength
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s p : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hp : 1 ≤ p)
    (extremeEnvelope : Bool → ℕ → BilateralField d → ℝ)
    (hnonneg : ∀ withIR N ω, 0 ≤ extremeEnvelope withIR N ω)
    (hmeas : ∀ withIR N, AEStronglyMeasurable (extremeEnvelope withIR N)
      (chaosSampleLaw M).toMeasure)
    (hmoment : ∀ withIR : Bool, ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      γ < s * Real.log 3 ∧
      ∀ N : ℕ,
        eLpNorm (extremeEnvelope withIR N)
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (C * Real.exp (γ * (N : ℝ)))) :
    ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
      ∀ withIR : Bool, ∀ N : ℕ,
        (3 : ℝ) ^ (-(s * (N : ℝ))) * extremeEnvelope withIR N ω ≤ K := by
  have aux : ∀ (f : ℕ → BilateralField d → ℝ), (∀ N ω, 0 ≤ f N ω) →
      (∀ N, AEStronglyMeasurable (f N) (chaosSampleLaw M).toMeasure) →
      ∀ (C γ : ℝ), 0 < C → γ < s * Real.log 3 →
      (∀ N, eLpNorm (f N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C * Real.exp (γ * N))) →
      ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
        (3 : ℝ) ^ (-(s * (N : ℝ))) * f N ω ≤ K := by
    intro f hnonneg hmeas C γ hC hγ hmom
    set A : ℝ := γ - s * Real.log 3 with hAdef
    have hAneg : A < 0 := by rw [hAdef]; linarith [hγ]
    have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
    let g : ℕ → BilateralField d → ℝ := fun N ω => (3:ℝ) ^ (-(s * (N:ℝ))) * f N ω
    let bad : ℕ → Set (BilateralField d) := fun N => {ω | (1:ℝ) ≤ g N ω}
    have hgnonneg : ∀ N ω, 0 ≤ g N ω := by
      intro N ω
      exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) _))
        (hnonneg N ω)
    have hkey : ∀ N : ℕ,
        (3:ℝ) ^ (-(s * (N:ℝ))) * (C * Real.exp (γ * (N:ℝ))) =
          C * Real.exp (A * (N:ℝ)) := by
      intro N
      have h3 : (3:ℝ) ^ (-(s * (N:ℝ))) * Real.exp (γ * (N:ℝ)) =
          Real.exp (A * (N:ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
        rw [← Real.exp_add]
        congr 1
        rw [hAdef]
        ring
      calc (3:ℝ) ^ (-(s * (N:ℝ))) * (C * Real.exp (γ * (N:ℝ)))
          = C * ((3:ℝ) ^ (-(s * (N:ℝ))) * Real.exp (γ * (N:ℝ))) := by ring
        _ = C * Real.exp (A * (N:ℝ)) := by rw [h3]
    have hterm : ∀ N : ℕ,
        (C * Real.exp (A * (N:ℝ))) ^ p = C ^ p * (Real.exp (A * p)) ^ N := by
      intro N
      rw [Real.mul_rpow (le_of_lt hC) (Real.exp_nonneg _)]
      congr 1
      rw [← Real.exp_mul (A * (N:ℝ)) p, ← Real.exp_nat_mul (A * p) N]
      congr 1
      ring
    have hsumm : Summable (fun N : ℕ => (C * Real.exp (A * (N:ℝ))) ^ p) := by
      have hgeo : Summable (fun N : ℕ => C ^ p * (Real.exp (A * p)) ^ N) :=
        (summable_geometric_of_lt_one (Real.exp_nonneg (A * p))
          (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos hAneg hp_pos))).mul_left (C ^ p)
      simpa only [hterm] using hgeo
    have hLp : ∀ N : ℕ, eLpNorm (g N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C * Real.exp (A * (N:ℝ))) := by
      intro N
      have hcN : 0 < (3:ℝ) ^ (-(s * (N:ℝ))) :=
        Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 3) _
      have hfun : g N = (3:ℝ) ^ (-(s * (N:ℝ))) • f N := rfl
      calc eLpNorm (g N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure
          = ENNReal.ofReal ((3:ℝ) ^ (-(s * (N:ℝ)))) *
              eLpNorm (f N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure := by
            rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal (le_of_lt hcN)]
        _ ≤ ENNReal.ofReal ((3:ℝ) ^ (-(s * (N:ℝ)))) *
              ENNReal.ofReal (C * Real.exp (γ * (N:ℝ))) := by
            exact mul_le_mul_left' (hmom N) _
        _ = ENNReal.ofReal ((3:ℝ) ^ (-(s * (N:ℝ))) * (C * Real.exp (γ * (N:ℝ)))) := by
            rw [← ENNReal.ofReal_mul (le_of_lt hcN)]
        _ = ENNReal.ofReal (C * Real.exp (A * (N:ℝ))) := by rw [hkey N]
    have hmono : ∀ N : ℕ,
        (chaosSampleLaw M).toMeasure (bad N) ≤
          ENNReal.ofReal ((C * Real.exp (A * (N:ℝ))) ^ p) := by
      intro N
      have hp_ne0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp_pos).ne'
      have hp_netop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
      have hmeasg : AEStronglyMeasurable (g N) (chaosSampleLaw M).toMeasure := by
        have hfun : g N = (3:ℝ) ^ (-(s * (N:ℝ))) • f N := rfl
        rw [hfun]
        exact (hmeas N).const_smul _
      have hmarkov := meas_ge_le_mul_pow_eLpNorm_enorm
          (μ := (chaosSampleLaw M).toMeasure) hp_ne0 hp_netop hmeasg
          (ε := (1:ℝ≥0∞)) (by simp) (fun h => absurd h ENNReal.one_ne_top)
      calc (chaosSampleLaw M).toMeasure (bad N)
          = (chaosSampleLaw M).toMeasure {ω | (1:ℝ≥0∞) ≤ ‖g N ω‖ₑ} := by
            congr 1
            ext ω
            simp only [bad, Set.mem_setOf_eq]
            rw [Real.enorm_eq_ofReal (hgnonneg N ω), ← ENNReal.ofReal_one]
            exact (ENNReal.ofReal_le_ofReal_iff (hgnonneg N ω)).symm
        _ ≤ (1:ℝ≥0∞)⁻¹ ^ (ENNReal.ofReal p).toReal *
              eLpNorm (g N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ^
                (ENNReal.ofReal p).toReal := hmarkov
        _ = eLpNorm (g N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ^ p := by
            rw [ENNReal.toReal_ofReal (le_of_lt hp_pos)]
            simp only [inv_one, ENNReal.one_rpow, one_mul]
        _ ≤ (ENNReal.ofReal (C * Real.exp (A * (N:ℝ)))) ^ p :=
            ENNReal.rpow_le_rpow (hLp N) (le_of_lt hp_pos)
        _ = ENNReal.ofReal ((C * Real.exp (A * (N:ℝ))) ^ p) := by
            rw [ENNReal.ofReal_rpow_of_nonneg
              (mul_nonneg (le_of_lt hC) (Real.exp_nonneg _)) (le_of_lt hp_pos)]
    have hsumm_bad : ∑' N : ℕ, (chaosSampleLaw M).toMeasure (bad N) ≠ ⊤ := by
      have hle : ∑' N : ℕ, (chaosSampleLaw M).toMeasure (bad N) ≤
          ∑' N : ℕ, ENNReal.ofReal ((C * Real.exp (A * (N:ℝ))) ^ p) :=
        ENNReal.tsum_le_tsum (fun N => hmono N)
      have htop : ∑' N : ℕ, ENNReal.ofReal ((C * Real.exp (A * (N:ℝ))) ^ p) < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun N => Real.rpow_nonneg (mul_nonneg (le_of_lt hC) (Real.exp_nonneg _)) _) hsumm]
        exact ENNReal.ofReal_lt_top
      exact ne_of_lt (lt_of_le_of_lt hle htop)
    have hbc : (chaosSampleLaw M).toMeasure (limsup bad atTop) = 0 :=
      measure_limsup_atTop_eq_zero (μ := (chaosSampleLaw M).toMeasure) (s := bad) hsumm_bad
    have hfin : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∀ᶠ N in atTop, g N ω < 1 := by
      rw [ae_iff]
      have hset : {ω | ¬ ∀ᶠ N in atTop, g N ω < 1} = limsup bad atTop := by
        ext ω
        simp only [Set.mem_setOf_eq, mem_limsup_iff_frequently_mem, not_eventually,
          bad, not_lt]
      rw [hset]
      exact hbc
    filter_upwards [hfin] with ω hω
    obtain ⟨N0, hN0⟩ := eventually_atTop.mp hω
    have hs : 0 ≤ ∑ n ∈ Finset.range N0, |g n ω| :=
      Finset.sum_nonneg (fun n _ => abs_nonneg _)
    refine ⟨1 + ∑ n ∈ Finset.range N0, |g n ω|, ?_, ?_⟩
    · linarith
    · intro N
      change g N ω ≤ 1 + ∑ n ∈ Finset.range N0, |g n ω|
      rcases lt_or_ge N N0 with h | h
      · have hmem : N ∈ Finset.range N0 := Finset.mem_range.mpr h
        have hle : |g N ω| ≤ ∑ n ∈ Finset.range N0, |g n ω| :=
          Finset.single_le_sum (fun n _ => abs_nonneg (g n ω)) hmem
        have h2 : g N ω ≤ ∑ n ∈ Finset.range N0, |g n ω| := le_trans (le_abs_self _) hle
        linarith
      · have h3 : g N ω < 1 := hN0 N h
        linarith
  have hfalse : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure,
      ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
        (3 : ℝ) ^ (-(s * (N : ℝ))) * extremeEnvelope false N ω ≤ K := by
    obtain ⟨C, γ, hC, hγpos, hγ, hmom⟩ := hmoment false
    exact aux (extremeEnvelope false) (hnonneg false) (hmeas false) C γ hC hγ hmom
  have htrue : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure,
      ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
        (3 : ℝ) ^ (-(s * (N : ℝ))) * extremeEnvelope true N ω ≤ K := by
    obtain ⟨C, γ, hC, hγpos, hγ, hmom⟩ := hmoment true
    exact aux (extremeEnvelope true) (hnonneg true) (hmeas true) C γ hC hγ hmom
  filter_upwards [hfalse, htrue] with ω hf ht
  obtain ⟨Kf, hKfpos, hKf⟩ := hf
  obtain ⟨Kt, hKtpos, hKt⟩ := ht
  refine ⟨max Kf Kt, lt_max_of_lt_left hKfpos, ?_⟩
  intro withIR N
  cases withIR with
  | false => exact le_trans (hKf N) (le_max_left _ _)
  | true => exact le_trans (hKt N) (le_max_right _ _)


end Paper
