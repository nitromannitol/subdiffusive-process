module

public import SubdiffusiveProcess.Paper.lem_as_regularity_reference_ratio
public import SubdiffusiveProcess.Paper.lem_as_coarse

@[expose] public section

/-! The coarse reference at physical level k is controlled by the coefficient
at cutoff k-1, with an annealed loss depending on k only. The reference envelope
is uniform in the actual cutoff N; no solution bound is claimed here.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- A normalized cutoff coefficient has the expected logarithm. -/
theorem aux_lem_as_regularity_reference_extremes_log {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (i : ℕ) (z : SpatialCoordinates d) :
    Real.log (cutoffCoefficient M H omega i z) =
      -Real.log (ahom M i) + H omega z +
        ∑ j ∈ Finset.range (i + 1), omega (-(j : ℤ)) z -
          ((i : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
  rw [cutoffCoefficient, Real.log_mul (inv_pos.mpr (ahom_pos M i)).ne'
    (Real.exp_pos _).ne', Real.log_inv, Real.log_exp, cutoffPotential]
  simp only [Int.ofNat_eq_natCast]
  ring

/-- The logarithmic reference correction is controlled by twice the variance times physical depth. -/
theorem aux_lem_as_regularity_reference_extremes_log_bound {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N i : ℕ) (hi : i + 1 ≤ N) (z : SpatialCoordinates d) :
    |Real.log (aux_in_deterministic_onestep_sref M H omega N (i + 1 : ℕ) z) -
      Real.log (cutoffCoefficient M H omega i z)| ≤
        2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((i : ℝ) + 1) := by
  have hnat : (((N : ℤ) - ((i + 1 : ℕ) : ℤ)).toNat : ℝ) = (N : ℝ) - (i + 1 : ℕ) := by
    have hh : ((N : ℤ) - ((i + 1 : ℕ) : ℤ)).toNat = N - (i + 1) := by omega
    rw [hh, Nat.cast_sub hi]
  have hrem : ((N : ℤ) - ((i + 1 : ℕ) : ℤ)).toNat ≤ N := by omega
  obtain ⟨hr1, hr2⟩ := aux_lem_as_regularity_reference_ratio_ahom M Rm _ N hrem
  have hl := Real.log_le_log (Real.exp_pos _) (Rm.ahom_lower i)
  have hu := Real.log_le_log (ahom_pos M i) (Rm.ahom_le_one i)
  rw [Real.log_exp] at hl
  rw [Real.log_one] at hu
  have ht := M.G4.tauSq_pos.le
  have hnn : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((i : ℝ) + 1) :=
    mul_nonneg ht (by positivity)
  rw [aux_lem_as_regularity_reference_ratio_log, aux_lem_as_regularity_reference_extremes_log,
    signedPrefix, if_pos (Int.natCast_nonneg _), aux_in_deterministic_onestep_sum_Ico_int,
    hnat]
  rw [hnat] at hr1
  push_cast at hr1 hr2 ⊢
  apply abs_le.mpr
  constructor <;> nlinarith only [hr1, hr2, hl, hu, hnn]

/-- Reference plus inverse is bounded by the lower-cutoff extremes with a deterministic depth loss. -/
theorem aux_lem_as_regularity_reference_extremes_compare {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N i : ℕ) (hi : i + 1 ≤ N) (z : SpatialCoordinates d) :
    aux_in_deterministic_onestep_sref M H omega N (i + 1 : ℕ) z +
      (aux_in_deterministic_onestep_sref M H omega N (i + 1 : ℕ) z)⁻¹ ≤
      Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((i : ℝ) + 1)) *
        (cutoffCoefficient M H omega i z + (cutoffCoefficient M H omega i z)⁻¹) := by
  apply aux_lem_as_coarse_exp_factor _ _
    (Real.log (aux_in_deterministic_onestep_sref M H omega N (i + 1 : ℕ) z) -
      Real.log (cutoffCoefficient M H omega i z)) _ (cutoffCoefficient_pos M H omega i z)
  · rw [Real.exp_sub, Real.exp_log (aux_in_deterministic_onestep_sref_pos M H omega N _ z),
      Real.exp_log (cutoffCoefficient_pos M H omega i z)]
    field_simp [(cutoffCoefficient_pos M H omega i z).ne']
  · exact aux_lem_as_regularity_reference_extremes_log_bound M Rm H omega N i hi z

/-- The reference at physical level zero is exactly the infrared exponential. -/
theorem aux_lem_as_regularity_reference_extremes_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) :
    aux_in_deterministic_onestep_sref M H omega N 0 z = Real.exp (H omega z) := by
  simp only [aux_in_deterministic_onestep_sref, sub_zero, Int.toNat_natCast,
    if_pos (le_refl (0 : ℤ)), Finset.Ico_self, Finset.sum_empty, add_zero,
    div_self (mul_pos (Real.exp_pos _) (ahom_pos M N)).ne', one_mul]

/-- A small disorder threshold controls the annealed depth exponent. -/
theorem aux_lem_as_regularity_reference_extremes_rate {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (e : ℝ)
    (hdel : M.delta ≤ min 1 (e * Real.log 3 / 8)) :
    2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ e * Real.log 3 / 4 := by
  have h1 := hdel.trans (min_le_left _ _)
  have h2 := hdel.trans (min_le_right _ _)
  have hd := M.shellPrefix.delta_pos.le
  have hlog : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hlog (sq_nonneg M.delta)
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ M.delta ^ 2 := by
    linarith only [tauSq_le_delta_sq M, hh, sq_nonneg M.delta]
  nlinarith only [h1, h2, hd, htau]

/-- The reference and its inverse have one cutoff-uniform envelope at every physical depth. -/
theorem lem_as_regularity_reference_extremes (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (e : ℝ) (he : 0 < e) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ V : ℝ, 0 < V ∧
        ∀ (N k : ℕ), k ≤ N →
        ∀ z ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
          aux_in_deterministic_onestep_sref M H omega N k z +
            (aux_in_deterministic_onestep_sref M H omega N k z)⁻¹ ≤
              V * (3 : ℝ) ^ (e * k) := by
  let s := min (e / 4) 1
  have hs0 : 0 < s := lt_min (by positivity) zero_lt_one
  have hs1 : s ≤ 1 := min_le_right _ _
  have hse : s ≤ e / 4 := min_le_left _ _
  obtain ⟨delta0, hd0, hext⟩ := aux_lem_as_coarse_root_extremes d hd s ⟨hs0, hs1⟩
  refine ⟨min delta0 (min 1 (e * Real.log 3 / 8)),
    lt_min hd0 (lt_min zero_lt_one (by positivity)), ?_⟩
  intro M Rm H hH hdelta
  have hrate := aux_lem_as_regularity_reference_extremes_rate M e
    (hdelta.trans (min_le_right _ _))
  filter_upwards [hext M H hH (hdelta.trans (min_le_left _ _))
    (fun _ => (1 / 2 : ℝ)) 1 one_pos] with omega hExt
  obtain ⟨K, hK, hExt⟩ := hExt
  have hcompact : IsCompact (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
      Set (SpatialCoordinates d)) := isCompact_closedBall _ _
  have hcont : Continuous (fun z => Real.exp (H omega z) + Real.exp (-(H omega z))) :=
    (Real.continuous_exp.comp (H omega).continuous).add
      (Real.continuous_exp.comp (H omega).continuous.neg)
  obtain ⟨K0, hK0⟩ := hcompact.bddAbove_image hcont.continuousOn
  let V := max 1 (max K K0)
  have hV : 0 < V := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨V, hV, ?_⟩
  intro N k hk z hz
  cases k with
  | zero =>
    simp only [Nat.cast_zero]
    rw [aux_lem_as_regularity_reference_extremes_zero]
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    rw [← Real.exp_neg]
    exact (hK0 ⟨z, hz, rfl⟩).trans ((le_max_right K K0).trans (le_max_right _ _))
  | succ i =>
    have hc := aux_lem_as_regularity_reference_extremes_compare M Rm H omega N i hk z
    have hx := hExt true i z hz
    simp only [↓reduceIte] at hx
    have hcoef : cutoffCoefficient M H omega i z + (cutoffCoefficient M H omega i z)⁻¹ ≤
        K * (3 : ℝ) ^ (s * i) := by
      have hh := mul_le_mul_of_nonneg_left hx (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (s * i)).le
      rw [← mul_assoc, ← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero,
        one_mul] at hh
      exact hh.trans_eq (mul_comm _ _)
    have hpow : Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((i : ℝ) + 1)) *
        (3 : ℝ) ^ (s * i) ≤ (3 : ℝ) ^ (e * (i + 1 : ℕ)) := by
      rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hr := mul_le_mul_of_nonneg_right hrate (show (0 : ℝ) ≤ i + 1 by positivity)
      have hs := mul_le_mul_of_nonneg_left hse (show (0 : ℝ) ≤ (i : ℝ) * Real.log 3 by positivity)
      have he0 : 0 ≤ e * Real.log 3 := by positivity
      have heI : 0 ≤ e * Real.log 3 * i := by positivity
      push_cast
      nlinarith only [hr, hs, he0, heI]
    calc aux_in_deterministic_onestep_sref M H omega N (i + 1 : ℕ) z +
          (aux_in_deterministic_onestep_sref M H omega N (i + 1 : ℕ) z)⁻¹ ≤
        Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((i : ℝ) + 1)) *
          (K * (3 : ℝ) ^ (s * i)) := hc.trans (mul_le_mul_of_nonneg_left hcoef (Real.exp_pos _).le)
      _ = K * (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((i : ℝ) + 1)) *
          (3 : ℝ) ^ (s * i)) := by ring
      _ ≤ K * (3 : ℝ) ^ (e * (i + 1 : ℕ)) := mul_le_mul_of_nonneg_left hpow hK.le
      _ ≤ V * (3 : ℝ) ^ (e * (i + 1 : ℕ)) := mul_le_mul_of_nonneg_right
        ((le_max_left K K0).trans (le_max_right _ _)) (Real.rpow_nonneg (by norm_num) _)

end Paper
