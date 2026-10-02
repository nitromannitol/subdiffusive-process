import SubdiffusiveProcess.Paper.in_deterministic
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Analysis.SignedPrefix
import SubdiffusiveProcess.Analysis.LogRatioBounds

/-! The actual normalized coarse reference has two-sided ratios controlled by
the original error-score sum, including negative padded root levels. This is a
pointwise comparison and contains no almost-sure prefix or mesh assertion.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- Annealed ordering bounds the logarithmic decrement at any two remaining cutoffs. -/
theorem aux_lem_as_regularity_reference_ratio_ahom {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (i j : ℕ) (hij : i ≤ j) :
    -(2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((j : ℝ) - i)) ≤
        Real.log (ahom M j) - Real.log (ahom M i) ∧
      Real.log (ahom M j) - Real.log (ahom M i) ≤ 0 := by
  rcases eq_or_lt_of_le hij with heq | hlt
  · subst j
    simp only [sub_self, mul_zero, neg_zero, le_refl, and_self]
  · obtain ⟨h1, h2⟩ := Rm.ahom_ordering i j hlt
    have hlog1 := Real.log_le_log (ahom_pos M j) h1
    have hlog2 := Real.log_le_log (ahom_pos M i) h2
    rw [Real.log_mul (Real.exp_pos _).ne' (ahom_pos M j).ne', Real.log_exp] at hlog2
    constructor <;> linarith only [hlog1, hlog2]

/-- The logarithm of the physical reference is its normalizer plus its signed field prefix. -/
theorem aux_lem_as_regularity_reference_ratio_log {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (k : ℤ) (w : SpatialCoordinates d) :
    Real.log (aux_in_deterministic_onestep_sref M H omega N k w) =
      ((((N : ℤ) - k).toNat : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
        Real.log (ahom M ((N : ℤ) - k).toNat) -
        (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P + Real.log (ahom M N)) +
        H omega w + signedPrefix (fun i => omega (-i) w) k := by
  unfold aux_in_deterministic_onestep_sref
  dsimp only
  rw [Real.log_mul (div_pos (mul_pos (Real.exp_pos _) (ahom_pos M _))
    (mul_pos (Real.exp_pos _) (ahom_pos M _))).ne' (Real.exp_pos _).ne',
    Real.log_div (mul_pos (Real.exp_pos _) (ahom_pos M _)).ne'
      (mul_pos (Real.exp_pos _) (ahom_pos M _)).ne',
    Real.log_mul (Real.exp_pos _).ne' (ahom_pos M _).ne',
    Real.log_mul (Real.exp_pos _).ne' (ahom_pos M _).ne',
    Real.log_exp, Real.log_exp, Real.log_exp]
  unfold signedPrefix
  ring

/-- A sum of physical layer magnitudes bounds the logarithmic reference ratio. -/
theorem aux_lem_as_regularity_reference_ratio_log_bound {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (k l : ℤ) (hkl : k ≤ l) (hlN : l ≤ (N : ℤ)) (w : SpatialCoordinates d) :
    |Real.log (aux_in_deterministic_onestep_sref M H omega N k w) -
      Real.log (aux_in_deterministic_onestep_sref M H omega N l w)| ≤
        ((l - k : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
          ∑ i ∈ Finset.Ico k l, |omega (-i) w| := by
  have hnat : ((N : ℤ) - l).toNat ≤ ((N : ℤ) - k).toNat := by omega
  have hdiff : (((N : ℤ) - k).toNat : ℝ) - (((N : ℤ) - l).toNat : ℝ) = ((l - k : ℤ) : ℝ) := by
    have hk : (((N : ℤ) - k).toNat : ℤ) = (N : ℤ) - k := Int.toNat_of_nonneg (by omega)
    have hl : (((N : ℤ) - l).toNat : ℤ) = (N : ℤ) - l := Int.toNat_of_nonneg (by omega)
    exact_mod_cast (show (((N : ℤ) - k).toNat : ℤ) - (((N : ℤ) - l).toNat : ℤ) = l - k by
      rw [hk, hl]; ring)
  obtain ⟨ha1, ha2⟩ := aux_lem_as_regularity_reference_ratio_ahom M Rm _ _ hnat
  rw [hdiff] at ha1
  have hsum := signedPrefix_sub (fun i => omega (-i) w) k l hkl
  have habs : |∑ i ∈ Finset.Ico k l, omega (-i) w| ≤
      ∑ i ∈ Finset.Ico k l, |omega (-i) w| := Finset.abs_sum_le_sum_abs _ _
  rw [aux_lem_as_regularity_reference_ratio_log, aux_lem_as_regularity_reference_ratio_log]
  have hs := abs_le.mp habs
  have hnorm : ((((N : ℤ) - k).toNat : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
      ((((N : ℤ) - l).toNat : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P =
        ((l - k : ℤ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
    rw [← hdiff]
    ring
  apply abs_le.mpr
  constructor <;> linarith only [ha1, ha2, hsum, hs.1, hs.2, hnorm]

/-- Original error scores control both directions of the signed-level reference ratio. -/
theorem lem_as_regularity_reference_ratio {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (s eps : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (F P R D : ℕ → Vec d → ENNReal) (Z : ℕ → Vec d → ℝ)
    (good : ℕ → Vec d → Prop) (hPS : primitive_scores d M s eps eta F P R D Z good)
    (w : SpatialCoordinates d) (k l : ℤ) (hkl : k ≤ l) (hlN : l ≤ (N : ℤ))
    (S : Finset ℤ) (hsub : Finset.Ico k l ⊆ S)
    (hfin : ∀ i ∈ S, D ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤)
    (Sig : ℝ) (hSig : ∑ i ∈ S, (D ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w)).toReal ≤ Sig) :
    Real.exp (-(((l - k : ℤ) : ℝ) * M.delta ^ 2 + 2 * Sig)) ≤
      aux_in_deterministic_onestep_sref M H omega N k w /
        aux_in_deterministic_onestep_sref M H omega N l w ∧
    aux_in_deterministic_onestep_sref M H omega N k w /
        aux_in_deterministic_onestep_sref M H omega N l w ≤
      Real.exp (((l - k : ℤ) : ℝ) * M.delta ^ 2 + 2 * Sig) := by
  have hlayers : (∑ i ∈ Finset.Ico k l, |omega (-i) w|) ≤ 2 * Sig := by
    have hle := Finset.sum_le_sum (fun i hi => aux_in_deterministic_onestep_omega_le_draw
      M omega N eta hEta s eps hs F P R D Z good hPS w i
      (lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 hlN) (hfin i (hsub hi)))
    rw [← Finset.mul_sum] at hle
    exact hle.trans (mul_le_mul_of_nonneg_left
      ((Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => ENNReal.toReal_nonneg)).trans hSig) (by norm_num))
  have hlog := aux_lem_as_regularity_reference_ratio_log_bound M Rm H omega N k l hkl hlN w
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ M.delta ^ 2 := by
    have hlog : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num)).trans_eq (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hlog (sq_nonneg M.delta)
    linarith only [tauSq_le_delta_sq M, hh, sq_nonneg M.delta]
  have hdelta := mul_le_mul_of_nonneg_left htau
    (show (0 : ℝ) ≤ ((l - k : ℤ) : ℝ) by exact_mod_cast sub_nonneg.mpr hkl)
  exact exp_ratio_of_log_sub (aux_in_deterministic_onestep_sref_pos M H omega N k w)
    (aux_in_deterministic_onestep_sref_pos M H omega N l w)
    (hlog.trans (add_le_add hdelta hlayers))

end Paper
