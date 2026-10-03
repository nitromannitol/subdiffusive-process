module

public import SubdiffusiveProcess.Paper.lem_as_regularity_clipped_response_pair

@[expose] public section

/-! A retained response comparison controls the complete accumulated-error
score at two cutoffs. The error is the clipped response tolerance, its
geometric discarded tail, and the older initial-layer term. This file makes
no probabilistic estimate for that last term.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- The physical shell-block contribution increases with the cutoff. -/
theorem aux_lem_as_regularity_error_score_pair_field {d : ℕ}
    (s : ℝ) (eta : ℕ → BilateralField d → PotentialSample d) (omega : BilateralField d)
    (hEta : ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
      omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (n : ℤ) (z : SpatialCoordinates d) (N N' : ℕ) (hn : n ≤ (N : ℤ))
    (hNN' : N ≤ N') :
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((N : ℤ) - n).toNat
      ((3 : ℝ) ^ N • z) (eta N omega)).toReal ≤
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s ((N' : ℤ) - n).toNat
      ((3 : ℝ) ^ N' • z) (eta N' omega)).toReal := by
  have hm := aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_value_mono s omega eta hEta
    (fun om1 om2 a k w hrel =>
      aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_mono_shift s om1 om2 a k w
        (fun j => aux_lem_prefix_limit_actual_coordinate_cauchy_shellBlock_normOn_shift
          om1 om2 a k j w hrel
          (aux_lem_prefix_limit_actual_coordinate_cauchy_shellBlock_shift om1 om2 a k j hrel)))
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_ne_top s) n z hNN'
  simpa only [if_pos hn, if_pos (show n ≤ (N' : ℤ) by omega)] using hm

/-- Finiteness of the derivative term identifies the real accumulated score with four summands. -/
theorem aux_lem_as_regularity_error_score_pair_split {d : ℕ} [NeZero d]
    (M : GMCModel d) (s eps : ℝ) (hs : 0 < s) (om : PotentialSample d)
    (F Praw Rraw Draw : ℕ → SpatialCoordinates d → ℝ≥0∞)
    (Z : ℕ → SpatialCoordinates d → ℝ) (rawGood : ℕ → SpatialCoordinates d → Prop)
    (hPrimitive : primitive_scores d M s eps om F Praw Rraw Draw Z rawGood)
    (k : ℕ) (w : SpatialCoordinates d)
    (hfin : aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 k w om ≠ ⊤) :
    (Draw k w).toReal =
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1 M s k w om).toReal +
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2 s k w om).toReal +
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s k w om).toReal +
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 k w om).toReal := by
  rw [aux_lem_prefix_limit_actual_coordinate_cauchy_Dsc_eq_sum M s eps om
    F Praw Rraw Draw Z rawGood hPrimitive k w]
  have h1 := aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_ne_top M s hs k w om
  have h2 := aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_ne_top s k w om
  have h3 := aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3_ne_top s k w om
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨h1, h2⟩, h3⟩) hfin,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) h3,
    ENNReal.toReal_add h1 h2]

/-- The full accumulated error admits a one-sided two-cutoff comparison with explicit residuals. -/
theorem lem_as_regularity_error_score_pair {d : ℕ} [NeZero d]
    (M : GMCModel d) (s eps : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d) (omega : BilateralField d)
    (hEta : ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
      omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ≥0∞)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (hPrimitive : ∀ N, primitive_scores d M s eps (eta N omega)
      (fun m y => F N m y omega) (fun m y => Praw N m y omega)
      (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
      (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (n : ℤ) (z : SpatialCoordinates d) (N N' H : ℕ)
    (hNN' : N ≤ N') (hN : n + (H : ℤ) ≤ (N : ℤ))
    (hfin : aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((N : ℤ) - n).toNat
      ((3 : ℝ) ^ N • z) (eta N omega) ≠ ⊤)
    (tol : ℝ) (htol : 0 ≤ tol)
    (hretained : ∀ rk ∈ aux_prefix_rraw_G d H,
      aux_prefix_rraw_atom M eta N (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega ≤
        (1 + tol) * aux_prefix_rraw_atom M eta N' (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega + tol) :
    (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal ≤
      (Draw N' ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) omega).toReal +
        Real.sqrt (2 * tol) + (3 : ℝ) ^ (-(s / 2) * ((H + 1 : ℕ) : ℝ)) +
        (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
          ((3 : ℝ) ^ N • z) (eta N omega)).toReal := by
  have h4 := (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_value_const
    omega eta hEta n z N (by omega)).trans
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_value_const
        omega eta hEta n z N' (by omega)).symm
  have hfin' : aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4 ((N' : ℤ) - n).toNat
      ((3 : ℝ) ^ N' • z) (eta N' omega) ≠ ⊤ := by rw [← h4]; exact hfin
  have hsplit (K : ℕ) (hf : aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4
      ((K : ℤ) - n).toNat ((3 : ℝ) ^ K • z) (eta K omega) ≠ ⊤) :=
    aux_lem_as_regularity_error_score_pair_split M s eps hs (eta K omega)
      (fun m y => F K m y omega) (fun m y => Praw K m y omega)
      (fun m y => Rraw K m y omega) (fun m y => Draw K m y omega)
      (fun m y => Z K m y omega) (fun m y => rawGood K m y omega)
      (hPrimitive K) ((K : ℤ) - n).toNat ((3 : ℝ) ^ K • z) hf
  rw [hsplit N hfin, hsplit N' hfin', h4]
  have h1 := lem_as_regularity_clipped_response_pair M s hs eta omega n z N N' H
    hNN' hN tol htol hretained
  have h2 := aux_lem_as_regularity_error_score_pair_field s eta omega hEta n z N N'
    (by omega) hNN'
  have h3 := ENNReal.toReal_nonneg (a :=
    aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N' : ℤ) - n).toNat
      ((3 : ℝ) ^ N' • z) (eta N' omega))
  linarith only [h1, h2, h3]

end Paper
