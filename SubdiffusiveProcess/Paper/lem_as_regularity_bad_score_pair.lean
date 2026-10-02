import SubdiffusiveProcess.Paper.lem_as_regularity_response_score_pair
import SubdiffusiveProcess.Analysis.ExtendedPrimitiveRamp

/-! A retained atom comparison and a small discarded response tail control
the actual bad score at two cutoffs. The field and product ramps use their
existing exact monotonicity. No probability bound is asserted here.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- The actual bad score has a one-sided comparison under retained-response and tail bounds. -/
theorem lem_as_regularity_bad_score_pair {d : ℕ} [NeZero d]
    (M : GMCModel d) (s eps : ℝ) (hs : 0 < s) (heps : 0 < eps)
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
    (tol : ℝ) (htol : 0 ≤ tol)
    (hretained : ∀ rk ∈ aux_prefix_rraw_G d H,
      aux_prefix_rraw_atom M eta N (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega ≤
        (1 + tol) * aux_prefix_rraw_atom M eta N' (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega + tol)
    (htail : (aux_prefix_rraw_tail M s (eta N omega) ((N : ℤ) - n).toNat
      ((3 : ℝ) ^ N • z) H).toReal ≤ tol) :
    Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega ≤
      Z N' ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) omega +
        (2 * tol) * (1 + eps ^ 2) / (eps ^ 2 - eps ^ 2 / 4) := by
  let m : ℕ → ℕ := fun K => ((K : ℤ) - n).toNat
  let w : ℕ → SpatialCoordinates d := fun K => (3 : ℝ) ^ K • z
  have hmon := aux_lem_prefix_limit_actual_coordinate_cauchy_raw_mono M s eps omega eta hEta
    F Praw Rraw Draw Z rawGood hPrimitive n z N N' (by omega) hNN'
  obtain ⟨_, _, _, _, _, _, hRN, _, _, hZN, _⟩ := hPrimitive N
  obtain ⟨_, _, _, _, _, _, hRN', _, _, hZN', _⟩ := hPrimitive N'
  have hR (K : ℕ) (hK : ∀ m' y', Rraw K m' y' omega =
      aux_prefix_rraw_Rset M s (eta K omega) m' y') :
      Rraw K (m K) (w K) omega ≠ ⊤ := by
    rw [hK]
    exact aux_psf_Rsc_ne_top M s (m K) (w K) (eta K omega)
  have hpair := lem_as_regularity_response_score_pair M s hs.le eta omega n z N N' H
    hNN' hN tol htol hretained
  have hidN : Rraw N (m N) (w N) omega =
      aux_prefix_rraw_Rset M s (eta N omega) (m N) (w N) := hRN _ _
  have hidN' : Rraw N' (m N') (w N') omega =
      aux_prefix_rraw_Rset M s (eta N' omega) (m N') (w N') := hRN' _ _
  change (aux_prefix_rraw_Rset M s (eta N omega) (m N) (w N)).toReal ≤
    (1 + tol) * (aux_prefix_rraw_Rset M s (eta N' omega) (m N') (w N')).toReal + tol +
      (aux_prefix_rraw_tail M s (eta N omega) (m N) (w N) H).toReal at hpair
  rw [← hidN, ← hidN'] at hpair
  have hrel : (Rraw N (m N) (w N) omega).toReal ≤
      (1 + 2 * tol) * (Rraw N' (m N') (w N') omega).toReal + 2 * tol := by
    have hnonneg := ENNReal.toReal_nonneg (a := Rraw N' (m N') (w N') omega)
    have hprod := mul_nonneg htol hnonneg
    linarith only [hpair, htail, hprod]
  have hramp := extendedPrimitiveRamp_le_of_relative_le (eps ^ 2 / 4) (eps ^ 2)
    (by positivity) (by nlinarith only [sq_pos_of_pos heps])
    (Rraw N (m N) (w N) omega) (Rraw N' (m N') (w N') omega)
    (hR N hRN) (hR N' hRN') (2 * tol) (by linarith only [htol]) hrel
  have hfield := extendedPrimitiveRamp_mono (eps / 2) eps hmon.1
  have hproduct := extendedPrimitiveRamp_mono 6 12 hmon.2
  have hzN := (hZN (m N) (w N)).1
  have hzN' := (hZN' (m N') (w N')).1
  change Z N (m N) (w N) omega =
    extendedPrimitiveRamp (eps / 2) eps (F N (m N) (w N) omega) +
      extendedPrimitiveRamp 6 12 (Praw N (m N) (w N) omega) +
      extendedPrimitiveRamp (eps ^ 2 / 4) (eps ^ 2) (Rraw N (m N) (w N) omega) at hzN
  change Z N' (m N') (w N') omega =
    extendedPrimitiveRamp (eps / 2) eps (F N' (m N') (w N') omega) +
      extendedPrimitiveRamp 6 12 (Praw N' (m N') (w N') omega) +
      extendedPrimitiveRamp (eps ^ 2 / 4) (eps ^ 2) (Rraw N' (m N') (w N') omega) at hzN'
  change Z N (m N) (w N) omega ≤ Z N' (m N') (w N') omega + _
  linarith only [hzN, hzN', hfield, hproduct, hramp]

end Paper
