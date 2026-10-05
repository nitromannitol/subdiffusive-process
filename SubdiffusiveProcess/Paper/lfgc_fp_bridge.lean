module

public import SubdiffusiveProcess.Paper.lfgc_fp_det
public import SubdiffusiveProcess.Paper.lfgc_fp_main
public import SubdiffusiveProcess.Paper.lfgc_rhs_bridge

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# The pad tests off the bank failure event

On a sample whose score families satisfy `primitive_scores` at the canonical sample of cutoff
`N`, the pad tests `F ≤ 1` and `P ≤ 12` hold at level `n` and every pad centre as soon as the
sample avoids the bank failure event `aux_lfgc_fp_cover_fpBad`.
-/

open MeasureTheory Filter Topology _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The pad tests off the bank failure event. -/
theorem aux_lfgc_fp_bridge_pad_tests_of_not_fpBad [NeZero d] (hd1 : (1 : ℝ) ≤ (d : ℝ)) (M : GMCModel d) (s eps : ℝ)
    (hs : 0 ≤ s) (eta : ℕ → BilateralField d → PotentialSample d)
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop) (omega : BilateralField d) (N n : ℕ)
    (h1 : ∀ (i : ℕ) (y : Vec d), eta N omega i y =
      omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (h2 : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps (eta N omega)
      (fun m y => F N m y omega) (fun m y => Praw N m y omega)
      (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
      (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    {ns : ℕ} (y : Fin ns → Vec d) (hω : omega ∉ aux_lfgc_fp_cover_fpBad s N n y) (t : Fin ns) :
    F N n (y t) omega ≤ 1 ∧ Praw N n (y t) omega ≤ 12 := by
  have hc : eta N omega = aux_lfgc_layer_tail_canonEta N omega := aux_lfgc_layer_tail_canonEta_eq N (eta N) omega h1
  obtain ⟨hF, hA, hB⟩ := lfgc_fp_cover s hs N n y omega hω t
  obtain ⟨-, -, -, -, h2F, h3P, -, -, -, -, -⟩ := h2
  refine ⟨?_, ?_⟩
  · rw [show F N n (y t) omega = _ from h2F n (y t), hc]
    exact aux_lfgc_fp_det_fsc_le_one s (aux_lfgc_layer_tail_canonEta N omega) n (y t) hF
  · rw [show Praw N n (y t) omega = _ from h3P n (y t), hc]
    exact lfgc_fp_det hd1 s (aux_lfgc_layer_tail_canonEta N omega) n (y t) hA hB



theorem lfgc_fp_bridge [NeZero d] (hd1 : (1 : ℝ) ≤ (d : ℝ)) (M : GMCModel d) (s eps : ℝ)
    (hs : 0 ≤ s) (eta : ℕ → BilateralField d → PotentialSample d)
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop) (omega : BilateralField d)
    (en ns : ℕ) (padRoot : Fin en) (enDepth : Fin en → ℕ) (hpad : enDepth padRoot = 1)
    (shift : Fin ns → Vec d) (m k : ℕ) (z : Vec d)
    (h1 : ∀ (i : ℕ) (y : Vec d), eta (m + k) omega i y =
      omega ((i : ℤ) - ((m + k : ℕ) : ℤ)) ((3 : ℝ) ^ (-((m + k : ℕ) : ℤ)) • y))
    (h2 : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps (eta (m + k) omega)
      (fun m' y => F (m + k) m' y omega) (fun m' y => Praw (m + k) m' y omega)
      (fun m' y => Rraw (m + k) m' y omega) (fun m' y => Draw (m + k) m' y omega)
      (fun m' y => Z (m + k) m' y omega) (fun m' y => rawGood (m + k) m' y omega))
    (hω : omega ∉ aux_lfgc_fp_cover_fpBad s (m + k) (m + 1)
      (fun t : Fin ns => (3 : ℝ) ^ (m + k) •
        (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth padRoot) • shift t))) :
    aux_lfgc_rhs_bridge_rhsFPOK en ns padRoot enDepth shift F Praw m k z omega := by
  intro t
  have h := aux_lfgc_fp_bridge_pad_tests_of_not_fpBad hd1 M s eps hs eta F Praw Rraw Draw Z rawGood omega (m + k)
    (m + 1) h1 h2 _ hω t
  rw [hpad]
  exact h

end SubdiffusiveProcess.Paper
