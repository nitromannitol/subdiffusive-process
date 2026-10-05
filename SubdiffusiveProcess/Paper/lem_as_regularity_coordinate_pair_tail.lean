module

public import SubdiffusiveProcess.Paper.lem_as_regularity_bad_score_pair
public import SubdiffusiveProcess.Paper.lem_as_regularity_error_score_pair

@[expose] public section

/-! The two original physical score coordinates are compared outside three
explicit exceptional events: retained response errors, the discarded response
tail, and the initial-layer term. This step does not estimate those events.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess _root_.SubdiffusiveProcess.Model
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Outside a relative-error exception, a nonnegative atom obeys the required one-sided comparison. -/
theorem aux_lem_as_regularity_coordinate_pair_tail_atom {x y tol : ℝ}
    (hy : 0 ≤ y) (htol : 0 ≤ tol) (htol1 : tol ≤ 1)
    (h : ¬ tol / 2 * (1 + x) < |x - y|) : x ≤ (1 + tol) * y + tol := by
  have ht : 0 ≤ tol / 2 := by linarith only [htol]
  have ht1 : tol / 2 ≤ 1 / 2 := by linarith only [htol1]
  have hc := relative_le_of_abs_le_left hy ht ht1 (le_of_not_gt h)
  convert hc using 1 ; ring

/-- A physical bad/error coordinate comparison fails only on the three specified exceptional events. -/
theorem lem_as_regularity_coordinate_pair_tail {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps : ℝ) (hs : 0 < s) (heps : 0 < eps)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ≥0∞)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (n : ℤ) (z : SpatialCoordinates d) (N N' H : ℕ)
    (hNN' : N ≤ N') (hN : n + (H : ℤ) ≤ (N : ℤ))
    (tol : ℝ) (htol : 0 ≤ tol) (htol1 : tol ≤ 1)
    (hgeom : (3 : ℝ) ^ (-(s / 2) * ((H + 1 : ℕ) : ℝ)) ≤ tol)
    (Ba Br Bt : ℝ≥0∞)
    (hAtom : (chaosSampleLaw M).toMeasure {omega | ∃ rk ∈ aux_prefix_rraw_G d H,
      tol / 2 * (1 + aux_prefix_rraw_atom M eta N (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega) <
        |aux_prefix_rraw_atom M eta N (-n - rk.1)
            (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega -
          aux_prefix_rraw_atom M eta N' (-n - rk.1)
            (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega|} ≤ Ba)
    (hRtail : (chaosSampleLaw M).toMeasure {omega | tol <
      (aux_prefix_rraw_tail M s (eta N omega) ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) H).toReal} ≤ Br)
    (hTtail : (chaosSampleLaw M).toMeasure {omega | tol <
      (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
        ((3 : ℝ) ^ N • z) (eta N omega)).toReal} ≤ Bt) :
    (chaosSampleLaw M).toMeasure {omega |
      (2 * tol) * (1 + eps ^ 2) / (eps ^ 2 - eps ^ 2 / 4) <
        Z N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega -
          Z N' ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) omega ∨
      Real.sqrt (2 * tol) + 2 * tol <
        (Draw N ((N : ℤ) - n).toNat ((3 : ℝ) ^ N • z) omega).toReal -
          (Draw N' ((N' : ℤ) - n).toNat ((3 : ℝ) ^ N' • z) omega).toReal} ≤
      Ba + Br + Bt := by
  have hfin := aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_ae_ne_top M eta hEta
    (fun K => ((K : ℤ) - n).toNat) (fun K => (3 : ℝ) ^ K • z)
  let A : Set (BilateralField d) := {omega | ∃ rk ∈ aux_prefix_rraw_G d H,
    tol / 2 * (1 + aux_prefix_rraw_atom M eta N (-n - rk.1)
        (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega) <
      |aux_prefix_rraw_atom M eta N (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega -
        aux_prefix_rraw_atom M eta N' (-n - rk.1)
          (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega|}
  let R : Set (BilateralField d) := {omega | tol <
    (aux_prefix_rraw_tail M s (eta N omega) ((N : ℤ) - n).toNat
      ((3 : ℝ) ^ N • z) H).toReal}
  let T : Set (BilateralField d) := {omega | tol <
    (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
      ((3 : ℝ) ^ N • z) (eta N omega)).toReal}
  refine (measure_mono_ae (t := (A ∪ R) ∪ T) ?_).trans
    ((measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add hAtom hRtail)) hTtail))
  filter_upwards [hEta, hPrimitive, hfin] with omega hE hP hf
  intro hbad
  by_cases ha : omega ∈ A
  · exact Or.inl (Or.inl ha)
  by_cases hr : omega ∈ R
  · exact Or.inl (Or.inr hr)
  by_cases ht : omega ∈ T
  · exact Or.inr ht
  have hretained rk (hrk : rk ∈ aux_prefix_rraw_G d H) :=
    aux_lem_as_regularity_coordinate_pair_tail_atom
      (aux_lem_as_regularity_clipped_response_pair_atom_nonneg M eta N' _ _ omega)
      htol htol1 (fun h => ha ⟨rk, hrk, h⟩)
  have hz := lem_as_regularity_bad_score_pair M s eps hs heps eta omega hE
    F Praw Rraw Draw Z rawGood hP n z N N' H hNN' hN tol htol hretained
      (le_of_not_gt hr)
  have hd := lem_as_regularity_error_score_pair M s eps hs eta omega hE
    F Praw Rraw Draw Z rawGood hP n z N N' H hNN' hN (hf N) tol htol hretained
  have ht' : (aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3 s ((N : ℤ) - n).toNat
      ((3 : ℝ) ^ N • z) (eta N omega)).toReal ≤ tol := le_of_not_gt ht
  rcases hbad with hz' | hd'
  · exfalso
    linarith only [hz, hz']
  · exfalso
    linarith only [hd, hgeom, ht', hd']

end SubdiffusiveProcess.Paper
