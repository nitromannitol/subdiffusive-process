module

public import SubdiffusiveProcess.Paper.lfgc_p1_main

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Interval witnesses for the failure of the prefix conjunct (main statement)

Constants are chosen in the order: band rates and widths (lem_band), truncation slope, moment
order `p`, truncation constants, offset `L0` and error scale, large-range threshold `K`, base
probability `M'`, and finally the disorder threshold.
-/

open MeasureTheory Filter Topology SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem lfgc_p1_cover {Cp c δ δs E : ℝ} (hCp : 0 < Cp) (hc : 0 < c) (hδ : 0 < δ) (hE : 0 < E)
    (hδs : δs = (E / Cp) ^ (1 / c)) (h : δ ≤ δs) : Cp * δ ^ c ≤ E := by
  have h1 : δ ^ c ≤ δs ^ c := Real.rpow_le_rpow hδ.le h hc.le
  rw [hδs, ← Real.rpow_mul (by positivity), one_div_mul_cancel hc.ne', Real.rpow_one] at h1
  rw [le_div_iff₀ hCp] at h1
  linarith

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_p1_cover_rpow_div_half (a' : ℝ) :
    (3 : ℝ) ^ (-a') / (3 : ℝ) ^ (-(a' / 2)) = (3 : ℝ) ^ (-(a' / 2)) := by
  rw [← Real.rpow_sub (by norm_num)]; ring_nf

end Paper
