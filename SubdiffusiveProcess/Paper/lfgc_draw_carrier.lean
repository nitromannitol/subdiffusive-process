module

public import SubdiffusiveProcess.Paper.lfgc_draw_sure

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Drift scores are finite at every centre on the carrier

On a sample where the score families satisfy `primitive_scores` at the given potential sample,
that sample is canonical, and every next-level majorant series at integer centres is finite,
every drift score `Draw N n y` is finite, for all cutoffs, levels and real centres.
-/

open MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Every drift score is finite on a canonical sample with finite lattice majorants. -/
theorem lfgc_draw_carrier (M : GMCModel d) (s eps : ℝ) (hs0 : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (omega : BilateralField d)
    (heta : ∀ (N i : ℕ) (x : Vec d),
      eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x))
    (hprim : ∀ N, Paper.primitive_scores d M s eps (eta N omega)
      (fun m z => F N m z omega) (fun m z => Praw N m z omega)
      (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
      (fun m z => Z N m z omega) (fun m z => rawGood N m z omega))
    (hlat : ∀ (N k : ℕ) (z' : Fin d → ℤ),
      (∑' j : ℕ, Paper.aux_psf_Dmaj4 (k + 1) (fun i => (z' i : ℝ)) j (aux_lfgc_layer_tail_canonEta N omega)) ≠ ⊤) :
    ∀ (N n : ℕ) (y : SpatialCoordinates d), Draw N n y omega ≠ ⊤ := by
  intro N n y
  have hη : eta N omega = aux_lfgc_layer_tail_canonEta N omega := aux_lfgc_layer_tail_canonEta_eq N (eta N) omega (fun i x => heta N i x)
  obtain ⟨-, -, -, -, -, -, -, h5, -, -, -⟩ := hprim N
  have h := h5 n y
  rw [hη] at h
  rw [show Draw N n y omega = _ from h]
  exact aux_lfgc_draw_sure_dsc_ne_top_of_near M s hs0 n y (fun i => (round (y i) : ℝ)) (fun i => abs_sub_round (y i))
    (aux_lfgc_layer_tail_canonEta N omega) (hlat N n (fun i => round (y i)))

end Paper
