module

public import SubdiffusiveProcess.Paper.primitive_scores_finite
public import SubdiffusiveProcess.Lane4.GoodCellCatalogue
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldTransport

@[expose] public section

open Filter MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- The actual accumulated-error scores are finite on every countable observation
catalogue. This supplies the finite-score guard without a new disorder restriction. -/
theorem gcat_finite_scores
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s eps : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (Cells : Type) [Countable Cells] (cellLevel : Cells → ℕ)
    (cellCentre : Cells → SpatialCoordinates d) (gH : ℕ) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (c : Cells) (N : ℕ) (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ)
        (code : (Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) (j : ℤ),
        Draw N ((N : ℤ) - j).toNat
          (((3 : ℝ) ^ N) • gcat_obsCentre gH (cellLevel c) (cellCentre c) U D code) omega ≠ ⊤ := by
  simp only [ae_all_iff]
  intro c N U D code j
  let k := ((N : ℤ) - j).toNat
  let w := ((3 : ℝ) ^ N) • gcat_obsCentre gH (cellLevel c) (cellCentre c) U D code
  have hnative := aux_psf_Dmaj4_tsum_ae M k w
  rw [← prefix_eta_law M eta hEta N] at hnative
  filter_upwards [ae_of_ae_map (prefix_eta_aemeasurable M eta hEta N) hnative, hPrimitive]
    with omega hfin hp
  obtain ⟨_, _, _, _, _, _, _, hD, _⟩ := hp N
  change Draw N k w omega ≠ ⊤
  have heq := hD k w
  dsimp only at heq
  rw [heq]
  exact aux_psf_Dsc_ne_top M s hs k w (eta N omega) hfin

end Paper
