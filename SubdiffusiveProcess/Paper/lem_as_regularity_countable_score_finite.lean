module

public import SubdiffusiveProcess.Paper.lem_prefix_limit_actual_coordinate_cauchy

@[expose] public section

/-! Original extended-valued error scores are finite simultaneously on every
countable family of native coordinates. The result transports the established
gradient-tail bound through eta; it makes no uncountable intersection claim.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace Paper

/-- A countable family of original error scores is almost surely finite at every cutoff. -/
theorem lem_as_regularity_countable_score_finite {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s eps : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F P R D : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (good : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => P N m y omega)
        (fun m y => R N m y omega) (fun m y => D N m y omega)
        (fun m y => Z N m y omega) (fun m y => good N m y omega))
    (ι : Type*) [Countable ι] (k : ι → ℕ → ℕ) (w : ι → ℕ → Vec d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (i : ι) (N : ℕ),
      D N (k i N) (w i N) omega ≠ ⊤ := by
  rw [ae_all_iff]
  intro i
  filter_upwards [hPrimitive,
    aux_lem_prefix_limit_actual_coordinate_cauchy_Dt4_ae_ne_top M eta hEta (k i) (w i)]
      with omega hPS h4
  intro N
  rw [aux_lem_prefix_limit_actual_coordinate_cauchy_Dsc_eq_sum M s eps (eta N omega)
    _ _ _ _ _ _ (hPS N)]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨aux_lem_prefix_limit_actual_coordinate_cauchy_Dt1_ne_top M s hs _ _ _,
      aux_lem_prefix_limit_actual_coordinate_cauchy_Dt2_ne_top s _ _ _⟩,
      aux_lem_prefix_limit_actual_coordinate_cauchy_Dt3_ne_top s _ _ _⟩, h4 N⟩

end Paper
