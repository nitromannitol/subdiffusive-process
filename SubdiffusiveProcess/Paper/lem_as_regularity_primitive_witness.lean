module

public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Main.PrimitiveScores
public import SubdiffusiveProcess.FiniteStopping.BilateralSamples

@[expose] public section

/-! Concrete witnesses for the pinned original primitive-score arrays.
The existing potential-sample lift supplies the relabeling; the canonical
extended-valued definitions satisfy every clause, including the conditional
zero-disorder baseline. No moment or finiteness assertion is made here.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- The canonical extended-valued definitions satisfy the complete primitive-score specification. -/
theorem aux_lem_as_regularity_primitive_witness_exact {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s eps : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    primitive_scores d M s eps omega
      (primitiveFieldScore s omega) (primitiveProductScore s omega)
      (primitiveResponseScore M s omega) (primitiveErrorScore M s omega)
      (primitiveBadScore M s eps omega) (primitiveGoodEvent M s eps omega) := by
  refine ⟨hs.1, hs.2, heps.1, heps.2,
    (fun _ _ => rfl), (fun _ _ => rfl), (fun _ _ => rfl), (fun _ _ => rfl),
    (fun _ _ => Iff.rfl), (fun m z => ⟨rfl, primitiveBadScore_bounds M s eps omega m z⟩), ?_⟩
  rintro ⟨htau, hahom, hz⟩ m z
  exact primitiveScores_zero M s hs.1 omega htau hahom hz m z

/-- One pinned potential relabeling carries concrete primitive-score arrays on the bilateral law. -/
theorem lem_as_regularity_primitive_witness {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s eps : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
      (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ≥0∞)
      (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
      (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop),
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
          omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        primitive_scores d M s eps (eta N omega)
          (fun m y => F N m y omega) (fun m y => Praw N m y omega)
          (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
          (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) := by
  obtain ⟨eta, hEta⟩ := FiniteStopping.ps_eta_exists M
  refine ⟨eta,
    (fun N m y omega => primitiveFieldScore s (eta N omega) m y),
    (fun N m y omega => primitiveProductScore s (eta N omega) m y),
    (fun N m y omega => primitiveResponseScore M s (eta N omega) m y),
    (fun N m y omega => primitiveErrorScore M s (eta N omega) m y),
    (fun N m y omega => primitiveBadScore M s eps (eta N omega) m y),
    (fun N m y omega => primitiveGoodEvent M s eps (eta N omega) m y), hEta, ?_⟩
  exact Filter.Eventually.of_forall (fun omega N =>
    aux_lem_as_regularity_primitive_witness_exact M s eps hs heps (eta N omega))

end Paper
