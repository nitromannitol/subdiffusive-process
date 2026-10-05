module

public import SubdiffusiveProcess.Paper.lem_as_regularity_atom_pair_tail
public import SubdiffusiveProcess.Probability.FiniteEventComparison

@[expose] public section

/-! A finite bank of physical primitive atoms has one future-cutoff threshold
and a tail bounded by its cardinality times the worst remaining-cutoff tail.
This statement leaves the geometric catalogue and its cardinality explicit.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Any finite physical response bank admits a common quantitative two-cutoff comparison. -/
theorem lem_as_regularity_finite_atom_bank
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ eps : ℝ, 0 < eps → ∃ C c : ℝ, ∃ N0 : ℕ, 0 < C ∧ 0 < c ∧
        ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (k : ℕ) (l : Fin k → ℤ) (y : Fin k → SpatialCoordinates d) (N K : ℕ),
          N0 ≤ K → (∀ i, 0 ≤ l i + (N : ℤ)) →
          (∀ i, K ≤ (l i + (N : ℤ)).toNat) →
          ∃ M0 : ℕ, N ≤ M0 ∧ ∀ N' : ℕ, M0 ≤ N' →
            (chaosSampleLaw M).toMeasure {omega | ∃ i : Fin k,
              eps * (1 + aux_prefix_rraw_atom M eta N (l i) (y i) omega) <
                |aux_prefix_rraw_atom M eta N (l i) (y i) omega -
                  aux_prefix_rraw_atom M eta N' (l i) (y i) omega|} ≤
              ENNReal.ofReal ((k : ℝ) * (C * (3 : ℝ) ^ (-c * (K : ℝ)))) := by
  obtain ⟨delta0, hdelta0, hroot⟩ := lem_as_regularity_atom_pair_tail
    d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hH hdelta eps heps
  obtain ⟨C, c, N0, hC, hc, htail⟩ := hroot M Rm Sreg It H hH hdelta eps heps
  refine ⟨C, c, N0, hC, hc, ?_⟩
  intro eta hEta k l y N K hK0 hN hK
  have hbank := finite_event_comparison_geometric (chaosSampleLaw M).toMeasure
    (fun i N' => {omega |
      eps * (1 + aux_prefix_rraw_atom M eta N (l i) (y i) omega) <
        |aux_prefix_rraw_atom M eta N (l i) (y i) omega -
          aux_prefix_rraw_atom M eta N' (l i) (y i) omega|})
    N K (fun i => (l i + (N : ℤ)).toNat) C c hC.le hc.le hK
    (fun i => htail eta hEta (l i) (y i) N (hN i) (hK0.trans (hK i)))
  simpa only [Fintype.card_fin] using! hbank

end SubdiffusiveProcess.Paper
