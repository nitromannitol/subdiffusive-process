import SubdiffusiveProcess.Paper.reference_coefficients_common
import SubdiffusiveProcess.Paper.gcat_prefix_limits_pair
open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- The actual deterministic reference limits and measurable good-cell array
limits of both candidates are produced on the same common refinement. -/
theorem gcat_prefix_reference_pair
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Pc : Paper.in_poincare d hd I) (Xc : Paper.in_extension d hd I)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (Dd : Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (gH cbuf : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
            omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          primitive_scores d M s eps (eta N omega)
            (fun m y => F N m y omega) (fun m y => Praw N m y omega)
            (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
            (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) →
      ∀ (Cells : Type) [Countable Cells] (cellLevel : Cells → ℕ)
        (cellCentre : Cells → SpatialCoordinates d)
        (N : Fin 2 → ℕ → ℕ), (∀ a, StrictMono (N a)) →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∃ eRef : Fin 2 → ℕ → ℝ,
      (∀ a k, 0 < eRef a k) ∧
      (∀ a (k : ℕ), Tendsto (fun n =>
        (let kappa : ℕ → ℝ := fun J =>
          Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
         kappa (((N a (psi n) : ℤ) - (k : ℤ)).toNat) / kappa (N a (psi n))))
        atTop (𝓝 (eRef a k))) ∧
      ∃ (ZLim DLim : Fin 2 → Cells → ∀ (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loLim hiLim : Fin 2 → Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AELim : Fin 2 → Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Fin 2 → Cells → Unit → BilateralField d → ℝ),
      ∀ a c,
        (∀ U D code, Measurable (ZLim a c U D code) ∧ Measurable (DLim a c U D code)) ∧
        (∀ U, Measurable (loLim a c U) ∧ Measurable (hiLim a c U) ∧
          ∀ i j, Measurable (fun omega => AELim a c U omega i j)) ∧
        Measurable (errLim a c ()) ∧ Measurable (ratioLim a c ()) ∧
        aux_affine_source_cells_env_cellArrays I M H s sigma gH cbuf Z Draw
          (fun n => N a (psi n)) (cellLevel c) (cellCentre c)
          (ZLim a c) (DLim a c) (loLim a c) (hiLim a c) (AELim a c)
          (errLim a c) (ratioLim a c) := by
  obtain ⟨delta0, hd0, hM⟩ := gcat_prefix_limits_pair d hd I Pc Xc W Sf Dd Cresp hCresp
    s sigma eps hs hsigma heps gH cbuf
  refine ⟨delta0, hd0, ?_⟩
  intro M hdelta Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
    Cells _ cellLevel cellCentre N hN
  obtain ⟨s0, hs0, eE, eF, he, hE, hF⟩ := reference_coefficients_common d M
    (N 0) (N 1) (hN 0) (hN 1)
  obtain ⟨s1, hs1, ZL, DL, loL, hiL, AL, errL, ratL, harr⟩ :=
    hM M hdelta Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
      Cells cellLevel cellCentre (fun a n => N a (s0 n)) (fun a => (hN a).comp hs0)
  refine ⟨fun n => s0 (s1 n), hs0.comp hs1, ![eE, eF], ?_, ?_,
    ZL, DL, loL, hiL, AL, errL, ratL, harr⟩
  · intro a k
    fin_cases a
    · exact (he k).1
    · exact (he k).2
  · intro a k
    fin_cases a
    · exact (hE k).comp hs1.tendsto_atTop
    · exact (hF k).comp hs1.tendsto_atTop
end Paper
