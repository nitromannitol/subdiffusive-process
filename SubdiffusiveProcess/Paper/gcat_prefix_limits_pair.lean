module

public import SubdiffusiveProcess.Paper.gcat_prefix_limits
public import SubdiffusiveProcess.Paper.affine_source_cells_env
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper
/-- Actual measurable good-cell array limits for both cutoff sequences on one
common refinement. Produces the array inputs used by the affine consumer. -/
theorem gcat_prefix_limits_pair
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Dd : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (s sigma eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (heps : eps ∈ Set.Ioo (0 : ℝ) 1) (gH cbuf : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d),
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
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
      ∃ (ZLim DLim : Fin 2 → Cells → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
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
  obtain ⟨delta0, hd0, hM⟩ := gcat_prefix_limits d hd I Pc Xc W Sf Dd Cresp hCresp
    s sigma eps hs hsigma heps gH cbuf
  refine ⟨delta0, hd0, ?_⟩
  intro M hdelta Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
    Cells _ cellLevel cellCentre N hN
  have h := hM M hdelta Rm hRm Sreg It H hH eta heta F Praw Rraw Draw Z rawGood hprim
    Cells cellLevel cellCentre
  obtain ⟨sE, hsE, ZE, DE, loE, hiE, AE, errE, ratioE, hE⟩ := h (N 0) (hN 0)
  obtain ⟨sF, hsF, ZF, DF, loF, hiF, AF, errF, ratioF, hF⟩ :=
    h (fun n => N 1 (sE n)) ((hN 1).comp hsE)
  refine ⟨fun n => sE (sF n), hsE.comp hsF,
    ![ZE, ZF], ![DE, DF], ![loE, loF], ![hiE, hiF], ![AE, AF],
    ![errE, errF], ![ratioE, ratioF], ?_⟩
  intro a c
  fin_cases a
  · change (∀ U D code, Measurable (ZE c U D code) ∧ Measurable (DE c U D code)) ∧
      (∀ U, Measurable (loE c U) ∧ Measurable (hiE c U) ∧
        ∀ i j, Measurable (fun omega => AE c U omega i j)) ∧
      Measurable (errE c ()) ∧ Measurable (ratioE c ()) ∧ _
    obtain ⟨hZm, hLm, hEm, hRm, hZ, hD, hlo, hhi, hA, herr, hrat⟩ := hE c
    refine ⟨hZm, hLm, hEm, hRm, ?_⟩
    exact ⟨fun U D code => (hZ U D code).comp hsF.tendsto_atTop,
      fun U D code => (hD U D code).comp hsF.tendsto_atTop,
      fun U => (hlo U).comp hsF.tendsto_atTop,
      fun U => (hhi U).comp hsF.tendsto_atTop,
      fun U i j => (hA U i j).comp hsF.tendsto_atTop,
      herr.comp hsF.tendsto_atTop, hrat.comp hsF.tendsto_atTop⟩
  · exact hF c

end SubdiffusiveProcess.Paper
