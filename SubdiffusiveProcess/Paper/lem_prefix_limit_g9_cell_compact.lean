module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Homogenization.Book.Ch02.Matrices
public import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationError
public import SubdiffusiveProcess.Paper.g9_cell_tag_combos
public import SubdiffusiveProcess.Paper.g9_origin_entry_package

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The compactness statement for the prefix-limit cell responses. -/
theorem lem_prefix_limit_g9_cell_compact {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I) (_Perturbation : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Sobolev : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      let F : ℕ → BilateralField d → Homogenization.Book.Ch02.TriadicCoeffFamily d :=
        fun K omega => I.chart 0 1 one_pos (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1
      let cVal : Homogenization.TriadicCube d → ℕ → BilateralField d →
          Fin 3 ⊕ (Bool × (Fin d × Fin d)) → ℝ :=
        fun R K omega tag =>
          Sum.elim
            (fun j => if j = 0 then Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R (F K omega)
              else if j = 1 then Homogenization.Book.Ch02.coarseBMatrixNorm R (F K omega)
              else (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R (F K omega) 1).toReal)
            (fun ab => if ab.1 then
                Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
                  ((F K omega).coeffOn R) ab.2.1 ab.2.2
              else Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
                  ((F K omega).coeffOn R) ab.2.1 ab.2.2) tag
      ∀ R : Homogenization.TriadicCube d,
        Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∀ tag : Fin 3 ⊕ (Bool × (Fin d × Fin d)),
        ∃ hmem : ∀ K, MemLp (cVal R K · tag) 1 (chaosSampleLaw M).toMeasure,
          IsCompact (closure (Set.range (fun K => (hmem K).toLp (cVal R K · tag)))) := by
  have : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩
  obtain ⟨delta0, hdelta0, hall⟩ :=
    g9_cell_tag_combos hd I _Poincare _Extension _Perturbation _Sobolev D Cresp hCresp
      (g9_origin_entry_package hd I _Poincare _Extension _Perturbation _Sobolev D Cresp hCresp)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hM Rm hRm Sreg _It H hH F cVal R hR tag
  obtain ⟨hentry, hB, hSigma, hProbe⟩ := hall M hM Rm hRm Sreg _It H hH R hR
  cases tag with
  | inl j =>
    fin_cases j
    · exact hSigma
    · exact hB
    · exact hProbe
  | inr ab =>
    exact hentry ab.1 ab.2.1 ab.2.2

end SubdiffusiveProcess.Paper
