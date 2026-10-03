module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Lane3.Subdivision
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.Lane2.CellDirichlet
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Lane4.Inputs
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Main.LayerScaling
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.cell_catalogue
public import SubdiffusiveProcess.Paper.good_event
public import SubdiffusiveProcess.Paper.paper_responses_bank
public import SubdiffusiveProcess.Paper.finite_response_ramp
public import SubdiffusiveProcess.Paper.lem_rare_tests
public import SubdiffusiveProcess.Paper.lem_finite_trace_tests
public import SubdiffusiveProcess.Paper.inputs_EM_witness
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.rem_bank
public import SubdiffusiveProcess.Paper.prop_16
public import SubdiffusiveProcess.Paper.lfsgs_trace_moments
public import SubdiffusiveProcess.Paper.aux_test_prop16_rd_band
public import SubdiffusiveProcess.Paper.classical_cube_fractional_interpolation
public import SubdiffusiveProcess.Paper.classical_cube_fractional_compact_embedding
public import SubdiffusiveProcess.FiniteStopping.BilateralSamples
public import SubdiffusiveProcess.FiniteStopping.CellRegularity
public import SubdiffusiveProcess.FiniteStopping.ZeroDisorderScores

@[expose] public section

/-! This module establishes hRegWitness of arbitrary Rm for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

variable {d : ℕ}

/-- primitive scores exists in the finite stopping construction. -/
theorem aux_lfsgs_hRegWitness_of_arbitrary_Rm_primitive_scores_exists
    [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sigma eps : ℝ)
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
      (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
      (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
      (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop),
      (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N i x,
        eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x)) ∧
      (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N,
        primitive_scores d model sigma eps (eta N omega)
          (fun m z => F N m z omega) (fun m z => Praw N m z omega)
          (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
          (fun m z => Z N m z omega) (fun m z => rawGood N m z omega)) := by
  obtain ⟨eta, heta⟩ := SubdiffusiveProcess.FiniteStopping.ps_eta_exists model

  let normOn : Set (SubdiffusiveProcess.CoarseGrainingVocab.Vec d) → (SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ) → ENNReal :=
    fun W f => sSup {v : ENNReal | ∃ x : SubdiffusiveProcess.CoarseGrainingVocab.Vec d, x ∈ W ∧ v = ENNReal.ofReal |f x|}
  let J : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ → SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ENNReal :=
    fun om n z => sSup {v : ENNReal | ∃ e : SubdiffusiveProcess.CoarseGrainingVocab.Vec d,
      Homogenization.vecNormSq e = 1 ∧
      v = ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.section6Response model n n om z e)}
  let eramp : ℝ → ℝ → ENNReal → ℝ :=
    fun a b X => (min (1 : ENNReal) ((X - ENNReal.ofReal a) / ENNReal.ofReal (b - a))).toReal
  let F : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal := fun N m z om =>
    sSup {v : ENNReal | ∃ j : ℕ,
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(sigma * (j : ℝ) / 8))) *
        ∑ i ∈ Finset.Icc (m - j) (m + j),
          normOn (SubdiffusiveProcess.CoarseGrainingVocab.translatedCube d (m + 1 + j) z)
            (fun x => |eta N om i x| + (3 : ℝ) ^ (i : ℝ) *
              Homogenization.euclideanNorm (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (eta N om i) x))}
  let Praw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal := fun N m z om =>
    sSup {v : ENNReal | ∃ j : ℕ,
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(sigma * (j : ℝ) / 8))) *
        sSup {w : ENNReal | ∃ x, x ∈ SubdiffusiveProcess.CoarseGrainingVocab.translatedCube d (m + 1 + j) z ∧
          w = (∏ i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal (Real.exp |eta N om i x|)) +
              sSup {u : ENNReal | ∃ K : ℕ,
                u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
                  ENNReal.ofReal (Real.exp (4 * |eta N om i x - eta N om i z|))}}}
  let Rraw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal := fun N m z om =>
    sSup {v : ENNReal | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧ ∃ x,
      SubdiffusiveProcess.CoarseGrainingVocab.OnTriadicGrid n (x - z) ∧
      x - z ∈ SubdiffusiveProcess.CoarseGrainingVocab.cube d j \ SubdiffusiveProcess.CoarseGrainingVocab.cube d (j - 1) ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(sigma * ((m : ℝ) - (n : ℝ)) / 8))) * J (eta N om) n x}
  let Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal := fun N k z om =>
    sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x,
        SubdiffusiveProcess.CoarseGrainingVocab.OnTriadicGrid l (x - z) ∧
        x - z ∈ SubdiffusiveProcess.CoarseGrainingVocab.cube d j \ SubdiffusiveProcess.CoarseGrainingVocab.cube d (j - 1) ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(sigma / 2) * ((k : ℝ) - (l : ℝ)))) *
          (min (J (eta N om) l x) 1) ^ (1 / 2 : ℝ)} +
      sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(sigma / 8) * ((k : ℝ) - (j : ℝ)))) *
          normOn (SubdiffusiveProcess.CoarseGrainingVocab.translatedCube d k z)
            (SubdiffusiveProcess.CoarseGrainingVocab.shellBlock k j (eta N om))} +
      ENNReal.ofReal ((3 : ℝ) ^ (-(sigma / 8) * (k : ℝ))) *
        normOn (SubdiffusiveProcess.CoarseGrainingVocab.translatedCube d k z) (eta N om 0) +
      ∑' j : ℕ, if k ≤ j then
        ENNReal.ofReal ((3 : ℝ) ^ k) *
          normOn (SubdiffusiveProcess.CoarseGrainingVocab.translatedCube d k z)
            (fun x => Homogenization.euclideanNorm (SubdiffusiveProcess.CoarseGrainingVocab.shellGradient (eta N om j) x))
        else 0
  let Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ := fun N m z om =>
    eramp (eps / 2) eps (F N m z om) + eramp 6 12 (Praw N m z om) +
      eramp (eps ^ 2 / 4) (eps ^ 2) (Rraw N m z om)
  let rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop := fun N m z om =>
    F N m z om ≤ ENNReal.ofReal eps ∧ Praw N m z om ≤ 6 ∧ Rraw N m z om ≤ ENNReal.ofReal (eps ^ 2)
  have heramp : ∀ a b X, 0 ≤ eramp a b X ∧ eramp a b X ≤ 1 := by
    intro a b X
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have h1 : min (1 : ENNReal) ((X - ENNReal.ofReal a) / ENNReal.ofReal (b - a)) ≤ 1 :=
      min_le_left _ _
    simpa only [ge_iff_le, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top h1
  refine ⟨eta, F, Praw, Rraw, Draw, Z, rawGood, heta, Filter.Eventually.of_forall ?_⟩
  intro om N
  refine ⟨hsigma.1, hsigma.2.le, heps.1, heps.2, fun m z => rfl, fun m z => rfl,
    fun m z => rfl, fun m z => rfl, fun m z => Iff.rfl, fun m z => ⟨rfl, ?_, ?_⟩, ?_⟩
  · have h1 := heramp (eps / 2) eps (F N m z om)
    have h2 := heramp 6 12 (Praw N m z om)
    have h3 := heramp (eps ^ 2 / 4) (eps ^ 2) (Rraw N m z om)
    show 0 ≤ eramp (eps / 2) eps (F N m z om) + eramp 6 12 (Praw N m z om) +
      eramp (eps ^ 2 / 4) (eps ^ 2) (Rraw N m z om)
    linarith only [hsigma, heps, heta, heramp, h1, h2, h3, h1.left, h2.left, h3.left]
  · have h1 := heramp (eps / 2) eps (F N m z om)
    have h2 := heramp 6 12 (Praw N m z om)
    have h3 := heramp (eps ^ 2 / 4) (eps ^ 2) (Rraw N m z om)
    show eramp (eps / 2) eps (F N m z om) + eramp 6 12 (Praw N m z om) +
      eramp (eps ^ 2 / 4) (eps ^ 2) (Rraw N m z om) ≤ 3
    linarith only [hsigma, heps, heta, heramp, h1, h2, h3, h1.right, h2.right, h3.right]
  · rintro ⟨htau, hahom, hz⟩ m z
    have hJ := fun n x e he =>
      SubdiffusiveProcess.FiniteStopping.ps_section6Response_nonpos model n (eta N om) htau (hahom n) hz x e he
    exact ⟨SubdiffusiveProcess.FiniteStopping.ps_F_zero sigma (eta N om) hz m z,
      SubdiffusiveProcess.FiniteStopping.ps_P_two sigma hsigma.1 (eta N om) hz m z,
      SubdiffusiveProcess.FiniteStopping.ps_R_zero model sigma (eta N om) hJ m z,
      SubdiffusiveProcess.FiniteStopping.ps_D_zero model sigma (eta N om) hJ hz m z⟩



theorem lfsgs_primitive_scores_exists
    [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sigma eps : ℝ)
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
      (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
      (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
      (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop),
      (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N i x,
        eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x)) ∧
      (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ N,
        primitive_scores d model sigma eps (eta N omega)
          (fun m z => F N m z omega) (fun m z => Praw N m z omega)
          (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
          (fun m z => Z N m z omega) (fun m z => rawGood N m z omega)) :=
  aux_lfsgs_hRegWitness_of_arbitrary_Rm_primitive_scores_exists model sigma eps hsigma heps

end Paper
