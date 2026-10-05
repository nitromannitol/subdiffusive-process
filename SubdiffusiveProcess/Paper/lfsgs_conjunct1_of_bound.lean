module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
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
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.cell_catalogue
public import SubdiffusiveProcess.Paper.good_event
public import SubdiffusiveProcess.Paper.lem_finite_good_cell
public import SubdiffusiveProcess.Paper.finite_interval_packing
public import SubdiffusiveProcess.Paper.paper_responses_bank
public import SubdiffusiveProcess.Paper.finite_response_ramp
public import SubdiffusiveProcess.Paper.lem_rare_tests
public import SubdiffusiveProcess.Paper.lem_finite_trace_tests
public import SubdiffusiveProcess.Paper.lem_local_normalizations
public import SubdiffusiveProcess.Paper.inputs_EM_witness
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.rem_bank
public import SubdiffusiveProcess.Paper.prop_16
public import SubdiffusiveProcess.Paper.lfsgs_trace_moments
public import SubdiffusiveProcess.Paper.aux_test_prop16_rd_band
public import SubdiffusiveProcess.Paper.classical_cube_fractional_interpolation
public import SubdiffusiveProcess.Paper.classical_cube_fractional_compact_embedding
public import SubdiffusiveProcess.FiniteStopping.CellRegularity
public import SubdiffusiveProcess.FiniteStopping.CutoffRestrictions
public import SubdiffusiveProcess.FiniteStopping.ObservationStages
public import SubdiffusiveProcess.FiniteStopping.ObservationTree

@[expose] public section

/-! This module establishes conjunct1 of bound for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

open Classical in
/-- conjunct1 of bound in the finite stopping construction. -/
theorem lfsgs_conjunct1_of_bound
    (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H1 : ℕ) (hH1 : 0 < H1) (z : SpatialCoordinates d) (j : ℤ) (N M : ℕ) (hNpos : 0 < N)
    (hj0 : 0 ≤ ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j)
    (hq0 : 0 ≤ (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) +
      SubdiffusiveProcess.FiniteStopping.rootQ H1 j)
    (theta thetaUsed : ℝ) (hthetaUsed : thetaUsed ≤ theta)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (alpha pad Cfin : ℝ) (hpad : 1 < pad)
    (TraceClose : ℕ → ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (omega : BilateralField d)
    (hbound : ∀ (v : Fin (SubdiffusiveProcess.FiniteStopping.rootRho H1 j) → OddGridIndex d 1)
        (w : ℕ → OddGridIndex d (subdivisionHalfWidth H1)),
      let k : ℕ → ℤ := fun n => (H1 : ℤ) * (n : ℤ) -
        (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j
      let zc : ℕ → SpatialCoordinates d := fun n =>
        descendantCenter (subdivisionHalfWidth H1)
          (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z v)
          ((3 : ℝ) ^ ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j)) n
          (fun i : Fin n => w i)
      (Nat.card {n : ℕ // (1 / 4 : ℝ) * (N : ℝ) ≤ (k n : ℝ) ∧
        (k n : ℝ) ≤ (3 / 4 : ℝ) * (N : ℝ) ∧
        ¬(SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad N
            (k n).toNat (zc n) omega ∧
          SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad M
            (k n).toNat (zc n) omega ∧
          TraceClose N M (k n).toNat (zc n) omega)} : ℝ) ≤
        thetaUsed * (N : ℝ) / (H1 : ℝ)) :
    ∃ Good : (Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) →
        (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Prop,
      (∀ (w0 : Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1)
        (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
        Good w0 n w ↔
          SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad N
            (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + n))
            (descendantCenter (subdivisionHalfWidth H1)
              (descendantCenter 1 z ((3 : ℝ) ^ j)
                (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
              (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j)
                ((3 : ℝ) ^ j)) n w) omega ∧
          SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad M
            (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + n))
            (descendantCenter (subdivisionHalfWidth H1)
              (descendantCenter 1 z ((3 : ℝ) ^ j)
                (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
              (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j)
                ((3 : ℝ) ^ j)) n w) omega ∧
          TraceClose N M
            (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + n))
            (descendantCenter (subdivisionHalfWidth H1)
              (descendantCenter 1 z ((3 : ℝ) ^ j)
                (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
              (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j)
                ((3 : ℝ) ^ j)) n w) omega) ∧
      ∀ (w0 : Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1)
        (w : Fin (SubdiffusiveProcess.FiniteStopping.obsB H1 N) →
          OddGridIndex d (subdivisionHalfWidth H1)),
        ((((Finset.univ : Finset (Fin (SubdiffusiveProcess.FiniteStopping.obsB H1 N))).filter
          fun i : Fin (SubdiffusiveProcess.FiniteStopping.obsB H1 N) => ¬ Good w0 (i.val + 1)
            (SubdiffusiveProcess.FiniteStopping.wordPrefix w (i.val + 1) i.isLt)).card : ℕ) : ℝ) ≤
          theta * (N : ℝ) / (H1 : ℝ) := by
  set jroot : ℤ := (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j with hjroot
  set Good : (Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1) →
      (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Prop :=
    fun w0 n w =>
      SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad N
        (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + n))
        (descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
          (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) n w)
        omega ∧
      SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad M
        (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + n))
        (descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
          (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) n w)
        omega ∧
      TraceClose N M
        (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + n))
        (descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
          (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j)) n w)
        omega with hGood
  refine ⟨Good, ?_, ?_⟩
  · intro w0 n w
    rw [hGood]
  intro w0 w
  have hcastle : SubdiffusiveProcess.FiniteStopping.rootRho H1 j ≤
      SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j := by
    rw [SubdiffusiveProcess.FiniteStopping.t0_split H1 N hH1 j hj0 hq0]; omega
  obtain ⟨W, hWagree, hWmatch⟩ :=
    SubdiffusiveProcess.FiniteStopping.cell2_eq_extended_fip_cell_all H1 hH1 j z N
      (SubdiffusiveProcess.FiniteStopping.obsB H1 N) hj0 hq0
      w0 w (fun _ => (0 : Fin (2 * subdivisionHalfWidth H1 + 1)))
  have hbnd := hbound (fun i => w0 (Fin.castLE hcastle i)) W
  set P : ℕ → Prop := fun n' =>
    ¬(SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad N
        (((H1 : ℤ) * (n' : ℤ) - jroot).toNat)
        (descendantCenter (subdivisionHalfWidth H1)
          (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z (fun i => w0 (Fin.castLE hcastle i)))
          ((3 : ℝ) ^ jroot) n' (fun i : Fin n' => W i)) omega ∧
      SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad M
        (((H1 : ℤ) * (n' : ℤ) - jroot).toNat)
        (descendantCenter (subdivisionHalfWidth H1)
          (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z (fun i => w0 (Fin.castLE hcastle i)))
          ((3 : ℝ) ^ jroot) n' (fun i : Fin n' => W i)) omega ∧
      TraceClose N M
        (((H1 : ℤ) * (n' : ℤ) - jroot).toNat)
        (descendantCenter (subdivisionHalfWidth H1)
          (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z (fun i => w0 (Fin.castLE hcastle i)))
          ((3 : ℝ) ^ jroot) n' (fun i : Fin n' => W i)) omega) with hP
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ n' : ℕ, (1 / 4 : ℝ) * (N : ℝ) ≤
      (((H1 : ℤ) * (n' : ℤ) - jroot : ℤ) : ℝ) →
      (((H1 : ℤ) * (n' : ℤ) - jroot : ℤ) : ℝ) ≤ (3 / 4 : ℝ) * (N : ℝ) → n' ≤ K := by
    refine ⟨N / H1 + jroot.natAbs + 1, fun n' _ hhi => ?_⟩
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hlt : (H1 : ℤ) * (n' : ℤ) - jroot < (N : ℤ) := by
      have : (((H1 : ℤ) * (n' : ℤ) - jroot : ℤ) : ℝ) < (N : ℝ) := by nlinarith only [ hH1, hNpos, hj0, hq0, hthetaUsed, hpad, hjroot, hGood, hcastle, hP, hNposR, hhi, hNposR]
      exact_mod_cast this
    have := aux_finite_interval_packing_depth_bound H1 N hH1 jroot n' hlt
    omega
  have hcb := SubdiffusiveProcess.FiniteStopping.card_bridge H1
    (SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j) (SubdiffusiveProcess.FiniteStopping.obsB H1 N)
    N (1 / 4) (3 / 4) jroot K
    P hK (SubdiffusiveProcess.FiniteStopping.card_bridge_window H1 hH1 j N hq0)
  have hPiff : ∀ i : Fin (SubdiffusiveProcess.FiniteStopping.obsB H1 N),
      P ((SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j) + i.val + 1) ↔
      ¬ Good w0 (i.val + 1) (SubdiffusiveProcess.FiniteStopping.wordPrefix w (i.val + 1) i.isLt) := by
    intro i
    rw [hP, hGood]
    dsimp only
    rw [hjroot,
      show (SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j + i.val + 1 : ℕ) =
        SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j + (i.val + 1) from by omega,
      ← hWmatch i.val i.isLt,
      SubdiffusiveProcess.FiniteStopping.k_toNat_eq H1 N j hq0 (i.val + 1)]
  refine le_trans ?_ (le_trans (hcb.trans hbnd) ?_)
  · exact_mod_cast Finset.card_le_card_of_injOn id
      (fun i hi => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq] at hi ⊢
        exact (hPiff i).mpr hi)
      (fun a _ b _ h => h)
  · gcongr

end SubdiffusiveProcess.Paper
