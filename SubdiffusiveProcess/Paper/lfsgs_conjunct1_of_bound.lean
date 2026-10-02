import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Inputs
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.Assumptions.Actions
import SubdiffusiveProcess.Main.LayerScaling
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.sum_errors_baseline_input
import SubdiffusiveProcess.Paper.primitive_scores
import SubdiffusiveProcess.Paper.cell_catalogue
import SubdiffusiveProcess.Paper.good_event
import SubdiffusiveProcess.Paper.lem_finite_good_cell
import SubdiffusiveProcess.Paper.finite_interval_packing
import SubdiffusiveProcess.Paper.paper_responses_bank
import SubdiffusiveProcess.Paper.finite_response_ramp
import SubdiffusiveProcess.Paper.lem_rare_tests
import SubdiffusiveProcess.Paper.lem_finite_trace_tests
import SubdiffusiveProcess.Paper.lem_local_normalizations
import SubdiffusiveProcess.Paper.inputs_EM_witness
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.rem_bank
import SubdiffusiveProcess.Paper.prop_16
import SubdiffusiveProcess.Paper.lfsgs_trace_moments
import SubdiffusiveProcess.Paper.aux_test_prop16_rd_band
import SubdiffusiveProcess.Paper.classical_cube_fractional_interpolation
import SubdiffusiveProcess.Paper.classical_cube_fractional_compact_embedding
import SubdiffusiveProcess.FiniteStopping.CellRegularity
import SubdiffusiveProcess.FiniteStopping.CutoffRestrictions
import SubdiffusiveProcess.FiniteStopping.ObservationStages
import SubdiffusiveProcess.FiniteStopping.ObservationTree

/-! This module establishes conjunct1 of bound for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

variable {d : ℕ}

open Classical in
/-- conjunct1 of bound in the finite stopping construction. -/
theorem lfsgs_conjunct1_of_bound
    (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H1 : ℕ) (hH1 : 0 < H1) (z : SpatialCoordinates d) (j : ℤ) (N M : ℕ) (hNpos : 0 < N)
    (hj0 : 0 ≤ ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j)
    (hq0 : 0 ≤ (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) +
      SubdiffusiveProcess.FiniteStopping.rootQ H1 j)
    (theta thetaUsed : ℝ) (hthetaUsed : thetaUsed ≤ theta)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
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
      have : (((H1 : ℤ) * (n' : ℤ) - jroot : ℤ) : ℝ) < (N : ℝ) := by nlinarith only [hd, hH1, hNpos, hj0, hq0, hthetaUsed, hpad, hjroot, hGood, hcastle, hP, hNposR, hhi, hNposR]
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
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
        exact (hPiff i).mpr hi)
      (fun a _ b _ h => h)
  · gcongr

end Paper
