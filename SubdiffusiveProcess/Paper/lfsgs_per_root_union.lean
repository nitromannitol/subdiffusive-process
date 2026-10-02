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
import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison
import SubdiffusiveProcess.FiniteStopping.CellRegularity
import SubdiffusiveProcess.FiniteStopping.ObservationTree

/-! This module establishes per root union for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

variable {d : ℕ}

/-- per root union in the finite stopping construction. -/
theorem lfsgs_per_root_union
    (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (a b theta alpha beta : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (htheta : 0 < theta) (hthetab : theta < b - a)
    (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1)
    (H1 : ℕ) (hH1 : 0 < H1)
    (Cfin Aext pad B : ℝ) (hCfin : 0 < Cfin) (hAext : 0 < Aext)
    (hpad : 1 < pad) (hpadL : pad < (3 : ℝ) ^ H1)
    (hB : B > 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / theta)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization model H)
    (z : SpatialCoordinates d) (j : ℤ)
    (hRegWitness : ∀ (N k : ℕ) (zc : SpatialCoordinates d), k ≤ N →
      ∃ W : ℕ+ → Set (BilateralField d),
        (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
          ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).restrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
              C(SpatialCoordinates d, ℝ)))] (W h)) ∧
        (∀ h : ℕ+, (chaosSampleLaw model).toMeasure (W h) ≤
          ENNReal.ofReal (Real.exp (-B * (h : ℝ)))) ∧
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
          ¬SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad N k zc omega →
            omega ∈ ⋃ h : ℕ+, W h))
    (eta : ℝ) (heta : 0 < eta) (m0 : ℕ)
    (TraceClose : ℕ → ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (hTraceClose : ∀ N M k z omega, TraceClose N M k z omega ↔
      SubdiffusiveProcess.FiniteStopping.trace_close model H alpha eta N M k z omega)
    (hTraceWitness : ∀ (N M k : ℕ) (zc : SpatialCoordinates d),
      k ≤ N → k ≤ M → m0 ≤ N - k → m0 ≤ M - k →
      ∃ W : ℕ+ → Set (BilateralField d),
        (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
          ((Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))).restrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ))) →
              C(SpatialCoordinates d, ℝ)))] (W h)) ∧
        (∀ h : ℕ+, (chaosSampleLaw model).toMeasure (W h) ≤
          ENNReal.ofReal (Real.exp (-B * (h : ℝ)))) ∧
        (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
          ¬TraceClose N M k zc omega → omega ∈ ⋃ h : ℕ+, W h)) :
    ∃ Ceta ceta : ℝ, ∃ N0 : ℕ, 0 < Ceta ∧ 0 < ceta ∧
      ∀ N M : ℕ, N0 ≤ N → N ≤ M →
        (∀ k : ℤ, a * (N : ℝ) ≤ (k : ℝ) → (k : ℝ) ≤ b * (N : ℝ) →
          0 ≤ k ∧ m0 ≤ N - k.toNat ∧ m0 ≤ M - k.toNat) ∧
        ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
          (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ))) ∧
          ∀ omega : BilateralField d, omega ∉ Bad →
            ∀ (v : Fin (SubdiffusiveProcess.FiniteStopping.rootRho H1 j) → OddGridIndex d 1)
              (w : ℕ → OddGridIndex d (subdivisionHalfWidth H1)),
              let k : ℕ → ℤ := fun n => (H1 : ℤ) * (n : ℤ) -
                (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j
              let zc : ℕ → SpatialCoordinates d := fun n =>
                descendantCenter (subdivisionHalfWidth H1)
                  (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z v)
                  ((3 : ℝ) ^ ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j)) n
                  (fun i : Fin n => w i)
              (Nat.card {n : ℕ // a * (N : ℝ) ≤ (k n : ℝ) ∧
                (k n : ℝ) ≤ b * (N : ℝ) ∧
                ¬(SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad N
                    (k n).toNat (zc n) omega ∧
                  SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad M
                    (k n).toNat (zc n) omega ∧
                  TraceClose N M (k n).toNat (zc n) omega)} : ℝ) ≤
                theta * (N : ℝ) / (H1 : ℝ) := by
  have hi : ∀ v : Fin (SubdiffusiveProcess.FiniteStopping.rootRho H1 j) → OddGridIndex d 1,
      ∃ Ceta ceta : ℝ, ∃ N0 : ℕ, 0 < Ceta ∧ 0 < ceta ∧
      ∀ N M : ℕ, N0 ≤ N → N ≤ M →
        (∀ k : ℤ, a * (N : ℝ) ≤ (k : ℝ) → (k : ℝ) ≤ b * (N : ℝ) →
          0 ≤ k ∧ m0 ≤ N - k.toNat ∧ m0 ≤ M - k.toNat) ∧
        ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
          (chaosSampleLaw model).toMeasure Bad ≤
            ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ))) ∧
          ∀ omega : BilateralField d, omega ∉ Bad →
            ∀ w : ℕ → OddGridIndex d (subdivisionHalfWidth H1),
              let k : ℕ → ℤ := fun n => (H1 : ℤ) * (n : ℤ) -
                (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j
              let zc : ℕ → SpatialCoordinates d := fun n =>
                descendantCenter (subdivisionHalfWidth H1)
                  (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z v)
                  ((3 : ℝ) ^ ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j)) n
                  (fun i : Fin n => w i)
              (Nat.card {n : ℕ // a * (N : ℝ) ≤ (k n : ℝ) ∧
                (k n : ℝ) ≤ b * (N : ℝ) ∧
                ¬(SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad N
                    (k n).toNat (zc n) omega ∧
                  SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad M
                    (k n).toNat (zc n) omega ∧
                  TraceClose N M (k n).toNat (zc n) omega)} : ℝ) ≤
                theta * (N : ℝ) / (H1 : ℝ) := by
    intro v
    exact finite_interval_packing d hd a b theta alpha beta ha hab hb htheta hthetab
      hbeta hba halpha H1 hH1 Cfin Aext pad B hCfin hAext hpad hpadL hB model H hH
      (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z v)
      ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j)
      (SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad)
      (SubdiffusiveProcess.FiniteStopping.hReg model H alpha H1 pad Cfin hpad)
      hRegWitness eta heta m0 TraceClose hTraceClose hTraceWitness
  exact SubdiffusiveProcess.FiniteStopping.fip_union_over_roots model H1
    (subdivisionHalfWidth H1)
    (fun v => SubdiffusiveProcess.FiniteStopping.rootCell H1 j z v)
    ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j)
    (SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad)
    TraceClose a b theta m0 hi

end Paper
