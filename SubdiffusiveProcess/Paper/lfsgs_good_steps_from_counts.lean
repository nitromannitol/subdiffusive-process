module

public import SubdiffusiveProcess.Paper.lfsgs_conjunct1_of_bound
public import SubdiffusiveProcess.FiniteStopping.GoodStepEvent

@[expose] public section

/-! This module joins the branch count and response estimate for the same goodness predicate. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.FiniteStopping
open scoped ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Paper

/-- A packed branch count and its specified trace predicate imply the full deterministic good-step event. -/
theorem lfsgs_good_steps_from_counts
    {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H1 : ℕ) (hH1 : 0 < H1) (z : SpatialCoordinates d) (j : ℤ) (N M : ℕ) (hNpos : 0 < N)
    (hj0 : 0 ≤ ((H1 * obsLo H1 N : ℕ) : ℤ) + j)
    (hq0 : 0 ≤ (obsLo H1 N : ℤ) +
      rootQ H1 j)
    (theta thetaUsed : ℝ) (hthetaUsed : thetaUsed ≤ theta)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (alpha pad Cfin : ℝ) (hpad : 1 < pad)
    (TraceClose : ℕ → ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (omega : BilateralField d)
    (hbound : ∀ (v : Fin (rootRho H1 j) → OddGridIndex d 1)
        (w : ℕ → OddGridIndex d (subdivisionHalfWidth H1)),
      let k : ℕ → ℤ := fun n => (H1 : ℤ) * (n : ℤ) -
        (H1 : ℤ) * rootQ H1 j
      let zc : ℕ → SpatialCoordinates d := fun n =>
        descendantCenter (subdivisionHalfWidth H1)
          (rootCell H1 j z v)
          ((3 : ℝ) ^ ((H1 : ℤ) * rootQ H1 j)) n
          (fun i : Fin n => w i)
      (Nat.card {n : ℕ // (1 / 4 : ℝ) * (N : ℝ) ≤ (k n : ℝ) ∧
        (k n : ℝ) ≤ (3 / 4 : ℝ) * (N : ℝ) ∧
        ¬(Reg model H alpha H1 pad Cfin hpad N
            (k n).toNat (zc n) omega ∧
          Reg model H alpha H1 pad Cfin hpad M
            (k n).toNat (zc n) omega ∧
          TraceClose N M (k n).toNat (zc n) omega)} : ℝ) ≤
        thetaUsed * (N : ℝ) / (H1 : ℝ))
    (eta : ℝ) (heta : 0 < eta) (hCfin : 0 < Cfin) (hpad3 : pad ≤ 3)
    (hTraceClose : ∀ N M k z omega, TraceClose N M k z omega ↔
      trace_close model H alpha eta N M k z omega)
    (reverse : Bool)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph
        (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)),
      ‖(v : SobolevData (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))
          (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))) v‖)
    (b : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))) :
    good_steps_at model H 2 H1 theta (Cfin ^ 2) eta z j N M reverse hP b omega := by
  classical
  obtain ⟨Good, hGoodIff, hGoodCount⟩ :=
    Paper.lfsgs_conjunct1_of_bound hd H1 hH1 z j N M hNpos
      hj0 hq0 theta thetaUsed hthetaUsed model H alpha pad Cfin hpad TraceClose omega
      hbound
  refine ⟨Good, hGoodCount, ?_⟩
  intro w0 s w hsB hGood hPad
  obtain ⟨hRegN, hRegM, hTrace⟩ := (hGoodIff w0 (s + 1) w).mp hGood
  let k := H1 * (obsLo H1 N + (s + 1))
  let zc := descendantCenter (subdivisionHalfWidth H1)
    (descendantCenter 1 z ((3 : ℝ) ^ j)
      (obsT0 H1 N j) w0)
    (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j))
    (s + 1) w
  have hRegSource : Reg model H alpha H1 pad Cfin hpad
      (if reverse then N else M) k zc omega := by
    cases reverse with
    | false => exact hRegM
    | true => exact hRegN
  have hTracePair : trace_close model H alpha eta (if reverse then M else N) (if reverse then N else M)
      k zc omega := by
    cases reverse with
    | false => exact (hTraceClose N M k zc omega).mp hTrace
    | true =>
      exact trace_close_symm model H alpha eta N M k zc omega
        ((hTraceClose N M k zc omega).mp hTrace)
  exact comparison_at_stage model H omega alpha eta Cfin
    pad heta hCfin hpad hpad3 H1 N (if reverse then M else N) (if reverse then N else M)
    hH1 z j (zpow_pos (by norm_num) j) hj0 hP b w0 s w hPad hRegSource hTracePair

end Paper
