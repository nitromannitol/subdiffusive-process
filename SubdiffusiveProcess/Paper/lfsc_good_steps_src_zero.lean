import SubdiffusiveProcess.Paper.lfsc_good_steps_src
import SubdiffusiveProcess.Paper.lem_finite_stopping_partition
import SubdiffusiveProcess.FiniteStopping.SourcedStageZero

/-! Sourced good steps for the infrared-free coefficient `A^0 = e^{-H} A` (weight-transfer route of the paper's
last paragraph): regularity `Reg model 0`, trace closeness of the characterized coefficient, and the Lipschitz
constant `LH` of `H` on the root cube (`wt ≥ e^{LH·3^{-N/4}}`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.FiniteStopping
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

/-- Stage cells have side at most `3^{-N/4}`. -/
theorem aux_lfsc_good_steps_src_zero_stage_side_le {d : ℕ} (H1 N : ℕ) (hH1 : 0 < H1) (z : SpatialCoordinates d) (j : ℤ)
    (hj0 : 0 ≤ ((H1 * obsLo H1 N : ℕ) : ℤ) + j) (s : ℕ) :
    descendantSide (subdivisionHalfWidth H1) (s + 1)
        (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j)) ≤ (3 : ℝ) ^ (-((N : ℝ) / 4)) := by
  have h := cell2_radius_eq H1 N hH1 j hj0 (s + 1)
  rw [h]
  have hle : N ≤ 4 * (H1 * obsLo H1 N) :=
    Paper.aux_lem_finite_stopping_partition_four_H1_obsLo_ge hH1 N
  have h1 : (3 : ℝ) ^ (-((H1 * (obsLo H1 N + (s + 1)) : ℕ) : ℤ)) =
      (3 : ℝ) ^ (-(((H1 * (obsLo H1 N + (s + 1)) : ℕ) : ℝ))) := by
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rw [h1]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h2 : (N : ℝ) ≤ 4 * ((H1 : ℝ) * (obsLo H1 N : ℝ)) := by exact_mod_cast hle
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) H1, Nat.cast_nonneg (α := ℝ) s]

/-- A packed branch count and the trace predicate imply the sourced good-step event for `A^0`. -/
theorem aux_lfsc_good_steps_src_zero_from_counts
    {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H1 : ℕ) (hH1 : 0 < H1) (z : SpatialCoordinates d) (j : ℤ) (N M : ℕ) (hNpos : 0 < N)
    (hj0 : 0 ≤ ((H1 * obsLo H1 N : ℕ) : ℤ) + j)
    (hq0 : 0 ≤ (obsLo H1 N : ℤ) + rootQ H1 j)
    (theta thetaUsed : ℝ) (hthetaUsed : thetaUsed ≤ theta)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (alpha pad Cfin : ℝ) (hpad : 1 < pad)
    (TraceClose : ℕ → ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (omega : BilateralField d)
    (hbound : ∀ (v : Fin (rootRho H1 j) → OddGridIndex d 1)
        (w : ℕ → OddGridIndex d (subdivisionHalfWidth H1)),
      let k : ℕ → ℤ := fun n => (H1 : ℤ) * (n : ℤ) - (H1 : ℤ) * rootQ H1 j
      let zc : ℕ → SpatialCoordinates d := fun n =>
        descendantCenter (subdivisionHalfWidth H1)
          (rootCell H1 j z v)
          ((3 : ℝ) ^ ((H1 : ℤ) * rootQ H1 j)) n
          (fun i : Fin n => w i)
      (Nat.card {n : ℕ // (1 / 4 : ℝ) * (N : ℝ) ≤ (k n : ℝ) ∧
        (k n : ℝ) ≤ (3 / 4 : ℝ) * (N : ℝ) ∧
        ¬(Reg model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) alpha H1 pad Cfin hpad N
            (k n).toNat (zc n) omega ∧
          Reg model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) alpha H1 pad Cfin hpad M
            (k n).toNat (zc n) omega ∧
          TraceClose N M (k n).toNat (zc n) omega)} : ℝ) ≤
        thetaUsed * (N : ℝ) / (H1 : ℝ))
    (eta : ℝ) (heta : 0 < eta) (hCfin : 0 < Cfin) (hpad3 : pad ≤ 3)
    (hTraceClose : ∀ N M k z omega, TraceClose N M k z omega ↔
      trace_close model H alpha eta N M k z omega)
    (LH : ℝ) (hLH : 0 ≤ LH)
    (hLip : ∀ x ∈ closedCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j),
      ∀ y ∈ closedCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j),
      |H omega x - H omega y| ≤ LH * dist x y)
    (wt : ℝ) (hwt : Real.exp (LH * (3 : ℝ) ^ (-((N : ℝ) / 4))) ≤ wt)
    (reverse : Bool) :
    good_steps_src_at model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) 2 H1 theta
      (2 * Cfin ^ 2) eta wt z j N M reverse omega := by
  classical
  obtain ⟨Good, hGoodIff, hGoodCount⟩ :=
    Paper.lfsgs_conjunct1_of_bound hd H1 hH1 z j N M hNpos
      hj0 hq0 theta thetaUsed hthetaUsed model (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
      alpha pad Cfin hpad TraceClose omega hbound
  refine ⟨Good, hGoodCount, ?_⟩
  intro w0 s w hsB hGood hPad u F Kf hFm hKf hFb hsol
  obtain ⟨hRegN, hRegM, hTrace⟩ := (hGoodIff w0 (s + 1) w).mp hGood
  let k := H1 * (obsLo H1 N + (s + 1))
  let zc := descendantCenter (subdivisionHalfWidth H1)
    (descendantCenter 1 z ((3 : ℝ) ^ j)
      (obsT0 H1 N j) w0)
    (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j))
    (s + 1) w
  have hRegSource : Reg model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) alpha H1 pad Cfin hpad
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
  have hwt' : Real.exp (LH * descendantSide (subdivisionHalfWidth H1) (s + 1)
      (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j))) ≤ wt :=
    le_trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (aux_lfsc_good_steps_src_zero_stage_side_le H1 N hH1 z j hj0 s) hLH)) hwt
  exact comparison_at_stage_src_zero model H omega alpha eta Cfin
    pad heta hCfin hpad hpad3 H1 N (if reverse then M else N) (if reverse then N else M)
    hH1 z j (zpow_pos (by norm_num) j) hj0 u F Kf hFm hKf hFb hsol w0 s w hPad LH hLH hLip wt hwt'
    hRegSource hTracePair

/-- Windows version of `aux_lfsc_good_steps_src_zero_from_counts`: outside one event `Bad` depending on `(N, M)` only,
the sourced good-step event for `A^0` holds for every Lipschitz bound `LH` of `H` on the root cube. -/
theorem lfsc_good_steps_src_zero
    {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H1 : ℕ) (hH1 : 0 < H1) (theta thetaPack alpha Cfin pad B : ℝ)
    (hthetaPack : 0 < thetaPack) (hthetaPack_le : thetaPack ≤ theta)
    (hthetaPack_gap : thetaPack < (3 / 4 : ℝ) - 1 / 4)
    (hCfin : 0 < Cfin) (hpad : 1 < pad) (hpad3 : pad ≤ 3)
    (hB : B > 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / thetaPack)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hRegWitness : ∀ (N k : ℕ) (zc : SpatialCoordinates d), k ≤ N →
      has_layer_windows (chaosSampleLaw model).toMeasure k B
        (Reg model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) alpha H1 pad Cfin hpad N k zc))
    (hTraceSup : has_trace_windows model H alpha B) :
    ∀ (z : SpatialCoordinates d) (j : ℤ) (eta : ℝ), 0 < eta →
      ∃ (C gamma : ℝ) (N0 : ℕ), 0 < C ∧ 0 < gamma ∧
        ∀ N M : ℕ, N0 ≤ N → N ≤ M →
          ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
            (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
            ∀ omega ∉ Bad, ∀ (LH : ℝ), 0 ≤ LH →
              (∀ x ∈ closedCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j),
                ∀ y ∈ closedCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j),
                |H omega x - H omega y| ≤ LH * dist x y) →
              ∀ wt : ℝ, Real.exp (LH * (3 : ℝ) ^ (-((N : ℝ) / 4))) ≤ wt → ∀ reverse : Bool,
                good_steps_src_at model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) 2 H1 theta (2 * Cfin ^ 2) eta wt z j N M reverse omega := by
  classical
  intro z j eta heta
  obtain ⟨m0, TraceClose, hTraceClose, hTraceWitness⟩ := hTraceSup eta heta
  obtain ⟨Ceta, ceta, Npack, hCeta, hceta, hpack⟩ :=
    Paper.lfsc_per_root_union hd (1 / 4) (3 / 4) thetaPack (by norm_num) (by norm_num)
      (by norm_num) hthetaPack hthetaPack_gap H1 hH1 B hB model z j
      (Reg model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) alpha H1 pad Cfin hpad) hRegWitness m0 TraceClose hTraceWitness
  obtain ⟨Ngeom, hgeom⟩ := hj0_hq0_exists H1 hH1 j
  refine ⟨Ceta, ceta, max 1 (max Npack Ngeom), hCeta, hceta, ?_⟩
  intro N M hN hNM
  have hNpack : Npack ≤ N := by omega
  have hNgeom : Ngeom ≤ N := by omega
  have hNpos : 0 < N := by omega
  obtain ⟨_, hBadPack⟩ := hpack N M hNpack hNM
  obtain ⟨Bad, hBadMeas, hBadProb, hBadCount⟩ := hBadPack
  refine ⟨Bad, hBadMeas, hBadProb, ?_⟩
  intro omega hOmega LH hLH hLip wt hwt reverse
  have ⟨hj0, hq0⟩ := hgeom N hNgeom
  exact aux_lfsc_good_steps_src_zero_from_counts hd H1 hH1 z j N M hNpos hj0 hq0
    theta thetaPack hthetaPack_le model H alpha pad Cfin hpad TraceClose omega
    (hBadCount omega hOmega) eta heta hCfin hpad3 hTraceClose LH hLH hLip wt hwt reverse

end Paper
