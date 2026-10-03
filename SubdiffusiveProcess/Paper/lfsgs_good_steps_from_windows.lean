module

public import SubdiffusiveProcess.FiniteStopping.LayerWindowWitness
public import SubdiffusiveProcess.Paper.lfsgs_per_root_union
public import SubdiffusiveProcess.Paper.lfsgs_good_steps_from_counts

@[expose] public section

/-! This module combines the original-field windows and deterministic good-step comparison. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.FiniteStopping
open scoped ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Paper

/-- Regularity and trace windows give a summable exceptional event for every root cube. -/
theorem lfsgs_good_steps_from_windows
    {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H1 : ℕ) (hH1 : 0 < H1) (theta thetaPack alpha beta Cfin pad B : ℝ)
    (hthetaPack : 0 < thetaPack) (hthetaPack_le : thetaPack ≤ theta)
    (hthetaPack_gap : thetaPack < (3 / 4 : ℝ) - 1 / 4)
    (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1)
    (hCfin : 0 < Cfin) (hpad : 1 < pad) (hpad3 : pad ≤ 3) (hpadL : pad < (3 : ℝ) ^ H1)
    (hB : B > 1000 * (H1 : ℝ) * ((d : ℝ) + 1) * (Real.log 3 + 1) / thetaPack)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization model H)
    (hRegWitness : ∀ (N k : ℕ) (zc : SpatialCoordinates d), k ≤ N →
      has_layer_windows (chaosSampleLaw model).toMeasure k B
        (Reg model H alpha H1 pad Cfin hpad N k zc))
    (hTraceSup : has_trace_windows model H alpha B) :
    ∀ (z : SpatialCoordinates d) (j : ℤ) (eta : ℝ), 0 < eta →
      ∃ (C gamma : ℝ) (N0 : ℕ), 0 < C ∧ 0 < gamma ∧
        good_steps_on_root model H 2 H1 theta (Cfin ^ 2) eta z j C gamma N0 := by
  classical
  intro z j eta heta
  obtain ⟨m0, TraceClose, hTraceClose, hTraceWitness⟩ :=
    hTraceSup eta heta
  let gammaThetaLo : ℝ := 1 / 4
  let gammaThetaHi : ℝ := 3 / 4
  have hLo : 0 < gammaThetaLo := by norm_num [gammaThetaLo]
  have hLoHi : gammaThetaLo < gammaThetaHi := by norm_num [gammaThetaLo, gammaThetaHi]
  have hHi : gammaThetaHi < 1 := by norm_num [gammaThetaHi]
  obtain ⟨Ceta, ceta, Npack, hCeta, hceta, hpack⟩ :=
    Paper.lfsgs_per_root_union hd gammaThetaLo gammaThetaHi thetaPack
      alpha beta hLo hLoHi hHi hthetaPack hthetaPack_gap hbeta hba halpha H1 hH1
      Cfin Cfin pad B hCfin hCfin hpad hpadL hB model H hH z j hRegWitness eta heta m0
      TraceClose hTraceClose hTraceWitness
  obtain ⟨Ngeom, hgeom⟩ := hj0_hq0_exists H1 hH1 j
  let N0 : ℕ := max 1 (max Npack Ngeom)
  refine ⟨Ceta, ceta, N0, hCeta, hceta, ?_⟩
  intro N M hN hNM reverse hP b
  have hNpack : Npack ≤ N := by dsimp [N0] at hN; omega
  have hNgeom : Ngeom ≤ N := by dsimp [N0] at hN; omega
  have hNpos : 0 < N := by dsimp [N0] at hN; omega
  obtain ⟨_, hBadPack⟩ := hpack N M hNpack hNM
  obtain ⟨Bad, hBadMeas, hBadProb, hBadCount⟩ := hBadPack
  refine ⟨Bad, hBadMeas, hBadProb, ?_⟩
  intro omega hOmega
  have ⟨hj0, hq0⟩ := hgeom N hNgeom
  exact lfsgs_good_steps_from_counts hd H1 hH1 z j N M hNpos hj0 hq0
    theta thetaPack hthetaPack_le model H alpha pad Cfin hpad TraceClose omega
    (hBadCount omega hOmega) eta heta hCfin hpad3 hTraceClose reverse hP b

end Paper
