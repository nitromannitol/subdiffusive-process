module

public import SubdiffusiveProcess.FiniteStopping.HarmonicStepComparison

@[expose] public section

/-! This module records the exact finite stopping event, without asserting that it occurs. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.FiniteStopping
open scoped ENNReal NNReal BigOperators ContDiff
noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

open Classical in
/-- One goodness predicate controls the branch count and every padded response comparison. -/
def good_steps_at
    {d : ℕ} [NeZero d]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (P H1 : ℕ) (theta Cg eta : ℝ) (z : SpatialCoordinates d) (j : ℤ)
    (N M : ℕ) (reverse : Bool)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph
        (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)),
      ‖(v : SobolevData (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))
          (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))) v‖)
    (b : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))) (omega : BilateralField d) : Prop :=
      let hr : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
      let target := if reverse then M else N
      let source := if reverse then N else M
      let aT := cutoffPositiveCoefficient model H omega target z hr
      let aS := cutoffPositiveCoefficient model H omega source z hr
      let u := @dirichletMinimizer d _ (@killedResponseSpace d _ hP) aS b
      let mg := subdivisionHalfWidth H1
      let t0 := obsT0 H1 N j
      let B := obsB H1 N
      ∃ Good : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop,
        (∀ (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg),
          ((((Finset.univ : Finset (Fin B)).filter fun i =>
            ¬ Good w0 (i.val + 1)
              (wordPrefix w (i.val + 1) i.isLt)).card :
                ℕ) : ℝ) ≤
              theta * (N : ℝ) / (H1 : ℝ)) ∧
        (∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin (s + 1) → OddGridIndex d mg),
          s + 1 ≤ B → Good w0 (s + 1) w →
          padLabel P (w (Fin.last s)) →
          respOn aT u
              (cell2_le_root z hr t0 mg w0 (s + 1) w)
              (cell2_killedPoincare z hr t0 mg w0 (s + 1)
                w) ≤
            kappaRatio model H1 target source
                (obsLo H1 N + (s + 1)) *
                respOn aS u
                  (cell2_le_root z hr t0 mg w0 (s + 1) w)
                  (cell2_killedPoincare z hr t0 mg w0
                    (s + 1) w) +
              Cg * eta *
                kappaRatio model H1 target source
                  (obsLo H1 N + (s + 1)) *
                energyOn aS u.val
                  (cell2 z hr t0 mg w0 s
                    (fun i => w i.castSucc)))

/-- The exact good-step event holds at every large cutoff outside an exponentially small event. -/
def good_steps_on_root
    {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (P H1 : ℕ) (theta Cg eta : ℝ) (z : SpatialCoordinates d) (j : ℤ)
    (C gamma : ℝ) (N0 : ℕ) : Prop :=
        ∀ (N M : ℕ), N0 ≤ N → N ≤ M → ∀ reverse : Bool,
        ∀ hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph
        (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)),
      ‖(v : SobolevData (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))
          (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))) v‖,
        ∀ b : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)),
          ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
            (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
            ∀ omega ∉ Bad, good_steps_at model H P H1 theta (Cg) eta z j N M reverse hP b omega

end SubdiffusiveProcess.FiniteStopping
