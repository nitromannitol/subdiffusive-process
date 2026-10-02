import SubdiffusiveProcess.FiniteStopping.SourcedStageAt

/-! The sourced good-step event of the finite stopping construction (paper
`\label{mfd:lem-finite-source-comparison}`, "use the partition of the proof of Lemma
`mfd:lem-finite-stopping`, now with `λ = Γ_M(u_M) + 3^{-ζN}B² dx`").

`good_steps_src_at` records, without asserting that it occurs, ONE goodness predicate `Good` on tree cells whose bad
levels are counted on every branch and whose good padded children satisfy the sourced local comparison for EVERY
source `(F, Kf)` and EVERY weak solution `u` of the sourced equation on the root (Dirichlet or Neumann alike, through the
Dirichlet-type test identity).  `Good` therefore cannot depend on the data: this is what lets the exceptional event of
the sourced partition be chosen before every source, datum and solution. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

open Classical in
/-- The sourced good-step event for the infrared coefficient `Hused`, with weight factor `wt`
(`wt = 1` for the characterized field; `wt ≥ e^{osc}` for the infrared-free coefficient, paper last paragraph). -/
def good_steps_src_at
    {d : ℕ} [NeZero d]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ))
    (P H1 : ℕ) (theta Cg eta wt : ℝ) (z : SpatialCoordinates d) (j : ℤ)
    (N M : ℕ) (reverse : Bool) (omega : BilateralField d) : Prop :=
  let hr : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  let target := if reverse then M else N
  let source := if reverse then N else M
  let aT := cutoffPositiveCoefficient model Hused omega target z hr
  let aS := cutoffPositiveCoefficient model Hused omega source z hr
  let mg := subdivisionHalfWidth H1
  let t0 := obsT0 H1 N j
  let B := obsB H1 N
  ∃ Good : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop,
    (∀ (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg),
      ((((Finset.univ : Finset (Fin B)).filter fun i =>
        ¬ Good w0 (i.val + 1) (wordPrefix w (i.val + 1) i.isLt)).card : ℕ) : ℝ) ≤
          theta * (N : ℝ) / (H1 : ℝ)) ∧
    (∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin (s + 1) → OddGridIndex d mg),
      s + 1 ≤ B → Good w0 (s + 1) w → padLabel P (w (Fin.last s)) →
      ∀ (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
        (F : SpatialCoordinates d → ℝ) (Kf : ℝ), Measurable F → 0 ≤ Kf →
        (∀ x ∈ centeredCube z ((3 : ℝ) ^ j) hr, |F x| ≤ Kf) →
        (∀ psi : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr),
          sobolevCoefficientForm aS (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
              (psi : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)) =
            ∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)),
              F x * (psi : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1 x) →
        respOn aT u (cell2_le_root z hr t0 mg w0 (s + 1) w)
            (cell2_killedPoincare z hr t0 mg w0 (s + 1) w) ≤
          wt * kappaRatio model H1 target source (obsLo H1 N + (s + 1)) *
              respOn aS u (cell2_le_root z hr t0 mg w0 (s + 1) w)
                (cell2_killedPoincare z hr t0 mg w0 (s + 1) w) +
            Cg * eta * (wt * kappaRatio model H1 target source (obsLo H1 N + (s + 1))) *
              (energyOn aS u.val (cell2 z hr t0 mg w0 s (fun i => w i.castSucc)) +
                (descendantSide mg (s + 1) (descendantSide 1 t0 ((3 : ℝ) ^ j))) ^ ((d : ℝ) + 2) *
                  (reference model Hused omega source (H1 * (obsLo H1 N + (s + 1)))
                    (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
                      (descendantSide 1 t0 ((3 : ℝ) ^ j)) (s + 1) w))⁻¹ * Kf ^ 2))

end SubdiffusiveProcess.FiniteStopping
