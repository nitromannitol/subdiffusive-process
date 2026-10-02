import SubdiffusiveProcess.Meyers.Ball
import SubdiffusiveProcess.Meyers.LpSum
import SubdiffusiveProcess.Meyers.Arith

/-! Assembly (dimension `d ≥ 2`): the exact Meyers leaf (`MeyersEstimate`) on the Euclidean grid balls,
mean subtraction + cube Poincaré, and the finite union bound give the derived form `E2Body` on cubes. -/

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Meyers

variable {d : ℕ}

theorem volume_real_ball (x0 : Vec d) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball x0 r) = (2 * r) ^ d := by
  rw [Measure.real, Real.volume_pi_ball x0 hr, ENNReal.toReal_ofReal (by positivity), Fintype.card_fin]

/-- Step 1: the sum over the grid balls of the `L^p` norms bounds the `L^p` norm on the cube. -/
theorem sum_grid_bound (x0 : Vec d) {l : ℝ} (hl : 0 < l) {p : ℝ} (hp : 2 ≤ p) {G : Vec d → ℝ}
    (hG2 : MemLp G 2 (volume.restrict (Metric.ball x0 (2 * l))))
    (hballs : ∀ k : Fin d → Fin (3 * d + 1),
      MemLp G (ENNReal.ofReal p) (volume.restrict (eBall (x0 + l • gridCenter d k) (l / 3)))) :
    MemLp G (ENNReal.ofReal p) (volume.restrict (Metric.ball x0 l)) ∧
      (eLpNorm G (ENNReal.ofReal p) (volume.restrict (Metric.ball x0 l))).toReal ≤
        ∑ k : Fin d → Fin (3 * d + 1),
          (eLpNorm G (ENNReal.ofReal p) (volume.restrict (eBall (x0 + l • gridCenter d k) (l / 3)))).toReal := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    rw [ENNReal.one_le_ofReal]; linarith
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcover : Metric.ball x0 l ⊆ ⋃ k : Fin d → Fin (3 * d + 1), eBall (x0 + l • gridCenter d k) (l / 3) := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_grid_ball x0 hl hx
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  have hsum := (eLpNorm_mono_measure G (Measure.restrict_mono hcover (le_refl (volume : Measure (Vec d))))).trans
    (eLpNorm_restrict_iUnion_le G hp1 hpt volume (fun k : Fin d → Fin (3 * d + 1) =>
      eBall (x0 + l • gridCenter d k) (l / 3)))
  have hfin : ∀ k ∈ (Finset.univ : Finset (Fin d → Fin (3 * d + 1))),
      eLpNorm G (ENNReal.ofReal p) (volume.restrict (eBall (x0 + l • gridCenter d k) (l / 3))) ≠ ⊤ :=
    fun k _ => (hballs k).eLpNorm_ne_top
  have hsumfin : ∑ k : Fin d → Fin (3 * d + 1),
      eLpNorm G (ENNReal.ofReal p) (volume.restrict (eBall (x0 + l • gridCenter d k) (l / 3))) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr hfin
  have hmeas : AEStronglyMeasurable G (volume.restrict (Metric.ball x0 l)) :=
    hG2.1.mono_measure (Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl)
  refine ⟨⟨hmeas, lt_of_le_of_lt hsum (lt_top_iff_ne_top.mpr hsumfin)⟩, ?_⟩
  rw [← ENNReal.toReal_sum hfin]
  exact ENNReal.toReal_mono hsumfin hsum

end SubdiffusiveProcess.Meyers
