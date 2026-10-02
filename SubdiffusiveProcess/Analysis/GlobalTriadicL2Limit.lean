import SubdiffusiveProcess.Analysis.GlobalTriadicAverages
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Set TopologicalSpace Filter
open SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section
namespace SubdiffusiveProcess

theorem globalTriadicAverages_exists_L2_limit_of_summable_increments
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (ν : Measure (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
  let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  (hE : ∀ n : ℕ, MemLp (E n) 2 ν) →
  Summable (fun n : ℕ =>
    (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal) →
  ∃ g : SpatialCoordinates d → ℝ, MemLp g 2 ν ∧
    Tendsto (fun n => eLpNorm (fun x => E n x - g x) 2 ν) atTop (nhds 0) := by
  intro E hE hsum
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let u : ℕ → Lp ℝ 2 ν := fun n => (hE n).toLp (E n)
  have hdist : ∀ n : ℕ,
      dist (u n) (u (n + 1)) = (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal := by
    intro n
    rw [dist_comm, Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    dsimp only [u]
    filter_upwards [(hE (n + 1)).coeFn_toLp, (hE n).coeFn_toLp] with x hx1 hx0
    simp only [Pi.sub_apply, hx1, hx0]
  have hfun_eq : (fun n : ℕ => (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal) =
      (fun n : ℕ => dist (u n) (u (n + 1))) := funext (fun n => (hdist n).symm)
  have hsummable_dist : Summable (fun n : ℕ => dist (u n) (u (n + 1))) := by
    rw [← hfun_eq]; exact hsum
  have hcauchy : CauchySeq u := cauchySeq_of_summable_dist hsummable_dist
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨(x : SpatialCoordinates d → ℝ), Lp.memLp x, ?_⟩
  have hdist' : ∀ n : ℕ,
      dist (u n) x =
        (eLpNorm (fun y => E n y - (x : SpatialCoordinates d → ℝ) y) 2 ν).toReal := by
    intro n
    rw [Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    dsimp only [u]
    filter_upwards [(hE n).coeFn_toLp] with y hy
    simp only [Pi.sub_apply, hy]
  have hxtendsto : Tendsto (fun n : ℕ => dist (u n) x) atTop (nhds 0) :=
    (tendsto_iff_dist_tendsto_zero).mp hx
  have hfun_eq' : (fun n : ℕ => dist (u n) x) =
      (fun n : ℕ =>
        (eLpNorm (fun y => E n y - (x : SpatialCoordinates d → ℝ) y) 2 ν).toReal) :=
    funext hdist'
  rw [hfun_eq'] at hxtendsto
  have hfin : ∀ n : ℕ,
      eLpNorm (fun y => E n y - (x : SpatialCoordinates d → ℝ) y) 2 ν ≠ ⊤ :=
    fun n => ((hE n).sub (Lp.memLp x)).2.ne
  have htop : (eLpNorm (fun y => E 0 y - (x : SpatialCoordinates d → ℝ) y) 2 ν) ≠ ⊤ :=
    hfin 0
  have hy0 : (0 : ENNReal) ≠ ⊤ := ENNReal.zero_ne_top
  have hreal0 : Tendsto
      (fun n : ℕ =>
        (eLpNorm (fun y => E n y - (x : SpatialCoordinates d → ℝ) y) 2 ν).toReal)
      atTop (nhds (0 : ENNReal).toReal) := by
    simpa using hxtendsto
  exact (ENNReal.tendsto_toReal_iff hfin hy0).mp hreal0

end SubdiffusiveProcess
