module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFailureHeight
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.SubquadraticGrowth
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubunitGeometry

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ}

/-- A concrete upper bound for a coefficient with linear spatial growth on a
translated cube. -/
def stoppingCellLinearUpperBound (K : ℝ) (scale : ℤ) (centre : Vec d) : ℝ :=
  K * (1 + ‖centre‖ + cubeRadius (originCube d (scale + 1)))

theorem stoppingCellLinearUpperBound_nonneg {K : ℝ} (hK : 0 ≤ K)
    (scale : ℤ) (centre : Vec d) :
    0 ≤ stoppingCellLinearUpperBound K scale centre := by
  unfold stoppingCellLinearUpperBound
  exact mul_nonneg hK
    (add_nonneg (add_nonneg zero_le_one (norm_nonneg centre))
      (cubeRadius_nonneg _))

/-- Linear growth gives the required `L^∞` bound on the centred threefold
enlargement of a stopping cell. -/
theorem le_stoppingCellLinearUpperBound_of_mem_enlargement
    {a : Vec d → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ x, a x ≤ K * (1 + ‖x‖))
    (scale : ℤ) (centre : Vec d) {x : Vec d}
    (hx : x ∈ translatedCube d (scale + 1) centre) :
    a x ≤ stoppingCellLinearUpperBound K scale centre := by
  have hdist : dist x centre < cubeRadius (originCube d (scale + 1)) := by
    rw [translatedCube_eq_metricBall] at hx
    exact Metric.mem_ball.mp hx
  have hnorm : ‖x‖ ≤ ‖centre‖ + cubeRadius (originCube d (scale + 1)) := by
    have htriangle : ‖x‖ ≤ ‖centre‖ + ‖x - centre‖ := by
      have hadd : centre + (x - centre) = x := by abel
      simpa only [hadd] using norm_add_le centre (x - centre)
    have hdistNorm : ‖x - centre‖ ≤ cubeRadius (originCube d (scale + 1)) := by
      simpa [dist_eq_norm] using hdist.le
    exact htriangle.trans (by
      simpa only [add_comm] using add_le_add_left hdistNorm ‖centre‖)
  exact (ha x).trans (mul_le_mul_of_nonneg_left (by linarith) hK)

/-- Almost surely, every requested stopping-cell enlargement has an explicit
finite upper coefficient bound. -/
theorem ae_forall_aCutoff_le_stoppingCellLinearUpperBound
    (M : GMCModel d) (L : ℕ) {Cell : Type*}
    (scale : Cell → ℤ) (centre : Cell → Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∃ K : ℝ, 0 ≤ K ∧
      ∀ q x, x ∈ translatedCube d (scale q + 1) (centre q) →
        aCutoff M L omega x ≤
          stoppingCellLinearUpperBound K (scale q) (centre q) := by
  filter_upwards [ae_exists_aCutoff_linear_growth M L] with omega hlinear
  obtain ⟨K, hK, ha⟩ := hlinear
  refine ⟨K, hK, ?_⟩
  intro q x hx
  exact le_stoppingCellLinearUpperBound_of_mem_enlargement hK ha
    (scale q) (centre q) hx

/-- The same conclusion for sample-dependent stopping-cell geometry.  The
linear majorant is global, so no measurability of the scale or centre maps is
needed. -/
theorem ae_forall_aCutoff_le_sampleStoppingCellLinearUpperBound
    (M : GMCModel d) (L : ℕ) {Cell : Type*}
    (scale : PotentialSample d → Cell → ℤ)
    (centre : PotentialSample d → Cell → Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∃ K : ℝ, 0 ≤ K ∧
      ∀ q x, x ∈ translatedCube d (scale omega q + 1) (centre omega q) →
        aCutoff M L omega x ≤
          stoppingCellLinearUpperBound K (scale omega q) (centre omega q) := by
  filter_upwards [ae_exists_aCutoff_linear_growth M L] with omega hlinear
  obtain ⟨K, hK, ha⟩ := hlinear
  refine ⟨K, hK, ?_⟩
  intro q x hx
  exact le_stoppingCellLinearUpperBound_of_mem_enlargement hK ha
    (scale omega q) (centre omega q) hx

/-- Specialization to the raw failure-height cells. -/
theorem ae_forall_aCutoff_le_overlappingStoppingCellEnlargement
    (M : GMCModel d) (L : ℕ) (base : ℤ)
    (failure : Lattice d → ℕ → Set (PotentialSample d)) :
    ∀ᵐ omega ∂M.P.toMeasure, ∃ K : ℝ, 0 ≤ K ∧
      ∀ z x,
        x ∈ translatedCube d
            (stoppingPartitionScale base failure omega z + 1)
            (gridCentre d base z) →
          aCutoff M L omega x ≤
            stoppingCellLinearUpperBound K
              (stoppingPartitionScale base failure omega z)
              (gridCentre d base z) :=
  ae_forall_aCutoff_le_sampleStoppingCellLinearUpperBound M L
    (stoppingPartitionScale base failure) (fun _ z ↦ gridCentre d base z)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
