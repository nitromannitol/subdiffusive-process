module

public import SubdiffusiveProcess.Sobolev.HarmonicWindowNorms

@[expose] public section

/-! Uniform convergence passes a fixed-window Campanato inequality to its limit.
This module supplies scalar limit passage and the positive-volume geometry of
the truncated balls; it does not assert any finite-cutoff PDE estimate.
-/

open Filter MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal

namespace SubdiffusiveProcess

/-- A ball about a point of an open set has positive intersection volume. -/
theorem volume_real_ball_inter_pos
    {d : ℕ} (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q)
    (x : SpatialCoordinates d) (hx : x ∈ Q) (r : ℝ) (hr : 0 < r) :
    0 < volume.real (Metric.ball x r ∩ Q) := by
  apply ENNReal.toReal_pos
  · exact ne_of_gt ((Metric.isOpen_ball.inter hQ).measure_pos volume
      ⟨x, Metric.mem_ball_self hr, hx⟩)
  · exact ne_of_lt ((measure_mono inter_subset_left).trans_lt
      Metric.isBounded_ball.measure_lt_top)

/-- Every fixed-window centered oscillation inequality survives uniform limits. -/
theorem campanato_bound_of_tendstoUniformlyOn
    {d : ℕ} (W P : Set (SpatialCoordinates d))
    (hWm : MeasurableSet W) (hPm : MeasurableSet P)
    (hWpos : 0 < volume.real W) (hPpos : 0 < volume.real P)
    (hWtop : volume W ≠ ⊤) (hPtop : volume P ≠ ⊤)
    (UN : ℕ → SpatialCoordinates d → ℝ) (U : SpatialCoordinates d → ℝ)
    (hNW : ∀ n, MemLp (UN n) 2 (volume.restrict W))
    (hNP : ∀ n, MemLp (UN n) 2 (volume.restrict P))
    (hUW : MemLp U 2 (volume.restrict W))
    (hUP : MemLp U 2 (volume.restrict P))
    (hlimW : TendstoUniformlyOn UN U atTop W)
    (hlimP : TendstoUniformlyOn UN U atTop P)
    (aN : ℕ → ℝ) (a : ℝ) (ha : a ≠ 0)
    (halim : Tendsto aN atTop (𝓝 a)) (C r F : ℝ)
    (hbound : ∀ᶠ n in atTop,
      normalizedL2On W (fun y => UN n y - (volume.real W)⁻¹ * ∫ t in W, UN n t) ≤
        C * (normalizedL2On P
          (fun y => UN n y - (volume.real P)⁻¹ * ∫ t in P, UN n t) +
          r ^ 2 * (aN n)⁻¹ * F)) :
    normalizedL2On W (fun y => U y - (volume.real W)⁻¹ * ∫ t in W, U t) ≤
      C * (normalizedL2On P
        (fun y => U y - (volume.real P)⁻¹ * ∫ t in P, U t) + r ^ 2 * a⁻¹ * F) := by
  have hleft := tendsto_centered_normalizedL2_of_tendstoUniformlyOn
    W hWm hWpos hWtop UN U hNW hUW hlimW
  have hosc := tendsto_centered_normalizedL2_of_tendstoUniformlyOn
    P hPm hPpos hPtop UN U hNP hUP hlimP
  have hright := (hosc.add (((halim.inv₀ ha).const_mul (r ^ 2)).mul_const F)).const_mul C
  exact le_of_tendsto_of_tendsto hleft hright hbound

end SubdiffusiveProcess
