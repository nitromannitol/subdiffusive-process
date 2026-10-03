module

public import SubdiffusiveProcess.Sobolev.WeightedHarmonicBoundaryMaximum

@[expose] public section

/-! A continuous harmonic extension stays within the oscillation of its boundary datum.
The estimate is uniform in the ellipticity ratio; this module constructs no extension. -/
open MeasureTheory Set TopologicalSpace Homogenization SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section
namespace SubdiffusiveProcess

/-- The boundary oscillation bounds the deviation of a harmonic extension from its continued datum. -/
theorem abs_sub_datum_le_of_harmonic_trace
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict W))
    (hbounds : ∀ᵐ x ∂volume.restrict W, lam ≤ a x ∧ a x ≤ Lam)
    (u : H1Function W) (hu : IsWeaklyHarmonicOn a W u)
    (U g : SpatialCoordinates d → ℝ) (hU : ContinuousOn U (closure W))
    (hrep : u.toFun =ᵐ[volume.restrict W] U)
    (htrace : ∀ x ∈ frontier W, U x = g x)
    (D : ℝ) (hOsc : ∀ x ∈ closure W, ∀ y ∈ frontier W, |g y - g x| ≤ D) :
    ∀ x ∈ closure W, |U x - g x| ≤ D := by
  intro x hx
  have hup := le_on_closure_of_harmonic_of_frontier_le hW a lam Lam hlam ha hbounds
    u hu U hU hrep (g x + D) (by
      intro y hy
      rw [htrace y hy]
      have h := (abs_le.mp (hOsc x hx y hy)).2
      linarith only [h]) x hx
  have hneg : (-u).toFun =ᵐ[volume.restrict W] fun y => -U y := by
    filter_upwards [hrep] with y hy
    simp only [H1Function.neg_toFun, hy]
  have hlo := le_on_closure_of_harmonic_of_frontier_le hW a lam Lam hlam ha hbounds
    (-u) (isWeaklyHarmonicOn_neg hu) (fun y => -U y) hU.neg hneg (-g x + D) (by
      intro y hy
      change -U y ≤ -g x + D
      rw [htrace y hy]
      have h := (abs_le.mp (hOsc x hx y hy)).1
      linarith only [h]) x hx
  apply abs_le.mpr
  constructor <;> linarith only [hup, hlo]

end SubdiffusiveProcess
