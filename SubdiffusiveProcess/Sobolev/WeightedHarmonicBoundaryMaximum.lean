import SubdiffusiveProcess.Sobolev.HarmonicBoundaryMaximum
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.CoarseGrainingVocab.Section6MeasurableMaxPrinciple
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BoundaryDataStability

/-! Frontier bounds for continuous harmonic functions with a scalar elliptic coefficient.
The comparison constant is independent of the ellipticity ratio; this module
does not construct harmonic solutions or a limit form.
-/

open Filter MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology

namespace SubdiffusiveProcess

/-- A continuous scalar elliptic harmonic representative is bounded above by its frontier values. -/
theorem le_on_closure_of_harmonic_of_frontier_le
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict W))
    (hbounds : ∀ᵐ x ∂volume.restrict W, lam ≤ a x ∧ a x ≤ Lam)
    (u : H1Function W) (hu : IsWeaklyHarmonicOn a W u)
    (U : SpatialCoordinates d → ℝ) (hU : ContinuousOn U (closure W))
    (hrep : u.toFun =ᵐ[volume.restrict W] U)
    (M : ℝ) (hbd : ∀ x ∈ frontier W, U x ≤ M) :
    ∀ x ∈ closure W, U x ≤ M := by
  intro x hx
  apply le_of_forall_pos_le_add
  intro eps heps
  have hb := hasBoundaryUpperBoundOn_of_continuous_frontier_lt hW u U hU hrep (M + eps)
    (fun y hy => lt_of_le_of_lt (hbd y hy) (lt_add_of_pos_right M heps))
  have hae : ∀ᵐ y ∂volume.restrict W, U y ≤ M + eps := by
    filter_upwards [ae_le_of_isWeaklyHarmonicOn hW hlam ha hbounds hu hb, hrep] with y hy hry
    exact hry ▸ hy
  exact le_on_closure_of_continuousOn_of_ae_le hW.isOpen U hU (M + eps) hae x hx

/-- An absolute frontier bound controls a continuous scalar elliptic harmonic representative. -/
theorem abs_le_on_closure_of_harmonic_of_frontier_le
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ) (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict W))
    (hbounds : ∀ᵐ x ∂volume.restrict W, lam ≤ a x ∧ a x ≤ Lam)
    (u : H1Function W) (hu : IsWeaklyHarmonicOn a W u)
    (U : SpatialCoordinates d → ℝ) (hU : ContinuousOn U (closure W))
    (hrep : u.toFun =ᵐ[volume.restrict W] U)
    (M : ℝ) (hbd : ∀ x ∈ frontier W, |U x| ≤ M) :
    ∀ x ∈ closure W, |U x| ≤ M := by
  have hup := le_on_closure_of_harmonic_of_frontier_le hW a lam Lam hlam ha hbounds
    u hu U hU hrep M (fun x hx => (abs_le.mp (hbd x hx)).2)
  have hrepneg : (-u).toFun =ᵐ[volume.restrict W] fun x => -U x := by
    filter_upwards [hrep] with x hx
    simp only [H1Function.neg_toFun, hx]
  have hlow := le_on_closure_of_harmonic_of_frontier_le hW a lam Lam hlam ha hbounds
    (-u) (isWeaklyHarmonicOn_neg hu) (fun x => -U x) hU.neg hrepneg M
    (fun x hx => neg_le.mpr (abs_le.mp (hbd x hx)).1)
  intro x hx
  exact abs_le.mpr ⟨neg_le.mp (hlow x hx), hup x hx⟩

/-- Equal-coefficient harmonic representatives satisfy a frontier difference bound throughout the closure. -/
theorem abs_sub_le_on_closure_of_harmonic_of_frontier_le
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W)
    (a : SpatialCoordinates d → ℝ) (ha : Measurable a)
    (lam Lam : ℝ) (hlam : 0 < lam)
    (hbounds : ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam)
    (u v : H1Function W) (hu : IsWeaklyHarmonicOn a W u) (hv : IsWeaklyHarmonicOn a W v)
    (U V : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure W)) (hV : ContinuousOn V (closure W))
    (hurep : u.toFun =ᵐ[volume.restrict W] U) (hvrep : v.toFun =ᵐ[volume.restrict W] V)
    (M : ℝ) (hbd : ∀ x ∈ frontier W, |U x - V x| ≤ M) :
    ∀ x ∈ closure W, |U x - V x| ≤ M := by
  have hEll := lane2_isEllipticFieldOn_scalar hW.isOpen.measurableSet ha hlam hbounds
  have hdiff := Section6Dirichlet.isWeaklyHarmonicOn_sub hEll hu hv
  have hrep : (u - v).toFun =ᵐ[volume.restrict W] fun x => U x - V x := by
    filter_upwards [hurep, hvrep] with x hx hy
    simp only [H1Function.sub_toFun, hx, hy]
  have hb : ∀ᵐ x ∂volume.restrict W, lam ≤ a x ∧ a x ≤ Lam := by
    filter_upwards [self_mem_ae_restrict hW.isOpen.measurableSet] with x hx
    exact hbounds x hx
  exact abs_le_on_closure_of_harmonic_of_frontier_le hW a lam Lam hlam
    ha.aestronglyMeasurable hb (u - v) hdiff (fun x => U x - V x) (hU.sub hV) hrep M hbd

end SubdiffusiveProcess
