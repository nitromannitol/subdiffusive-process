import SubdiffusiveProcess.Analysis.FractionalCellVariance
import SubdiffusiveProcess.Analysis.GlobalTriadicAverages
import SubdiffusiveProcess.Geometry.OddGridPartition
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory Filter Set TopologicalSpace Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- Indicators of the actual grid cells in the parent L2 space. -/
def cubeCellBasis {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (m : ℕ) (k : OddGridIndex d m) : DomainL2 (centeredCube z r hr) :=
  indicatorConstLp 2 (oddGridCell z r hr m k).isOpen.measurableSet
    (measure_ne_top (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) _)
    (1 : ℝ)

/-- The finite sum reconstructing a grid-constant L2 function from its cell values. -/
def cubeCellReconstruct {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (m : ℕ) (c : OddGridIndex d m → ℝ) : DomainL2 (centeredCube z r hr) :=
  ∑ k, c k • cubeCellBasis z r hr m k

/-- The averaging approximation on the actual equal-volume cube grid. -/
def cubeCellProjection {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (m : ℕ) (f : DomainL2 (centeredCube z r hr)) : DomainL2 (centeredCube z r hr) :=
  cubeCellReconstruct z r hr m (fun k => averageOn
    (oddGridCell z r hr m k : Set (SpatialCoordinates d)) f)

theorem cubeCellReconstruct_coeFn {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (m : ℕ) (c : OddGridIndex d m → ℝ) :
    (cubeCellReconstruct z r hr m c : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => ∑ k, (oddGridCell z r hr m k : Set (SpatialCoordinates d)).indicator
        (fun _ => c k) x := by
  classical
  have hsum : ∀ t : Finset (OddGridIndex d m),
      (∑ k ∈ t, c k • cubeCellBasis z r hr m k : DomainL2 (centeredCube z r hr))
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => ∑ k ∈ t, (oddGridCell z r hr m k : Set (SpatialCoordinates d)).indicator
          (fun _ => c k) x := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (Lp.coeFn_zero ℝ 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    | @insert k t hk ih =>
      simp only [Finset.sum_insert hk]
      filter_upwards [Lp.coeFn_add (c k • cubeCellBasis z r hr m k)
          (∑ j ∈ t, c j • cubeCellBasis z r hr m j),
        Lp.coeFn_smul (c k) (cubeCellBasis z r hr m k),
        indicatorConstLp_coeFn (p := 2) (hs := (oddGridCell z r hr m k).isOpen.measurableSet)
          (hμs := measure_ne_top (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) _)
          (c := (1 : ℝ)), ih] with x hadd hsmul hind ht
      change (cubeCellBasis z r hr m k : SpatialCoordinates d → ℝ) x =
        (oddGridCell z r hr m k : Set (SpatialCoordinates d)).indicator (fun _ => (1 : ℝ)) x at hind
      rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hind, ht]
      by_cases hx : x ∈ (oddGridCell z r hr m k : Set (SpatialCoordinates d))
      · simp only [Set.indicator_of_mem hx, mul_one]
      · simp only [Set.indicator_of_notMem hx, mul_zero]
  exact hsum Finset.univ

theorem cubeCellProjection_coeFn_on_cell {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (m : ℕ) (f : DomainL2 (centeredCube z r hr))
    (k : OddGridIndex d m) :
    (cubeCellProjection z r hr m f : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (oddGridCell z r hr m k : Set (SpatialCoordinates d))]
      fun _ => averageOn (oddGridCell z r hr m k : Set (SpatialCoordinates d)) f := by
  have hrep := cubeCellReconstruct_coeFn z r hr m
    (fun j => averageOn (oddGridCell z r hr m j : Set (SpatialCoordinates d)) f)
  have hsub := oddGridCell_subset z hr m k
  have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hrep
  filter_upwards [hae, self_mem_ae_restrict (oddGridCell z r hr m k).isOpen.measurableSet]
    with x hx hxcell
  exact hx.trans (sum_indicator_triadicCell_eq z hr m x _ k hxcell)

/-- Each fixed grid sends an L2-bounded sequence into a totally bounded range. -/
theorem totallyBounded_range_cubeCellProjection {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (m : ℕ)
    (f : ℕ → DomainL2 (centeredCube z r hr)) (R : ℝ)
    (hR : ∀ n, ‖f n‖ ≤ R) :
    TotallyBounded (range (fun n => cubeCellProjection z r hr m (f n))) := by
  classical
  let q : OddGridIndex d m → Set (SpatialCoordinates d) := fun k => oddGridCell z r hr m k
  let vol : ℝ := (r / (2 * (m : ℝ) + 1)) ^ d
  have hvol : 0 < vol := pow_pos (div_pos hr (by positivity)) d
  have havg (n : ℕ) (k : OddGridIndex d m) :
      averageOn (q k) (f n) = inner ℝ (cubeCellBasis z r hr m k) (f n) / vol := by
    have hinner : inner ℝ (cubeCellBasis z r hr m k) (f n) = ∫ x in q k, f n x := by
      rw [cubeCellBasis, L2.inner_indicatorConstLp_one]
      rw [Measure.restrict_restrict (oddGridCell z r hr m k).isOpen.measurableSet,
        inter_eq_left.mpr (oddGridCell_subset z hr m k)]
    rw [hinner, div_eq_inv_mul]
    unfold averageOn volumeAverage
    rw [show (volume (q k)).toReal = vol from oddGridCell_volume_real z hr m k]
  let C : ℝ := ∑ k : OddGridIndex d m, ‖cubeCellBasis z r hr m k‖ / vol
  have hC (k : OddGridIndex d m) : ‖cubeCellBasis z r hr m k‖ / vol ≤ C :=
    Finset.single_le_sum (fun j _ => div_nonneg (norm_nonneg _) hvol.le) (Finset.mem_univ k)
  have hR0 : 0 ≤ R := (norm_nonneg (f 0)).trans (hR 0)
  have hcoeff (n : ℕ) (k : OddGridIndex d m) : |averageOn (q k) (f n)| ≤ C * R := by
    rw [havg, abs_div, abs_of_pos hvol]
    calc
      |inner ℝ (cubeCellBasis z r hr m k) (f n)| / vol ≤
          (‖cubeCellBasis z r hr m k‖ * ‖f n‖) / vol :=
        div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) hvol.le
      _ = (‖cubeCellBasis z r hr m k‖ / vol) * ‖f n‖ := by ring
      _ ≤ (‖cubeCellBasis z r hr m k‖ / vol) * R :=
        mul_le_mul_of_nonneg_left (hR n) (div_nonneg (norm_nonneg _) hvol.le)
      _ ≤ C * R := mul_le_mul_of_nonneg_right (hC k) hR0
  have hcont : Continuous (cubeCellReconstruct z r hr m) := by
    apply continuous_finset_sum
    intro k hk
    exact (continuous_apply k).smul continuous_const
  have hcompact := (isCompact_closedBall (0 : OddGridIndex d m → ℝ) (C * R)).image hcont
  apply hcompact.totallyBounded.subset
  rintro _ ⟨n, rfl⟩
  refine ⟨fun k => averageOn (q k) (f n), ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg
    (Finset.sum_nonneg (fun k _ => div_nonneg (norm_nonneg _) hvol.le)) hR0)).mpr
  intro k
  exact hcoeff n k

end SubdiffusiveProcess
