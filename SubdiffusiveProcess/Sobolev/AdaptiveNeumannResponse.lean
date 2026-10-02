import SubdiffusiveProcess.Sobolev.TriadicPartitionDefect
import SubdiffusiveProcess.Sobolev.PartitionEnergy
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation

/-! # Adaptive partition inequality for the inverse Neumann response

Restrict a root optimizer to each actual cell and subtract its cell average.
The resulting mean-zero competitors retain the restricted gradient. Finite
partition identities then split the unnormalized load and energy exactly.
This proves the dual finite-partition step used in Part A's fold convolution.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- The actual adaptive partition bounds the root inverse Neumann response. -/
theorem triadicAdaptive_affineInverseNeumannResponse_le_sum
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {I : Finset (Fin d)} (hI : I.Nonempty) (J : ℕ)
    (hN0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖)
    (hN : ∀ n (k : OddGridIndex d (triadicHalf n)), ∃ K : ℝ≥0,
      ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf n) k),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf n) k)).1‖ ≤
          K * ‖subspaceGradient
            (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf n) k)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr)) (p : Fin d → ℝ) :
    affineInverseNeumannResponse hN0 a p ≤
      ∑ t ∈ triadicAdaptiveLabels I J,
        affineInverseNeumannResponse
          (triadicAdaptiveCell_meanZeroPoincare z hr hN J t)
          (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) a) p := by
  let Ω := centeredCube z r hr
  let S := triadicAdaptiveLabels I J
  let q : TriadicAdaptiveIndex d J → Opens (SpatialCoordinates d) :=
    triadicAdaptiveCell z r hr J
  let hq : ∀ t, q t ≤ Ω := fun t => triadicAdaptiveCell_subset_root z hr J t
  let hroot := affineInverseNeumannResponse_isGreatest hN0 a p
  rcases hroot.1 with ⟨u, hu⟩
  have huweak : (u.val : SobolevData Ω) ∈ weakSobolevGraph Ω :=
    (mem_meanZeroSobolevGraph_iff u.val).mp u.property |>.1
  let uw : weakSobolevGraph Ω := ⟨u.val, huweak⟩
  let w : ∀ t, weakSobolevGraph (q t) := fun t =>
    ⟨sobolevDataRestrict (hq t) uw.val,
      sobolevDataRestrict_mem_weak (hq t) uw.property⟩
  let v : ∀ t, meanZeroSobolevGraph (q t) := fun t =>
    meanZeroSobolevRepresentative (triadicAdaptiveCell_isBounded z hr J t)
      (triadicAdaptiveCell_volume_pos z hr J t).ne' (w t)
  have hvgrad (t : TriadicAdaptiveIndex d J) :
      subspaceGradient (meanZeroSobolevGraph (q t)) (v t) =
        domainGradientRestrict (hq t) (sobolevGradient uw.val) := by
    dsimp [v, w]
    rw [meanZeroSobolevRepresentative_gradient]
    rfl
  have hloc (t : TriadicAdaptiveIndex d J) :
      2 * (∑ i : Fin d, ∫ x in (q t : Set (SpatialCoordinates d)),
          p i * (v t : SobolevData (q t)).2 i x) -
        ∑ i : Fin d, ∫ x in (q t : Set (SpatialCoordinates d)),
          (positiveCoefficientRestrict (hq t) a).val x *
            ((v t : SobolevData (q t)).2 i x * (v t : SobolevData (q t)).2 i x) ≤
      affineInverseNeumannResponse
        (triadicAdaptiveCell_meanZeroPoincare z hr hN J t)
        (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) a) p := by
    have hg := affineInverseNeumannResponse_isGreatest
      (triadicAdaptiveCell_meanZeroPoincare z hr hN J t)
      (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) a) p
    have hh := hg.2 (Set.mem_range_self (v t))
    simpa [q, hq] using hh
  have hload_restrict (t : TriadicAdaptiveIndex d J) (i : Fin d) :
      (∫ x in (q t : Set (SpatialCoordinates d)),
        p i * (domainGradientRestrict (hq t) (sobolevGradient uw.val)) i x) =
      ∫ x in (q t : Set (SpatialCoordinates d)),
        p i * (sobolevGradient uw.val) i x := by
    apply integral_congr_ae
    filter_upwards [domainGradientRestrict_coeFn (hq t) (sobolevGradient uw.val) i]
      with x hx
    rw [hx]
  have hload :
      (∑ t ∈ S, ∑ i : Fin d, ∫ x in (q t : Set (SpatialCoordinates d)),
        p i * (v t : SobolevData (q t)).2 i x) =
      ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        p i * (u : SobolevData Ω).2 i x := by
    simp_rw [show ∀ t, (v t : SobolevData (q t)).2 =
      domainGradientRestrict (hq t) (sobolevGradient uw.val) from fun t => by
        rw [← hvgrad t]
        rfl]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∑ t ∈ S, ∫ x in (q t : Set (SpatialCoordinates d)),
          p i * (domainGradientRestrict (hq t) (sobolevGradient uw.val)) i x) =
          ∑ t ∈ S, ∫ x in (q t : Set (SpatialCoordinates d)),
            p i * (sobolevGradient uw.val) i x := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hload_restrict t i
      _ = ∫ x in (Ω : Set (SpatialCoordinates d)),
          p i * (sobolevGradient uw.val) i x := by
        simpa [S, q, Ω] using
          (integral_triadicAdaptiveCells z hr hI J
            (f := fun x => p i * (sobolevGradient uw.val) i x)
            (((Lp.memLp ((sobolevGradient uw.val) i)).integrable (by norm_num)).const_mul _))
      _ = ∫ x in (Ω : Set (SpatialCoordinates d)),
          p i * (u : SobolevData Ω).2 i x := by
        rfl
  have henergy :
      (∑ t ∈ S, ∑ i : Fin d, ∫ x in (q t : Set (SpatialCoordinates d)),
        (positiveCoefficientRestrict (hq t) a).val x *
          ((v t : SobolevData (q t)).2 i x * (v t : SobolevData (q t)).2 i x)) =
      ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        a.val x * ((u : SobolevData Ω).2 i x * (u : SobolevData Ω).2 i x) := by
    have hform := weightedGradientForm_triadicAdaptiveCells z hr hI J a
      (sobolevGradient uw.val) (sobolevGradient uw.val)
    calc
      _ = ∑ t ∈ S,
          weightedGradientForm (positiveCoefficientRestrict (hq t) a).val
            (subspaceGradient (meanZeroSobolevGraph (q t)) (v t))
            (subspaceGradient (meanZeroSobolevGraph (q t)) (v t)) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [weightedGradientForm_apply]
        rfl
      _ = ∑ t ∈ S,
          weightedGradientForm (positiveCoefficientRestrict (hq t) a).val
            (domainGradientRestrict (hq t) (sobolevGradient uw.val))
            (domainGradientRestrict (hq t) (sobolevGradient uw.val)) := by
        simp_rw [hvgrad]
      _ = weightedGradientForm a.val (sobolevGradient uw.val)
          (sobolevGradient uw.val) := by
        simpa [S, q, hq] using hform
      _ = _ := by
        rw [weightedGradientForm_apply]
        rfl
  have hsum :
      (∑ t ∈ S,
        (2 * (∑ i : Fin d, ∫ x in (q t : Set (SpatialCoordinates d)),
            p i * (v t : SobolevData (q t)).2 i x) -
          ∑ i : Fin d, ∫ x in (q t : Set (SpatialCoordinates d)),
            (positiveCoefficientRestrict (hq t) a).val x *
              ((v t : SobolevData (q t)).2 i x * (v t : SobolevData (q t)).2 i x))) =
      2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          p i * (u : SobolevData Ω).2 i x) -
        ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * ((u : SobolevData Ω).2 i x * (u : SobolevData Ω).2 i x) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hload, henergy]
  calc
    affineInverseNeumannResponse hN0 a p =
        2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          p i * (u : SobolevData Ω).2 i x) -
          ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            a.val x * ((u : SobolevData Ω).2 i x * (u : SobolevData Ω).2 i x) := by
      simpa [Ω] using hu.symm
    _ = ∑ t ∈ S,
        (2 * (∑ i : Fin d, ∫ x in (q t : Set (SpatialCoordinates d)),
            p i * (v t : SobolevData (q t)).2 i x) -
          ∑ i : Fin d, ∫ x in (q t : Set (SpatialCoordinates d)),
            (positiveCoefficientRestrict (hq t) a).val x *
              ((v t : SobolevData (q t)).2 i x * (v t : SobolevData (q t)).2 i x)) := hsum.symm
    _ ≤ ∑ t ∈ S,
        affineInverseNeumannResponse
          (triadicAdaptiveCell_meanZeroPoincare z hr hN J t)
          (positiveCoefficientRestrict (triadicAdaptiveCell_subset_root z hr J t) a) p := by
      exact Finset.sum_le_sum (fun t ht => hloc t)
    _ = _ := by rfl

end SubdiffusiveProcess
