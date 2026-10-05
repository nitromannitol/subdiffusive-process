module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ResponseTruncation
public import Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingAggregation
public import Homogenization.Book.Ch05.Theorems.Section52.GeometrySeries.DescendantCardinality

@[expose] public section

/-!
# Descendant-energy partition for the Dirichlet coarse-graining call

At `p = 2`, every physical-scale descendant average of the local symmetric
energy is exactly the parent normalized energy.  Consequently the full
weighted aggregation is just the square root of one scalar geometric series
times the parent energy.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open scoped BigOperators ENNReal

noncomputable section

/-- Exact partition of the squared local symmetric energy at one admissible
physical descendant scale. -/
theorem descendantsAtScaleENNAverage_localSymmetricEnergyENorm_sq_eq
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) :
    ((descendantsAtScale Q k).card : ℝ≥0∞)⁻¹ *
        (descendantsAtScale Q k).attach.sum (fun R =>
        (localSymmetricEnergyENorm R.1
          (a.restrictToSubcube
            (openCubeSet_subset_of_mem_descendantsAtScale hk R.2))
          (restrictH1ToSubcube u
            (openCubeSet_subset_of_mem_descendantsAtScale hk R.2))) ^ (2 : ℕ)) =
      (localSymmetricEnergyENorm Q a u) ^ (2 : ℕ) := by
  classical
  let j := Int.toNat (Q.scale - k)
  let f : Vec d → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    (vecDot (u.grad x) (matVecMul (symmPart (a.toCoeffField x)) (u.grad x)))
  have hlocal : ∀ R : {R : TriadicCube d // R ∈ descendantsAtScale Q k},
      (localSymmetricEnergyENorm R.1
          (a.restrictToSubcube
            (openCubeSet_subset_of_mem_descendantsAtScale hk R.2))
          (restrictH1ToSubcube u
            (openCubeSet_subset_of_mem_descendantsAtScale hk R.2))) ^ (2 : ℕ) =
        ∫⁻ x, f x ∂normalizedCubeMeasure R.1 := by
    intro R
    unfold localSymmetricEnergyENorm
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
    apply lintegral_congr
    intro x
    rfl
  have hscale : (descendantsAtScale Q k) = descendantsAtDepth Q j :=
    descendantsAtScale_eq_descendantsAtDepth Q hk
  have hparent : (localSymmetricEnergyENorm Q a u) ^ (2 : ℕ) =
      ∫⁻ x, f x ∂normalizedCubeMeasure Q := by
    unfold localSymmetricEnergyENorm
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
    rfl
  calc
    ((descendantsAtScale Q k).card : ℝ≥0∞)⁻¹ *
          (descendantsAtScale Q k).attach.sum (fun R =>
            (localSymmetricEnergyENorm R.1
              (a.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtScale hk R.2))
              (restrictH1ToSubcube u
                (openCubeSet_subset_of_mem_descendantsAtScale hk R.2))) ^ (2 : ℕ)) =
        ((descendantsAtScale Q k).card : ℝ≥0∞)⁻¹ *
          ∑ R ∈ descendantsAtScale Q k, ∫⁻ x, f x ∂normalizedCubeMeasure R := by
      congr 1
      calc
        (descendantsAtScale Q k).attach.sum (fun R =>
            (localSymmetricEnergyENorm R.1
              (a.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtScale hk R.2))
              (restrictH1ToSubcube u
                (openCubeSet_subset_of_mem_descendantsAtScale hk R.2))) ^ (2 : ℕ)) =
            (descendantsAtScale Q k).attach.sum (fun R =>
              ∫⁻ x, f x ∂normalizedCubeMeasure R.1) := by
                apply Finset.sum_congr rfl
                intro R _
                exact hlocal R
        _ = ∑ R ∈ descendantsAtScale Q k,
              ∫⁻ x, f x ∂normalizedCubeMeasure R := by
                simpa using Finset.sum_attach
                  (s := descendantsAtScale Q k)
                  (f := fun R => ∫⁻ x, f x ∂normalizedCubeMeasure R)
    _ = descendantsENNAverage Q j
        (fun R => ∫⁻ x, f x ∂normalizedCubeMeasure R) := by
      unfold descendantsENNAverage
      rw [← hscale]
    _ = ∫⁻ x, f x ∂normalizedCubeMeasure Q :=
      descendantsENNAverage_lintegral_normalizedCubeMeasure_eq Q j f
    _ = (localSymmetricEnergyENorm Q a u) ^ (2 : ℕ) := hparent.symm

/-- Exact `p=2` evaluation of the weighted local symmetric-energy carrier. -/
theorem weightedLocalSymmetricEnergyLp_two_sq_eq
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (n : ℤ)
    (hn : n ≤ Q.scale) (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) (s1 s : FractionalOrder)
    (hgap : 0 < s.1 - s1.1) :
    (weightedLocalSymmetricEnergyLp Q n hn a u s1 s
        FiniteLpExponent.two) ^ (2 : ℕ) =
      ENNReal.ofReal
          ((Ch02.geometricDiscount (2 * (s.1 - s1.1)) 1)⁻¹) *
        (localSymmetricEnergyENorm Q a u) ^ (2 : ℕ) := by
  have hweighted := weightedLocalSymmetricEnergyLp_rpow_eq_tsum
    Q n hn a u s1 s FiniteLpExponent.two
  norm_num at hweighted
  rw [show (weightedLocalSymmetricEnergyLp Q n hn a u s1 s
      FiniteLpExponent.two) ^ (2 : ℕ) = _ by
        simpa only [ENNReal.rpow_natCast] using hweighted]
  have hterm : ∀ j : ℕ,
      ((descendantsAtScale Q (n - (j : ℤ))).card : ℝ≥0∞)⁻¹ *
          (descendantsAtScale Q (n - (j : ℤ))).attach.sum (fun R =>
            (localSymmetricEnergyENorm R.1
              (a.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
              (restrictH1ToSubcube u
                (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^
              (2 : ℕ)) = (localSymmetricEnergyENorm Q a u) ^ (2 : ℕ) := by
    intro j
    exact descendantsAtScaleENNAverage_localSymmetricEnergyENorm_sq_eq Q
      (k := n - (j : ℤ)) (by omega) a u
  calc
    (∑' j : ℕ,
        ENNReal.ofReal (Real.rpow 3 (-((s.1 - s1.1) * 2 * (j : ℝ)))) *
          ((descendantsAtScale Q (n - (j : ℤ))).card : ℝ≥0∞)⁻¹ *
            (descendantsAtScale Q (n - (j : ℤ))).attach.sum (fun R =>
              (localSymmetricEnergyENorm R.1
                (a.restrictToSubcube
                  (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
                (restrictH1ToSubcube u
                  (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^
                (2 : ℕ))) =
        ∑' j : ℕ,
          ENNReal.ofReal (Real.rpow 3 (-((s.1 - s1.1) * 2 * (j : ℝ)))) *
            (localSymmetricEnergyENorm Q a u) ^ (2 : ℕ) := by
      apply tsum_congr
      intro j
      rw [mul_assoc]
      congr 1
      convert hterm j using 1
    _ = ENNReal.ofReal
          ((Ch02.geometricDiscount (2 * (s.1 - s1.1)) 1)⁻¹) *
        (localSymmetricEnergyENorm Q a u) ^ (2 : ℕ) := by
      rw [ENNReal.tsum_mul_right]
      congr 1
      have hseries :
          (∑' j : ℕ, Real.rpow 3 (-(2 * (s.1 - s1.1)) * (j : ℝ))) =
            (Ch02.geometricDiscount (2 * (s.1 - s1.1)) 1)⁻¹ :=
        Homogenization.Book.Ch05.Section52.tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount
          (show 0 < 2 * (s.1 - s1.1) by positivity)
      have hsummable :=
        Homogenization.Book.Ch05.Section52.summable_rpow_three_neg_mul_nat
          (show 0 < 2 * (s.1 - s1.1) by positivity)
      calc
        (∑' j : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-((s.1 - s1.1) * 2 * (j : ℝ))))) =
            ∑' j : ℕ,
              ENNReal.ofReal (Real.rpow 3 (-(2 * (s.1 - s1.1)) * (j : ℝ))) := by
                apply tsum_congr
                intro j
                congr 1
                ring_nf
        _ = ENNReal.ofReal
              (∑' j : ℕ, Real.rpow 3 (-(2 * (s.1 - s1.1)) * (j : ℝ))) :=
          (ENNReal.ofReal_tsum_of_nonneg
            (fun j ↦ Real.rpow_nonneg (by norm_num) _) hsummable).symm
        _ = ENNReal.ofReal
              ((Ch02.geometricDiscount (2 * (s.1 - s1.1)) 1)⁻¹) := by
                rw [hseries]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
