import SubdiffusiveProcess.Analysis.GlobalTriadicAverageBound
import SubdiffusiveProcess.Analysis.TriadicGrowthCoefficient
import Mathlib

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

theorem globalTriadicAverages_summable_increment_eLpNorm_of_finite_kernel
    {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hroot : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Q))
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (ν : Measure (SpatialCoordinates d)) (hν : IsFiniteMeasure ν)
    (hsupp : ν (closure (Homogenization.openCubeSet Q))ᶜ = 0)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Q), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2 (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hI : (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal ((f y - f x) ^ 2) /
                (ENNReal.ofReal
                  (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1)) ≠ ⊤) :
  let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  Summable (fun n : ℕ => (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal) := by
  let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  change Summable (fun n : ℕ =>
    (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal)
  let I : ℝ≥0∞ := ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal ((f y - f x) ^ 2) /
                (ENNReal.ofReal
                  (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1)
  let a : ℕ → ℝ := fun n => Real.sqrt
      ((((r / (3 : ℝ) ^ n) / 3) ^ t) *
        ((((r / (3 : ℝ) ^ n) / 3) ^ d) *
          ((r / (3 : ℝ) ^ n) ^ d))⁻¹ *
        (Real.sqrt (d : ℝ) * (r / (3 : ℝ) ^ n)) ^ ((d : ℝ) + 1))
  have hcoef : Summable a := by
    simpa [a] using (summable_triadicGrowthCoefficients hd r t hr ht)
  let C : ℝ := Real.sqrt ((K + ν.real Set.univ) * I.toReal)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound : ∀ n : ℕ,
      (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal ≤ C * a n := by
    intro n
    let Δ : SpatialCoordinates d → ℝ := fun x => E (n + 1) x - E n x
    have hinc := globalTriadicAverages_memLp_and_increment_bound
      hd Q z hr hroot K t hK ht n ν hν hsupp hgrowth f hf
    dsimp only at hinc
    have hmem : MemLp Δ 2 ν := by
      simpa [Δ, E] using hinc.2.1
    have hsq := hinc.2.2
    have hden : 2 * (triadicHalf n : ℝ) + 1 = (3 : ℝ) ^ n :=
      triadic_denominator n
    have hell : r / (2 * (triadicHalf n : ℝ) + 1) = r / (3 : ℝ) ^ n := by
      rw [hden]
    have hsq' : eLpNorm Δ 2 ν ^ (2 : ℕ) ≤
        ENNReal.ofReal ((K + ν.real Set.univ) *
          (((r / (3 : ℝ) ^ n) / 3) ^ t) *
            ((((r / (3 : ℝ) ^ n) / 3) ^ d) *
              ((r / (3 : ℝ) ^ n) ^ d))⁻¹) *
          (ENNReal.ofReal (Real.sqrt d * (r / (3 : ℝ) ^ n))) ^ ((d : ℝ) + 1) * I := by
      simpa [I, hell] using hsq
    let R : ℝ≥0∞ := ENNReal.ofReal ((K + ν.real Set.univ) *
          (((r / (3 : ℝ) ^ n) / 3) ^ t) *
            ((((r / (3 : ℝ) ^ n) / 3) ^ d) *
              ((r / (3 : ℝ) ^ n) ^ d))⁻¹) *
          (ENNReal.ofReal (Real.sqrt d * (r / (3 : ℝ) ^ n))) ^ ((d : ℝ) + 1)
    have hsqR : eLpNorm Δ 2 ν ^ (2 : ℕ) ≤ R * I := by
      simpa [R] using hsq'
    have hRtop : R * I ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · simp
        · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (by finiteness)
      · exact hI
    have hsqreal : (eLpNorm Δ 2 ν).toReal ^ (2 : ℕ) ≤ (R * I).toReal := by
      rw [← ENNReal.toReal_pow]
      exact (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top hmem.2.ne) hRtop).mpr hsqR
    have hsqrt : (eLpNorm Δ 2 ν).toReal ≤ Real.sqrt (R * I).toReal := by
      exact Real.le_sqrt_of_sq_le hsqreal
    have hRreal : (R * I).toReal =
        ((K + ν.real Set.univ) * I.toReal) * (a n) ^ (2 : ℕ) := by
      dsimp [R, a]
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal]
      rw [Real.sq_sqrt (by positivity)]
      · ring
      · positivity
      · positivity
    calc
      (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal =
          (eLpNorm Δ 2 ν).toReal := by rfl
      _ ≤ Real.sqrt (R * I).toReal := hsqrt
      _ = C * a n := by
        rw [hRreal, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Summable.of_nonneg_of_le
    (fun n => ENNReal.toReal_nonneg) hbound
    (hcoef.mul_left C)

end SubdiffusiveProcess
