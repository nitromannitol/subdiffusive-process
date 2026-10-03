module

public import SubdiffusiveProcess.Analysis.GlobalTriadicIncrement
public import SubdiffusiveProcess.Analysis.GlobalTriadicAverages
public import SubdiffusiveProcess.Geometry.GrowthBoundary

@[expose] public section

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section

namespace SubdiffusiveProcess

theorem globalTriadicAverages_memLp_and_increment_bound
    {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hroot : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Q))
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (n : ℕ) (ν : Measure (SpatialCoordinates d)) (hν : IsFiniteMeasure ν)
    (hsupp : ν (closure (Homogenization.openCubeSet Q))ᶜ = 0)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Q), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2 (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)))) :
  let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  let ell : ℝ := r / (2 * (triadicHalf n : ℝ) + 1)
  let Δ : SpatialCoordinates d → ℝ := fun x => E (n + 1) x - E n x
  (∀ m : ℕ, MemLp (E m) 2 ν) ∧ MemLp Δ 2 ν ∧
    eLpNorm Δ 2 ν ^ (2 : ℕ) ≤
      ENNReal.ofReal
          (((K + ν.real Set.univ) * (ell / 3) ^ t) *
            (((ell / 3) ^ d) * (ell ^ d))⁻¹) *
        (ENNReal.ofReal (Real.sqrt d * ell)) ^ ((d : ℝ) + 1) *
          (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal ((f y - f x) ^ 2) /
                (ENNReal.ofReal
                  (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1)) := by
  letI := hν
  dsimp only
  let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  let ell : ℝ := r / (2 * (triadicHalf n : ℝ) + 1)
  let Δ : SpatialCoordinates d → ℝ := fun x => E (n + 1) x - E n x
  change (∀ m : ℕ, MemLp (E m) 2 ν) ∧ MemLp Δ 2 ν ∧
    eLpNorm Δ 2 ν ^ (2 : ℕ) ≤
      ENNReal.ofReal
          (((K + ν.real Set.univ) * (ell / 3) ^ t) *
            (((ell / 3) ^ d) * (ell ^ d))⁻¹) *
        (ENNReal.ofReal (Real.sqrt d * ell)) ^ ((d : ℝ) + 1) *
          (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal ((f y - f x) ^ 2) /
                (ENNReal.ofReal
                  (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1))
  have hE : ∀ m : ℕ, MemLp (E m) 2 ν := by
    intro m
    dsimp [E]
    apply memLp_finset_sum
    intro k hk
    apply memLp_indicator_const
    · exact (oddGridCell z r hr (triadicHalf m) k).isOpen.measurableSet
    · exact Or.inr (by finiteness)
  have hplanes : ∀ (i : Fin d) (c : ℝ), ν {x | x i = c} = 0 :=
    (growth_cube_boundary_noAtoms hd Q ν hν K t hK ht hsupp hgrowth).1
  have haeq : Δ =ᵐ[ν] (fun x =>
      ∑ j : OddGridIndex d (triadicHalf (n + 1)),
        (oddGridCell z r hr (triadicHalf (n + 1)) j : Set (SpatialCoordinates d)).indicator
          (fun _ => averageOn
              (oddGridCell z r hr (triadicHalf (n + 1)) j : Set (SpatialCoordinates d)) f -
            averageOn
              (oddGridCell z r hr (triadicHalf n) (triadicParent n j) :
                Set (SpatialCoordinates d)) f) x) := by
    simpa [E, Δ] using
      (globalTriadicAverages_sub_eq_increment_ae z hr n ν hplanes f)
  have hinc := globalTriadicIncrement_memLp_and_eLpNorm_sq_le_fractionalKernel
    hd Q z hr hroot K t hK ht n ν hν hsupp hgrowth f hf
  dsimp only at hinc
  refine ⟨hE, ?_⟩
  constructor
  · exact (MeasureTheory.memLp_congr_ae haeq).mpr hinc.1
  · rw [MeasureTheory.eLpNorm_congr_ae haeq]
    simpa [ell] using hinc.2

end SubdiffusiveProcess
