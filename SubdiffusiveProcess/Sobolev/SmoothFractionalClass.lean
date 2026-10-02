import SubdiffusiveProcess.Sobolev.ContDiffFractionalL2
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal ContDiff
namespace SubdiffusiveProcess

/-- A smooth representative gives finite fractional seminorm for its actual L2 classes; zero class is exactly zero restriction on the cube. Supplies the smooth test carrier in M, lines 988–1037. -/
theorem smoothRepresentative_cube_fractional_finite_and_zero
    {d k : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (O : Opens (SpatialCoordinates d))
    (hO : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ O)
    (f : SpatialCoordinates d → Fin k → ℝ)
    (hf : ContDiffOn ℝ ∞ f (O : Set (SpatialCoordinates d)))
    (u : Fin k → DomainL2 (centeredCube z r hr))
    (hu : ∀ i : Fin k, (u i : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (fun x => f x i))
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    (((ENNReal.ofReal s / volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (∑ i : Fin k, (u i x - u i y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * s)) ^ (1 / 2 : ℝ) < ⊤) ∧
    (u = 0 ↔ ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x = 0) := by
  obtain ⟨hmem, hfinite⟩ :=
    contDiffOn_cube_fractional_L2 hd z r hr O hO f hf s hs hs1
  have heq (i : Fin k) : (hmem i).toLp (fun x => f x i) = u i := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp (hmem i)).trans (hu i).symm
  constructor
  · simpa only [heq] using hfinite
  · constructor
    · intro huzero
      have hcoord (i : Fin k) :
          ContinuousOn (fun x => f x i)
            (centeredCube z r hr : Set (SpatialCoordinates d)) :=
        ((continuous_apply i).comp_continuousOn hf.continuousOn).mono
          (fun _ hx => hO (subset_closure hx))
      intro x hx
      funext i
      have hui : u i = 0 := congr_fun huzero i
      have hae : (fun x => f x i) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          (0 : SpatialCoordinates d → ℝ) := by
        have hz : (u i : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
            (0 : SpatialCoordinates d → ℝ) := by
          rw [hui]
          exact Lp.coeFn_zero ℝ 2
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
        exact (hu i).symm.trans hz
      exact Measure.eqOn_open_of_ae_eq hae (centeredCube z r hr).isOpen
        (hcoord i) continuousOn_const hx
    · intro hfzero
      funext i
      apply Lp.ext
      filter_upwards [hu i, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet,
        Lp.coeFn_zero ℝ 2
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))] with x hux hx hz
      exact hux.trans ((congr_fun (hfzero x hx) i).trans hz.symm)

end SubdiffusiveProcess
