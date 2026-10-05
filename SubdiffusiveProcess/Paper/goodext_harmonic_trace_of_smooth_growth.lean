module

public import SubdiffusiveProcess.Paper.goodext_harmonic_trace_compact_continuous
public import SubdiffusiveProcess.Sobolev.SmoothBoundaryApproximation

@[expose] public section

/-! Smooth-data regularity supplies the actual Holder trace minimizer bank.
The energy-response bound is explicit and is not replaced by a regularity premise. -/
open Filter MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Smooth-data growth and a finite response bound produce a subsequentially compact minimizer bank for the exact Holder trace. -/
theorem goodext_harmonic_trace_of_smooth_growth
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (Sob : SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (beta alpha : ℝ) (hbeta : beta ∈ Ioo (1 / 2 : ℝ) 1) (halpha : 0 < alpha)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : ℕ → SpatialCoordinates d → ℝ) (hA : ∀ n, Continuous (A n))
    (haA : ∀ n, (a n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] A n)
    (lam Lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n)
    (hbounds : ∀ n x, x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) →
      lam n ≤ A n x ∧ A n x ≤ Lam n)
    (g : SpatialCoordinates d → ℝ)
    (hgc : ContinuousOn g (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hgh : IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) g)
    (hReg : ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph (centeredCube z r hr)),
        ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] phi) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
          ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer (killedResponseSpace hP) (a n) b).val.1 :
            SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
          IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) V ≤ C)
    (Ebound : ℕ → ℝ)
    (hResponse : ∀ n (b : weakSobolevGraph (centeredCube z r hr))
        (B : SpatialCoordinates d → ℝ),
      ContinuousOn B (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
      ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] B) →
      EqOn B g (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) →
      dirichletResponse (killedResponseSpace hP) (a n) b ≤ Ebound n)
    :
    ∃ (b : weakSobolevGraph (centeredCube z r hr))
      (VN : ℕ → SpatialCoordinates d → ℝ),
      (∀ n, ContinuousOn (VN n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (((dirichletMinimizer (killedResponseSpace hP) (a n) b).val.1 :
          SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] VN n) ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), VN n x = g x) ∧
        dirichletResponse (killedResponseSpace hP) (a n) b ≤ Ebound n) ∧
      ∀ sigma : ℕ → ℕ, StrictMono sigma →
        ∃ (tau : ℕ → ℕ) (V : SpatialCoordinates d → ℝ), StrictMono tau ∧
          ContinuousOn V (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          TendstoUniformlyOn (fun n => VN (sigma (tau n))) V atTop
            (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), V x = g x  := by
  classical
  obtain ⟨b, B, hBc, hBr, hBt⟩ :=
    aux_candidate_holder_harmonic_extension_datum hd Sob beta hbeta z r hr g hgh
  obtain ⟨greg, hgreg, hUniform⟩ := exists_smooth_uniform_approximation B hBc
  choose breg hbreg using fun m => exists_weak_datum_of_smooth z r hr (greg m) (hgreg m)
  choose C hC hRegular using fun m => hReg (greg m) (hgreg m) (breg m) (hbreg m)
  have hApprox : TendstoUniformlyOn greg g atTop
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro eps heps
    filter_upwards [Metric.tendstoUniformly_iff.mp hUniform eps heps] with n hn
    intro x hx
    rw [← hBt x hx]
    exact hn x
  exact goodext_harmonic_trace_compact_continuous hd Sob z r hr beta alpha hbeta halpha hP
    a A hA haA lam Lam hlam hbounds g hgc hgh breg greg
    (fun m => (hgreg m).continuous.continuousOn) hbreg hApprox C hC hRegular Ebound hResponse

end SubdiffusiveProcess.Paper
