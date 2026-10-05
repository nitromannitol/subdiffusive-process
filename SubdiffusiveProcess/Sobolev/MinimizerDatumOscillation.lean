module

public import SubdiffusiveProcess.Sobolev.WeightedHarmonicityTransfer
public import SubdiffusiveProcess.Sobolev.HarmonicTraceOscillation

@[expose] public section

/-! The maximum principle bounds a native Dirichlet minimizer by its continued datum's oscillation.
This module does not construct continuous representatives. -/
open MeasureTheory Set TopologicalSpace Homogenization SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section
namespace SubdiffusiveProcess

/-- A native Dirichlet minimizer remains within the boundary-to-interior oscillation of its datum. -/
theorem dirichletMinimizer_abs_sub_datum_le
    {d : ℕ} [NeZero d] {Q : Opens (SpatialCoordinates d)}
    (hQ : IsOpenBoundedConvexDomain (Q : Set (SpatialCoordinates d)))
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (a : PositiveCoefficient Q) (c : SpatialCoordinates d → ℝ) (hc : Continuous c)
    (hac : (a.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (lam Lam : ℝ) (hlam : 0 < lam)
    (hbounds : ∀ x ∈ (Q : Set (SpatialCoordinates d)), lam ≤ c x ∧ c x ≤ Lam)
    (b : weakSobolevGraph Q) (V g : SpatialCoordinates d → ℝ)
    (hV : ContinuousOn V (closure (Q : Set (SpatialCoordinates d))))
    (hrep : ((dirichletMinimizer S a b).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V)
    (htrace : ∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), V x = g x)
    (D : ℝ) (hOsc : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      ∀ y ∈ frontier (Q : Set (SpatialCoordinates d)), |g y - g x| ≤ D) :
    ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), |V x - g x| ≤ D := by
  have heuler : ∀ psi : killedSobolevGraph Q,
      sobolevCoefficientForm a (dirichletMinimizer S a b).val psi.val = 0 := by
    intro psi
    let psiS : S.space := ⟨psi.val, hS.symm ▸ psi.property⟩
    exact dirichletMinimizer_euler S a b psiS
  obtain ⟨w, hw, hharm⟩ := isWeaklyHarmonicOn_of_sobolevCoefficientForm_zero a c hac
    (dirichletMinimizer S a b) heuler
  have hwrep : w.toFun =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V := by
    filter_upwards [hrep] with x hx
    exact (congrFun hw x).trans hx
  have hAE : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      lam ≤ c x ∧ c x ≤ Lam := by
    filter_upwards [ae_restrict_mem Q.isOpen.measurableSet] with x hx
    exact hbounds x hx
  exact abs_sub_datum_le_of_harmonic_trace hQ c lam Lam hlam hc.aestronglyMeasurable hAE
    w hharm V g hV hwrep htrace D hOsc

end SubdiffusiveProcess
