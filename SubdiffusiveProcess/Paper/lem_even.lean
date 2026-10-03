module

public import SubdiffusiveProcess.Paper.lem_even_fold_construction
public import SubdiffusiveProcess.Paper.lem_even_weak_transport
public import SubdiffusiveProcess.Paper.lem_even_energy_transport
public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_even :
  ∀ (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (I P : Finset (Fin d))
    (a : PositiveCoefficient (centeredCube w r hr)) (F : SpatialCoordinates d → ℝ)
    (MF : ℝ), 0 ≤ MF →
    AEMeasurable F (volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d))) →
    (∀ᵐ x ∂volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d)),
      |F x| ≤ MF) →
    (∫ x in (centeredCube w r hr : Set (SpatialCoordinates d)), F x) = 0 →
  ∀ (v : weakSobolevGraph (centeredCube w r hr)),
    (∀ ψ : weakSobolevGraph (centeredCube w r hr),
      sobolevCoefficientForm a (v : SobolevData (centeredCube w r hr))
          (ψ : SobolevData (centeredCube w r hr)) =
        ∫ x in (centeredCube w r hr : Set (SpatialCoordinates d)),
          F x * (ψ : SobolevData (centeredCube w r hr)).1 x) →
  ∃ (af : PositiveCoefficient (foldedCube w r hr I P))
    (vf : weakSobolevGraph (foldedCube w r hr I P)),
    ((af.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
      fun x => a.val (coordinateFold (foldedCubeCenter w r I P) I P x)) ∧
    (((vf : SobolevData (foldedCube w r hr I P)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
      fun x => (v : SobolevData (centeredCube w r hr)).1
        (coordinateFold (foldedCubeCenter w r I P) I P x)) ∧
    (∀ ψ : weakSobolevGraph (foldedCube w r hr I P),
      sobolevCoefficientForm af (vf : SobolevData (foldedCube w r hr I P))
          (ψ : SobolevData (foldedCube w r hr I P)) =
        ∫ x in (foldedCube w r hr I P : Set (SpatialCoordinates d)),
          F (coordinateFold (foldedCubeCenter w r I P) I P x) *
            (ψ : SobolevData (foldedCube w r hr I P)).1 x) ∧
    (∀ (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B),
      (∀ J : Finset (Fin d), J ⊆ I →
        coordinateReflection (foldedCubeCenter w r I P) J ⁻¹' B = B) →
      localGradientEnergy af hB (sobolevGradient (vf : SobolevData (foldedCube w r hr I P))) =
        2 ^ I.card *
          localGradientEnergy a (hB.inter (centeredCube w r hr).isOpen.measurableSet)
            (sobolevGradient (v : SobolevData (centeredCube w r hr)))) := by
  intro d w r hr I P a F MF hMF hFmeas hFbound hFmean v hv
  obtain ⟨af, vf, ha, hvf, hg⟩ := lem_even_fold_construction d w r hr I P a v
  exact ⟨af, vf, ha, hvf,
    fun ψ => lem_even_weak_transport d w r hr I P a v af vf ha hg F MF hMF hFmeas hFbound hFmean hv ψ,
    fun B hB hsym => lem_even_energy_transport d w r hr I P a v af vf ha hg B hB hsym⟩


end Paper
