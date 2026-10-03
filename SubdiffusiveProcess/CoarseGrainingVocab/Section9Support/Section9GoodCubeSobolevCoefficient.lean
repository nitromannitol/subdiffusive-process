module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables
public import SubdiffusiveProcess.Frozen.Section8.WeightedLocalSobolev

@[expose] public section

/-!
# Cutoff coefficients for the translated weighted Sobolev estimate

The translated sample gives the exact scalar coefficient family for the
physical cutoff coefficient pulled back to the reference cube. Continuity
also supplies local ellipticity and the normalized negative Besov carrier.
These are deterministic facts, valid for every sample.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The translated cutoff supplies all coefficient and carrier side conditions
of the translated weighted Sobolev estimate, with pointwise representatives. -/
theorem goodCube_cutoff_sobolev_data {d : ℕ} (M : GMCModel d) (L : ℕ)
    (omega : PotentialSample d) (z : Vec d) (Q : Homogenization.TriadicCube d) :
    let b : Vec d → ℝ := fun x => aCutoff M L omega (x + z)
    CoefficientOn (openCubeSet Q) b ∧
      ExactCircIntegrable Q (fun x => b x / cubeAverage Q b - 1) ∧
      ∀ x, ((aCutoffFamily M L (translatePotentialSample z omega)).coeffOn Q).toCoeffField x =
        scalarMatrix (b x) := by
  intro b
  have hbx : ∀ x, b x = aCutoff M L (translatePotentialSample z omega) x := fun x =>
    (Section6Covariance.aCutoff_translatePotentialSample M L z omega x).symm
  have hbfun : b = fun x => aCutoff M L (translatePotentialSample z omega) x := funext hbx
  have hfun : (fun x => b x / cubeAverage Q b - 1) =
      fun x => aCutoff M L (translatePotentialSample z omega) x / cubeAverage Q b - 1 :=
    funext fun x => by rw [hbx x]
  refine ⟨?_, ?_, ?_⟩
  · rw [hbfun]
    let data := aCutoffCoeffOnData M L (translatePotentialSample z omega)
      (Homogenization.Book.Ch02.cubeDomain Q)
    refine ⟨?_, data.lam, data.Lam, data.lam_pos, ?_⟩
    · exact (continuous_aCutoff M L (translatePotentialSample z omega)).aestronglyMeasurable
    · simpa only [Homogenization.volumeMeasureOn, Homogenization.Book.Ch02.cubeDomain_coe]
      using data.aeBounds
  · rw [hfun]
    exact exactCircIntegrable_of_continuous Q
      (((continuous_aCutoff M L (translatePotentialSample z omega)).div_const
        (cubeAverage Q b)).sub continuous_const)
  · intro x
    rw [hbx x]
    rfl

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
