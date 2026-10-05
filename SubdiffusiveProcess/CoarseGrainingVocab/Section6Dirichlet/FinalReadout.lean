module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DifferenceFields
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DirichletSpectralReadout
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport

@[expose] public section

/-!
# Final deterministic readout for the cutoff Dirichlet theorem

This file combines the two analytic readouts after prebalance.  A common
zero-trace representative identifies its gradient almost everywhere with the
literal gradient-difference carrier.  The spectral estimate supplies the
scalar `L²` term, while the two fractional duals supply the ordinary
vector `H⁻¹` terms.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- The paper negative fractional dual depends only on the almost-everywhere
class of its Euclidean `L²` field. -/
theorem paperNegativeFractionalDual_congr_ae
    {d : ℕ} {Q : TriadicCube d} (s : FractionalOrder)
    (p : FiniteLpExponent)
    (F G : CubeEuclideanLpField Q FiniteLpExponent.two)
    (hFG : F.toField =ᵐ[normalizedCubeMeasure Q] G.toField) :
    paperNegativeFractionalDual Q s p F =
      paperNegativeFractionalDual Q s p G := by
  unfold paperNegativeFractionalDual
  apply iSup_congr
  intro h
  have hpair : cubeEuclideanNormalizedSmoothPairing F h.1 =
      cubeEuclideanNormalizedSmoothPairing G h.1 := by
    unfold cubeEuclideanNormalizedSmoothPairing
    apply integral_congr_ae
    filter_upwards [hFG] with x hx
    rw [hx]
  rw [hpair]

/-- Dimension/order-only coefficient for the simultaneous scalar `L²` and
two ordinary vector `H⁻¹` readouts. -/
noncomputable def dirichletFinalReadoutConstant
    (s : FractionalOrder) (d : ℕ) [NeZero d] : ℝ≥0∞ :=
  dirichletSpectralReadoutConstant s d +
    ((d : ℕ) : ℝ≥0∞) * negativeNormReadoutConstant s d

theorem dirichletFinalReadoutConstant_lt_top
    (s : FractionalOrder) (d : ℕ) [NeZero d] :
    dirichletFinalReadoutConstant s d < ∞ := by
  unfold dirichletFinalReadoutConstant
  exact ENNReal.add_lt_top.mpr
    ⟨dirichletSpectralReadoutConstant_lt_top s d,
      ENNReal.mul_lt_top (ENNReal.natCast_lt_top d)
        (negativeNormReadoutConstant_lt_top s d)⟩

/-- A common-zero-trace difference turns a bound for the two manuscript
fractional duals into the exact three deterministic terms printed in the
cutoff Dirichlet conclusion. -/
theorem dirichletFinalReadout_le_paperNegativeFractionalDual_sum
    {d : ℕ} [NeZero d] (s : FractionalOrder)
    (u v : H1Function (openCubeSet (originCube d 0)))
    (gradDifference fluxDifference : L2VectorField (originCube d 0))
    (hgrad : ∀ x, gradDifference.toFun x = u.grad x - v.grad x)
    (hzero : HasH10Difference (originCube d 0) u v) :
    l2Size (originCube d 0) (fun x ↦ u.toFun x - v.toFun x) +
          ordinaryVectorHMinusOne (originCube d 0) gradDifference +
        ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
      dirichletFinalReadoutConstant s d *
        (paperNegativeFractionalDual (originCube d 0) s
            FiniteLpExponent.two
            (l2VectorFieldToCubeEuclideanL2Field
              (originCube d 0) gradDifference) +
          paperNegativeFractionalDual (originCube d 0) s
            FiniteLpExponent.two
            (l2VectorFieldToCubeEuclideanL2Field
              (originCube d 0) fluxDifference)) := by
  obtain ⟨w, hwValue⟩ := hzero
  let uv : H1Function (openCubeSet (originCube d 0)) := u - v
  have hwValue' : w.toH1Function.toFun
      =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uv.toFun := by
    filter_upwards [hwValue] with x hx
    simpa only [uv, H1Function.sub_toFun] using hx
  have hwGrad : w.toH1Function.grad
      =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uv.grad :=
    H1Function.grad_ae_eq_of_toFun_ae_eq
      (isOpen_openCubeSet (originCube d 0)) hwValue'
  have hfield :
      (unitH10GradientEuclideanL2Field w).toField
        =ᵐ[normalizedCubeMeasure (originCube d 0)]
          (l2VectorFieldToCubeEuclideanL2Field
            (originCube d 0) gradDifference).toField := by
    rw [normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
    filter_upwards [hwGrad] with x hx
    rw [unitH10GradientEuclideanL2Field_toField,
      l2VectorFieldToCubeEuclideanL2Field_toField, hx]
    simpa only [uv, H1Function.sub_grad] using (hgrad x).symm
  have hdual :
      paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (unitH10GradientEuclideanL2Field w) =
        paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (l2VectorFieldToCubeEuclideanL2Field
            (originCube d 0) gradDifference) :=
    paperNegativeFractionalDual_congr_ae s FiniteLpExponent.two _ _ hfield
  have hL2 : l2Size (originCube d 0)
      (fun x ↦ u.toFun x - v.toFun x) ≤
      dirichletSpectralReadoutConstant s d *
        paperNegativeFractionalDual (originCube d 0) s FiniteLpExponent.two
          (l2VectorFieldToCubeEuclideanL2Field
            (originCube d 0) gradDifference) := by
    have hspectral := l2Size_le_paperNegativeFractionalDual_gradient s w
    rw [hdual] at hspectral
    unfold l2Size at hspectral ⊢
    rw [← eLpNorm_congr_ae hwValue]
    exact hspectral
  have hHgrad := ordinaryVectorHMinusOne_le_paperNegativeFractionalDual
    s gradDifference
  have hHflux := ordinaryVectorHMinusOne_le_paperNegativeFractionalDual
    s fluxDifference
  let C0 : ℝ≥0∞ := dirichletSpectralReadoutConstant s d
  let C1 : ℝ≥0∞ := ((d : ℕ) : ℝ≥0∞) * negativeNormReadoutConstant s d
  let Dg : ℝ≥0∞ := paperNegativeFractionalDual (originCube d 0) s
    FiniteLpExponent.two
      (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) gradDifference)
  let Df : ℝ≥0∞ := paperNegativeFractionalDual (originCube d 0) s
    FiniteLpExponent.two
      (l2VectorFieldToCubeEuclideanL2Field (originCube d 0) fluxDifference)
  change l2Size (originCube d 0) (fun x ↦ u.toFun x - v.toFun x) ≤
    C0 * Dg at hL2
  change ordinaryVectorHMinusOne (originCube d 0) gradDifference ≤
    C1 * Dg at hHgrad
  change ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
    C1 * Df at hHflux
  change
    l2Size (originCube d 0) (fun x ↦ u.toFun x - v.toFun x) +
          ordinaryVectorHMinusOne (originCube d 0) gradDifference +
        ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
      (C0 + C1) * (Dg + Df)
  calc
    _ ≤ C0 * Dg + C1 * Dg + C1 * Df :=
      add_le_add (add_le_add hL2 hHgrad) hHflux
    _ = (C0 + C1) * Dg + C1 * Df := by ring
    _ ≤ (C0 + C1) * Dg + (C0 + C1) * Df := by
      apply add_le_add le_rfl
      have hcoef : C1 ≤ C0 + C1 := le_add_left le_rfl
      have hmul := mul_le_mul_right hcoef Df
      simpa only [mul_comm] using hmul
    _ = (C0 + C1) * (Dg + Df) := by ring

/-- The concrete cutoff fields from `DifferenceFields.lean`, with their
literal pointwise identities and the final deterministic readout bundled in
the exact existential shape used by the theorem. -/
theorem exists_cutoffDirichletDifferenceFields_with_readout
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (s : FractionalOrder)
    (u v : H1Function (openCubeSet (originCube d 0)))
    (hzero : HasH10Difference (originCube d 0) u v) :
    ∃ gradDifference fluxDifference : L2VectorField (originCube d 0),
      (∀ x, gradDifference.toFun x = u.grad x - v.grad x) ∧
      (∀ x, fluxDifference.toFun x =
        rescaledCutoffCoefficient M L N omega x • u.grad x - v.grad x) ∧
      l2Size (originCube d 0) (fun x ↦ u.toFun x - v.toFun x) +
            ordinaryVectorHMinusOne (originCube d 0) gradDifference +
          ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
        dirichletFinalReadoutConstant s d *
          (paperNegativeFractionalDual (originCube d 0) s
              FiniteLpExponent.two
              (l2VectorFieldToCubeEuclideanL2Field
                (originCube d 0) gradDifference) +
            paperNegativeFractionalDual (originCube d 0) s
              FiniteLpExponent.two
              (l2VectorFieldToCubeEuclideanL2Field
                (originCube d 0) fluxDifference)) := by
  refine ⟨cutoffDirichletGradientDifference N u v,
    cutoffDirichletFluxDifference M L N omega u v,
    cutoffDirichletGradientDifference_toFun N u v,
    cutoffDirichletFluxDifference_toFun M L N omega u v, ?_⟩
  exact dirichletFinalReadout_le_paperNegativeFractionalDual_sum s u v
    (cutoffDirichletGradientDifference N u v)
    (cutoffDirichletFluxDifference M L N omega u v)
    (cutoffDirichletGradientDifference_toFun N u v) hzero

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
