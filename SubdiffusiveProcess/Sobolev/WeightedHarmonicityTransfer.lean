module

public import SubdiffusiveProcess.Lane4.Bridge
public import SubdiffusiveProcess.Sobolev.NativeH10Reverse
public import SubdiffusiveProcess.Sobolev.WeightedHarmonicBoundaryMaximum

@[expose] public section

/-! This file transfers scalar weighted Euler equations on native Sobolev graphs to upstream weak harmonicity and applies the boundary difference bound to Dirichlet minimizers. It does not assert any converse or construct minimizers. -/

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section

namespace SubdiffusiveProcess

/-- A weighted native Euler equation is the usual scalar weak harmonic equation. -/
theorem isWeaklyHarmonicOn_of_sobolevCoefficientForm_zero
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (A : SpatialCoordinates d → ℝ)
    (ha : (a.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] A)
    (v : weakSobolevGraph Q)
    (hv : ∀ psi : killedSobolevGraph Q, sobolevCoefficientForm a v.val psi.val = 0) :
    ∃ w : H1Function (Q : Set (SpatialCoordinates d)),
      w.toFun = (fun x => v.val.1 x) ∧
      IsWeaklyHarmonicOn A (Q : Set (SpatialCoordinates d)) w := by
  obtain ⟨w, hwval, hwgrad⟩ := exists_nativeH1Function_of_weakSobolevGraph v
  refine ⟨w, ?_, ?_⟩
  · change (w : SpatialCoordinates d → ℝ) = (fun x => v.val.1 x)
    exact hwval
  · intro phi
    obtain ⟨u, humem, huval, hugrad⟩ := exists_killedSobolevGraph_of_h10Function phi
    have hform := hv (⟨u, humem⟩ : killedSobolevGraph Q)
    change sobolevCoefficientForm a v.val u = 0 at hform
    rw [Lane4.sobolevCoefficientForm_eq_upstream_integral a A ha v.val u] at hform
    have hformScalar :
        (∫ x in (Q : Set (SpatialCoordinates d)),
          Homogenization.vecDot ((A x) • (fun i => v.val.2 i x))
            (fun i => u.2 i x) ∂volume) = 0 := by
      simpa only [SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField,
        Homogenization.matVecMul_scalarMatrix] using hform
    have hgradAE : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        ∀ i : Fin d, u.2 i x = phi.toH1Function.grad x i :=
      ae_all_iff.mpr hugrad
    have hcompare :
        (∫ x in (Q : Set (SpatialCoordinates d)),
          Homogenization.vecDot ((A x) • w.grad x)
            (fun i => phi.toH1Function.grad x i) ∂volume) =
        (∫ x in (Q : Set (SpatialCoordinates d)),
          Homogenization.vecDot ((A x) • (fun i => v.val.2 i x))
            (fun i => u.2 i x) ∂volume) := by
      refine integral_congr_ae ?_
      filter_upwards [hgradAE] with x hx
      rw [hwgrad]
      have htest : (fun i => phi.toH1Function.grad x i) = (fun i => u.2 i x) :=
        funext (fun i => (hx i).symm)
      rw [htest]
    change (∫ x in (Q : Set (SpatialCoordinates d)),
      Homogenization.vecDot ((A x) • w.grad x)
        (fun i => phi.toH1Function.grad x i) ∂volume) = 0
    rw [hcompare]
    exact hformScalar

/-- Dirichlet minimizers with one scalar coefficient obey the frontier difference bound on the closure. -/
theorem dirichletMinimizer_abs_sub_le_of_frontier_le
    {d : ℕ} [NeZero d] {Q : Opens (SpatialCoordinates d)}
    (hQ : IsOpenBoundedConvexDomain (Q : Set (SpatialCoordinates d)))
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (a : PositiveCoefficient Q) (A : SpatialCoordinates d → ℝ) (hA : Measurable A)
    (ha : (a.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] A)
    (lam Lam : ℝ) (hlam : 0 < lam)
    (hbounds : ∀ x ∈ (Q : Set (SpatialCoordinates d)), lam ≤ A x ∧ A x ≤ Lam)
    (b0 b1 : weakSobolevGraph Q) (V0 V1 : SpatialCoordinates d → ℝ)
    (hV0 : ContinuousOn V0 (closure (Q : Set (SpatialCoordinates d))))
    (hV1 : ContinuousOn V1 (closure (Q : Set (SpatialCoordinates d))))
    (hr0 : ((dirichletMinimizer S a b0).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V0)
    (hr1 : ((dirichletMinimizer S a b1).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V1)
    (M : ℝ) (hbd : ∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), |V0 x - V1 x| ≤ M) :
    ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), |V0 x - V1 x| ≤ M := by
  have heuler0 : ∀ psi : killedSobolevGraph Q,
      sobolevCoefficientForm a (dirichletMinimizer S a b0).val psi.val = 0 := by
    intro psi
    have hmem : psi.val ∈ S.space := hS.symm ▸ psi.property
    let psiS : S.space := ⟨psi.val, hmem⟩
    have he := dirichletMinimizer_euler S a b0 psiS
    change sobolevCoefficientForm a (dirichletMinimizer S a b0).val psi.val = 0 at he
    exact he
  have heuler1 : ∀ psi : killedSobolevGraph Q,
      sobolevCoefficientForm a (dirichletMinimizer S a b1).val psi.val = 0 := by
    intro psi
    have hmem : psi.val ∈ S.space := hS.symm ▸ psi.property
    let psiS : S.space := ⟨psi.val, hmem⟩
    have he := dirichletMinimizer_euler S a b1 psiS
    change sobolevCoefficientForm a (dirichletMinimizer S a b1).val psi.val = 0 at he
    exact he
  obtain ⟨w0, hw0val, hharm0⟩ :=
    isWeaklyHarmonicOn_of_sobolevCoefficientForm_zero a A ha
      (dirichletMinimizer S a b0) heuler0
  obtain ⟨w1, hw1val, hharm1⟩ :=
    isWeaklyHarmonicOn_of_sobolevCoefficientForm_zero a A ha
      (dirichletMinimizer S a b1) heuler1
  have hrep0 : w0.toFun =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V0 := by
    filter_upwards [hr0] with x hx
    exact (congrFun hw0val x).trans hx
  have hrep1 : w1.toFun =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V1 := by
    filter_upwards [hr1] with x hx
    exact (congrFun hw1val x).trans hx
  exact abs_sub_le_on_closure_of_harmonic_of_frontier_le hQ A hA lam Lam hlam
    hbounds w0 w1 hharm0 hharm1 V0 V1 hV0 hV1 hrep0 hrep1 M hbd

end SubdiffusiveProcess
