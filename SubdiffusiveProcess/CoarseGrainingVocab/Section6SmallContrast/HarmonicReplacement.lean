module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.EnergyMinimality
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.Carrier
public import Homogenization.Book.Ch01.Theorems.MeanSquareDeviation

@[expose] public section

/-!
# Harmonic replacement on Euclidean balls

This is the Dirichlet comparison `h_r` in the Schauder `C^α` estimate.  The existing
Schauder-datum constructor already supplies the weakly harmonic replacement;
the strengthened endpoint below retains its concrete `H^1_0` witness and the
pointwise gradient identity needed by the energy test and Dirichlet principle.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

noncomputable section

variable {d : ℕ}

/-- Explicit Euclidean balls are open bounded convex domains. -/
theorem isOpenBoundedConvexDomain_euclideanBall (z : Vec d) {r : ℝ}
    (hr : 0 < r) : IsOpenBoundedConvexDomain (euclideanBall z r) := by
  refine ⟨isOpen_euclideanBall z r, ?_, convex_euclideanBall z r⟩
  exact Bornology.IsBounded.isBoundedDomain
    (Metric.isBounded_ball.subset (euclideanBall_subset_metricBall hr))

/-- The exact replacement package: `h = Phi + rho`, with `rho in H^1_0`, and
`h` weakly harmonic. -/
theorem exists_unitHarmonicReplacement_withGradient [NeZero d]
    {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (Phi : H1Function V) :
    ∃ h : H1Function V, ∃ rho : H10Function V,
      IsUnitWeaklyHarmonicOn V h ∧
      (∀ x, h.toFun x = Phi.toFun x + rho.toH1Function.toFun x) ∧
      ∀ x, h.grad x = Phi.grad x + rho.toH1Function.grad x := by
  let : IsFiniteMeasure (volumeMeasureOn V) := hV.isFiniteMeasure_restrict_volume
  have hgrad : MemVectorL2 V Phi.grad := Phi.grad_memVectorL2
  have hg : MemVectorL2 V (fun x => -Phi.grad x) := hgrad.neg
  have hrealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization V :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      hV
  obtain ⟨rho, hrho⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := unitCoeffField d) (U := V) (g := fun x => -Phi.grad x)
      (lam := 1) (Lam := 1) hg hrealize hne
      (isEllipticFieldOn_unitCoeffField hV.isOpen.measurableSet)
  have hrhoL2 : MemVectorL2 V rho.toH1Function.grad :=
    rho.toH1Function.grad_memVectorL2
  let h : H1Function V := Phi + rho.toH1Function
  have hharm : IsUnitWeaklyHarmonicOn V h := by
    intro phi
    have hsplit := integral_vecDot_add_left_split (U := V) hgrad hrhoL2
      (H := h.grad) (fun x => by simp [h]) phi
    have hid := hrho phi
    have hunit :
        ∫ x in V, vecDot (matVecMul (unitCoeffField d x)
              (rho.toH1Function.grad x)) (phi.toH1Function.grad x) ∂volume =
          ∫ x in V, vecDot (rho.toH1Function.grad x)
              (phi.toH1Function.grad x) ∂volume := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change vecDot (matVecMul (unitCoeffField d x) (rho.toH1Function.grad x))
          (phi.toH1Function.grad x) =
        vecDot (rho.toH1Function.grad x) (phi.toH1Function.grad x)
      rw [matVecMul_unitCoeffField]
    rw [hunit] at hid
    have hneg :
        ∫ x in V, vecDot (-Phi.grad x) (phi.toH1Function.grad x) ∂volume =
          -∫ x in V, vecDot (Phi.grad x) (phi.toH1Function.grad x) ∂volume := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change vecDot (-Phi.grad x) (phi.toH1Function.grad x) =
        -vecDot (Phi.grad x) (phi.toH1Function.grad x)
      rw [vecDot_neg_left]
    rw [hneg] at hid
    rw [hsplit, hid]
    ring
  refine ⟨h, rho, hharm, ?_, ?_⟩
  · intro x
    simp [h, H1Function.add_toFun]
  · intro x
    simp [h, H1Function.add_grad]

/-- The replacement on the source ball `B_r`, including its exact Dirichlet
energy comparison with the datum. -/
theorem exists_unitHarmonicReplacement_euclideanBall [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall z r)) :
    ∃ h : H1Function (euclideanBall z r), ∃ rho : H10Function (euclideanBall z r),
      IsUnitWeaklyHarmonicOn (euclideanBall z r) h ∧
      (∀ x, h.toFun x = u.toFun x + rho.toH1Function.toFun x) ∧
      (∀ x, h.grad x = u.grad x + rho.toH1Function.grad x) ∧
      (∫ x in euclideanBall z r, vecDot (h.grad x) (h.grad x) ∂volume ≤
        ∫ x in euclideanBall z r, vecDot (u.grad x) (u.grad x) ∂volume) := by
  obtain ⟨h, rho, hharm, hfun, hgrad⟩ :=
    exists_unitHarmonicReplacement_withGradient
      (isOpenBoundedConvexDomain_euclideanBall z hr)
      (euclideanBall_nonempty z hr) u
  refine ⟨h, rho, hharm, hfun, hgrad, ?_⟩
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.integral_vecDot_grad_self_le_of_isUnitWeaklyHarmonicOn
    hharm rho hgrad

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
