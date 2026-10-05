module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Homogenization.Sobolev.H1.BasicLemmas
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import Mathlib
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
public import SubdiffusiveProcess.Probability.ConditionalPullback
public import SubdiffusiveProcess.Sobolev.AffineData
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Lnorm.BoundaryResponseFamily

@[expose] public section

/-! This module establishes BoundaryMomentAlgebra for the cutoff-response compactness construction;
it does not identify subsequential limits or assert local-normalization convergence. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff
noncomputable section

namespace SubdiffusiveProcess.Lnorm

section


/-- prop16 le of add six for the cutoff-response compactness construction. -/
theorem prop16_le_of_add_six {a1 a2 a3 a4 a5 a6 B : ℝ≥0∞}
    (h : a1 + a2 + a3 + a4 + a5 + a6 ≤ B) :
    a1 ≤ B ∧ a2 ≤ B ∧ a3 ≤ B ∧ a4 ≤ B ∧ a5 ≤ B ∧ a6 ≤ B := by
  have e1 : a1 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a1 = a1 + 0 + 0 + 0 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le
  have e2 : a2 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a2 = 0 + a2 + 0 + 0 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le
  have e3 : a3 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a3 = 0 + 0 + a3 + 0 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le
  have e4 : a4 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a4 = 0 + 0 + 0 + a4 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le
  have e5 : a5 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a5 = 0 + 0 + 0 + 0 + a5 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le
  have e6 : a6 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a6 = 0 + 0 + 0 + 0 + 0 + a6 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le
  exact ⟨e1.trans h, e2.trans h, e3.trans h, e4.trans h, e5.trans h, e6.trans h⟩

end

section


/-- prop16 kap for the cutoff-response compactness construction. -/
def prop16_kap {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) : ℝ :=
  Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N

end

section


/-- prop16 kap pos for the cutoff-response compactness construction. -/
theorem prop16_kap_pos {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    0 < SubdiffusiveProcess.Lnorm.prop16_kap M N :=
  mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)

end

section


/-- prop16 aD for the cutoff-response compactness construction. -/
def prop16_aD (d : ℕ) : ℝ :=
  ((d : ℝ) - 1 / 2) * (((d : ℝ) - 1 / 2) - (d : ℝ) + 1) / (((d : ℝ) - 1 / 2) + 1) /
    (8 * Real.log 3)

end

section


/-- prop16 cutoff ae exp for the cutoff-response compactness construction. -/
theorem prop16_cutoff_ae_exp {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ((cutoffPositiveCoefficient M H omega N z hr).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      (fun x => Real.exp (cutoffPotential H omega N x - Real.log (SubdiffusiveProcess.Lnorm.prop16_kap M N))) := by
  have instCubeClosure : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have h0 := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube z r hr) (closedCube z r hr) (cutoffCoefficientCM M H omega N z hr)
    (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [h0, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxm
  have := hx hxm
  change (cutoffPositiveCoefficient M H omega N z hr).val x = _
  unfold cutoffPositiveCoefficient
  rw [this, div_one]
  change cutoffCoefficient M H omega N x = _
  unfold cutoffCoefficient SubdiffusiveProcess.Lnorm.prop16_kap
  have hA := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have key : ∀ u : ℝ, Real.exp (u - Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)) =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * Real.exp u := by
    intro u; rw [Real.exp_sub, Real.exp_log hA, div_eq_inv_mul]
  rw [Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_exp, sub_add_eq_sub_sub]
  exact (key _).symm

end

section


/-- prop16 lge inter for the cutoff-response compactness construction. -/
theorem prop16_lge_inter {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Ω)
    (x : SpatialCoordinates d) (rho : ℝ) (g : HilbertGradient Ω) :
    localGradientEnergy a (s := Metric.ball x rho ∩ (Ω : Set (SpatialCoordinates d)))
        (Metric.isOpen_ball.inter Ω.isOpen).measurableSet g =
      localGradientEnergy a (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet g := by
  simp only [localGradientEnergy_eq_integral]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Measure.restrict_restrict (Metric.isOpen_ball.inter Ω.isOpen).measurableSet,
    Measure.restrict_restrict Metric.isOpen_ball.measurableSet, Set.inter_assoc, Set.inter_self]

end

section


/-- prop16 bump for the cutoff-response compactness construction. -/
theorem prop16_bump {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ f : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0) ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) := by
  have hcube : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl
  set bmp : ContDiffBump z := ⟨r / 8, r / 4, by linarith only [hr, hcube], by linarith only [hr, hcube]⟩ with hbmp
  refine ⟨bmp, bmp.contDiff, bmp.hasCompactSupport, ?_, ⟨z, ?_, ?_⟩,
    fun x => ⟨bmp.nonneg' x, bmp.le_one⟩⟩
  · rw [bmp.tsupport_eq, hcube]
    apply Metric.closedBall_subset_ball
    dsimp [bmp]
    linarith only [hr, hcube, hbmp]
  · rw [hcube]
    exact Metric.mem_ball_self (by linarith only [hr, hcube, hbmp])
  · have := bmp.one_of_mem_closedBall (Metric.mem_closedBall_self (by dsimp [bmp]; linarith only [hr, hcube, hbmp]))
    rw [this]
    norm_num

end

end SubdiffusiveProcess.Lnorm
