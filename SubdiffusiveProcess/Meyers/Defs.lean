module

public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane2.NativeBridge

@[expose] public section




open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

namespace SubdiffusiveProcess.Meyers

/-- The open Euclidean ball `{x : |x - x0|₂ < R}` in `Vec d`. -/
def eBall {d : ℕ} (x0 : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | ∑ i : Fin d, (x i - x0 i) ^ 2 < R ^ 2}



def MeyersEstimate (d : ℕ) (p epsilon C : ℝ) : Prop :=
      ∀ (x0 : Vec d) (R : ℝ), 0 < R →
      ∀ (a h : Vec d → ℝ),
        AEMeasurable a (volume.restrict (eBall x0 (3 * R))) →
        (∀ᵐ x ∂volume.restrict (eBall x0 (3 * R)),
          |a x - 1| ≤ epsilon) →
        MemLp h (ENNReal.ofReal p) (volume.restrict (eBall x0 (3 * R))) →
      ∀ u : H1Function (eBall x0 (3 * R)),
        (∀ phi : H10Function (eBall x0 (3 * R)),
          (∫ x in eBall x0 (3 * R),
              a x * (∑ i : Fin d, u.grad x i * phi.toH1Function.grad x i)) =
            -∫ x in eBall x0 (3 * R),
              h x * phi.toH1Function.toFun x) →
        MemLp (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) (ENNReal.ofReal p)
            (volume.restrict (eBall x0 R)) ∧
          (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) (ENNReal.ofReal p)
              (volume.restrict (eBall x0 R))).toReal ≤
            C * (R ^ ((d : ℝ) * (1 / p - 1 / 2) - 1) *
                (eLpNorm u.toFun 2
                  (volume.restrict (eBall x0 (2 * R)))).toReal +
              R * (eLpNorm h (ENNReal.ofReal p)
                (volume.restrict (eBall x0 (2 * R)))).toReal)



def E2Body (d : ℕ) (p epsilon C : ℝ) : Prop :=
      ∀ (x0 : Vec d) (l : ℝ), 0 < l →
      ∀ (a : Vec d → ℝ) (a0 : ℝ), 0 < a0 →
        AEMeasurable a (volume.restrict (Metric.ball x0 (2 * l))) →
        (∀ᵐ x ∂volume.restrict (Metric.ball x0 (2 * l)), |a x - a0| ≤ epsilon * a0) →
      ∀ (F : Vec d → ℝ) (Kf : ℝ),
        AEMeasurable F (volume.restrict (Metric.ball x0 (2 * l))) → 0 ≤ Kf →
        (∀ᵐ x ∂volume.restrict (Metric.ball x0 (2 * l)), |F x| ≤ Kf) →
      ∀ u : H1Function (Metric.ball x0 (2 * l)),
        (∀ phi : H10Function (Metric.ball x0 (2 * l)),
          (∫ x in Metric.ball x0 (2 * l), a x * (∑ i : Fin d, u.grad x i * phi.toH1Function.grad x i)) =
          ∫ x in Metric.ball x0 (2 * l), F x * phi.toH1Function.toFun x) →
        MemLp (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) (ENNReal.ofReal p) (volume.restrict (Metric.ball x0 l)) ∧
        (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) (ENNReal.ofReal p) (volume.restrict (Metric.ball x0 l))).toReal /
          (volume.real (Metric.ball x0 l)) ^ (1 / p) ≤
        C * ((eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2)) 2 (volume.restrict (Metric.ball x0 (2 * l)))).toReal /
          (volume.real (Metric.ball x0 (2 * l))) ^ (1 / 2 : ℝ)) + C * l * a0⁻¹ * Kf

end SubdiffusiveProcess.Meyers
