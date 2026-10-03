module

public import SubdiffusiveProcess.Section10.PhysicalAttachment
public import SubdiffusiveProcess.Section10.PhysicalLocalTransportCoefficients

@[expose] public section

/-!
# The single physical early-exit supplier needed by the mean-exit application

This is a named, explicitly conditional interface for the Section 8 producer.
It supplies no estimate or witness. The law, all-start characterization and
clock are the actual physical ones, including every finite cutoff and top.
-/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Filter Topology
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.Section10.PhysicalAttachment SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- The source characterization of the physical family, with the same
coefficient in both slots of its weak reversible resolvent. -/
def IsPhysicalMeanExitFamily {d : ℕ} (M : GMCModel d)
    (X : WithTop ℕ → PhysicalKernel d) : Prop :=
  ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
    ∃ D : C0ResolventDatum (Vec d),
    ∃ hdense : ∀ mu, DenseRange (D.operator mu),
      IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
      (D.fellerKernelSemigroup hdense).IsConservative ∧
      ∀ (I : Finset ℝ≥0) (x : Vec d),
        ((X L).map (ContinuousPath.finsetEvaluation I)) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x

/-- The quantitative Section 8 bank at exactly the physical scope consumed
by the lower inner-start mean-exit estimate. Higher moments must be chosen
before its disorder threshold. This proposition remains a producer obligation. -/
def PhysicalMeanExitEarlyExitSupplier (d : ℕ) : Prop :=
  ∀ Q : ℝ, 1 ≤ Q → ∃ δ : ℝ, 0 < δ ∧
    ∀ M : GMCModel d, M.delta ≤ δ → ∃ C : ℝ, 0 < C ∧
      ∀ X : WithTop ℕ → PhysicalKernel d,
        (∀ L, IsMarkovKernel (X L)) → IsPhysicalMeanExitFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
          ∃ F : AnchoredC11Sample d → ℝ, Measurable F ∧ (∀ omega, 1 ≤ F omega) ∧
            (∫⁻ omega, ENNReal.ofReal (F omega ^ Q)
              ∂(physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
            ∀ᵐ omega ∂(physicalLaw M).toMeasure,
              ∀ t : ℝ, 0 < t → ∀ x ∈ Metric.ball z ((3 : ℝ) ^ ((m : ℤ) - 2) / 2),
                X L (omega, x) {w |
                  ContinuousPath.exitTime (Metric.ball z ((3 : ℝ) ^ (m : ℤ) / 2)) w ≤
                    ENNReal.ofReal (t * (rawClock M L m : ℝ))} ≤
                      ENNReal.ofReal (F omega * Real.sqrt t)

/-- The family part of the interface has an actual constructed inhabitant;
only the early-exit estimate and its moment bank remain quantitative inputs. -/
theorem exists_physicalMeanExitFamily {d : ℕ} [NeZero d]
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] (M : GMCModel d) :
    ∃ X : WithTop ℕ → PhysicalKernel d,
      (∀ L, IsMarkovKernel (X L)) ∧ IsPhysicalMeanExitFamily M X :=
  exists_physical_family M

end SubdiffusiveProcess.Section10
