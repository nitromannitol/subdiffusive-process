module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}



def conv_energy_measure_normalization
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) : Prop :=
  (∀ u φ : DomainL2 Q, E.MemCore u → E.MemCore φ →
      ∀ uc φc : SpatialCoordinates d → ℝ, Continuous uc → Continuous φc →
        ((u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] uc) →
        ((φ : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] φc) →
      ∀ uφ u2 : DomainL2 Q, uφ ∈ E.domain → u2 ∈ E.domain →
        ((uφ : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
              fun x => uc x * φc x) →
        ((u2 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
              fun x => uc x ^ 2) →
        (∫ x, φc x ∂(Gamma.measure u)) = E.form u uφ - (1 / 2 : ℝ) * E.form u2 φ) ∧
    (∀ u ∈ E.domain, (Gamma.measure u Set.univ).toReal = E.form u u) ∧
    (∀ u ∈ E.domain, ∀ v ∈ E.domain, Gamma.cross u v Set.univ = E.form u v) ∧
    (∀ u : DomainL2 Q, u ∈ E.domain → ∀ f : SpatialCoordinates d → ℝ, Continuous f →
      ((u : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f) →
      Gamma.measure u (tsupport f)ᶜ = 0)

end SubdiffusiveProcess.Paper
