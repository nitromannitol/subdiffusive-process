module

public import SubdiffusiveProcess.Paper.Support.B7cTraceExists
public import SubdiffusiveProcess.Paper.Support.B7cTraceTransports

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Clause (i) derived for the genuine native limit-form family. -/
theorem aux_mfd_prop_gluing_clause_one
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ) (hr : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (rad j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (omega : Ω)
    (Gs : ∀ j, DomainL2 (centeredCube (z j) (rad j) (hr j)) →L[ℝ]
      DomainL2 (centeredCube (z j) (rad j) (hr j)))
    (Ls : ∀ j, aux_limit_form_package_limit_side d hd (z j) (rad j) (hr j) (S j) (Gs j)
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j) (hr j)))
    (hR : conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey) (hmem : omega ∈ G) :
∀ (iq iQ : J) (hz : z iQ = z iq) (hrad : rad iQ = 3 * rad iq),
    ∀ b : SpatialCoordinates d → ℝ,
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (frontier (centeredCube (z iq) (rad iq) (hr iq) : Set (SpatialCoordinates d))) b →
      ∃ lam : ℝ, ∃ U : DomainL2 (centeredCube (z iQ) (rad iQ) (hr iQ)),
        ∃ Uc : SpatialCoordinates d → ℝ,
          aux_mfd_prop_gluing_trace_package d hd M H (fun n => env n omega) cutoff
            (z iq) (rad iq) (hr iq) (z iQ) (rad iQ) (hr iQ) hz hrad (S iQ)
            (Gs iQ) (Ls iQ) E Cext beta alpha b lam U Uc := by
  intro iq iQ hz hrad b hb
  have hS := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 iQ
  have h3r : 0 < 3 * rad iq := mul_pos (by norm_num) (hr iq)
  apply aux_mfd_prop_gluing_trace_transport hd M H (fun n => env n omega) cutoff
    (z iq) (z iQ) (rad iq) (rad iQ) (hr iq) (hr iQ) h3r hz hrad (S iQ) (Gs iQ) (Ls iQ)
    hS E Cext beta alpha b
  intro S0 G0 L0 hS0
  exact aux_mfd_prop_gluing_trace_exists d hd M H Ω P cutoff env J j0 z rad hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey
    omega iQ (z iq) (rad iq) (hr iq) h3r hz hrad S0 G0 L0 hR hmem hS0 b hb

end SubdiffusiveProcess.Paper
