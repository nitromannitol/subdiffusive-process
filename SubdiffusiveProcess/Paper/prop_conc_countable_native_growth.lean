module

public import SubdiffusiveProcess.Paper.prop_conc_countable_native_growth_with_bank
public import SubdiffusiveProcess.Paper.prop_conc_countable_cell_growth
public import SubdiffusiveProcess.Paper.prop_conc_form_cutoff_continuity
public import SubdiffusiveProcess.Sobolev.NativeBoundaryMinimizer
public import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative
public import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative

@[expose] public section

/-! Actual cell growth for continuous native harmonic minimizers on a countable cube catalogue.
The bounds share one further subsequence but may depend on the cell. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff
namespace Paper
noncomputable section

/-- The countable actual growth bounds apply to the native minimizing mesh representatives. -/
theorem prop_conc_countable_native_growth
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (ι : Type) [Countable ι] (z : ι → SpatialCoordinates d) (r : ι → ℝ)
        (hr : ∀ i, 0 < r i),
      ∀ N : ℕ → ℕ,
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∀ i : ι, ∃ K : ℝ, 0 ≤ K ∧
        ∀ (n : ℕ) (phi : SpatialCoordinates d → ℝ), ContDiff ℝ 2 phi →
        ∀ beta v : H1Function (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          (beta.toFun =ᵐ[volume.restrict
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] phi) →
          HasZeroTraceDifferenceOn (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) v beta →
          energy (cutoffCoefficient M H om (N (seq n)))
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) v ≤
            cellDirichletInfimum (cutoffCoefficient M H om (N (seq n)))
              (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) beta →
          ContinuousOn v.toFun (closure
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) →
          IsHolderOn alpha (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) v.toFun ∧
          cAlphaNorm alpha (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) v.toFun ≤
            K * c2Norm (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) phi ∧
          ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube (z i) (r i) (hr i) →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om (N (seq n)) (z i) (hr i))
              (s := Metric.ball x rad ∩ (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
              (Metric.isOpen_ball.measurableSet.inter (centeredCube (z i) (r i) (hr i)).isOpen.measurableSet)
              (sobolevGradient (sobolevDataOfH1 v)) ≤
                K * (c2Norm (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) phi) ^ 2 *
                  rad ^ t := by
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_countable_native_growth_with_bank d hd I Pin X W Cp Sob
    t alpha ht htd ha ha1
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta ι _ z r hr N
  filter_upwards [hs M Rm Sreg It H hIR hdelta ι z r hr (fun _ _ => 0) 0
    (fun _ => MemLp.zero)
    (fun _ => by rw [show (fun _ : BilateralField d => (0 : ℝ)) = 0 from rfl, eLpNorm_zero]; exact le_rfl)
    N] with om hom
  obtain ⟨seq, hseq, _, hcells⟩ := hom
  exact ⟨seq, hseq, hcells⟩

end
end Paper
