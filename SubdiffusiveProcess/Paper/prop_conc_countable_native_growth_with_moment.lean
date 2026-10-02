import SubdiffusiveProcess.Paper.prop_conc_countable_cell_growth_with_moment
import SubdiffusiveProcess.Paper.prop_conc_form_cutoff_continuity
import SubdiffusiveProcess.Sobolev.NativeBoundaryMinimizer
import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative
import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative

/-! Actual cell growth for continuous native harmonic minimizers on a countable cube catalogue.
The distinguished bank has a uniform moment majorant; the cell bounds share its subsequence. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff
namespace Paper
noncomputable section

/-- The countable actual growth bounds apply to the native minimizing mesh representatives. -/
theorem prop_conc_countable_native_growth_with_moment
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
      ∀ (Bbank : ℕ → BilateralField d → ℝ) (Cbank : ℝ≥0),
        (∀ n, MemLp (Bbank n) 1 (chaosSampleLaw M).toMeasure) →
        (∀ n, eLpNorm (Bbank n) 1 (chaosSampleLaw M).toMeasure ≤ Cbank) →
      ∀ (Qbank : ℕ → BilateralField d → ℝ) (p : ℝ), 1 ≤ p →
      ∀ Qbound : ℝ≥0,
        (∀ n, MemLp (Qbank n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) →
        (∀ n, eLpNorm (Qbank n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ Qbound) →
      ∀ N : ℕ → ℕ,
      ∃ Kbank : BilateralField d → ℝ, Measurable Kbank ∧ (∀ om, 0 ≤ Kbank om) ∧
        eLpNorm Kbank (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (2 * ((Qbound : ℝ) + 1)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∃ seq : ℕ → ℕ, StrictMono seq ∧
        (∀ n, |Qbank (N (seq n)) om| ≤ Kbank om) ∧
        (∃ B : ℝ, 0 ≤ B ∧ ∀ n, |Bbank (N (seq n)) om| ≤ B) ∧
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
  haveI dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_countable_cell_growth_with_moment d hd I Pin X W Cp Sob
    t alpha ht htd ha ha1
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta ι _ z r hr Bbank Cbank hBmem hBnorm Qbank p hp Qbound hQmem hQnorm N
  obtain ⟨Kbank, hKm, hK0, hKn, hsamples⟩ :=
    hs M Rm Sreg It H hIR hdelta ι z r hr Bbank Cbank hBmem hBnorm
      Qbank p hp Qbound hQmem hQnorm N
  refine ⟨Kbank, hKm, hK0, hKn, ?_⟩
  filter_upwards [hsamples] with om hom
  obtain ⟨seq, hseq, hQbound, hbank, hcells⟩ := hom
  refine ⟨seq, hseq, hQbound, hbank, ?_⟩
  intro i
  obtain ⟨K, hK, hbnd⟩ := hcells i
  refine ⟨K, hK, ?_⟩
  intro n phi hphi beta v hbeta htrace hmin hvcont
  let a := cutoffPositiveCoefficient M H om (N (seq n)) (z i) (hr i)
  have hc := (cutoffPositiveCoefficient_representative M H om (N (seq n)) (z i) (hr i)).2.2.2
  have hP := centeredCube_killedPoincare (z i) (hr i)
  have hsolve := solvesDirichlet_zero_of_native_minimum hP a _ hc beta v htrace hmin
  obtain ⟨henergy, U, hUcont, hUae, hUholder, hUnorm⟩ := hbnd n (fun _ => 0) 0 le_rfl
    aemeasurable_const (Filter.Eventually.of_forall fun _ => by norm_num)
    phi _ hphi le_rfl _ _ ((sobolevDataOfH1_fst_coeFn beta).trans hbeta) hsolve
  have heq := eqOn_closure_of_ae_eq_restrict (centeredCube (z i) (r i) (hr i)).isOpen
    hvcont hUcont.continuousOn ((sobolevDataOfH1_fst_coeFn v).symm.trans hUae)
  rw [aux_prop_conc_form_cutoff_continuity_closure_cube] at heq
  refine ⟨(isHolderOn_congr heq).mpr hUholder, ?_, ?_⟩
  · rw [cAlphaNorm_congr heq]
    simpa only [zero_add] using hUnorm
  · simpa only [zero_add] using henergy

end
end Paper
