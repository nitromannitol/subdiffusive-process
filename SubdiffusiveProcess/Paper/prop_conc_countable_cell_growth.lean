module

public import SubdiffusiveProcess.Paper.prop_conc_countable_cell_growth_with_bank
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.inputs_classical_countable_bounded_subsequence

@[expose] public section

/-! Actual cutoff growth on a countable family of arbitrary cubes.
One samplewise further subsequence works for every cell and every source and
boundary datum. The cell bounds are not asserted to be uniform in their indices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff
namespace Paper
noncomputable section

/-- The actual countable cell catalogue shares one further subsequence with finite growth and Holder bounds. -/
theorem prop_conc_countable_cell_growth
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
        ∀ (n : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube (z i) (r i) (hr i))),
          ((b : SobolevData (centeredCube (z i) (r i) (hr i))).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om (N (seq n)) (z i) (hr i)) F b u →
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube (z i) (r i) (hr i) →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om (N (seq n)) (z i) (hr i))
                (s := Metric.ball x rad ∩ (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
                (Metric.isOpen_ball.measurableSet.inter
                  (centeredCube (z i) (r i) (hr i)).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube (z i) (r i) (hr i)))) ≤
              K * (Kf + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube (z i) (r i) (hr i))).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) U ≤
              K * (Kf + Cphi)) := by
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_countable_cell_growth_with_bank d hd I Pin X W Cp Sob
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
