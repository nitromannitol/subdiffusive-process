import SubdiffusiveProcess.Paper.prop_conc_finite_cell_growth
import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy
import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative

/-! Bounds for the actual native boundary energies on finitely many cells.
The common samplewise subsequence is independent of boundary data. The moment
constant may depend on the model and cells, and no limiting form is asserted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

namespace Paper
noncomputable section

/-- The finite-cell growth bound controls all smooth native boundary energies on one subsequence. -/
theorem prop_conc_finite_boundary_energy
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (p : ℝ) (hp : 1 ≤ p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (ι : Type) [Fintype ι] (z : ι → SpatialCoordinates d) (r : ι → ℝ)
        (hr : ∀ i, 0 < r i), (∀ i, r i ≤ 1) →
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ → ℕ,
      ∃ K : BilateralField d → ℝ,
        Measurable K ∧ (∀ om, 0 < K om) ∧
        eLpNorm K (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∀ (i : ι) (n : ℕ)
          (_hP : ∃ B : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
            ‖w.val.1‖ ≤ B *
              ‖subspaceGradient (killedSobolevGraph (centeredCube (z i) (r i) (hr i))) w‖)
          (phi : SpatialCoordinates d → ℝ),
          ContDiff ℝ 2 phi →
          ∀ beta : H1Function (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)),
          (beta.toFun =ᵐ[volume.restrict
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] phi) →
          cellDirichletInfimum (cutoffCoefficient M H om (N (seq n)))
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) beta ≤
            K om * (c2Norm (closedCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) phi) ^ 2 := by
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_finite_cell_growth d hd I Pin X W Cp Sob
    ((d : ℝ) - 1 / 2) (1 / 2) p (by linarith only []) (by linarith only [])
    (by norm_num) (by norm_num) hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta ι _ z r hr hr1
  obtain ⟨C, hC, hN⟩ := hs M Rm Sreg It H hIR hdelta ι z r hr hr1
  refine ⟨C, hC, ?_⟩
  intro N
  obtain ⟨K, hKm, hKpos, hKn, hg⟩ := hN N
  refine ⟨K, hKm, hKpos, hKn, ?_⟩
  filter_upwards [hg] with om hom
  obtain ⟨seq, hseq, hbound⟩ := hom
  refine ⟨seq, hseq, ?_⟩
  intro i n hP phi hphi beta hbeta
  let a := cutoffPositiveCoefficient M H om (N (seq n)) (z i) (hr i)
  let b : weakSobolevGraph (centeredCube (z i) (r i) (hr i)) :=
    ⟨sobolevDataOfH1 beta, sobolevDataOfH1_mem_weak beta⟩
  have hb : (b.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] phi :=
    (sobolevDataOfH1_fst_coeFn beta).trans hbeta
  have henergy := (hbound i n (fun _ => 0) 0 le_rfl aemeasurable_const
    (Filter.Eventually.of_forall fun _ => by norm_num) phi _ hphi le_rfl b
    (dirichletMinimizer (killedResponseSpace hP) a b) hb
    (dirichletMinimizer_solves_zero hP a b)).1
  have hc := (cutoffPositiveCoefficient_representative M H om (N (seq n)) (z i) (hr i)).2.2.2
  apply cellDirichletInfimum_le_of_unit_growth (z i) (hr i) (hr1 i) hP a _ hc beta
  simpa only [zero_add, Real.one_rpow, mul_one] using
    henergy (z i) 1 (Metric.mem_ball_self (half_pos (hr i))) zero_lt_one le_rfl

end
end Paper
