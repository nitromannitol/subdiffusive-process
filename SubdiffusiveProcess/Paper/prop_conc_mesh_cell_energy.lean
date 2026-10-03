module

public import SubdiffusiveProcess.Paper.prop_conc_finite_boundary_energy
public import SubdiffusiveProcess.Lane2.MeshGeometry

@[expose] public section

/-! Bounded sums of native boundary energies on any fixed finite triadic mesh.
Only the small cells need side at most one; the parent cube is arbitrary. The
subsequence can depend on the mesh and sample, but is chosen before boundary data. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators

namespace Paper
noncomputable section

/-- All smooth data on a fixed triadic mesh have bounded total boundary energy on one further subsequence. -/
theorem prop_conc_mesh_cell_energy
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ → ℕ),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ J : ℕ, r / (3 : ℝ) ^ J ≤ 1 →
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∀ (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
        (hcompact : HasCompactSupport phi),
      ∃ B : ℝ, ∀ n : ℕ,
        (∑ k : OddGridIndex d (triadicHalf J),
          cellDirichletInfimum (cutoffCoefficient M H om (N (seq n)))
            (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))
            ((H1Function.ofContDiff (centeredCube z r hr).isOpen
                (hphi.of_le (by norm_num)) hcompact).restrict
              (oddGridCell z r hr (triadicHalf J) k).isOpen
              (oddGridCell_subset z hr (triadicHalf J) k))) ≤ B := by
  classical
  haveI dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_finite_boundary_energy d hd I Pin X W Cp Sob 1 le_rfl
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr N
  apply ae_all_iff.mpr
  intro J
  by_cases hside : r / (3 : ℝ) ^ J ≤ 1
  · let side : ℝ := r / (2 * (triadicHalf J : ℝ) + 1)
    have hsidepos : 0 < side := div_pos hr (by positivity)
    have hside1 : side ≤ 1 := (lane2_cell_side_eq r J).le.trans hside
    obtain ⟨_, _, hN⟩ := hs M Rm Sreg It H hIR hdelta (OddGridIndex d (triadicHalf J))
      (oddGridCenter z r (triadicHalf J)) (fun _ => side) (fun _ => hsidepos) (fun _ => hside1)
    obtain ⟨K, _, _, _, hseq⟩ := hN N
    filter_upwards [hseq] with om hom
    intro _
    obtain ⟨seq, hmono, hbound⟩ := hom
    refine ⟨seq, hmono, ?_⟩
    intro phi hphi hcompact
    refine ⟨∑ k : OddGridIndex d (triadicHalf J),
      K om * (c2Norm (closedCube (oddGridCenter z r (triadicHalf J) k) side hsidepos :
        Set (SpatialCoordinates d)) phi) ^ 2, ?_⟩
    intro n
    apply Finset.sum_le_sum
    intro k _
    exact hbound k n (centeredCube_killedPoincare
      (oddGridCenter z r (triadicHalf J) k) hsidepos) phi
      (hphi.of_le (WithTop.coe_le_coe.mpr le_top))
      ((H1Function.ofContDiff (centeredCube z r hr).isOpen
          (hphi.of_le (by norm_num)) hcompact).restrict
        (oddGridCell z r hr (triadicHalf J) k).isOpen
        (oddGridCell_subset z hr (triadicHalf J) k)) (Filter.Eventually.of_forall fun _ => rfl)
  · exact Filter.Eventually.of_forall fun _ h => False.elim (hside h)

end
end Paper
