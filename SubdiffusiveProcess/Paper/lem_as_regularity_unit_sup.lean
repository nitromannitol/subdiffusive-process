module

public import SubdiffusiveProcess.Paper.lem_as_coarse
public import SubdiffusiveProcess.Paper.inputs_hES_witness
public import SubdiffusiveProcess.Paper.inputs_classical_fractional_dirichlet_sup
public import SubdiffusiveProcess.Paper.prop_growth_holder_assembly

@[expose] public section

/-! The uniform Dirichlet supremum follows from the already established
pathwise fractional coercivity and the classical Stampacchia estimate.
This file asserts no energy decay or Holder estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

namespace SubdiffusiveProcess.Paper

/-- One almost-sure constant bounds all cutoff Dirichlet solutions with bounded
source and bounded smooth boundary data on the closed unit cube. -/
theorem lem_as_regularity_unit_sup
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ B : ℝ, 0 < B ∧
        ∀ N : ℕ,
          ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
            AEMeasurable F
              (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
            (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
              |F x| ≤ Kf) →
            ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
              ContDiff ℝ 2 phi →
              c2Norm
                  (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                    Set (SpatialCoordinates d)) phi ≤ Cphi →
              ∀ (b u : weakSobolevGraph (unitNeumannCube d)),
                ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
                    phi →
                SolvesDirichlet
                    (cutoffPositiveCoefficient M H omega N
                      (fun _ => (1 / 2 : ℝ)) one_pos) F b u →
                ∀ U : SpatialCoordinates d → ℝ, Continuous U →
                  ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                    =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U →
                  ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)),
                    |U x| ≤ B * (Kf + Cphi)  := by
  obtain ⟨delta0, hdelta0, hcoarse⟩ :=
    lem_as_coarse d hd E Pc Xc Sf W Cp D inputs_hES_witness Step Dbase Interp
      (1 / 8) (3 / 4) (by norm_num) (by norm_num)
  obtain ⟨C, hC, hstamp⟩ := inputs_classical_fractional_dirichlet_sup
    d hd threeQuarterOrder (fun _ => (1 / 2 : ℝ)) 1 one_pos
  refine ⟨min 1 delta0, lt_min one_pos hdelta0, ?_⟩
  intro M Rm Sreg It H hIR hdelta
  have hevent := hcoarse M Rm Sreg It H hIR hdelta
    (fun _ => (1 / 2 : ℝ)) 1 one_pos ⟨0, by norm_num⟩
  filter_upwards [hevent] with omega homega
  obtain ⟨K, hK, hbank⟩ := homega
  refine ⟨1 + C * K, add_pos one_pos (mul_pos hC hK), ?_⟩
  intro N F Kf hKf hF hFb phi Cphi hphi hCphi b u hb hsol U hU hu x hx
  have hcoerc := (hbank true).2.1 N
  have hbound := hstamp
    (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos)
    K hK hcoerc F Kf hKf hF hFb phi Cphi hphi.continuous
    (fun y hy => (aux_prop_growth_holder_assembly_abs_le_c2Norm
      (fun _ => (1 / 2 : ℝ)) one_pos hphi.continuous hy).trans hCphi)
    b u hb hsol U hU hu x hx
  have hCphi0 : 0 ≤ Cphi :=
    (aux_prop_growth_holder_assembly_c2Norm_nonneg _ _).trans hCphi
  have hprod : 0 ≤ C * K * Cphi := mul_nonneg (mul_nonneg hC.le hK.le) hCphi0
  calc
    |U x| ≤ Cphi + C * K * Kf := hbound
    _ ≤ (1 + C * K) * (Kf + Cphi) := by nlinarith only [hKf, hprod]

end SubdiffusiveProcess.Paper
