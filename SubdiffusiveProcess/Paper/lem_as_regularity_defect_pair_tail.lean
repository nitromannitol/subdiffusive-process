module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_bank_limit_tail
public import SubdiffusiveProcess.Paper.inputs_classical_affine_response_polarization
public import SubdiffusiveProcess.Probability.FiniteRelativeComparison

@[expose] public section

/-! Quantitative two-cutoff comparison of the maximal unit response defect.
The finite affine response bank and classical polarization give a relative
comparison, uniform in the future cutoff. No growing-mesh transfer is claimed.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The maximal normalized diagonal response defect on the zero-infrared unit cube. -/
def aux_lem_as_regularity_defect_pair_tail_value {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) (omega : BilateralField d) : ℝ :=
  sSup {v : ℝ | ∃ e : SpatialCoordinates d, (∑ i : Fin d, (e i) ^ 2) = 1 ∧
    v = (aux_matched_affine_finite_response M e false N omega +
      aux_matched_affine_finite_response M e true N omega) /
      (2 * volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) - 1}

/-- The fixed finite polarization directions. -/
def aux_lem_as_regularity_defect_pair_tail_dirs (d : ℕ) :
    Fin d ⊕ (Fin d × Fin d) → SpatialCoordinates d :=
  Sum.elim (fun i => Pi.single i 1) (fun ij => Pi.single ij.1 1 + Pi.single ij.2 1)

/-- The dimensional constant supplied by classical polarization. -/
def aux_lem_as_regularity_defect_pair_tail_constant (d : ℕ) [NeZero d] : ℝ :=
  (inputs_classical_affine_response_polarization d (Nat.pos_of_ne_zero (NeZero.ne d))).choose

/-- The polarization constant is positive. -/
theorem aux_lem_as_regularity_defect_pair_tail_constant_pos (d : ℕ) [NeZero d] :
    0 < aux_lem_as_regularity_defect_pair_tail_constant d :=
  (inputs_classical_affine_response_polarization d
    (Nat.pos_of_ne_zero (NeZero.ne d))).choose_spec.1

/-- A finite affine-response comparison controls the pointwise maximal defect. -/
theorem aux_lem_as_regularity_defect_pair_tail_point {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N N' : ℕ) (omega : BilateralField d)
    (eta : ℝ) (heta : 0 ≤ eta)
    (herr : ∀ i branch,
      |aux_matched_affine_finite_response M (aux_lem_as_regularity_defect_pair_tail_dirs d i)
          branch N omega -
        aux_matched_affine_finite_response M (aux_lem_as_regularity_defect_pair_tail_dirs d i)
          branch N' omega| ≤ eta *
        (volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
            Set (SpatialCoordinates d)) +
          aux_matched_affine_finite_response M (aux_lem_as_regularity_defect_pair_tail_dirs d i)
            branch N omega)) :
    |aux_lem_as_regularity_defect_pair_tail_value M N omega -
      aux_lem_as_regularity_defect_pair_tail_value M N' omega| ≤
      aux_lem_as_regularity_defect_pair_tail_constant d * eta *
        (1 + aux_lem_as_regularity_defect_pair_tail_value M N omega) := by
  have hpol := (inputs_classical_affine_response_polarization d
    (Nat.pos_of_ne_zero (NeZero.ne d))).choose_spec.2
  have hp := hpol (0 : SpatialCoordinates d) 1 one_pos
    (aux_matched_root_poincare (d := d)).1 (aux_matched_root_poincare (d := d)).2
    (cutoffPositiveCoefficient M (fun _ => 0) omega N' (0 : SpatialCoordinates d) one_pos)
    (cutoffPositiveCoefficient M (fun _ => 0) omega N (0 : SpatialCoordinates d) one_pos)
    eta heta (by
      intro i branch
      change |aux_matched_affine_finite_response M
          (aux_lem_as_regularity_defect_pair_tail_dirs d i) branch N' omega -
        aux_matched_affine_finite_response M
          (aux_lem_as_regularity_defect_pair_tail_dirs d i) branch N omega| ≤ _
      rw [abs_sub_comm]
      exact herr i branch)
  change |aux_lem_as_regularity_defect_pair_tail_value M N' omega -
    aux_lem_as_regularity_defect_pair_tail_value M N omega| ≤
      aux_lem_as_regularity_defect_pair_tail_constant d * eta *
        (1 + aux_lem_as_regularity_defect_pair_tail_value M N omega) at hp
  rwa [abs_sub_comm] at hp

/-- Polarization transfers the affine response comparison to the maximal defect. -/
theorem lem_as_regularity_defect_pair_tail
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ eps : ℝ, 0 < eps → ∃ C c : ℝ, ∃ N0 : ℕ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, N0 ≤ N → ∃ M0 : ℕ, N ≤ M0 ∧ ∀ N' : ℕ, M0 ≤ N' →
          (chaosSampleLaw M).toMeasure {omega |
            eps * (1 + aux_lem_as_regularity_defect_pair_tail_value M N omega) <
              |aux_lem_as_regularity_defect_pair_tail_value M N omega -
                aux_lem_as_regularity_defect_pair_tail_value M N' omega|} ≤
            ENNReal.ofReal (C * (3 : ℝ) ^ (-c * (N : ℝ))) := by
  obtain ⟨dD, gD, hdD, hgD, hD⟩ := aux_actual_root_dirichlet_pair_tail
    d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  obtain ⟨dN, gN, hdN, hgN, hN⟩ := aux_actual_root_inverse_neumann_pair_tail
    d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  let Cpol := aux_lem_as_regularity_defect_pair_tail_constant d
  have hCpol : 0 < Cpol := aux_lem_as_regularity_defect_pair_tail_constant_pos d
  refine ⟨min 1 (min dD dN), lt_min zero_lt_one (lt_min hdD hdN), ?_⟩
  intro M Rm Sreg It H hH hdelta eps heps
  have hMD : M.delta ≤ min 1 dD :=
    hdelta.trans (min_le_min_left 1 (min_le_left _ _))
  have hMN : M.delta ≤ min 1 dN :=
    hdelta.trans (min_le_min_left 1 (min_le_right _ _))
  let dirs := aux_lem_as_regularity_defect_pair_tail_dirs d
  let Index := Bool × (Fin d ⊕ (Fin d × Fin d))
  let F : Index → ℕ → BilateralField d → ℝ :=
    fun i => aux_matched_affine_finite_response M (dirs i.2) i.1
  have hbank : ∀ i (eta : ℝ), 0 < eta →
      ∃ C c : ℝ, ∃ N0 : ℕ, 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, N0 ≤ N → ∃ M0 : ℕ, N ≤ M0 ∧ ∀ N' : ℕ, M0 ≤ N' →
          (chaosSampleLaw M).toMeasure {omega | eta * F i N omega +
            C * (3 : ℝ) ^ (-c * (N : ℝ)) < |F i N omega - F i N' omega|} ≤
              ENNReal.ofReal (C * (3 : ℝ) ^ (-c * (N : ℝ))) := by
    rintro ⟨branch, i⟩ eta heta
    cases branch with
    | false =>
      have hscale : gD * (eta / gD) = eta := by field_simp [hgD.ne']
      obtain ⟨C, c, N0, hC, hc, hcomp⟩ := hD M Rm Sreg It H hH hMD
        (dirs i) (eta / gD) (div_pos heta hgD)
      refine ⟨C, c, N0, hC, hc, ?_⟩
      simpa only [F, neg_mul, ← mul_assoc, hscale] using hcomp
    | true =>
      have hscale : gN * (eta / gN) = eta := by field_simp [hgN.ne']
      obtain ⟨C, c, N0, hC, hc, hcomp⟩ := hN M Rm Sreg It H hH hMN
        (dirs i) (eta / gN) (div_pos heta hgN)
      refine ⟨C, c, N0, hC, hc, ?_⟩
      simpa only [F, neg_mul, ← mul_assoc, hscale] using hcomp
  let vol : ℝ := volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
    Set (SpatialCoordinates d))
  have hvol : 0 < vol := centeredCube_volume_pos (0 : SpatialCoordinates d) one_pos
  obtain ⟨C, c, N0, hC, hc, hcomp⟩ := finite_relative_pair_comparison
    (chaosSampleLaw M).toMeasure F hbank (eps / Cpol) vol (div_pos heps hCpol) hvol
  refine ⟨C, c, N0, hC, hc, ?_⟩
  intro N hN0
  obtain ⟨M0, hNM0, hM0⟩ := hcomp N hN0
  refine ⟨M0, hNM0, fun N' hN' => ?_⟩
  refine (measure_mono (fun omega homega => ?_)).trans (hM0 N' hN')
  by_contra hnot
  have herr (i : Index) : |F i N omega - F i N' omega| ≤
      (eps / Cpol) * (vol + F i N omega) :=
    le_of_not_gt (fun hi => hnot ⟨i, hi⟩)
  have hp := aux_lem_as_regularity_defect_pair_tail_point M N N' omega
    (eps / Cpol) (div_pos heps hCpol).le (fun i branch => herr (branch, i))
  have hscale : Cpol * (eps / Cpol) = eps := by field_simp [hCpol.ne']
  change _ ≤ Cpol * (eps / Cpol) * _ at hp
  rw [hscale] at hp
  exact (not_le_of_gt homega) hp

end SubdiffusiveProcess.Paper
