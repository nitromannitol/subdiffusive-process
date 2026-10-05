module

public import SubdiffusiveProcess.Paper.lem_prefix_limit_atom_extraction

@[expose] public section

/-! # Uniform unit-cell response moments

The existing response bank bounds the unit-cell zero-infrared response with a
constant chosen before the model. No concentration assertion is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators Topology
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- The native response moment bound is uniform over sufficiently small-disorder models. -/
theorem prop_conc_uniform_response_moments (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta1 B : ℝ, 0 < delta1 ∧ 0 ≤ B ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta1 →
      ∀ N : ℕ,
        MemLp (aux_lem_prefix_limit_atom_extraction_Rf M N) (ENNReal.ofReal q)
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_lem_prefix_limit_atom_extraction_Rf M N) (ENNReal.ofReal q)
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  obtain ⟨c, C, _hc, _hC, hbank⟩ := aux_psf_exists_Jval_spatial_moment_small_disorder d
  obtain ⟨δ0, hδ0, hδ⟩ := hbank q hq
  let B : ℝ := |C| * q * Real.log (2 + q) + 1
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hlog : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith only [hq])
  have hB : 0 ≤ B := add_nonneg (mul_nonneg (mul_nonneg (abs_nonneg C) hqpos.le) hlog) zero_le_one
  refine ⟨δ0, B, hδ0, hB, ?_⟩
  intro M hM
  have hMpos : 0 < M.delta := M.shellPrefix.delta_pos
  set P := (chaosSampleLaw M).toMeasure with hP
  set eta := aux_lem_prefix_limit_atom_extraction_etaC (d := d) with heta
  have hEta := aux_lem_prefix_limit_atom_extraction_etaC_spec M
  have hq0 : ENNReal.ofReal q ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hqpos
  set B1 : ℝ := C * q * Real.log (2 + q) * M.delta ^ 2 with hB1
  set E1 : ℝ≥0∞ := eLpNorm (fun _ : BilateralField d => (1 : ℝ)) (ENNReal.ofReal q) P with hE1
  have hE1fin : E1 < ∞ := (memLp_const (1 : ℝ)).eLpNorm_lt_top
  have hEone : E1 = 1 := by
    dsimp [E1]
    rw [eLpNorm_const (1 : ℝ) hq0 (NeZero.ne P)]
    simp only [enorm_one, measure_univ, ENNReal.one_rpow, mul_one]
  have hB1 : B1 ≤ |C| * q * Real.log (2 + q) := by
    have hdelta1 : M.delta ≤ 1 := M.shellPrefix.delta_le_half.trans (by norm_num)
    have hdelta2 : M.delta ^ 2 ≤ 1 := by nlinarith only [hMpos, hdelta1]
    calc
      B1 ≤ (|C| * q * Real.log (2 + q)) * M.delta ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hqpos.le) hlog)
          (sq_nonneg _)
      _ ≤ |C| * q * Real.log (2 + q) :=
        mul_le_of_le_one_right (mul_nonneg (mul_nonneg (abs_nonneg C) hqpos.le) hlog) hdelta2
  intro N
  have hshift0 : ∀ ω : BilateralField d, aux_lem_prefix_limit_atom_extraction_shift 0 0 ω = ω := by
    intro ω
    funext c
    ext x
    simp only [aux_lem_prefix_limit_atom_extraction_shift,
      aux_lem_prefix_limit_atom_extraction_affine, Int.add_zero, zero_add,
      zpow_zero, one_smul,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  have hcar := aux_lem_prefix_limit_atom_extraction_carrier M eta hEta 0 0
  have hatom : ∀ ω, aux_lem_prefix_limit_atom_extraction_atom M eta N 0 0 ω =
      (aux_psf_Jval M N (eta N ω) 0).toReal := by
    intro ω
    simp only [aux_lem_prefix_limit_atom_extraction_atom, zero_add, Int.toNat_natCast, Int.natCast_nonneg, ite_true, smul_zero]
  have hae : aux_lem_prefix_limit_atom_extraction_Rf M N =ᵐ[P]
      fun ω => (aux_psf_Jval M N (eta N ω) 0).toReal + 1 := by
    filter_upwards [hcar] with ω h
    have h' := h N (by omega)
    rw [hshift0, hatom] at h'
    simp only [zero_add, Int.toNat_natCast] at h'
    linarith only [h']
  have hlaw : Measure.map (eta N) P = M.P.toMeasure := prefix_eta_law M eta hEta N
  have hetam : AEMeasurable (eta N) P := prefix_eta_aemeasurable M eta hEta N
  have hfm : Measurable (fun η : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      (aux_psf_Jval M N η 0).toReal) :=
    (aux_lem_prefix_limit_actual_J_meas M N 0).ennreal_toReal
  have hA : eLpNorm (fun ω => (aux_psf_Jval M N (eta N ω) 0).toReal) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal B1 := by
    have heq : (fun ω => (aux_psf_Jval M N (eta N ω) 0).toReal) =
        (fun η : _root_.SubdiffusiveProcess.Model.PotentialSample d => (aux_psf_Jval M N η 0).toReal) ∘
          eta N := rfl
    rw [heq, ← eLpNorm_map_measure (hlaw ▸ hfm.aestronglyMeasurable) hetam, hlaw]
    exact hδ M hMpos hM N 0
  have hAm : AEStronglyMeasurable (fun ω => (aux_psf_Jval M N (eta N ω) 0).toReal) P :=
    (hfm.comp_aemeasurable hetam).aestronglyMeasurable
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hbound : eLpNorm (aux_lem_prefix_limit_atom_extraction_Rf M N) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal (max B1 0 + E1.toReal) := by
    rw [eLpNorm_congr_ae hae]
    refine (eLpNorm_add_le hq1).trans ?_
    rw [ENNReal.ofReal_add (le_max_right _ _) ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hE1fin.ne]
    gcongr
    exact hA.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hfinal : eLpNorm (aux_lem_prefix_limit_atom_extraction_Rf M N) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal B := hbound.trans (ENNReal.ofReal_le_ofReal (by
        rw [hEone, ENNReal.toReal_one]
        have hh := max_le hB1 (mul_nonneg (mul_nonneg (abs_nonneg C) hqpos.le) hlog)
        dsimp [B]
        linarith only [hh]))
  exact ⟨hfinal.trans_lt ENNReal.ofReal_lt_top, hfinal⟩

end
end SubdiffusiveProcess.Paper
