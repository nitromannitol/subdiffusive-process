module

public import SubdiffusiveProcess.Sobolev.UnitResponseSource
public import SubdiffusiveProcess.Lane2.MeshGluing

@[expose] public section

/-! A fixed harmonic mesh supplies a nondegenerate test for the killed inverse.
The energy bound is a finite sum of cell Dirichlet infima; no moment bound is assumed. -/

open MeasureTheory Set TopologicalSpace Homogenization Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators

namespace SubdiffusiveProcess
noncomputable section

/-- A pointwise bound on the unit cube is also its unnormalized L² bound. -/
theorem unitCube_l2_norm_le_of_ae_bound {d : ℕ}
    (f : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  have h := Lp.norm_le_of_ae_bound hC hf
  simpa only [measureUnivNNReal, Measure.restrict_apply_univ, centeredCube_volume,
    one_pow, ENNReal.ofReal_one, ENNReal.toNNReal_one, NNReal.coe_one,
    Real.one_rpow, one_mul] using h

/-- One deterministic mesh makes its maximum-principle error smaller than a given tolerance. -/
theorem exists_triadic_mesh_error_lt (C D epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ J : ℕ, C * (1 / (3 : ℝ) ^ J) * |D| < epsilon := by
  have ht : Tendsto (fun J : ℕ => C * (1 / (3 : ℝ) ^ J) * |D|) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)).const_mul C).mul_const |D|
    simpa only [one_div, inv_pow, mul_zero, zero_mul] using h
  exact (ht.eventually (gt_mem_nhds hepsilon)).exists

/-- A smooth nonzero source admits a coefficient-independent mesh response test. -/
theorem exists_unit_mesh_inverseResponse_bound {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (phi : H1Function (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)))
    (hphi : ContDiff ℝ ∞ phi.toFun) (hcompact : HasCompactSupport phi.toFun)
    (hsupport : tsupport phi.toFun ⊆
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
    (hsource : (sobolevDataOfH1 phi).1 ≠ 0) :
    ∃ J : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ (S : ResponseSpace (centeredCube (0 : SpatialCoordinates d) 1 one_pos)),
      S.space = killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos) →
      ∀ (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
        (c : SpatialCoordinates d → ℝ) (lam Lam : ℝ),
      0 < lam → Continuous c →
      (∀ x ∈ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
        lam ≤ c x ∧ c x ≤ Lam) →
      ((fun x => a.val x) =ᵐ[volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))] c) →
      0 < inverseResponse S a
          ((sobolevVolumeLoad (sobolevDataOfH1 phi).1).comp S.space.subtypeL) ∧
        (inverseResponse S a
          ((sobolevVolumeLoad (sobolevDataOfH1 phi).1).comp S.space.subtypeL))⁻¹ ≤
          B * ∑ k : OddGridIndex d (triadicHalf J),
            cellDirichletInfimum c
              (oddGridCell (0 : SpatialCoordinates d) 1 one_pos (triadicHalf J) k :
                Set (SpatialCoordinates d))
              (phi.restrict (oddGridCell (0 : SpatialCoordinates d) 1 one_pos
                (triadicHalf J) k).isOpen (oddGridCell_subset 0 one_pos (triadicHalf J) k)) := by
  obtain ⟨C, hC, hmesh⟩ := lane2_meshInterpolator hd
  let D := sSup ((fun y => ‖fderiv ℝ phi.toFun y‖) ''
    closure (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
  obtain ⟨J, hJ⟩ := exists_triadic_mesh_error_lt C D
    (‖(sobolevDataOfH1 phi).1‖ / 2) (half_pos (norm_pos_iff.mpr hsource))
  refine ⟨J, ((‖(sobolevDataOfH1 phi).1‖ ^ 2 / 2) ^ 2)⁻¹, by positivity, ?_⟩
  intro S hS a c lam Lam hlam hc hbounds hca
  obtain ⟨v, _hcont, _hcells, henergy, herror⟩ :=
    hmesh 0 1 one_pos J c lam Lam hlam hc hbounds phi hphi hcompact hsupport
  let w : S.space := ⟨sobolevDataOfH1 v.toH1Function, by
    rw [hS]
    exact sobolevDataOfH1_mem_killed v⟩
  have hclose : ‖w.val.1 - (sobolevDataOfH1 phi).1‖ ≤
      ‖(sobolevDataOfH1 phi).1‖ / 2 := by
    apply (unitCube_l2_norm_le_of_ae_bound _
      (mul_nonneg (mul_nonneg hC (by positivity)) (abs_nonneg D)) ?_).trans hJ.le
    filter_upwards [Lp.coeFn_sub w.val.1 (sobolevDataOfH1 phi).1,
      sobolevDataOfH1_fst_coeFn v.toH1Function, sobolevDataOfH1_fst_coeFn phi,
      ae_restrict_mem (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet]
      with x hsub hv hp hx
    change ‖(w.val.1 - (sobolevDataOfH1 phi).1) x‖ ≤ _
    rw [hsub, Pi.sub_apply]
    change ‖(sobolevDataOfH1 v.toH1Function).1 x - (sobolevDataOfH1 phi).1 x‖ ≤ _
    rw [hv, hp, Real.norm_eq_abs]
    exact (herror x hx).trans
      (mul_le_mul_of_nonneg_left (le_abs_self D) (mul_nonneg hC (by positivity)))
  have htest := inverseResponse_inv_le_of_source_approximation S a
    (sobolevDataOfH1 phi).1 hsource w hclose
  refine ⟨htest.1, htest.2.trans_eq ?_⟩
  have heq : responseForm S a w w =
      energy c (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) v.toH1Function :=
    (energy_eq_sobolevCoefficientForm a c hca v.toH1Function).symm
  rw [heq, henergy, div_eq_mul_inv, mul_comm]
  rfl

end
end SubdiffusiveProcess
