import SubdiffusiveProcess.Paper.rem_resolved_meshes

/-! Dilation and reflection of an arbitrary Neumann coefficient with a global
representative. This identifies the root weak equation and exact root energies;
it contains no probabilistic or regularity estimate.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal BigOperators Pointwise
noncomputable section
namespace Paper

/-- A physical Neumann solution gives a reflected native root with the exact energy scaling. -/
theorem lem_as_regularity_physical_root {d : ℕ}
    (l : ℝ) (hl : 0 < l) (cF : ℝ) (hcF : 0 < cF)
    (a : PositiveCoefficient (unitNeumannCube d))
    (A : PositiveCoefficient (centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl))
    (f : SpatialCoordinates d → ℝ)
    (hrep : (A.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl : Set (SpatialCoordinates d))] f)
    (ha : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        a.val y = cF * A.val (l • y))
    (f2 : SpatialCoordinates d → ℝ) (hf2m : Measurable f2) (Kf' : ℝ) (hKf' : 0 ≤ Kf')
    (hf2b : ∀ y, |f2 y| ≤ Kf')
    (hf20 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f2 y) = 0)
    (u : meanZeroSobolevGraph (unitNeumannCube d))
    (hu2 : ∀ ψ : weakSobolevGraph (unitNeumannCube d),
      sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d)) ψ =
        ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
          f2 x * (ψ : SobolevData (unitNeumannCube d)).1 x)
    (y : SpatialCoordinates d) (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (I : Finset (Fin d)) (Lstar Rk : ℝ) (hLstar : 10 ≤ Lstar) (hRk : 0 < Rk) (hRk3 : 3 * Rk < 1)
    (hI : ∀ i, i ∉ I → 4 * Lstar * Rk ≤ min (y i) (1 - y i))
    (ρ : ℝ) (hρ : 0 < ρ) (hρeq : ρ / 2 = l * (3 * Rk)) :
    ∃ (fc : PositiveCoefficient (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ))
      (ut : weakSobolevGraph (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ)),
      ((fc.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ :
            Set (SpatialCoordinates d))]
        fun x => f
          (coordinateFold (l • aux_rem_resolved_meshes_center y I) I
            (aux_rem_resolved_meshes_faceSet y I) x)) ∧
      (∀ φ : killedSobolevGraph (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ),
        sobolevCoefficientForm fc (ut : SobolevData (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ)) (φ : SobolevData (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ)) =
          ∫ x in (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ : Set (SpatialCoordinates d)),
            ((cF * l)⁻¹ * f2 (l⁻¹ • coordinateFold (l • aux_rem_resolved_meshes_center y I) I
              (aux_rem_resolved_meshes_faceSet y I) x)) * (φ : SobolevData (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ)).1 x) ∧
      (∀ (r : ℝ) (hr : 0 < r), r ≤ ρ →
        localGradientEnergy fc (centeredCube (l • aux_rem_resolved_meshes_center y I) r hr).isOpen.measurableSet
            (sobolevGradient (ut : SobolevData (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ))) =
          2 ^ I.card * (l ^ d * cF⁻¹ *
            aux_rem_resolved_meshes_energy a u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (r / (2 * l))))) := by
  have hset : ((centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)) = l • (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    rw [aux_rem_resolved_meshes_cube_eq_smul _ hl hl]
    change l • Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (l / (2 * l)) =
      l • Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)
    congr 2
    field_simp
  obtain ⟨v, -, hv2, hveq⟩ := aux_rem_resolved_meshes_neumann_dilate hl hset a
    A cF hcF ha f2 ⟨u.1, u.2.1⟩ hu2
  have hFm : Measurable (fun x : SpatialCoordinates d => (cF * l)⁻¹ * f2 (l⁻¹ • x)) :=
    measurable_const.mul (hf2m.comp (measurable_const_smul _))
  have hMF : 0 ≤ (cF * l)⁻¹ * Kf' := by positivity
  have hFb : ∀ x : SpatialCoordinates d, |(cF * l)⁻¹ * f2 (l⁻¹ • x)| ≤ (cF * l)⁻¹ * Kf' := by
    intro x
    rw [abs_mul, abs_of_pos (inv_pos.mpr (mul_pos hcF hl))]
    exact mul_le_mul_of_nonneg_left (hf2b _) (by positivity)
  have hF0 : (∫ x in (centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl : Set (SpatialCoordinates d)),
      (cF * l)⁻¹ * f2 (l⁻¹ • x)) = 0 := by
    rw [hset, aux_rem_resolved_meshes_setIntegral_smul _ (unitNeumannCube d).isOpen.measurableSet hl]
    have : ∀ y : SpatialCoordinates d, (cF * l)⁻¹ * f2 (l⁻¹ • (l • y)) = (cF * l)⁻¹ * f2 y :=
      fun y => by rw [smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
    simp only [this]
    rw [integral_const_mul, hf20]; ring
  have hsub := aux_rem_resolved_meshes_root_sub_folded y hy I Lstar Rk hLstar hRk hRk3 hI l hl ρ hρ hρeq
  obtain ⟨fc, ut, hfc, hueq, hE⟩ := aux_rem_resolved_meshes_fold_restrict
    (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl I (aux_rem_resolved_meshes_faceSet y I)
    A _
    ((cF * l)⁻¹ * Kf') hMF hFm.aemeasurable (Filter.Eventually.of_forall hFb) hF0 v hveq
    (l • aux_rem_resolved_meshes_center y I) ρ hρ hsub
  have hZ : ∀ i ∈ I, foldedCubeCenter (l • (fun _ : Fin d => (1 / 2 : ℝ))) l I
      (aux_rem_resolved_meshes_faceSet y I) i = (l • aux_rem_resolved_meshes_center y I) i :=
    fun i hi => aux_rem_resolved_meshes_foldCenter_eq y I l i hi
  have hfold := aux_rem_resolved_meshes_fold_center_congr _ _ I (aux_rem_resolved_meshes_faceSet y I) hZ
  refine ⟨fc, ut, ?_, ?_, ?_⟩
  · have hqmp := aux_lem_repair_err_fold_carrier_bridge_fold_qmp
      (l • aux_rem_resolved_meshes_center y I) I (aux_rem_resolved_meshes_faceSet y I)
    have hae := hqmp.ae ((ae_restrict_iff' (centeredCube _ _ _).isOpen.measurableSet).mp hrep)
    have hplane : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
        ∀ i : Fin d, x i ≠ (l • aux_rem_resolved_meshes_center y I) i := by
      rw [ae_all_iff]
      intro i
      exact Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i _
    rw [hfold] at hfc
    filter_upwards [hfc, ae_restrict_of_ae hae, ae_restrict_of_ae hplane,
      ae_restrict_mem (centeredCube _ _ _).isOpen.measurableSet] with x hx hxrep hxplane hxmem
    exact hx.trans (hxrep (aux_rem_resolved_meshes_fold_maps y hy I Lstar Rk
      hLstar hRk hRk3 hI l hl ρ hρ hρeq x hxmem hxplane))
  · intro φ
    rw [hueq φ, hfold]
  · intro r hr hrρ
    have hsubr : (centeredCube (l • aux_rem_resolved_meshes_center y I) r hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ : Set (SpatialCoordinates d)) :=
      Metric.ball_subset_ball (by linarith only [hrρ])
    rw [hE _ _ hsubr (fun J hJ => aux_rem_resolved_meshes_cube_symm _ _ I hZ hr J hJ)]
    rw [aux_rem_resolved_meshes_root_energy l hl hset a _ cF hcF ha u v hv2 _ r hr
      (centeredCube (l • aux_rem_resolved_meshes_center y I) r hr).isOpen.measurableSet]

end Paper
