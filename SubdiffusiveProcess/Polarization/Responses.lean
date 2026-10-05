module

public import SubdiffusiveProcess.Polarization.Defect
public import SubdiffusiveProcess.Sobolev.DiagonalDefect
public import SubdiffusiveProcess.Sobolev.AffineLinearMap

@[expose] public section

/-!
# The affine responses are symmetric quadratic forms in the slope

The affine Dirichlet response is the energy of the (unique, hence linear in the boundary datum)
harmonic minimizer with affine trace, and the inverse affine Neumann response is the energy of the
(unique, hence linear in the load) weak solution.  Each is therefore `p ↦ B(m p, m p)` with `m`
linear and `B` the symmetric coefficient form, i.e. `quadForm G` for the Gram matrix
`G i j = B(m e_i, m e_j)`.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- A symmetric continuous bilinear form composed with a linear map is a quadratic form. -/
theorem polarization_quadForm_repr {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u) (m : (Fin d → ℝ) →ₗ[ℝ] V) :
    ∃ G : Fin d → Fin d → ℝ, (∀ i j, G i j = G j i) ∧
      ∀ p, B (m p) (m p) = Polarization.quadForm G p := by
  classical
  refine ⟨fun i j => B (m (Pi.single i 1)) (m (Pi.single j 1)), fun i j => hB _ _, fun p => ?_⟩
  have hm : m p = ∑ i, p i • m (Pi.single i 1) := by
    conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ m p]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hv : (fun j : Fin d => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [hv]
  rw [hm]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, Polarization.quadForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hB (m (Pi.single j 1)) (m (Pi.single i 1))]
  ring

variable {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

theorem domainConstantL2_add' (c c' : ℝ) :
    domainConstantL2 (Ω := Ω) (c + c') = domainConstantL2 (Ω := Ω) c + domainConstantL2 (Ω := Ω) c' := by
  apply Lp.ext
  filter_upwards [domainConstantL2_coeFn (Ω := Ω) (c + c'), domainConstantL2_coeFn (Ω := Ω) c,
    domainConstantL2_coeFn (Ω := Ω) c',
    Lp.coeFn_add (domainConstantL2 (Ω := Ω) c) (domainConstantL2 (Ω := Ω) c')] with x h1 h2 h3 h4
  rw [h4, h1]
  simp [h2, h3]

theorem domainConstantL2_smul' (t c : ℝ) :
    domainConstantL2 (Ω := Ω) (t * c) = t • domainConstantL2 (Ω := Ω) c := by
  apply Lp.ext
  filter_upwards [domainConstantL2_coeFn (Ω := Ω) (t * c), domainConstantL2_coeFn (Ω := Ω) c,
    Lp.coeFn_smul t (domainConstantL2 (Ω := Ω) c)] with x h1 h2 h3
  rw [h3, h1]
  simp [h2]

theorem affineSobolevData_add (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p p' : Fin d → ℝ) :
    affineSobolevData hΩ (p + p') 0 = affineSobolevData hΩ p 0 + affineSobolevData hΩ p' 0 := by
  obtain ⟨T, hT, -⟩ := existsUnique_affineL2_linearMap hΩ
  refine Prod.ext ?_ ?_
  · change affineL2 hΩ (p + p') 0 = affineL2 hΩ p 0 + affineL2 hΩ p' 0
    have := map_add T (p, 0) (p', 0)
    rw [hT, hT, hT] at this
    simpa using this
  · funext i
    change domainConstantL2 ((p + p') i) = domainConstantL2 (p i) + domainConstantL2 (p' i)
    exact domainConstantL2_add' _ _

theorem affineSobolevData_smul (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (t : ℝ) (p : Fin d → ℝ) :
    affineSobolevData hΩ (t • p) 0 = t • affineSobolevData hΩ p 0 := by
  obtain ⟨T, hT, -⟩ := existsUnique_affineL2_linearMap hΩ
  refine Prod.ext ?_ ?_
  · change affineL2 hΩ (t • p) 0 = t • affineL2 hΩ p 0
    have := map_smul T t (p, 0)
    rw [hT, hT] at this
    simpa using this
  · funext i
    change domainConstantL2 (t * p i) = t • domainConstantL2 (p i)
    exact domainConstantL2_smul' _ _

omit [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))] in
/-- The Dirichlet minimizer is additive in the boundary datum. -/
theorem dirichletMinimizer_val_add {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [_finite : IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b b1 b2 : weakSobolevGraph Ω) (hb : b.val = b1.val + b2.val) :
    (dirichletMinimizer S a b).val =
      (dirichletMinimizer S a b1).val + (dirichletMinimizer S a b2).val := by
  have hu : ((dirichletMinimizer S a b1).val + (dirichletMinimizer S a b2).val) - b.val ∈ S.space := by
    have := S.space.add_mem (dirichletMinimizer_mem_affine S a b1)
      (dirichletMinimizer_mem_affine S a b2)
    convert this using 1
    rw [hb]; abel
  have he : ∀ w : S.space, sobolevCoefficientForm a
      ((dirichletMinimizer S a b1).val + (dirichletMinimizer S a b2).val) w.val = 0 := by
    intro w
    rw [map_add, add_apply, dirichletMinimizer_euler, dirichletMinimizer_euler,
      add_zero]
  have := dirichletMinimizer_eq_of_euler S a b
    ⟨(dirichletMinimizer S a b1).val + (dirichletMinimizer S a b2).val,
      (weakSobolevGraph Ω).add_mem (dirichletMinimizer S a b1).property
        (dirichletMinimizer S a b2).property⟩ hu he
  exact (congrArg Subtype.val this).symm

omit [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))] in
/-- The Dirichlet minimizer is homogeneous in the boundary datum. -/
theorem dirichletMinimizer_val_smul {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [_finite : IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b b1 : weakSobolevGraph Ω) (t : ℝ) (hb : b.val = t • b1.val) :
    (dirichletMinimizer S a b).val = t • (dirichletMinimizer S a b1).val := by
  have hu : t • (dirichletMinimizer S a b1).val - b.val ∈ S.space := by
    have := S.space.smul_mem t (dirichletMinimizer_mem_affine S a b1)
    convert this using 1
    rw [hb, smul_sub]
  have he : ∀ w : S.space, sobolevCoefficientForm a (t • (dirichletMinimizer S a b1).val) w.val = 0 := by
    intro w
    rw [map_smul, smul_apply, dirichletMinimizer_euler, smul_zero]
  have := dirichletMinimizer_eq_of_euler S a b
    ⟨t • (dirichletMinimizer S a b1).val,
      (weakSobolevGraph Ω).smul_mem t (dirichletMinimizer S a b1).property⟩ hu he
  exact (congrArg Subtype.val this).symm

/-- The affine Dirichlet response is a symmetric quadratic form in the slope. -/
theorem affineDirichletResponse_isQuad
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) :
    ∃ G : Fin d → Fin d → ℝ, (∀ i j, G i j = G j i) ∧
      ∀ p, affineDirichletResponse hΩ hP a p = Polarization.quadForm G p := by
  let S := killedResponseSpace hP
  let m : (Fin d → ℝ) →ₗ[ℝ] SobolevData Ω :=
    { toFun := fun p => (dirichletMinimizer S a (affineSobolev hΩ p 0)).val
      map_add' := fun p p' =>
        dirichletMinimizer_val_add S a _ _ _ (affineSobolevData_add hΩ p p')
      map_smul' := fun t p => by
        simpa using dirichletMinimizer_val_smul S a _ _ t (affineSobolevData_smul hΩ t p) }
  obtain ⟨G, hG, hGq⟩ := polarization_quadForm_repr (sobolevCoefficientForm a)
    (sobolevCoefficientForm_symm a) m
  exact ⟨G, hG, fun p => hGq p⟩

omit [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))] in
/-- The weak solution is additive in the load. -/
theorem responseSolution_val_add {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [_finite : IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L L1 L2 : S.space →L[ℝ] ℝ) (hL : L = L1 + L2) :
    responseSolution S a L = responseSolution S a L1 + responseSolution S a L2 := by
  symm
  apply responseSolution_eq
  intro v
  rw [map_add, add_apply, responseSolution_spec, responseSolution_spec, hL]
  rfl

omit [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))] in
theorem responseSolution_val_smul {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [_finite : IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L L1 : S.space →L[ℝ] ℝ) (t : ℝ) (hL : L = t • L1) :
    responseSolution S a L = t • responseSolution S a L1 := by
  symm
  apply responseSolution_eq
  intro v
  rw [map_smul, smul_apply, responseSolution_spec, hL]
  rfl

theorem affineNeumannLoad_add (p p' : Fin d → ℝ) :
    affineNeumannLoad (Ω := Ω) (p + p') = affineNeumannLoad p + affineNeumannLoad p' := by
  ext g
  simp only [affineNeumannLoad, sum_apply, add_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, PiLp.proj_apply, Pi.add_apply,
    domainConstantL2_add', inner_add_left, Finset.sum_add_distrib]

theorem affineNeumannLoad_smul (t : ℝ) (p : Fin d → ℝ) :
    affineNeumannLoad (Ω := Ω) (t • p) = t • affineNeumannLoad p := by
  ext g
  simp only [affineNeumannLoad, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, PiLp.proj_apply, Pi.smul_apply,
    smul_eq_mul, domainConstantL2_smul', inner_smul_left, Finset.mul_sum]
  simp

/-- The inverse affine Neumann response is a symmetric quadratic form in the slope. -/
theorem affineInverseNeumannResponse_isQuad
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) :
    ∃ G : Fin d → Fin d → ℝ, (∀ i j, G i j = G j i) ∧
      ∀ p, affineInverseNeumannResponse hP a p = Polarization.quadForm G p := by
  let S := meanZeroResponseSpace hP
  let m : (Fin d → ℝ) →ₗ[ℝ] S.space :=
    { toFun := fun p => responseSolution S a
        ((affineNeumannLoad p).comp (subspaceGradient (meanZeroSobolevGraph Ω)))
      map_add' := fun p p' => by
        apply responseSolution_val_add
        simpa only [affineNeumannLoad_add] using!
          ContinuousLinearMap.add_comp (affineNeumannLoad p) (affineNeumannLoad p')
            (subspaceGradient (meanZeroSobolevGraph Ω))
      map_smul' := fun t p => by
        simp only [RingHom.id_apply]
        apply responseSolution_val_smul
        simpa only [affineNeumannLoad_smul] using!
          ContinuousLinearMap.smul_comp t (affineNeumannLoad p)
            (subspaceGradient (meanZeroSobolevGraph Ω)) }
  obtain ⟨G, hG, hGq⟩ := polarization_quadForm_repr (responseForm S a)
    (responseForm_symm S a) m
  exact ⟨G, hG, fun p => hGq p⟩

end SubdiffusiveProcess
