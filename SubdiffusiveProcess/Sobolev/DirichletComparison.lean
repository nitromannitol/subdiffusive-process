module

public import SubdiffusiveProcess.Sobolev.DirichletResponse

@[expose] public section

/-! # Coefficient comparison for actual boundary minima

The variational class is unchanged when the coefficient is changed. Energy
order and scalar homogeneity therefore give multiplicative continuity of the
boundary response, as needed for retained-potential compactness.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Scalar homogeneity of the coefficient energy on full Sobolev data. -/
theorem sobolevCoefficientForm_scale (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient Ω) (u v : SobolevData Ω) :
    sobolevCoefficientForm (scalePositiveCoefficient r hr a) u v =
      r * sobolevCoefficientForm a u v := by
  simp only [sobolevCoefficientForm, ContinuousLinearMap.bilinearComp_apply,
    weightedGradientForm, sum_apply, PiLp.proj_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => weightedL2Form_smul (E := ℝ) r a.val _ _

/-- Coefficient order is energy order, including for nonzero boundary data. -/
theorem sobolevCoefficientForm_mono (a b : PositiveCoefficient Ω)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ b.val x)
    (u : SobolevData Ω) : sobolevCoefficientForm a u u ≤ sobolevCoefficientForm b u u := by
  simp only [sobolevCoefficientForm, ContinuousLinearMap.bilinearComp_apply,
    weightedGradientForm, sum_apply, PiLp.proj_apply]
  exact Finset.sum_le_sum fun i _ => weightedL2Form_mono (E := ℝ) hab _

/-- Increasing the coefficient increases the actual boundary minimum. -/
theorem dirichletResponse_mono (S : ResponseSpace Ω) (a b : PositiveCoefficient Ω)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ b.val x)
    (g : weakSobolevGraph Ω) : dirichletResponse S a g ≤ dirichletResponse S b g := by
  let w : S.space := ⟨(dirichletMinimizer S b g).val - g.val,
    dirichletMinimizer_mem_affine S b g⟩
  have hw : g.val + w.val = (dirichletMinimizer S b g).val := by
    dsimp [w]
    abel
  have h := (dirichletResponse_isLeast S a g).2 ⟨w, rfl⟩
  change dirichletResponse S a g ≤ sobolevCoefficientForm a (g.val + w.val) (g.val + w.val) at h
  rw [hw] at h
  exact h.trans (sobolevCoefficientForm_mono a b hab _)

/-- Multiplying the coefficient by a positive constant leaves its harmonic extension unchanged. -/
theorem dirichletMinimizer_scale_coefficient (S : ResponseSpace Ω)
    (r : ℝ) (hr : 0 < r) (a : PositiveCoefficient Ω) (g : weakSobolevGraph Ω) :
    dirichletMinimizer S (scalePositiveCoefficient r hr a) g = dirichletMinimizer S a g := by
  symm
  apply dirichletMinimizer_eq_of_euler
  · exact dirichletMinimizer_mem_affine S a g
  · intro w
    rw [sobolevCoefficientForm_scale, dirichletMinimizer_euler, mul_zero]

/-- The actual boundary minimum has direct scalar coefficient homogeneity. -/
theorem dirichletResponse_scale_coefficient (S : ResponseSpace Ω)
    (r : ℝ) (hr : 0 < r) (a : PositiveCoefficient Ω) (g : weakSobolevGraph Ω) :
    dirichletResponse S (scalePositiveCoefficient r hr a) g = r * dirichletResponse S a g := by
  unfold dirichletResponse
  rw [dirichletMinimizer_scale_coefficient, sobolevCoefficientForm_scale]

/-- The two-sided coefficient comparison gives the boundary-response estimate
used by finite-band compactness. -/
theorem dirichletResponse_exp_comparison (S : ResponseSpace Ω)
    (a b : PositiveCoefficient Ω) (g : weakSobolevGraph Ω) (D : ℝ)
    (hl : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      Real.exp (-D) * a.val x ≤ b.val x)
    (hu : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      b.val x ≤ Real.exp D * a.val x) :
    Real.exp (-D) * dirichletResponse S a g ≤ dirichletResponse S b g ∧
      dirichletResponse S b g ≤ Real.exp D * dirichletResponse S a g := by
  have hlow := dirichletResponse_mono S
    (scalePositiveCoefficient (Real.exp (-D)) (Real.exp_pos (-D)) a) b
    (by
      filter_upwards [hl, scalePositiveCoefficient_coeFn (Real.exp (-D)) (Real.exp_pos (-D)) a]
        with x hx he
      rwa [he]) g
  have hupp := dirichletResponse_mono S b (scalePositiveCoefficient (Real.exp D) (Real.exp_pos D) a)
    (by
      filter_upwards [hu, scalePositiveCoefficient_coeFn (Real.exp D) (Real.exp_pos D) a] with x hx he
      rwa [he]) g
  rw [dirichletResponse_scale_coefficient] at hlow hupp
  exact ⟨hlow, hupp⟩

end SubdiffusiveProcess
