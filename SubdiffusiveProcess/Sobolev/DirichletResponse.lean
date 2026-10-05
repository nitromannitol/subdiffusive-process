module

public import SubdiffusiveProcess.Sobolev.ResponseComparison
public import SubdiffusiveProcess.Sobolev.ResponsePositivity

@[expose] public section

/-!
# Canonical boundary responses

Boundary data are actual elements of the weak H1 graph. Admissible functions
differ by an element of the concrete variation space; for the killed space
this is the usual H1/H1_0 boundary class. The minimizer is constructed from
the source solver with load -E(b, ·), and the minimum is proved attained.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- The actual coefficient form on full function/gradient data. -/
def sobolevCoefficientForm (a : PositiveCoefficient Ω) :
    SobolevData Ω →L[ℝ] SobolevData Ω →L[ℝ] ℝ :=
  (weightedGradientForm a.val).bilinearComp sobolevGradient sobolevGradient

/-- Symmetry also holds before imposing killed or mean-zero variations. -/
theorem sobolevCoefficientForm_symm (a : PositiveCoefficient Ω) (u v : SobolevData Ω) :
    sobolevCoefficientForm a u v = sobolevCoefficientForm a v u :=
  weightedGradientForm_symm a.val _ _

/-- Full gradient energies are nonnegative, without a Poincare condition. -/
theorem sobolevCoefficientForm_nonneg (a : PositiveCoefficient Ω) (u : SobolevData Ω) :
    0 ≤ sobolevCoefficientForm a u u := by
  obtain ⟨c, hc, ha⟩ := a.property
  obtain ⟨c', hc', hb⟩ := weightedGradientForm_coercive a.val hc ha
  exact (mul_nonneg (mul_nonneg hc'.le (norm_nonneg _)) (norm_nonneg _)).trans (hb _)

/-- The load that corrects a given H1 extension to a harmonic one. -/
def boundaryCorrectionLoad (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) : S.space →L[ℝ] ℝ :=
  -((sobolevCoefficientForm a b.val).comp S.space.subtypeL)

/-- The actual harmonic extension in the given affine Sobolev class. -/
def dirichletMinimizer (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) : weakSobolevGraph Ω :=
  ⟨b.val + (responseSolution S a (boundaryCorrectionLoad S a b) : SobolevData Ω),
    (weakSobolevGraph Ω).add_mem b.property (S.le_weak (responseSolution S a _).property)⟩

/-- The correction belongs to the specified variation space. -/
theorem dirichletMinimizer_mem_affine (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) :
    (dirichletMinimizer S a b).val - b.val ∈ S.space := by
  simpa only [dirichletMinimizer, add_sub_cancel_left] using
    (responseSolution S a (boundaryCorrectionLoad S a b)).property

/-- The constructed extension satisfies the harmonic Euler equation. -/
theorem dirichletMinimizer_euler (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) (w : S.space) :
    sobolevCoefficientForm a (dirichletMinimizer S a b).val w.val = 0 := by
  have he := responseSolution_spec S a (boundaryCorrectionLoad S a b) w
  change sobolevCoefficientForm a (responseSolution S a (boundaryCorrectionLoad S a b)).val w.val =
    -(sobolevCoefficientForm a b.val w.val) at he
  change sobolevCoefficientForm a (b.val + (responseSolution S a (boundaryCorrectionLoad S a b)).val)
    w.val = 0
  rw [map_add, add_apply, he, add_neg_cancel]

/-- The scalar boundary response is the actual energy of its constructed extension. -/
def dirichletResponse (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) : ℝ :=
  sobolevCoefficientForm a (dirichletMinimizer S a b).val (dirichletMinimizer S a b).val

/-- Every admissible competitor loses exactly the energy of its difference from the minimizer. -/
theorem dirichletResponse_energy_gap (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) (w : S.space) :
    sobolevCoefficientForm a (b.val + w.val) (b.val + w.val) =
      dirichletResponse S a b + sobolevCoefficientForm a
        (b.val + w.val - (dirichletMinimizer S a b).val)
        (b.val + w.val - (dirichletMinimizer S a b).val) := by
  apply bilinear_affine_energy_gap _ (sobolevCoefficientForm_symm a)
  have he := dirichletMinimizer_euler S a b
    (w - responseSolution S a (boundaryCorrectionLoad S a b))
  simpa only [dirichletMinimizer, Submodule.coe_sub, add_sub_add_left_eq_sub] using he

/-- The boundary variational formula is an attained least value. -/
theorem dirichletResponse_isLeast (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) :
    IsLeast (Set.range fun w : S.space =>
      sobolevCoefficientForm a (b.val + w.val) (b.val + w.val)) (dirichletResponse S a b) := by
  constructor
  · exact ⟨responseSolution S a (boundaryCorrectionLoad S a b), rfl⟩
  · rintro x ⟨w, rfl⟩
    change dirichletResponse S a b ≤ sobolevCoefficientForm a (b.val + w.val) (b.val + w.val)
    rw [dirichletResponse_energy_gap]
    exact le_add_of_nonneg_right (sobolevCoefficientForm_nonneg a _)

/-- Nonnegativity is proved for the actual boundary response. -/
theorem dirichletResponse_nonneg (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) : 0 ≤ dirichletResponse S a b := sobolevCoefficientForm_nonneg a _

/-- A minimizing extension is unique in its affine Sobolev class. -/
theorem dirichletMinimizer_unique (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b : weakSobolevGraph Ω) (w : S.space)
    (hmin : sobolevCoefficientForm a (b.val + w.val) (b.val + w.val) ≤ dirichletResponse S a b) :
    b.val + w.val = (dirichletMinimizer S a b).val := by
  have hg := dirichletResponse_energy_gap S a b w
  have hz : sobolevCoefficientForm a
      (b.val + w.val - (dirichletMinimizer S a b).val)
      (b.val + w.val - (dirichletMinimizer S a b).val) = 0 := by
    linarith [sobolevCoefficientForm_nonneg a
      (b.val + w.val - (dirichletMinimizer S a b).val)]
  have hdiff : responseForm S a
      (w - responseSolution S a (boundaryCorrectionLoad S a b))
      (w - responseSolution S a (boundaryCorrectionLoad S a b)) = 0 := by
    change sobolevCoefficientForm a
      (w - responseSolution S a (boundaryCorrectionLoad S a b)).val
      (w - responseSolution S a (boundaryCorrectionLoad S a b)).val = 0
    simpa only [dirichletMinimizer, Submodule.coe_sub, add_sub_add_left_eq_sub] using hz
  have hw := sub_eq_zero.mp ((responseForm_self_eq_zero_iff S a _).mp hdiff)
  exact congrArg (fun v : S.space => b.val + v.val) hw

/-- The harmonic equation uniquely characterizes the extension in its boundary class. -/
theorem dirichletMinimizer_eq_of_euler (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b u : weakSobolevGraph Ω) (hu : u.val - b.val ∈ S.space)
    (he : ∀ w : S.space, sobolevCoefficientForm a u.val w.val = 0) :
    u = dirichletMinimizer S a b := by
  let v : S.space := ⟨u.val - (dirichletMinimizer S a b).val, by
    convert S.space.sub_mem hu (dirichletMinimizer_mem_affine S a b) using 1
    abel⟩
  have hz : responseForm S a v v = 0 := by
    change sobolevCoefficientForm a (u.val - (dirichletMinimizer S a b).val) v.val = 0
    rw [map_sub (sobolevCoefficientForm a) u.val (dirichletMinimizer S a b).val,
      sub_apply, he, dirichletMinimizer_euler, sub_self]
  have hv := (responseForm_self_eq_zero_iff S a v).mp hz
  apply Subtype.ext
  exact sub_eq_zero.mp (congrArg (fun w : S.space => w.val) hv)

/-- The minimizer depends only on the boundary class, not its chosen H1 extension. -/
theorem dirichletMinimizer_eq_of_sub_mem (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b c : weakSobolevGraph Ω) (hbc : b.val - c.val ∈ S.space) :
    dirichletMinimizer S a b = dirichletMinimizer S a c := by
  apply dirichletMinimizer_eq_of_euler
  · convert S.space.add_mem (dirichletMinimizer_mem_affine S a b) hbc using 1
    abel
  · exact dirichletMinimizer_euler S a b

/-- The scalar boundary response likewise descends to the Sobolev boundary class. -/
theorem dirichletResponse_eq_of_sub_mem (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b c : weakSobolevGraph Ω) (hbc : b.val - c.val ∈ S.space) :
    dirichletResponse S a b = dirichletResponse S a c := by
  unfold dirichletResponse
  rw [dirichletMinimizer_eq_of_sub_mem S a b c hbc]

/-- The canonical harmonic extension is additive in its boundary datum. -/
theorem dirichletMinimizer_add
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (b c : weakSobolevGraph Ω) :
    dirichletMinimizer S a (b + c) =
      dirichletMinimizer S a b + dirichletMinimizer S a c := by
  symm
  apply dirichletMinimizer_eq_of_euler
  · change (dirichletMinimizer S a b).val + (dirichletMinimizer S a c).val -
      (b.val + c.val) ∈ S.space
    convert S.space.add_mem (dirichletMinimizer_mem_affine S a b)
      (dirichletMinimizer_mem_affine S a c) using 1
    abel
  · intro w
    change sobolevCoefficientForm a
      ((dirichletMinimizer S a b).val + (dirichletMinimizer S a c).val) w.val = 0
    rw [map_add, add_apply,
      dirichletMinimizer_euler, dirichletMinimizer_euler, add_zero]

/-- The canonical harmonic extension respects real scalar multiplication. -/
theorem dirichletMinimizer_smul
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (r : ℝ) (b : weakSobolevGraph Ω) :
    dirichletMinimizer S a (r • b) = r • dirichletMinimizer S a b := by
  symm
  apply dirichletMinimizer_eq_of_euler
  · change r • (dirichletMinimizer S a b).val - r • b.val ∈ S.space
    simpa only [smul_sub] using
      S.space.smul_mem r (dirichletMinimizer_mem_affine S a b)
  · intro w
    change sobolevCoefficientForm a (r • (dirichletMinimizer S a b).val) w.val = 0
    rw [map_smul, smul_apply,
      dirichletMinimizer_euler, smul_zero]

end SubdiffusiveProcess
