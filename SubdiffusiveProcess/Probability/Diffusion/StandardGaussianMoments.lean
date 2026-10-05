module

public import SubdiffusiveProcess.Model.HeatSemigroupVec

@[expose] public section

/-!
# First and second moments of the standard Gaussian vector

`SubdiffusiveProcess.Model.HeatSemigroupVec.gaussianVec_eq_map` writes every Gaussian on `Vec d` as a shift and
a scaling of the standard one, `stdGaussianVec d = gaussianVec d 0 1`.  The generator
identification for `laplacianSemigroup d` -- package target (i-a) of the Brownian witness -- needs
exactly the first two moments of that fixed measure, and they are proved here:

* `integral_coord` — the coordinates are centred;
* `integral_coord_sq` — each coordinate has unit variance;
* `integral_coord_mul_of_ne` — distinct coordinates are uncorrelated.

All three are instances of Mathlib's `integral_fintype_prod_eq_prod` for product measures: the
integrand is written as a product over the coordinates in which all but one or two factors are
the constant `1`.  Independence therefore does the work, with no Fubini bookkeeping and no
integrability side conditions.

The scalar inputs are Mathlib's `integral_id_gaussianReal` and `variance_fun_id_gaussianReal`;
`integral_sq_gaussianReal_std` is the second one specialised to mean zero, where the variance
**is** the second moment.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory Set
open SubdiffusiveProcess.Model.HeatSemigroupVec
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The standard Gaussian on `Vec d`: independent coordinates, mean zero, variance one. -/
abbrev stdGaussianVec (d : ℕ) : Measure (Vec d) := gaussianVec d 0 1

theorem stdGaussianVec_eq_pi :
    stdGaussianVec d = Measure.pi (fun _ : Fin d => gaussianReal (0:ℝ) 1) := by
  unfold stdGaussianVec gaussianVec
  congr 1

/-- The second moment of the standard real Gaussian. -/
theorem integral_sq_gaussianReal_std : ∫ y : ℝ, y ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hvar := variance_fun_id_gaussianReal (μ := (0:ℝ)) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hvar
  simpa using hvar

/-- **The standard Gaussian vector has unit variance in every coordinate.** -/
theorem integral_coord_sq (i : Fin d) :
    ∫ z : Vec d, (z i) ^ 2 ∂(stdGaussianVec d) = 1 := by
  classical
  have hprod : ∀ z : Vec d, (z i) ^ 2 =
      ∏ k : Fin d, (if k = i then (fun y : ℝ => y ^ 2) else fun _ => (1:ℝ)) (z k) := by
    intro z
    rw [Finset.prod_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  simp only [hprod]
  rw [stdGaussianVec_eq_pi, integral_fintype_prod_eq_prod
    (f := fun k : Fin d => if k = i then (fun y : ℝ => y ^ 2) else fun _ => (1:ℝ))
    (μ := fun _ : Fin d => gaussianReal (0:ℝ) 1)]
  rw [Finset.prod_eq_single i]
  · simpa using integral_sq_gaussianReal_std
  · intro k _ hk
    simp [hk]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

/-- **The standard Gaussian vector has uncorrelated coordinates.** -/
theorem integral_coord_mul_of_ne {i j : Fin d} (hij : i ≠ j) :
    ∫ z : Vec d, z i * z j ∂(stdGaussianVec d) = 0 := by
  classical
  have hprod : ∀ z : Vec d, z i * z j =
      ∏ k : Fin d,
        (if k = i then (fun y : ℝ => y) else if k = j then (fun y : ℝ => y)
          else fun _ => (1:ℝ)) (z k) := by
    intro z
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    rw [Finset.prod_eq_single j]
    · simp [Ne.symm hij, mul_comm]
    · intro k hk hkj
      rcases Finset.mem_erase.mp hk with ⟨hki, -⟩
      simp [hki, hkj]
    · intro hmem
      exact absurd (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩) hmem
  simp only [hprod]
  rw [stdGaussianVec_eq_pi, integral_fintype_prod_eq_prod
    (f := fun k : Fin d => if k = i then (fun y : ℝ => y) else if k = j then (fun y : ℝ => y)
      else fun _ => (1:ℝ))
    (μ := fun _ : Fin d => gaussianReal (0:ℝ) 1)]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp [integral_id_gaussianReal (μ := (0:ℝ)) (v := 1)]

/-- **The standard Gaussian vector is centred.** -/
theorem integral_coord (i : Fin d) : ∫ z : Vec d, z i ∂(stdGaussianVec d) = 0 := by
  classical
  have hprod : ∀ z : Vec d, z i =
      ∏ k : Fin d, (if k = i then (fun y : ℝ => y) else fun _ => (1:ℝ)) (z k) := by
    intro z
    rw [Finset.prod_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  simp only [hprod]
  rw [stdGaussianVec_eq_pi, integral_fintype_prod_eq_prod
    (f := fun k : Fin d => if k = i then (fun y : ℝ => y) else fun _ => (1:ℝ))
    (μ := fun _ : Fin d => gaussianReal (0:ℝ) 1)]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp [integral_id_gaussianReal (μ := (0:ℝ)) (v := 1)]

end SubdiffusiveProcess.Probability.Diffusion
