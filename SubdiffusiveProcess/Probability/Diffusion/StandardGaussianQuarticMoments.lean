module

public import SubdiffusiveProcess.Probability.Diffusion.StandardGaussianMoments

@[expose] public section

/-!
# Fourth moments of the standard Gaussian vector

The uniform
difference-quotient limit `tendstoUniformly_gaussian_differenceQuotient` — collection target (i-a) of
the Brownian witness — needs, besides the first and second moments already proved in
`StandardGaussianMoments.lean`, the two **fourth**-order facts that control the Gaussian tail in
the bulk/tail split: `E[|Z|²] = d` and `E[|Z|⁴] = d(d+2)`, together with the integrability that
lets `integral_mono` be applied to the dominating function.

The plan flagged the scalar input `∫ y⁴ ∂(gaussianReal 0 1) = 3` as the single library gap: it is
absent from Mathlib at this pinned toolchain (no explicit numeric moment of `gaussianReal` beyond
the mean and the variance, and no kurtosis lemma anywhere).  It is proved here the same way
Mathlib proves the variance — through the moment generating function:
`ProbabilityTheory.iteratedDeriv_mgf_zero` turns the `n`-th moment into the `n`-th derivative of
`mgf` at `0`, `mgf_fun_id_gaussianReal` evaluates that to `t ↦ exp (t²/2)`, and four explicit
`HasDerivAt` steps give `(3 + 6t² + t⁴)·exp(t²/2)` at `t = 0`.  No integration by parts and no new
Gaussian analysis.

* `integral_pow4_gaussianReal_std` — `∫ y⁴ = 3` in one dimension.
* `integral_coord_pow4`, `integral_coord_sq_mul_sq_of_ne` — the two vector moments, by the same
  `integral_fintype_prod_eq_prod` / `integral_comp_eval` mechanism as the existing second-moment
  lemmas: independence does the work.
* `integrable_pow_gaussianReal_std`, `integrable_coord_pow`, `integrable_coord_sq_mul_sq`,
  `integrable_vecNormSq`, `integrable_vecNormSq_sq` — the integrability the value lemmas do not
  supply.  `integral_fintype_prod_eq_prod` carries no integrability hypothesis, so the *values*
  come for free, but `integral_finset_sum` and `integral_mono` do need it; it is supplied by
  `integrable_pow_of_mem_interior_integrableExpSet` plus `Integrable.fintype_prod` /
  `integrable_comp_eval`.
* `integral_vecNormSq`, `integral_vecNormSq_sq` — the two moments of the Euclidean square norm
  `Homogenization.vecNormSq`.  Note this is **not** the ambient norm on `Vec d`, which is the sup
  norm; the exchange between the two is made where it is used, not here.

`E[|Z|⁴] = d(d+2)` is the sharp constant: `d` diagonal terms contributing `3` and `d(d-1)`
off-diagonal terms contributing `1`.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion

private theorem deriv_gaussMgf :
    deriv (fun t : ℝ => Real.exp (t ^ 2 / 2)) = fun t : ℝ => t * Real.exp (t ^ 2 / 2) := by
  ext t
  have hinner : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
    simpa using (hasDerivAt_pow 2 t).div_const 2
  have h := hinner.exp
  rw [h.deriv]
  ring

private theorem deriv_gaussMgf1 :
    deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) =
      fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
  ext t
  have hinner : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
    simpa using (hasDerivAt_pow 2 t).div_const 2
  have h := (hasDerivAt_id' (x := t)).fun_mul hinner.exp
  rw [h.deriv]
  ring

private theorem deriv_gaussMgf2 :
    deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2)) =
      fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
  ext t
  have hinner : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
    simpa using (hasDerivAt_pow 2 t).div_const 2
  have hpoly : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add (1 : ℝ)
  have h := hpoly.fun_mul hinner.exp
  rw [h.deriv]
  ring

private theorem deriv_gaussMgf3 :
    deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) =
      fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
  ext t
  have hinner : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
    simpa using (hasDerivAt_pow 2 t).div_const 2
  have hpoly : HasDerivAt (fun s : ℝ => 3 * s + s ^ 3) (3 + 3 * t ^ 2) t := by
    have h1 : HasDerivAt (fun s : ℝ => 3 * s) (3 : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (3 : ℝ)
    have h2 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
      simpa using hasDerivAt_pow 3 t
    simpa only [Pi.add_def] using! h1.add h2
  have h := hpoly.fun_mul hinner.exp
  rw [h.deriv]
  ring

/-- **The fourth moment of the standard real Gaussian.** -/
theorem integral_pow4_gaussianReal_std : ∫ y : ℝ, y ^ 4 ∂(gaussianReal 0 1) = 3 := by
  have hint : (0:ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by
    simp
  have hmom := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) hint 4
  have hmgf : mgf (fun x : ℝ => x) (gaussianReal 0 1) = fun t : ℝ => Real.exp (t ^ 2 / 2) := by
    rw [mgf_fun_id_gaussianReal]
    ext t
    norm_num
  rw [hmgf] at hmom
  have hval : iteratedDeriv 4 (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 = 3 := by
    rw [iteratedDeriv_succ', deriv_gaussMgf, iteratedDeriv_succ', deriv_gaussMgf1,
      iteratedDeriv_succ', deriv_gaussMgf2, iteratedDeriv_one, deriv_gaussMgf3]
    norm_num
  rw [hval] at hmom
  simpa using hmom.symm

variable {d : ℕ}

/-- Every polynomial moment of the standard real Gaussian is finite. -/
theorem integrable_pow_gaussianReal_std (n : ℕ) :
    Integrable (fun y : ℝ => y ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (by simp) n

/-- Every polynomial moment of a single coordinate is integrable. -/
theorem integrable_coord_pow (i : Fin d) (n : ℕ) :
    Integrable (fun z : Vec d => (z i) ^ n) (stdGaussianVec d) := by
  rw [stdGaussianVec_eq_pi]
  exact integrable_comp_eval (integrable_pow_gaussianReal_std n)

/-- **The fourth moment of a coordinate of the standard Gaussian vector.** -/
theorem integral_coord_pow4 (i : Fin d) :
    ∫ z : Vec d, (z i) ^ 4 ∂(stdGaussianVec d) = 3 := by
  rw [stdGaussianVec_eq_pi]
  have h := integral_comp_eval (X := fun _ : Fin d => ℝ)
    (μ := fun _ : Fin d => gaussianReal (0:ℝ) 1) (i := i) (f := fun y : ℝ => y ^ 4)
    (by fun_prop)
  exact h.trans integral_pow4_gaussianReal_std

/-- Products of two coordinate squares are integrable. -/
theorem integrable_coord_sq_mul_sq (i j : Fin d) :
    Integrable (fun z : Vec d => (z i) ^ 2 * (z j) ^ 2) (stdGaussianVec d) := by
  classical
  by_cases hij : i = j
  · subst hij
    have : (fun z : Vec d => (z i) ^ 2 * (z i) ^ 2) = fun z : Vec d => (z i) ^ 4 := by
      funext z; ring
    rw [this]
    exact integrable_coord_pow i 4
  · have hprod : (fun z : Vec d => (z i) ^ 2 * (z j) ^ 2) =
        fun z : Vec d => ∏ k : Fin d,
          (if k = i then (fun y : ℝ => y ^ 2) else if k = j then (fun y : ℝ => y ^ 2)
            else fun _ => (1:ℝ)) (z k) := by
      funext z
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      rw [Finset.prod_eq_single j]
      · simp [Ne.symm hij, mul_comm]
      · intro k hk hkj
        rcases Finset.mem_erase.mp hk with ⟨hki, -⟩
        simp [hki, hkj]
      · intro hmem
        exact absurd (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩) hmem
    rw [hprod, stdGaussianVec_eq_pi]
    refine Integrable.fintype_prod (f := fun k : Fin d =>
      if k = i then (fun y : ℝ => y ^ 2) else if k = j then (fun y : ℝ => y ^ 2)
        else fun _ => (1:ℝ)) ?_
    intro k
    by_cases hki : k = i
    · simpa [hki] using integrable_pow_gaussianReal_std 2
    · by_cases hkj : k = j
      · simpa [hki, hkj] using integrable_pow_gaussianReal_std 2
      · simp only [hki, hkj, ite_false]
        exact integrable_const (1:ℝ)

/-- **Distinct coordinate squares are uncorrelated.** -/
theorem integral_coord_sq_mul_sq_of_ne {i j : Fin d} (hij : i ≠ j) :
    ∫ z : Vec d, (z i) ^ 2 * (z j) ^ 2 ∂(stdGaussianVec d) = 1 := by
  classical
  have hprod : ∀ z : Vec d, (z i) ^ 2 * (z j) ^ 2 =
      ∏ k : Fin d,
        (if k = i then (fun y : ℝ => y ^ 2) else if k = j then (fun y : ℝ => y ^ 2)
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
    (f := fun k : Fin d => if k = i then (fun y : ℝ => y ^ 2) else if k = j then (fun y : ℝ => y ^ 2)
      else fun _ => (1:ℝ))
    (μ := fun _ : Fin d => gaussianReal (0:ℝ) 1)]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [Finset.prod_eq_single j]
  · simp [Ne.symm hij, integral_sq_gaussianReal_std]
  · intro k hk hkj
    rcases Finset.mem_erase.mp hk with ⟨hki, -⟩
    simp [hki, hkj]
  · intro hmem
    exact absurd (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩) hmem

/-- The Euclidean square norm is integrable against the standard Gaussian vector. -/
theorem integrable_vecNormSq :
    Integrable (fun z : Vec d => vecNormSq z) (stdGaussianVec d) := by
  have hrw : (fun z : Vec d => vecNormSq z) = fun z : Vec d => ∑ i : Fin d, (z i) ^ 2 := by
    funext z
    simp [vecNormSq, vecDot, sq]
  rw [hrw]
  exact integrable_finsetSum _ fun i _ => integrable_coord_pow i 2

/-- Its square is integrable too. -/
theorem integrable_vecNormSq_sq :
    Integrable (fun z : Vec d => vecNormSq z ^ 2) (stdGaussianVec d) := by
  have hrw : (fun z : Vec d => vecNormSq z ^ 2) =
      fun z : Vec d => ∑ i : Fin d, ∑ j : Fin d, (z i) ^ 2 * (z j) ^ 2 := by
    funext z
    simp only [vecNormSq, vecDot, sq]
    rw [← Finset.sum_mul_sum]
  rw [hrw]
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => integrable_coord_sq_mul_sq i j

/-- **`E[|Z|²] = d`.** -/
theorem integral_vecNormSq :
    ∫ z : Vec d, vecNormSq z ∂(stdGaussianVec d) = (d : ℝ) := by
  have hrw : (fun z : Vec d => vecNormSq z) = fun z : Vec d => ∑ i : Fin d, (z i) ^ 2 := by
    funext z
    simp [vecNormSq, vecDot, sq]
  rw [hrw, integral_finsetSum _ fun i _ => integrable_coord_pow i 2]
  simp [integral_coord_sq]

/-- **`E[|Z|⁴] = d(d+2)`.** -/
theorem integral_vecNormSq_sq :
    ∫ z : Vec d, vecNormSq z ^ 2 ∂(stdGaussianVec d) = (d : ℝ) * ((d : ℝ) + 2) := by
  classical
  have hrw : (fun z : Vec d => vecNormSq z ^ 2) =
      fun z : Vec d => ∑ i : Fin d, ∑ j : Fin d, (z i) ^ 2 * (z j) ^ 2 := by
    funext z
    simp only [vecNormSq, vecDot, sq]
    rw [← Finset.sum_mul_sum]
  rw [hrw, integral_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => integrable_coord_sq_mul_sq i j]
  have hinner : ∀ i : Fin d,
      ∫ z : Vec d, ∑ j : Fin d, (z i) ^ 2 * (z j) ^ 2 ∂(stdGaussianVec d) = (d : ℝ) + 2 := by
    intro i
    rw [integral_finsetSum _ fun j _ => integrable_coord_sq_mul_sq i j]
    have hterm : ∀ j : Fin d,
        ∫ z : Vec d, (z i) ^ 2 * (z j) ^ 2 ∂(stdGaussianVec d)
          = 1 + (if j = i then (2:ℝ) else 0) := by
      intro j
      by_cases hji : j = i
      · subst hji
        have : (fun z : Vec d => (z j) ^ 2 * (z j) ^ 2) = fun z : Vec d => (z j) ^ 4 := by
          funext z; ring
        rw [this, integral_coord_pow4]
        norm_num
      · rw [integral_coord_sq_mul_sq_of_ne (Ne.symm hji)]
        simp [hji]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_ite_eq' Finset.univ i (fun _ => (2:ℝ))]
    simp
  rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.sum_const]
  simp
  ring

end SubdiffusiveProcess.Probability.Diffusion
