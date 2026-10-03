module

public import SubdiffusiveProcess.Section10.BrownianScalingApplicationsFDD

@[expose] public section

/-! Brownian centered path-law scaling from the supplied joint Gaussian increment formula.
No covariance inverse, rank condition, or Brownian exit event is assumed. -/
open MeasureTheory MarkovProcess
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- The covariance cancellation is valid for every finite matrix, including zero. -/
theorem covariance_clock_cancellation {d : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (a c u v : ℝ) (xi : Fin d → ℝ)
    (hclock : a ^ 2 * c = 1) :
    (c * u - c * v) * dotProduct (a • xi) (S.mulVec (a • xi)) =
      (u - v) * dotProduct xi (S.mulVec xi) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  calc
    _ = (a ^ 2 * c) * ((u - v) * dotProduct xi (S.mulVec xi)) := by ring
    _ = _ := by rw [hclock, one_mul]

/-- Scale the complete joint characteristic function, with the clock cancellation explicit. -/
theorem increment_charFun_centeredScale {d : ℕ}
    (Q : Measure (FiniteRealPath d)) (S : Matrix (Fin d) (Fin d) ℝ)
    (hinc : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
      ∀ xi : Fin n → Fin d → ℝ,
        ∫ w, Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
            ((xi j i * (w (t j.succ) i - w (t j.castSucc) i) : ℝ) : ℂ)) ∂Q =
          Complex.exp (-(1 / 2 : ℂ) * ∑ j : Fin n,
            ((((t j.succ : ℝ) - (t j.castSucc : ℝ)) *
              dotProduct (xi j) (S.mulVec (xi j)) : ℝ) : ℂ)))
    (a : ℝ) (c : ℝ≥0) (hclock : a ^ 2 * (c : ℝ) = 1)
    (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t)
    (xi : Fin n → Fin d → ℝ) :
    ∫ w, Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
        ((xi j i * pathIncrements t w j i : ℝ) : ℂ)) ∂(Q.map (centeredScale a c)) =
      Complex.exp (-(1 / 2 : ℂ) * ∑ j : Fin n,
        ((((t j.succ : ℝ) - (t j.castSucc : ℝ)) *
          dotProduct (xi j) (S.mulVec (xi j)) : ℝ) : ℂ)) := by
  have hm : Continuous (fun w : FiniteRealPath d =>
      Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
        ((xi j i * pathIncrements t w j i : ℝ) : ℂ))) := by
    unfold pathIncrements
    fun_prop
  rw [integral_map (measurable_centeredScale a c).aemeasurable hm.aestronglyMeasurable]
  let ct : Fin (n + 1) → ℝ≥0 := fun j => c * t j
  have hct : Monotone ct := fun i j hij => mul_le_mul_right (ht hij) c
  have hphase : (fun w : FiniteRealPath d =>
      Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
        ((xi j i * pathIncrements t (centeredScale a c w) j i : ℝ) : ℂ))) =
      (fun w => Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
        (((a • xi j) i * (w (ct j.succ) i - w (ct j.castSucc) i) : ℝ) : ℂ))) := by
    funext w
    congr 2
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    dsimp [pathIncrements, centeredScale, ct]
    ring
  rw [hphase, hinc n ct hct (fun j => a • xi j)]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  simpa only [ct, NNReal.coe_mul] using
    covariance_clock_cancellation S a (c : ℝ) (t j.succ : ℝ) (t j.castSucc : ℝ)
      (xi j) hclock

/-- Centering removes the arbitrary start; Gaussian increments determine the entire scaled law. -/
theorem map_centeredScale_eq_of_gaussian_increments {d : ℕ}
    (Q : Measure (FiniteRealPath d)) [IsFiniteMeasure Q]
    (S : Matrix (Fin d) (Fin d) ℝ)
    (hinc : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
      ∀ xi : Fin n → Fin d → ℝ,
        ∫ w, Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
            ((xi j i * (w (t j.succ) i - w (t j.castSucc) i) : ℝ) : ℂ)) ∂Q =
          Complex.exp (-(1 / 2 : ℂ) * ∑ j : Fin n,
            ((((t j.succ : ℝ) - (t j.castSucc : ℝ)) *
              dotProduct (xi j) (S.mulVec (xi j)) : ℝ) : ℂ)))
    (a : ℝ) (c : ℝ≥0) (hclock : a ^ 2 * (c : ℝ) = 1) :
    Q.map (centeredScale a c) = Q.map (centeredScale 1 1) := by
  have hz : ∀ (b : ℝ) (s : ℝ≥0), ∀ᵐ w ∂(Q.map (centeredScale b s)), w 0 = 0 := by
    intro b s
    apply (ae_map_iff (measurable_centeredScale b s).aemeasurable
      (measurableSet_eq_fun (ContinuousEvalConst.continuous_eval_const 0).measurable
        measurable_const)).mpr
    exact ae_of_all _ (fun w => by simp [centeredScale])
  apply finite_path_measure_eq_of_increment_charFun _ _ (hz a c) (hz 1 1)
  intro n t ht xi
  rw [increment_charFun_centeredScale Q S hinc a c hclock n t ht xi,
    increment_charFun_centeredScale Q S hinc 1 1 (by norm_num) n t ht xi]

/-- The positive spatial scaling uses the precise NNReal inverse-square clock. -/
theorem map_centeredScale_inverse_square {d : ℕ}
    (Q : Measure (FiniteRealPath d)) [IsFiniteMeasure Q]
    (S : Matrix (Fin d) (Fin d) ℝ)
    (hinc : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
      ∀ xi : Fin n → Fin d → ℝ,
        ∫ w, Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
            ((xi j i * (w (t j.succ) i - w (t j.castSucc) i) : ℝ) : ℂ)) ∂Q =
          Complex.exp (-(1 / 2 : ℂ) * ∑ j : Fin n,
            ((((t j.succ : ℝ) - (t j.castSucc : ℝ)) *
              dotProduct (xi j) (S.mulVec (xi j)) : ℝ) : ℂ)))
    (a : ℝ) (ha : 0 < a) :
    Q.map (centeredScale a (Real.toNNReal (a⁻¹ ^ 2))) =
      Q.map (centeredScale 1 1) := by
  apply map_centeredScale_eq_of_gaussian_increments Q S hinc
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  field_simp [ne_of_gt ha]

/-- All-zero increment characteristic functions identify the centered law with the zero path.
This checks the degenerate covariance branch without an exit moment or nondegeneracy premise. -/
theorem map_centeredScale_eq_dirac_zero_of_zero_increments {d : ℕ}
    (Q : Measure (FiniteRealPath d)) [IsFiniteMeasure Q]
    (hinc : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
      ∀ xi : Fin n → Fin d → ℝ,
        ∫ w, Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
            ((xi j i * (w (t j.succ) i - w (t j.castSucc) i) : ℝ) : ℂ)) ∂Q = 1) :
    Q.map (centeredScale 1 1) = Measure.dirac (0 : FiniteRealPath d) := by
  have hg : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
      ∀ xi : Fin n → Fin d → ℝ,
        ∫ w, Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
            ((xi j i * (w (t j.succ) i - w (t j.castSucc) i) : ℝ) : ℂ)) ∂Q =
          Complex.exp (-(1 / 2 : ℂ) * ∑ j : Fin n,
            ((((t j.succ : ℝ) - (t j.castSucc : ℝ)) *
              dotProduct (xi j) ((0 : Matrix (Fin d) (Fin d) ℝ).mulVec (xi j)) : ℝ) : ℂ)) := by
    intro n t ht xi
    simpa using hinc n t ht xi
  have hz : ∀ᵐ w ∂(Q.map (centeredScale (d := d) 1 1)), w 0 = 0 := by
    apply (ae_map_iff (measurable_centeredScale 1 1).aemeasurable
      (measurableSet_eq_fun (ContinuousEvalConst.continuous_eval_const 0).measurable
        measurable_const)).mpr
    exact ae_of_all _ (fun w => by simp [centeredScale])
  apply finite_path_measure_eq_of_increment_charFun _ _ hz (by simp)
  intro n t ht xi
  rw [increment_charFun_centeredScale Q 0 hg 1 1 (by norm_num) n t ht xi,
    integral_dirac]
  simp [pathIncrements]

/-- The inverse-square clock at a triadic spatial factor, retaining the exact NNReal carrier. -/
theorem triadic_inverse_square_clock (k : ℕ) :
    Real.toNNReal (((3 : ℝ) ^ k)⁻¹ ^ 2) = ((3 : ℝ≥0) ^ (2 * k))⁻¹ := by
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (sq_nonneg _), NNReal.coe_inv, NNReal.coe_pow]
  norm_num only [NNReal.coe_ofNat]
  rw [mul_comm 2 k, pow_mul, inv_pow]





end SubdiffusiveProcess.Section10
