import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.L2Stability




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### `L²` housekeeping for vector fields -/

/-- The Euclidean magnitude of a vector `L²` field is a scalar `L²` function. -/
theorem memLp_euclideanNorm_of_memVectorL2 {W : Set (Vec d)}
    {F : Vec d → Vec d} (hF : MemVectorL2 W F) :
    MemLp (fun x ↦ euclideanNorm (F x)) 2 (volume.restrict W) := by
  have hh := (memHilbertVectorL2_hilbertifyVecField hF).norm
  simpa [hilbertifyVecField, euclideanNorm_eq_norm_ofVec] using hh

/-- The squared Euclidean magnitude of a vector `L²` field is integrable. -/
theorem integrableOn_vecNormSq_of_memVectorL2 {W : Set (Vec d)}
    {F : Vec d → Vec d} (hF : MemVectorL2 W F) :
    IntegrableOn (fun x ↦ vecNormSq (F x)) W := by
  simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hF hF

/-! ### The square-root weight -/

/-- `(√s − √t)² ≤ |s − t|` for nonnegative `s`, `t`. -/
theorem sq_sqrt_sub_sqrt_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (Real.sqrt s - Real.sqrt t) ^ 2 ≤ |s - t| := by
  have hp : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  have hq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  have hpn : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hqn : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  rcases le_total t s with h | h
  · have hqp : Real.sqrt t ≤ Real.sqrt s := Real.sqrt_le_sqrt h
    rw [abs_of_nonneg (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hqp hqn]
  · have hpq : Real.sqrt s ≤ Real.sqrt t := Real.sqrt_le_sqrt h
    rw [abs_of_nonpos (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hpq hpn]

/-- The square root of a two-sided bounded continuous coefficient carries the
ellipticity certificate the `L²` theory expects. -/
theorem isEllipticFieldOn_sqrt_of_bounds {W : Set (Vec d)} {c : Vec d → ℝ}
    {lam Lam : ℝ} (hlam : 0 < lam) (hcont : Continuous c)
    (hWm : MeasurableSet W)
    (hb : ∀ x ∈ W, lam ≤ c x ∧ c x ≤ Lam) :
    IsEllipticFieldOn (Real.sqrt lam) (Real.sqrt Lam) W
      (scalarCoeffField fun x ↦ Real.sqrt (c x)) := by
  refine Section6TheoremC.isEllipticFieldOn_scalarCoeffField_of_bounds
    (Real.sqrt_pos.2 hlam) ?_ (fun x hx ↦ Real.sqrt_le_sqrt (hb x hx).1)
    (fun x hx ↦ Real.sqrt_le_sqrt (hb x hx).2)
  exact (Real.continuous_sqrt.comp hcont).measurable.ite hWm measurable_const

/-- The weighted gradient `√c ∇u` of an `H¹` function is a vector `L²` field. -/
theorem memVectorL2_sqrt_smul_grad {W : Set (Vec d)} {c : Vec d → ℝ}
    {lam Lam : ℝ} (hlam : 0 < lam) (hcont : Continuous c)
    (hWm : MeasurableSet W) (hb : ∀ x ∈ W, lam ≤ c x ∧ c x ≤ Lam)
    (u : H1Function W) :
    MemVectorL2 W (fun x ↦ Real.sqrt (c x) • u.grad x) :=
  Section6TheoremC.memVectorL2_smul_grad
    (isEllipticFieldOn_sqrt_of_bounds hlam hcont hWm hb) u

/-! ### The weighted energy of the difference vanishes -/

/-- **The composite field converges in energy.**  With uniform ellipticity, a
vanishing gradient energy for `w_J = u_J − u` and a uniformly vanishing
coefficient defect, the weighted fields `√(ã_J) ∇u_J` converge in `L²(W)` to
`√(a) ∇u`. -/
theorem tendsto_integral_weighted_sub_zero {W : Set (Vec d)}
    {a : Vec d → ℝ} {b : ℕ → Vec d → ℝ} {Lam : ℝ}
    {u : H1Function W} {v : ℕ → H1Function W} {w : ℕ → H10Function W}
    (hW : MeasurableSet W) (hLamnn : 0 ≤ Lam)
    (hbnn : ∀ j x, 0 ≤ b j x) (hann : ∀ x, 0 ≤ a x)
    (hbLam : ∀ j, ∀ x ∈ W, b j x ≤ Lam)
    (hgrad : ∀ j, ∀ x, (v j).grad x = u.grad x + (w j).toH1Function.grad x)
    (hint : ∀ j, IntegrableOn (fun x ↦ vecNormSq
      (Real.sqrt (b j x) • (v j).grad x - Real.sqrt (a x) • u.grad x)) W)
    (hE : Tendsto
      (fun j ↦ ∫ x in W, vecNormSq ((w j).toH1Function.grad x) ∂volume)
      atTop (nhds 0))
    (hdefect : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x ∈ W, |a x - b j x| ≤ ε) :
    Tendsto (fun j ↦ ∫ x in W, vecNormSq
        (Real.sqrt (b j x) • (v j).grad x - Real.sqrt (a x) • u.grad x) ∂volume)
      atTop (nhds 0) := by
  set Iu := ∫ x in W, vecNormSq (u.grad x) ∂volume with hIudef
  have hIuint : IntegrableOn (fun x ↦ vecNormSq (u.grad x)) W :=
    integrableOn_vecNormSq_h1Grad u
  have hIunn : 0 ≤ Iu := by
    rw [hIudef]
    exact setIntegral_nonneg_of_ae_restrict
      (Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg _)
  -- The key pointwise bound on `W`, for a defect bound `eta`.
  have hpt : ∀ (j : ℕ) (eta : ℝ), (∀ x ∈ W, |a x - b j x| ≤ eta) →
      ∀ x ∈ W, vecNormSq
          (Real.sqrt (b j x) • (v j).grad x - Real.sqrt (a x) • u.grad x) ≤
        2 * Lam * vecNormSq ((w j).toH1Function.grad x) +
          2 * eta * vecNormSq (u.grad x) := by
    intro j eta hj x hx
    have hsplit :
        Real.sqrt (b j x) • (v j).grad x - Real.sqrt (a x) • u.grad x =
          Real.sqrt (b j x) • (w j).toH1Function.grad x +
            (Real.sqrt (b j x) - Real.sqrt (a x)) • u.grad x := by
      rw [hgrad j x, smul_add, sub_smul]
      abel
    rw [hsplit]
    refine (vecNormSq_add_le _ _).trans ?_
    have h1 : vecNormSq (Real.sqrt (b j x) • (w j).toH1Function.grad x) ≤
        Lam * vecNormSq ((w j).toH1Function.grad x) := by
      rw [vecNormSq_smul, Real.sq_sqrt (hbnn j x)]
      exact mul_le_mul_of_nonneg_right (hbLam j x hx) (vecNormSq_nonneg _)
    have h2 : vecNormSq ((Real.sqrt (b j x) - Real.sqrt (a x)) • u.grad x) ≤
        eta * vecNormSq (u.grad x) := by
      rw [vecNormSq_smul]
      refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg _)
      have hswap : (Real.sqrt (b j x) - Real.sqrt (a x)) ^ 2 =
          (Real.sqrt (a x) - Real.sqrt (b j x)) ^ 2 := by ring
      rw [hswap]
      exact (sq_sqrt_sub_sqrt_le (hann x) (hbnn j x)).trans (hj x hx)
    linarith
  refine NormedAddCommGroup.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  set eta : ℝ := ε / (4 * (Iu + 1)) with hetadef
  have hetapos : 0 < eta := div_pos hε (by linarith)
  have hEsmall : ∀ᶠ j in atTop,
      ∫ x in W, vecNormSq ((w j).toH1Function.grad x) ∂volume <
        ε / (4 * (Lam + 1)) := by
    have hpos : 0 < ε / (4 * (Lam + 1)) := div_pos hε (by linarith)
    have := NormedAddCommGroup.tendsto_nhds_zero.1 hE _ hpos
    filter_upwards [this] with j hj
    have hnn : 0 ≤ ∫ x in W, vecNormSq ((w j).toH1Function.grad x) ∂volume :=
      setIntegral_nonneg_of_ae_restrict
        (Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg _)
    rwa [Real.norm_eq_abs, abs_of_nonneg hnn] at hj
  filter_upwards [hdefect eta hetapos, hEsmall] with j hjdef hjE
  set Ej := ∫ x in W, vecNormSq ((w j).toH1Function.grad x) ∂volume with hEjdef
  have hEjnn : 0 ≤ Ej := by
    rw [hEjdef]
    exact setIntegral_nonneg_of_ae_restrict
      (Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg _)
  have hIwint : IntegrableOn
      (fun x ↦ vecNormSq ((w j).toH1Function.grad x)) W :=
    integrableOn_vecNormSq_zeroTraceGrad (w j)
  have hRint : IntegrableOn
      (fun x ↦ 2 * Lam * vecNormSq ((w j).toH1Function.grad x) +
        2 * eta * vecNormSq (u.grad x)) W :=
    (hIwint.const_mul _).add (hIuint.const_mul _)
  have hmono := setIntegral_mono_on (hint j) hRint hW (hpt j eta hjdef)
  rw [integral_add (hIwint.const_mul _) (hIuint.const_mul _),
    integral_const_mul, integral_const_mul] at hmono
  have hLHSnn : 0 ≤ ∫ x in W, vecNormSq
      (Real.sqrt (b j x) • (v j).grad x - Real.sqrt (a x) • u.grad x) ∂volume :=
    setIntegral_nonneg_of_ae_restrict
      (Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg _)
  have hb1 : 2 * Lam * Ej < ε / 2 := by
    have hkey : 2 * Lam * Ej ≤ 2 * Lam * (ε / (4 * (Lam + 1))) := by
      have := mul_le_mul_of_nonneg_left hjE.le (by linarith : (0:ℝ) ≤ 2 * Lam)
      linarith
    have hrw : 2 * Lam * (ε / (4 * (Lam + 1))) =
        2 * Lam * ε / (4 * (Lam + 1)) := by ring
    have hstrict : 2 * Lam * (ε / (4 * (Lam + 1))) < ε / 2 := by
      rw [hrw, div_lt_iff₀ (by linarith : (0:ℝ) < 4 * (Lam + 1))]
      nlinarith
    linarith
  have hb2 : 2 * eta * Iu < ε / 2 := by
    have hrw : 2 * eta * Iu = 2 * ε * Iu / (4 * (Iu + 1)) := by
      rw [hetadef]; ring
    rw [hrw, div_lt_iff₀ (by linarith : (0:ℝ) < 4 * (Iu + 1))]
    nlinarith
  have hmono' : ∫ x in W, vecNormSq
      (Real.sqrt (b j x) • (v j).grad x - Real.sqrt (a x) • u.grad x) ∂volume
      ≤ 2 * Lam * Ej + 2 * eta * Iu := by
    rw [hEjdef, hIudef]; exact hmono
  have hfinal : ∫ x in W, vecNormSq
      (Real.sqrt (b j x) • (v j).grad x - Real.sqrt (a x) • u.grad x) ∂volume
      < ε := by linarith
  rwa [Real.norm_eq_abs, abs_of_nonneg hLHSnn]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut
