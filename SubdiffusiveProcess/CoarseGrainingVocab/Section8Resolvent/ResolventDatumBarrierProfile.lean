module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrier
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Filter Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### The derivative of the squared Euclidean magnitude -/

/-- The Fréchet derivative of `x ↦ |x|²` at `x`. -/
def normSqDeriv (x : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ j : Fin d, (2 * x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j

theorem normSqDeriv_apply (x v : Vec d) : normSqDeriv x v = 2 * vecDot x v := by
  simp only [normSqDeriv, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    vecDot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

theorem normSqDeriv_basisVec (x : Vec d) (i : Fin d) :
    normSqDeriv x (basisVec i) = 2 * x i := by
  rw [normSqDeriv_apply]
  congr 1
  simp [vecDot, basisVec_apply]

theorem hasFDerivAt_vecNormSq (x : Vec d) :
    HasFDerivAt (vecNormSq : Vec d → ℝ) (normSqDeriv x) x := by
  have hterm : ∀ j : Fin d, HasFDerivAt (fun y : Vec d ↦ y j * y j)
      ((2 * x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j) x := by
    intro j
    have hproj : HasFDerivAt (fun y : Vec d ↦ y j)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j) x :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j).hasFDerivAt
    have hmul := hproj.mul hproj
    have hcoe : (x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j +
        (x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j =
        (2 * x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j := by
      rw [two_mul, add_smul]
    rw [hcoe] at hmul
    exact hmul
  have hsum := HasFDerivAt.sum (fun j (_ : j ∈ Finset.univ) ↦ hterm j)
  have heq : (∑ j : Fin d, fun y : Vec d ↦ y j * y j) = (vecNormSq : Vec d → ℝ) := by
    funext y
    simp [vecNormSq, vecDot, Finset.sum_apply]
  rw [heq] at hsum
  exact hsum

theorem contDiff_vecNormSq {n : ℕ∞} : ContDiff ℝ n (vecNormSq : Vec d → ℝ) := by
  have h : ContDiff ℝ n (fun y : Vec d ↦ ∑ j : Fin d, y j * y j) :=
    ContDiff.sum (fun j _ ↦ (contDiff_apply ℝ ℝ j).mul (contDiff_apply ℝ ℝ j))
  exact h

/-! ### The divergence of the flux of a radial function -/

/-- The coordinate derivative of a radial function of `|x|²`. -/
theorem euclideanCoordDeriv_compVecNormSq {F F' : ℝ → ℝ}
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (F' t) t) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y : Vec d ↦ F (vecNormSq y)) x =
      F' (vecNormSq x) * (2 * x i) := by
  have hcomp : HasFDerivAt (fun y : Vec d ↦ F (vecNormSq y))
      (F' (vecNormSq x) • normSqDeriv x) x :=
    (hF (vecNormSq x) (vecNormSq_nonneg x)).comp_hasFDerivAt x (hasFDerivAt_vecNormSq x)
  rw [euclideanCoordDeriv, hcomp.fderiv]
  rw [ContinuousLinearMap.smul_apply, normSqDeriv_basisVec, smul_eq_mul]

/-- **The classical divergence of the flux of a radial function.**  For a
differentiable coefficient `c` and `b = F(|x|²)`,

  `∇·(c ∇b) = 2 F'(|x|²) x·∇c + c (4 |x|² F''(|x|²) + 2 d F'(|x|²))`. -/
theorem coeffFluxDiv_compVecNormSq {c : Vec d → ℝ} (hc : Differentiable ℝ c)
    {F F' F'' : ℝ → ℝ} (hF : ∀ t, 0 ≤ t → HasDerivAt F (F' t) t)
    (hF' : ∀ t, 0 ≤ t → HasDerivAt F' (F'' t) t) (x : Vec d) :
    coeffFluxDiv c (fun y : Vec d ↦ F (vecNormSq y)) x =
      2 * F' (vecNormSq x) * vecDot x (euclideanGradient c x) +
        c x * (4 * vecNormSq x * F'' (vecNormSq x) +
          2 * (d : ℝ) * F' (vecNormSq x)) := by
  classical
  have hproj : ∀ (i : Fin d) (y : Vec d), HasFDerivAt (fun z : Vec d ↦ z i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) i) y :=
    fun i y ↦ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) i).hasFDerivAt
  -- the `i`th component of the flux, in closed form
  have hflux : ∀ i : Fin d,
      (fun y : Vec d ↦ c y * euclideanCoordDeriv i (fun z : Vec d ↦ F (vecNormSq z)) y) =
        fun y : Vec d ↦ c y * (F' (vecNormSq y) * (2 * y i)) := by
    intro i
    funext y
    rw [euclideanCoordDeriv_compVecNormSq hF i y]
  -- the derivative of the inner factor
  have hinner : ∀ i : Fin d, HasFDerivAt (fun y : Vec d ↦ F' (vecNormSq y) * (2 * y i))
      (F' (vecNormSq x) • ((2 : ℝ) • ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin d ↦ ℝ) i) +
        (2 * x i) • (F'' (vecNormSq x) • normSqDeriv x)) x := by
    intro i
    have hu : HasFDerivAt (fun y : Vec d ↦ F' (vecNormSq y))
        (F'' (vecNormSq x) • normSqDeriv x) x :=
      (hF' (vecNormSq x) (vecNormSq_nonneg x)).comp_hasFDerivAt x (hasFDerivAt_vecNormSq x)
    have hv : HasFDerivAt (fun y : Vec d ↦ 2 * y i)
        ((2 : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) i) x :=
      (hproj i x).const_mul 2
    exact hu.mul hv
  have hterm : ∀ i : Fin d,
      euclideanCoordDeriv i
          (fun y : Vec d ↦ c y * euclideanCoordDeriv i
            (fun z : Vec d ↦ F (vecNormSq z)) y) x =
        c x * (2 * F' (vecNormSq x) + 4 * x i * x i * F'' (vecNormSq x)) +
          F' (vecNormSq x) * (2 * x i) * euclideanCoordDeriv i c x := by
    intro i
    rw [hflux i]
    have hcx : HasFDerivAt c (fderiv ℝ c x) x := (hc x).hasFDerivAt
    have hmul := hcx.mul (hinner i)
    rw [euclideanCoordDeriv]
    show (fderiv ℝ (c * fun y : Vec d ↦ F' (vecNormSq y) * (2 * y i)) x) (basisVec i) = _
    rw [hmul.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, normSqDeriv_basisVec,
      basisVec_apply]
    rw [euclideanCoordDeriv]
    simp only [if_true]
    ring
  have hsum : coeffFluxDiv c (fun y : Vec d ↦ F (vecNormSq y)) x =
      ∑ i : Fin d, (c x * (2 * F' (vecNormSq x) + 4 * x i * x i * F'' (vecNormSq x)) +
        F' (vecNormSq x) * (2 * x i) * euclideanCoordDeriv i c x) :=
    Finset.sum_congr rfl fun i _ ↦ hterm i
  rw [hsum, Finset.sum_add_distrib]
  have h1 : ∑ i : Fin d,
      c x * (2 * F' (vecNormSq x) + 4 * x i * x i * F'' (vecNormSq x)) =
      c x * (4 * vecNormSq x * F'' (vecNormSq x) + 2 * (d : ℝ) * F' (vecNormSq x)) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have h4 : ∑ i : Fin d, 4 * x i * x i * F'' (vecNormSq x) =
        4 * vecNormSq x * F'' (vecNormSq x) := by
      have hstep : ∑ i : Fin d, 4 * x i * x i * F'' (vecNormSq x) =
          (∑ i : Fin d, x i * x i) * (4 * F'' (vecNormSq x)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      have hq : vecNormSq x = ∑ i : Fin d, x i * x i := rfl
      rw [hstep, hq]
      ring
    rw [h4]
    ring
  have h2 : ∑ i : Fin d, F' (vecNormSq x) * (2 * x i) * euclideanCoordDeriv i c x =
      2 * F' (vecNormSq x) * vecDot x (euclideanGradient c x) := by
    rw [vecDot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      simp only [euclideanGradient]
      ring
  rw [h1, h2]
  ring

/-! ### The radial power barrier -/

/-- The radial profile `t ↦ A (1+t)^{-β/2}`. -/
def radialProfile (A beta t : ℝ) : ℝ := A * (1 + t) ^ (-(beta / 2))

/-- Its first derivative. -/
def radialProfileD (A beta t : ℝ) : ℝ :=
  A * (-(beta / 2)) * (1 + t) ^ (-(beta / 2) - 1)

/-- Its second derivative. -/
def radialProfileDD (A beta t : ℝ) : ℝ :=
  A * (-(beta / 2)) * (-(beta / 2) - 1) * (1 + t) ^ (-(beta / 2) - 2)

/-- **The radial power barrier** `A (1 + |x|²)^{-β/2}`. -/
def radialBarrier (A beta : ℝ) (x : Vec d) : ℝ := radialProfile A beta (vecNormSq x)

theorem radialBarrier_apply (A beta : ℝ) (x : Vec d) :
    radialBarrier A beta x = A * (1 + vecNormSq x) ^ (-(beta / 2)) := rfl

theorem hasDerivAt_radialProfile (A beta : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (radialProfile A beta) (radialProfileD A beta t) t := by
  have hpos : (0 : ℝ) < 1 + t := by linarith
  have h1 : HasDerivAt (fun s : ℝ ↦ 1 + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add (1 : ℝ)
  have h2 := h1.rpow_const (p := -(beta / 2)) (Or.inl (ne_of_gt hpos))
  have h3 := h2.const_mul A
  refine h3.congr_deriv ?_
  simp only [radialProfileD]
  ring

theorem hasDerivAt_radialProfileD (A beta : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (radialProfileD A beta) (radialProfileDD A beta t) t := by
  have hpos : (0 : ℝ) < 1 + t := by linarith
  have h1 : HasDerivAt (fun s : ℝ ↦ 1 + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add (1 : ℝ)
  have h2 := h1.rpow_const (p := -(beta / 2) - 1) (Or.inl (ne_of_gt hpos))
  have h3 := h2.const_mul (A * (-(beta / 2)))
  refine h3.congr_deriv ?_
  simp only [radialProfileDD]
  have hexp : -(beta / 2) - 1 - 1 = -(beta / 2) - 2 := by ring
  rw [hexp]
  ring

theorem radialBarrier_pos {A : ℝ} (hA : 0 < A) (beta : ℝ) (x : Vec d) :
    0 < radialBarrier A beta x := by
  rw [radialBarrier_apply]
  have hpos : (0 : ℝ) < 1 + vecNormSq x := by
    have := vecNormSq_nonneg x; linarith
  exact mul_pos hA (Real.rpow_pos_of_pos hpos _)

theorem contDiff_radialBarrier (A beta : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialBarrier (d := d) A beta) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hpos : (0 : ℝ) < 1 + vecNormSq x := by
    have := vecNormSq_nonneg x; linarith
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ t ^ (-(beta / 2))) (1 + vecNormSq x) :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt hpos)
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Vec d ↦ 1 + vecNormSq y) x :=
    (contDiff_const.add contDiff_vecNormSq).contDiffAt
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞)
      ((fun t : ℝ ↦ t ^ (-(beta / 2))) ∘ fun y : Vec d ↦ 1 + vecNormSq y) x :=
    h1.comp x h2
  have h4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Vec d ↦ (1 + vecNormSq y) ^ (-(beta / 2))) x := h3
  exact contDiffAt_const.mul h4

/-- The barrier is monotone in `|x|²`: a lower bound on a ball. -/
theorem radialBarrier_ge_of_vecNormSq_le {A beta : ℝ} (hA : 0 < A) (hbeta : 0 ≤ beta)
    {x : Vec d} {T : ℝ} (hT : vecNormSq x ≤ T) :
    A * (1 + T) ^ (-(beta / 2)) ≤ radialBarrier A beta x := by
  rw [radialBarrier_apply]
  have hpos : (0 : ℝ) < 1 + vecNormSq x := by
    have := vecNormSq_nonneg x; linarith
  have hle : (1 : ℝ) + vecNormSq x ≤ 1 + T := by linarith
  have := Real.rpow_le_rpow_of_nonpos hpos hle (by linarith : -(beta / 2) ≤ 0)
  exact mul_le_mul_of_nonneg_left this hA.le

/-- The barrier vanishes at infinity. -/
theorem tendsto_radialBarrier_cocompact (A : ℝ) {beta : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto (radialBarrier (d := d) A beta) (Filter.cocompact (Vec d))
      (nhds 0) := by
  have hnorm : Filter.Tendsto (fun x : Vec d ↦ ‖x‖) (Filter.cocompact (Vec d))
      Filter.atTop := tendsto_norm_cocompact_atTop
  have hq : Filter.Tendsto (fun x : Vec d ↦ 1 + vecNormSq x)
      (Filter.cocompact (Vec d)) Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun x ↦ ?_) hnorm
    have hx : ‖x‖ ≤ euclideanNorm x := by
      refine pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg x) |>.2 fun i ↦ ?_
      have hsq : (x i) ^ (2 : ℕ) ≤ vecNormSq x := sq_apply_le_vecNormSq x i
      have h1 : |x i| ≤ euclideanNorm x := by
        have h2 : |x i| ^ 2 ≤ (euclideanNorm x) ^ 2 := by
          rw [euclideanNorm_sq, sq_abs]; exact hsq
        have := Real.sqrt_le_sqrt h2
        rwa [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (euclideanNorm_nonneg x)] at this
      simpa [Real.norm_eq_abs] using h1
    have hE : euclideanNorm x ≤ 1 + vecNormSq x := by
      have h0 := euclideanNorm_nonneg x
      have hsq : (euclideanNorm x) ^ 2 = vecNormSq x := euclideanNorm_sq x
      nlinarith [sq_nonneg (euclideanNorm x - 1)]
    linarith
  have hprof : Filter.Tendsto (fun t : ℝ ↦ A * t ^ (-(beta / 2))) Filter.atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (y := beta / 2) (by linarith)
    have := h.const_mul A
    simpa using this
  have := hprof.comp hq
  refine this.congr fun x ↦ ?_
  simp only [Function.comp_apply, radialBarrier_apply]

/-! ### Elementary comparisons between the two magnitudes -/

/-- Cauchy--Schwarz for the explicit Euclidean magnitude. -/
theorem abs_vecDot_le_euclideanNorm_mul (x y : Vec d) :
    |vecDot x y| ≤ euclideanNorm x * euclideanNorm y := by
  have h1 : (vecDot x y) ^ 2 ≤ (euclideanNorm x * euclideanNorm y) ^ 2 := by
    rw [mul_pow, euclideanNorm_sq, euclideanNorm_sq]
    exact sq_vecDot_le_vecNormSq_mul_vecNormSq x y
  have h2 : 0 ≤ euclideanNorm x * euclideanNorm y :=
    mul_nonneg (euclideanNorm_nonneg x) (euclideanNorm_nonneg y)
  have h3 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq h2] at h3

/-- The product sup norm is dominated by the Euclidean magnitude. -/
theorem norm_le_euclideanNorm (x : Vec d) : ‖x‖ ≤ euclideanNorm x := by
  refine (pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg x)).2 fun i ↦ ?_
  have hsq : |x i| ^ 2 ≤ (euclideanNorm x) ^ 2 := by
    rw [euclideanNorm_sq, sq_abs]
    exact sq_apply_le_vecNormSq x i
  have h3 := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (euclideanNorm_nonneg x)] at h3
  simpa [Real.norm_eq_abs] using h3

/-- The squared Euclidean magnitude is at most `d` times the squared sup norm. -/
theorem vecNormSq_le_dim_mul_sq_norm (x : Vec d) : vecNormSq x ≤ (d : ℝ) * ‖x‖ ^ 2 := by
  have hterm : ∀ i : Fin d, x i * x i ≤ ‖x‖ ^ 2 := by
    intro i
    have hi : |x i| ≤ ‖x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
    nlinarith [abs_nonneg (x i), sq_abs (x i), norm_nonneg x]
  have hsum : (∑ i : Fin d, x i * x i) ≤ ∑ _i : Fin d, ‖x‖ ^ 2 :=
    Finset.sum_le_sum fun i _ ↦ hterm i
  simpa [vecNormSq, vecDot, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    using hsum

/-- The Euclidean magnitude is dominated by `√d` times the product sup norm. -/
theorem euclideanNorm_le_sqrt_dim_mul_norm (x : Vec d) :
    euclideanNorm x ≤ Real.sqrt d * ‖x‖ := by
  have hbound : vecNormSq x ≤ (d : ℝ) * ‖x‖ ^ 2 := vecNormSq_le_dim_mul_sq_norm x
  have hd : Real.sqrt ((d : ℝ) * ‖x‖ ^ 2) = Real.sqrt d * ‖x‖ := by
    rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (norm_nonneg x)]
  calc euclideanNorm x = Real.sqrt (vecNormSq x) := rfl
    _ ≤ Real.sqrt ((d : ℝ) * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt d * ‖x‖ := hd

/-! ### The supersolution estimate -/

/-- The scalar inequality behind the supersolution estimate. -/
theorem barrier_scalar_bound {dd : ℕ} {E G C R n K beta mu s : ℝ}
    (hG0 : 0 ≤ G) (hC0 : 0 ≤ C) (hRpos : 0 < R) (hn0 : 0 ≤ n)
    (hK : 0 ≤ K) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hEd : E ≤ Real.sqrt dd * n) (hgx : G + C ≤ K * R * (1 + n))
    (hs_ge : 1 + n ^ 2 ≤ s)
    (hbetaK : beta * K * (2 * Real.sqrt dd + 6) ≤ mu / 2) :
    beta * (E * G + 2 * (beta / 2 + 1) * C) ≤ mu / 2 * (R * s) := by
  have hsd0 : 0 ≤ Real.sqrt dd := Real.sqrt_nonneg _
  have hGle : G ≤ K * R * (1 + n) := by linarith
  have hCle : C ≤ K * R * (1 + n) := by linarith
  have h4 : n * (1 + n) ≤ 2 * s := by nlinarith [hs_ge, sq_nonneg (n - 1)]
  have h5 : (1 : ℝ) + n ≤ 2 * s := by nlinarith [hs_ge, sq_nonneg (4 * n - 1)]
  have hKR : 0 ≤ Real.sqrt dd * K * R := mul_nonneg (mul_nonneg hsd0 hK) hRpos.le
  have hKR' : 0 ≤ K * R := mul_nonneg hK hRpos.le
  have hstepA : E * G ≤ 2 * Real.sqrt dd * K * R * s := by
    calc E * G ≤ (Real.sqrt dd * n) * G := mul_le_mul_of_nonneg_right hEd hG0
      _ ≤ (Real.sqrt dd * n) * (K * R * (1 + n)) :=
          mul_le_mul_of_nonneg_left hGle (mul_nonneg hsd0 hn0)
      _ = (Real.sqrt dd * K * R) * (n * (1 + n)) := by ring
      _ ≤ (Real.sqrt dd * K * R) * (2 * s) := mul_le_mul_of_nonneg_left h4 hKR
      _ = 2 * Real.sqrt dd * K * R * s := by ring
  have hstepB : C ≤ 2 * K * R * s := by
    calc C ≤ K * R * (1 + n) := hCle
      _ ≤ K * R * (2 * s) := mul_le_mul_of_nonneg_left h5 hKR'
      _ = 2 * K * R * s := by ring
  have h1 : 2 * (beta / 2 + 1) * C ≤ 3 * (2 * K * R * s) := by
    have hcoef : 2 * (beta / 2 + 1) ≤ 3 := by linarith
    nlinarith [hstepB, hC0, hcoef]
  have h2 : E * G + 2 * (beta / 2 + 1) * C ≤
      (2 * Real.sqrt dd + 6) * (K * R * s) := by nlinarith [hstepA, h1, hsd0]
  have h3 : beta * (E * G + 2 * (beta / 2 + 1) * C) ≤
      beta * ((2 * Real.sqrt dd + 6) * (K * R * s)) :=
    mul_le_mul_of_nonneg_left h2 hbeta.le
  have hRS : 0 ≤ R * s := by nlinarith [hRpos, hs_ge, sq_nonneg n]
  have h6 := mul_le_mul_of_nonneg_right hbetaK hRS
  nlinarith [h3, h6]

/-- The algebraic assembly of the supersolution estimate. -/
theorem barrier_algebraic_bound {P PP V E G C R b s q beta mu dd : ℝ}
    (hP : P * s = -(beta / 2) * b) (hPP : PP * (s * s) = beta / 2 * (beta / 2 + 1) * b)
    (hbpos : 0 < b) (hspos : 0 < s) (hqs : q ≤ s)
    (hVle : -V ≤ E * G) (hC0 : 0 ≤ C) (hbeta : 0 < beta) (hd0 : 0 ≤ dd)
    (hkey : beta * (E * G + 2 * (beta / 2 + 1) * C) ≤ mu / 2 * (R * s)) :
    2 * P * V + C * (4 * q * PP + 2 * dd * P) ≤ mu * R / 2 * b := by
  have hss : 0 < s * s := mul_pos hspos hspos
  have hbs : 0 ≤ b * s := mul_nonneg hbpos.le hspos.le
  have hmain : (2 * P * V + C * (4 * q * PP + 2 * dd * P)) * (s * s) ≤
      (mu * R / 2 * b) * (s * s) := by
    have e1 : (2 * P * V + C * (4 * q * PP + 2 * dd * P)) * (s * s) =
        2 * (P * s) * V * s + C * (4 * q * (PP * (s * s)) + 2 * dd * (P * s) * s) := by
      ring
    rw [e1, hP, hPP]
    have h1 : 2 * (-(beta / 2) * b) * V * s ≤ beta * (E * G) * (b * s) := by
      have hrw : 2 * (-(beta / 2) * b) * V * s = beta * (-V) * (b * s) := by ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVle hbeta.le) hbs
    have hAnn : 0 ≤ C * (4 * (beta / 2 * (beta / 2 + 1) * b)) := by
      have hfac : 0 ≤ beta / 2 * (beta / 2 + 1) * b :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) hbpos.le
      nlinarith [hC0, hfac]
    have h2 : C * (4 * q * (beta / 2 * (beta / 2 + 1) * b)) ≤
        beta * (2 * (beta / 2 + 1) * C) * (b * s) := by
      have hmul := mul_le_mul_of_nonneg_left hqs hAnn
      nlinarith [hmul]
    have h3 : C * (2 * dd * (-(beta / 2) * b) * s) ≤ 0 := by
      have hnn : 0 ≤ C * dd * beta * b * s :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hd0) hbeta.le) hbpos.le)
          hspos.le
      linarith [hnn]
    have h4 : beta * (E * G) * (b * s) + beta * (2 * (beta / 2 + 1) * C) * (b * s) ≤
        mu * R / 2 * b * (s * s) := by
      have hprod := mul_le_mul_of_nonneg_right hkey hbs
      calc beta * (E * G) * (b * s) + beta * (2 * (beta / 2 + 1) * C) * (b * s)
          = (beta * (E * G + 2 * (beta / 2 + 1) * C)) * (b * s) := by ring
        _ ≤ (mu / 2 * (R * s)) * (b * s) := hprod
        _ = mu * R / 2 * b * (s * s) := by ring
    linarith
  exact le_of_mul_le_mul_right hmain hss

/-- **The barrier is a supersolution.**  If the coefficient obeys the linear
growth bound `‖∇c‖ + c ≤ K ρ (1 + ‖x‖)` and the exponent satisfies
`β K (2√d + 6) ≤ μ/2` with `0 < β ≤ 1`, then

  `∇·(c ∇b) ≤ (μ ρ / 2) b`,  `b = A (1 + |x|²)^{-β/2}`,

so `μ b − ρ⁻¹ ∇·(c∇b) ≥ μ b / 2 > 0` everywhere.

The point of the estimate is that the exponent `β` is *free*: a coefficient
whose gradient grows linearly is beaten by taking `β` small, whereas an
exponential barrier would need a decay rate `≍ μ/‖∇c‖` whose integral
converges. -/
theorem coeffFluxDiv_radialBarrier_le
    {c rho : Vec d → ℝ} (hc : Differentiable ℝ c) (hcnn : ∀ x, 0 ≤ c x)
    {K mu A beta : ℝ} (hK : 0 ≤ K) (hA : 0 < A)
    (hrho : ∀ x, 0 < rho x)
    (hgrowth : ∀ x, euclideanNorm (euclideanGradient c x) + c x ≤ K * rho x * (1 + ‖x‖))
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hbetaK : beta * K * (2 * Real.sqrt d + 6) ≤ mu / 2) (x : Vec d) :
    coeffFluxDiv c (radialBarrier A beta) x ≤
      mu * rho x / 2 * radialBarrier A beta x := by
  classical
  have hq0 : 0 ≤ vecNormSq x := vecNormSq_nonneg x
  have hspos : (0 : ℝ) < 1 + vecNormSq x := by linarith
  have hbpos : 0 < radialBarrier A beta x := radialBarrier_pos hA beta x
  have hb : radialBarrier A beta x = A * (1 + vecNormSq x) ^ (-(beta / 2)) := rfl
  have hP : radialProfileD A beta (vecNormSq x) * (1 + vecNormSq x) =
      -(beta / 2) * radialBarrier A beta x := by
    have hrw : (1 + vecNormSq x) ^ (-(beta / 2) - 1) =
        (1 + vecNormSq x) ^ (-(beta / 2)) / (1 + vecNormSq x) := by
      rw [Real.rpow_sub hspos, Real.rpow_one]
    rw [radialProfileD, hrw, hb]
    field_simp
    try ring
  have hPP : radialProfileDD A beta (vecNormSq x) *
      ((1 + vecNormSq x) * (1 + vecNormSq x)) =
      beta / 2 * (beta / 2 + 1) * radialBarrier A beta x := by
    have h2 : (1 + vecNormSq x) ^ (2 : ℝ) = (1 + vecNormSq x) * (1 + vecNormSq x) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    have hrw : (1 + vecNormSq x) ^ (-(beta / 2) - 2) =
        (1 + vecNormSq x) ^ (-(beta / 2)) /
          ((1 + vecNormSq x) * (1 + vecNormSq x)) := by
      rw [Real.rpow_sub hspos, h2]
    rw [radialProfileDD, hrw, hb]
    field_simp
    try ring
  have hdiv : coeffFluxDiv c (radialBarrier A beta) x =
      2 * radialProfileD A beta (vecNormSq x) * vecDot x (euclideanGradient c x) +
        c x * (4 * vecNormSq x * radialProfileDD A beta (vecNormSq x) +
          2 * (d : ℝ) * radialProfileD A beta (vecNormSq x)) :=
    coeffFluxDiv_compVecNormSq hc (fun t ht ↦ hasDerivAt_radialProfile A beta ht)
      (fun t ht ↦ hasDerivAt_radialProfileD A beta ht) x
  have hVle : -vecDot x (euclideanGradient c x) ≤
      euclideanNorm x * euclideanNorm (euclideanGradient c x) :=
    (neg_le_abs _).trans (abs_vecDot_le_euclideanNorm_mul x (euclideanGradient c x))
  have hs_ge : 1 + ‖x‖ ^ 2 ≤ 1 + vecNormSq x := by
    have hnE : ‖x‖ ≤ euclideanNorm x := norm_le_euclideanNorm x
    have hEsq : (euclideanNorm x) ^ 2 = vecNormSq x := euclideanNorm_sq x
    nlinarith [norm_nonneg x, euclideanNorm_nonneg x]
  have hkey := barrier_scalar_bound (dd := d)
    (E := euclideanNorm x) (G := euclideanNorm (euclideanGradient c x))
    (C := c x) (R := rho x) (n := ‖x‖) (K := K) (beta := beta) (mu := mu)
    (s := 1 + vecNormSq x)
    (euclideanNorm_nonneg _) (hcnn x) (hrho x) (norm_nonneg x) hK hbeta hbeta1
    (euclideanNorm_le_sqrt_dim_mul_norm x) (hgrowth x) hs_ge hbetaK
  rw [hdiv]
  exact barrier_algebraic_bound hP hPP hbpos hspos (by linarith) hVle (hcnn x)
    hbeta (Nat.cast_nonneg d) hkey

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
