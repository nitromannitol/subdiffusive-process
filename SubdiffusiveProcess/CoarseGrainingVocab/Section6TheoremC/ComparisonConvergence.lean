module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CutoffEllipticity

@[expose] public section

/-!
# S4 → S5 wiring: the comparison solutions converge (B3)

`EnergyBound.integral_vecNormSq_grad_le` closed S5 modulo two things: its
integrability side conditions, and the passage `N → ∞`.  Both are supplied here.

* **Integrability.**  All six side conditions are discharged from the
  CoarseGraining library's own `L²` lemmas
  (`integrableOn_vecNormSq_h1Grad`, `integrableOn_vecDot_of_memVectorL2`,
  `memVectorL2_matVecMul_of_isEllipticFieldOn`), given ellipticity carriers for
  the two coefficients.  Nothing is assumed that `B2` does not already provide
  for `coefficientAt`.

* **Window-local ellipticity.**  `EnergyBound.lower_bound_energy` asks for
  `λ ≤ b` *globally*.  That is too strong for `coefficientAt`, whose global
  infimum over `ℝᵈ` is `0`; the bound only holds on the cube.  This file
  restates the energy bound with the hypotheses localized to a measurable
  window, which is the form B2's constants actually have.

* **The limit.**  With `K_N := sup_{𝔠_m}|ã_N − a| → 0` from the PROVED anchor
  `l.finite.cutoff.coefficient.convergence` (paper label `l.finite.cutoff.coefficient.convergence`), the
  bound `∫|∇w_N|² ≤ (K_N/λ)²·∫|∇u|²` forces `∫|∇w_N|² → 0`, which is
  `‖∇u_N − ∇u‖_{L²(𝔠_m)} → 0` — the display asserted at
  paper label `l.finite.cutoff.coefficient.convergence`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Discharging the integrability side conditions -/

/-- The flux of an `H¹` gradient against a scalar elliptic coefficient is `L²`. -/
theorem memVectorL2_smul_grad {W : Set (Vec d)} {b : Vec d → ℝ} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField b))
    (u : H1Function W) :
    MemVectorL2 W (fun x ↦ b x • u.grad x) := by
  have h := memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  simpa [scalarCoeffField, matVecMul_scalarMatrix] using h

/-- The tested product of two `H¹` gradients against a scalar elliptic
coefficient is integrable. -/
theorem integrableOn_vecDot_smul_grad {W : Set (Vec d)} {b : Vec d → ℝ}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField b))
    (u v : H1Function W) :
    IntegrableOn (fun x ↦ vecDot (b x • u.grad x) (v.grad x)) W :=
  integrableOn_vecDot_of_memVectorL2 (memVectorL2_smul_grad hEll u)
    v.grad_memVectorL2

/-- The energy density of a scalar elliptic coefficient is integrable. -/
theorem integrableOn_mul_vecNormSq_grad {W : Set (Vec d)} {b : Vec d → ℝ}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField b))
    (u : H1Function W) :
    IntegrableOn (fun x ↦ b x * vecNormSq (u.grad x)) W := by
  have h := integrableOn_vecDot_smul_grad hEll u u
  refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  show vecDot (b x • u.grad x) (u.grad x) = b x * vecNormSq (u.grad x)
  rw [vecDot_smul_left, vecNormSq]

/-- The coefficient defect tested against two gradients is integrable. -/
theorem integrableOn_defect {W : Set (Vec d)} {a b : Vec d → ℝ}
    {lam Lam lam' Lam' : ℝ}
    (hElla : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    (hEllb : IsEllipticFieldOn lam' Lam' W (scalarCoeffField b))
    (u v : H1Function W) :
    IntegrableOn (fun x ↦ (a x - b x) * vecDot (u.grad x) (v.grad x)) W := by
  have ha := integrableOn_vecDot_smul_grad hElla u v
  have hb := integrableOn_vecDot_smul_grad hEllb u v
  refine (ha.sub hb).congr (Filter.Eventually.of_forall fun x ↦ ?_)
  show vecDot (a x • u.grad x) (v.grad x) - vecDot (b x • u.grad x) (v.grad x)
      = (a x - b x) * vecDot (u.grad x) (v.grad x)
  rw [vecDot_smul_left, vecDot_smul_left]
  ring

/-! ### The energy bound with window-local ellipticity -/

/-- Ellipticity on the window bounds the energy below.  The window-local form of
`EnergyBound.lower_bound_energy`. -/
theorem lower_bound_energy_on {W : Set (Vec d)} {b : Vec d → ℝ} {lam : ℝ}
    (hW : MeasurableSet W) (hlam : ∀ x ∈ W, lam ≤ b x) {gw : Vec d → Vec d}
    (hint1 : IntegrableOn (fun x ↦ lam * vecNormSq (gw x)) W)
    (hint2 : IntegrableOn (fun x ↦ b x * vecNormSq (gw x)) W) :
    ∫ x in W, lam * vecNormSq (gw x) ∂volume ≤
      ∫ x in W, b x * vecNormSq (gw x) ∂volume :=
  setIntegral_mono_on hint1 hint2 hW fun x hx ↦
    mul_le_mul_of_nonneg_right (hlam x hx) (vecNormSq_nonneg _)

/-- **The energy bound, with all side conditions discharged.**  The window-local
counterpart of `EnergyBound.integral_vecNormSq_grad_le`, needing only the two
ellipticity carriers and the defect bound. -/
theorem integral_vecNormSq_grad_le_on {W : Set (Vec d)}
    {a b : Vec d → ℝ} {lam Lam lam' Lam' K : ℝ}
    {u v : H1Function W} {w : H10Function W}
    (hW : MeasurableSet W) (hlam : 0 < lam)
    (hElla : IsEllipticFieldOn lam' Lam' W (scalarCoeffField a))
    (hEllb : IsEllipticFieldOn lam Lam W (scalarCoeffField b))
    (hb : ∀ x ∈ W, lam ≤ b x) (hK : ∀ x, |a x - b x| ≤ K)
    (hu : IsWeaklyHarmonicOn a W u) (hv : IsWeaklyHarmonicOn b W v)
    (hgrad : ∀ x, v.grad x = u.grad x + w.toH1Function.grad x) :
    ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume ≤
      (K / lam) ^ 2 * ∫ x in W, vecNormSq (u.grad x) ∂volume := by
  set Iw := ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume with hIwdef
  set Iu := ∫ x in W, vecNormSq (u.grad x) ∂volume with hIudef
  have hIw : IntegrableOn (fun x ↦ vecNormSq (w.toH1Function.grad x)) W :=
    integrableOn_vecNormSq_zeroTraceGrad w
  have hIu : IntegrableOn (fun x ↦ vecNormSq (u.grad x)) W :=
    integrableOn_vecNormSq_h1Grad u
  have hE : IntegrableOn
      (fun x ↦ b x * vecNormSq (w.toH1Function.grad x)) W :=
    integrableOn_mul_vecNormSq_grad hEllb w.toH1Function
  have hD : IntegrableOn
      (fun x ↦ (a x - b x) *
        vecDot (u.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_defect hElla hEllb u w.toH1Function
  have hintv : IntegrableOn
      (fun x ↦ vecDot (b x • v.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_vecDot_smul_grad hEllb v w.toH1Function
  have hintu : IntegrableOn
      (fun x ↦ vecDot (a x • u.grad x) (w.toH1Function.grad x)) W :=
    integrableOn_vecDot_smul_grad hElla u w.toH1Function
  -- Left: window-local ellipticity.
  have hleft : lam * Iw ≤
      ∫ x in W, b x * vecNormSq (w.toH1Function.grad x) ∂volume := by
    rw [hIwdef, ← integral_const_mul]
    exact lower_bound_energy_on hW hb (hIw.const_mul lam) hE
  -- Right: defect, then Young.
  have hYoung : ∀ x,
      (a x - b x) * vecDot (u.grad x) (w.toH1Function.grad x) ≤
        K ^ 2 / (2 * lam) * vecNormSq (u.grad x) +
          lam / 2 * vecNormSq (w.toH1Function.grad x) := by
    intro x
    refine (defect_le hK u.grad w.toH1Function.grad x).trans ?_
    have hy := young_pointwise (K := K) (A := euclideanNorm (u.grad x))
      (B := euclideanNorm (w.toH1Function.grad x)) hlam
    rwa [euclideanNorm_sq, euclideanNorm_sq] at hy
  have hRint : IntegrableOn
      (fun x ↦ K ^ 2 / (2 * lam) * vecNormSq (u.grad x) +
        lam / 2 * vecNormSq (w.toH1Function.grad x)) W :=
    (hIu.const_mul _).add (hIw.const_mul _)
  have hright : ∫ x in W, (a x - b x) *
        vecDot (u.grad x) (w.toH1Function.grad x) ∂volume ≤
      K ^ 2 / (2 * lam) * Iu + lam / 2 * Iw := by
    have hmono := integral_mono hD hRint hYoung
    rwa [integral_add (hIu.const_mul _) (hIw.const_mul _),
      integral_const_mul, integral_const_mul] at hmono
  have hid := integral_energy_eq hu hv hgrad hintv hintu hE hD
  have hchain : lam * Iw ≤ K ^ 2 / (2 * lam) * Iu + lam / 2 * Iw := by
    rw [hid] at hleft; exact hleft.trans hright
  have hhalf : lam / 2 * Iw ≤ K ^ 2 / (2 * lam) * Iu := by linarith
  have key : lam ^ 2 * Iw ≤ K ^ 2 * Iu := by
    have h := mul_le_mul_of_nonneg_left hhalf (by linarith : (0 : ℝ) ≤ 2 * lam)
    calc lam ^ 2 * Iw = 2 * lam * (lam / 2 * Iw) := by ring
      _ ≤ 2 * lam * (K ^ 2 / (2 * lam) * Iu) := h
      _ = K ^ 2 * Iu := by field_simp
  rw [div_pow, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity : (0 : ℝ) < lam ^ 2)]
  linarith [key]

/-! ### The limit `N → ∞` -/

/-- **B3.**  If the coefficient defect vanishes, so does the energy of the
difference.  This is the passage in the comparison argument.

`E N` is `∫_{𝔠_m}|∇w_N|²`, `K N` the defect `sup_{𝔠_m}|ã_N − a|`, and `Iu` the
fixed energy `∫_{𝔠_m}|∇u|²`. -/
theorem tendsto_energy_of_tendsto_defect {E K : ℕ → ℝ} {lam Iu : ℝ}
    (hEnn : ∀ N, 0 ≤ E N)
    (hbound : ∀ N, E N ≤ (K N / lam) ^ 2 * Iu)
    (hK : Tendsto K atTop (nhds 0)) :
    Tendsto E atTop (nhds 0) := by
  have hmaj : Tendsto (fun N ↦ (K N / lam) ^ 2 * Iu) atTop (nhds 0) := by
    have h1 : Tendsto (fun N ↦ K N / lam) atTop (nhds 0) := by
      simpa using hK.div_const lam
    have h2 : Tendsto (fun N ↦ (K N / lam) ^ 2) atTop (nhds 0) := by
      simpa using h1.pow 2
    simpa using h2.mul_const Iu
  exact squeeze_zero hEnn hbound hmaj

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
