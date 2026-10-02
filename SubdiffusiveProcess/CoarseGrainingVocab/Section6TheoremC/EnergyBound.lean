import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.EnergyIdentity




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### Pointwise Young -/

/-- Young's inequality in the form used to absorb the cross term. -/
theorem young_pointwise {lam K A B : ℝ} (hlam : 0 < lam) :
    K * (A * B) ≤ K ^ 2 / (2 * lam) * A ^ 2 + lam / 2 * B ^ 2 := by
  have hkey : 0 ≤ (lam * B - K * A) ^ 2 := sq_nonneg _
  have hexp : K ^ 2 / (2 * lam) * A ^ 2 + lam / 2 * B ^ 2 - K * (A * B) =
      (lam * B - K * A) ^ 2 / (2 * lam) := by
    field_simp
    ring
  nlinarith [hkey, hlam, div_nonneg hkey (by linarith : (0 : ℝ) ≤ 2 * lam)]

/-! ### The integral comparison -/

/-- **S5, closed.**  The Dirichlet energy of the difference is controlled by the
coefficient defect times the energy of the reference solution. -/
theorem integral_vecNormSq_grad_le {W : Set (Vec d)}
    {a b : Vec d → ℝ} {lam K : ℝ} {u v : H1Function W} {w : H10Function W}
    (hlam : 0 < lam) (hb : ∀ x, lam ≤ b x) (hK : ∀ x, |a x - b x| ≤ K)
    (hu : IsWeaklyHarmonicOn a W u) (hv : IsWeaklyHarmonicOn b W v)
    (hgrad : ∀ x, v.grad x = u.grad x + w.toH1Function.grad x)
    (hintv : IntegrableOn
      (fun x ↦ vecDot (b x • v.grad x) (w.toH1Function.grad x)) W)
    (hintu : IntegrableOn
      (fun x ↦ vecDot (a x • u.grad x) (w.toH1Function.grad x)) W)
    (hE : IntegrableOn (fun x ↦ b x * vecNormSq (w.toH1Function.grad x)) W)
    (hD : IntegrableOn
      (fun x ↦ (a x - b x) * vecDot (u.grad x) (w.toH1Function.grad x)) W)
    (hIw : IntegrableOn (fun x ↦ vecNormSq (w.toH1Function.grad x)) W)
    (hIu : IntegrableOn (fun x ↦ vecNormSq (u.grad x)) W) :
    ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume ≤
      (K / lam) ^ 2 * ∫ x in W, vecNormSq (u.grad x) ∂volume := by
  set Iw := ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume with hIwdef
  set Iu := ∫ x in W, vecNormSq (u.grad x) ∂volume with hIudef
  -- Left: ellipticity.
  have hleft : lam * Iw ≤ ∫ x in W, b x * vecNormSq (w.toH1Function.grad x) ∂volume := by
    rw [hIwdef, ← integral_const_mul]
    exact lower_bound_energy hb (hIw.const_mul lam) hE
  -- Right: defect, then Young, pointwise.
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
  -- Combine through the energy identity.
  have hid := integral_energy_eq hu hv hgrad hintv hintu hE hD
  have hchain : lam * Iw ≤ K ^ 2 / (2 * lam) * Iu + lam / 2 * Iw := by
    rw [hid] at hleft; exact hleft.trans hright
  have hIwnn : 0 ≤ Iw := by
    rw [hIwdef]
    exact setIntegral_nonneg_of_ae_restrict
      (Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg _)
  have hIunn : 0 ≤ Iu := by
    rw [hIudef]
    exact setIntegral_nonneg_of_ae_restrict
      (Filter.Eventually.of_forall fun x ↦ vecNormSq_nonneg _)
  -- `(λ/2)·Iw ≤ K²/(2λ)·Iu`, then clear denominators.
  have hhalf : lam / 2 * Iw ≤ K ^ 2 / (2 * lam) * Iu := by linarith
  have key : lam ^ 2 * Iw ≤ K ^ 2 * Iu := by
    have h := mul_le_mul_of_nonneg_left hhalf (by linarith : (0 : ℝ) ≤ 2 * lam)
    calc lam ^ 2 * Iw = 2 * lam * (lam / 2 * Iw) := by ring
      _ ≤ 2 * lam * (K ^ 2 / (2 * lam) * Iu) := h
      _ = K ^ 2 * Iu := by field_simp
  rw [div_pow, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity : (0 : ℝ) < lam ^ 2)]
  linarith [key]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
