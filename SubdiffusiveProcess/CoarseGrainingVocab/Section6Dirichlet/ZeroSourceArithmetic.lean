import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourcePrebalanceArithmetic

/-!
# Zero-source arithmetic for the cutoff Dirichlet estimate
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- When the divergence lift vanishes, the fractional-datum term disappears
before the two source slots are merged. -/
theorem sourceDirichletPrebalanceRHS_zeroDatum_le
    {C s s1 s2 E1 E2 W Y G CG CD H : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hs : 0 < s) (hss2 : s < s2)
    (hE1 : 0 ≤ E1) (hW : 0 ≤ W) (hY : 0 ≤ Y)
    (hCD : 0 ≤ CD) (hH : 0 ≤ H)
    (hGprice : G ≤ CG * H) :
    sourceDirichletPrebalanceRHS C s s1 s2 k E1 E2 W Y G 0 ≤
      sourceDirichletPrebalanceConstant C s s2 W CG CD *
        (Real.rpow 3 (s1 * (k : ℝ)) * E1 * Y) * H := by
  let A := C * Real.rpow s (-(3 / 2 : ℝ)) * W
  let X := Real.rpow 3 (s1 * (k : ℝ)) * E1 * Y
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hs.le _)) hW
  have hX : 0 ≤ X := by
    dsimp only [X]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hE1) hY
  have hB : 0 ≤ C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹ * CD :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg hs.le _))
          (inv_nonneg.mpr (sub_nonneg.mpr hss2.le))) hCD
  have hcoef : A * CG ≤ sourceDirichletPrebalanceConstant C s s2 W CG CD := by
    unfold sourceDirichletPrebalanceConstant
    dsimp only [A]
    linarith
  unfold sourceDirichletPrebalanceRHS
  simp only [mul_zero, add_zero]
  calc
    C * Real.rpow s (-(3 / 2 : ℝ)) *
          Real.rpow 3 (s1 * (k : ℝ)) * E1 * W * Y * G =
        A * X * G := by dsimp only [A, X]; ring
    _ ≤ A * X * (CG * H) :=
      mul_le_mul_of_nonneg_left hGprice (mul_nonneg hA hX)
    _ = (A * CG) * X * H := by ring
    _ ≤ sourceDirichletPrebalanceConstant C s s2 W CG CD * X * H := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef hX) hH

/-- The zero-source summand of the common random factor is independent of
the optimizing scale.  This is the arbitrary-`k` form needed to reuse the
same final random variable in both frozen estimates. -/
theorem mul_growth_one_mul_response_mul_le_randomFactor_mul_delta_mul
    {C delta vartheta s1 s2 E1 E2 Y D : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hE1 : 0 ≤ E1) (hY : 0 ≤ Y) (hD : 0 ≤ D) :
    C * Real.rpow 3 s1 * E1 * Y * D ≤
      Real.rpow 3 s1 *
        dirichletRandomFactor C delta vartheta s1 s2 k
          (fun _ : Unit ↦ E1) (fun _ : Unit ↦ E2)
          (fun _ : Unit ↦ Y) () * delta * D := by
  let Z := dirichletRandomFactor C delta vartheta s1 s2 k
    (fun _ : Unit ↦ E1) (fun _ : Unit ↦ E2) (fun _ : Unit ↦ Y) ()
  have hcore : 0 ≤ dirichletPrebalanceCore s1 s2 k E1 E2 Y :=
    dirichletPrebalanceCore_nonneg hE1 hY
  have hnormalized : C * Real.rpow delta (-1) * E1 * Y ≤ Z := by
    dsimp only [Z]
    unfold dirichletRandomFactor
    change C * Real.rpow delta (-1) * E1 * Y ≤
      1 + C * Real.rpow delta (-vartheta) *
          dirichletPrebalanceCore s1 s2 k E1 E2 Y +
        C * Real.rpow delta (-1) * E1 * Y
    have hmiddle : 0 ≤ C * Real.rpow delta (-vartheta) *
        dirichletPrebalanceCore s1 s2 k E1 E2 Y :=
      mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hdelta.le _)) hcore
    linarith
  have hcancel : Real.rpow delta (-1) * delta = 1 := by
    change delta ^ (-1 : ℝ) * delta = 1
    rw [Real.rpow_neg_one, inv_mul_cancel₀ hdelta.ne']
  have hlinear : C * E1 * Y ≤ Z * delta := by
    calc
      C * E1 * Y = (C * Real.rpow delta (-1) * E1 * Y) * delta := by
        symm
        calc
          (C * Real.rpow delta (-1) * E1 * Y) * delta =
              C * E1 * Y * (Real.rpow delta (-1) * delta) := by ring
          _ = C * E1 * Y := by rw [hcancel, mul_one]
      _ ≤ Z * delta := mul_le_mul_of_nonneg_right hnormalized hdelta.le
  have hgrowth : 0 ≤ Real.rpow 3 s1 := Real.rpow_nonneg (by norm_num) _
  exact mul_le_mul_of_nonneg_right
    (by
      calc
        C * Real.rpow 3 s1 * E1 * Y =
            Real.rpow 3 s1 * (C * E1 * Y) := by ring
        _ ≤ Real.rpow 3 s1 * (Z * delta) :=
          mul_le_mul_of_nonneg_left hlinear hgrowth
        _ = Real.rpow 3 s1 * Z * delta := by ring)
    hD

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
