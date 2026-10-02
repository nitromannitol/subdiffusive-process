import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.RandomFactorMoment

/-!
# Consuming the balanced Dirichlet random factor

The random factor was defined by adjoining two normalized copies of the
prebalance right-hand side: the optimizing-scale copy normalized by
`delta^vartheta`, and the zero-forcing linear copy normalized by `delta`.
This file records the two resulting pointwise bounds.  They are the final
arithmetic step after `e.Dirichlet.prebalance` and use the same random factor
in both conclusions.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- The two-term scalar core in `e.Dirichlet.prebalance`. -/
def dirichletPrebalanceCore
    (s1 s2 : ℝ) (k : ℕ) (E1 E2 Y : ℝ) : ℝ :=
  Real.rpow 3 (s1 * (k : ℝ)) * E1 * Y +
    Real.rpow 3 (-s2 * (k : ℝ)) *
      (1 + Real.rpow 3 (s1 * (k : ℝ)) * E2 ^ (2 : ℕ))

theorem dirichletPrebalanceCore_nonneg
    {s1 s2 E1 E2 Y : ℝ} {k : ℕ}
    (hE1 : 0 ≤ E1) (hY : 0 ≤ Y) :
    0 ≤ dirichletPrebalanceCore s1 s2 k E1 E2 Y := by
  unfold dirichletPrebalanceCore
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hE1) hY)
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (add_nonneg zero_le_one
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg E2))))

/-- The optimizing-scale prebalance core is paid by the common random factor
times `delta^vartheta`. -/
theorem mul_dirichletPrebalanceCore_le_dirichletRandomFactor_mul_rpow
    {C delta vartheta s1 s2 E1 E2 Y : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hE1 : 0 ≤ E1) (hY : 0 ≤ Y) :
    C * dirichletPrebalanceCore s1 s2 k E1 E2 Y ≤
      dirichletRandomFactor C delta vartheta s1 s2 k
          (fun _ : Unit ↦ E1) (fun _ : Unit ↦ E2) (fun _ : Unit ↦ Y) () *
        Real.rpow delta vartheta := by
  let A := dirichletPrebalanceCore s1 s2 k E1 E2 Y
  let Z := dirichletRandomFactor C delta vartheta s1 s2 k
    (fun _ : Unit ↦ E1) (fun _ : Unit ↦ E2) (fun _ : Unit ↦ Y) ()
  have hA : 0 ≤ A := dirichletPrebalanceCore_nonneg hE1 hY
  have hlast : 0 ≤ C * Real.rpow delta (-1) * E1 * Y :=
    mul_nonneg
      (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hdelta.le _)) hE1) hY
  have hnormalized : C * Real.rpow delta (-vartheta) * A ≤ Z := by
    dsimp only [Z]
    unfold dirichletRandomFactor
    change C * Real.rpow delta (-vartheta) * A ≤
      1 + C * Real.rpow delta (-vartheta) * A +
        C * Real.rpow delta (-1) * E1 * Y
    linarith
  have hpower : 0 ≤ Real.rpow delta vartheta :=
    Real.rpow_nonneg hdelta.le _
  have hcancel :
      Real.rpow delta (-vartheta) * Real.rpow delta vartheta = 1 := by
    change delta ^ (-vartheta) * delta ^ vartheta = 1
    rw [← Real.rpow_add hdelta, neg_add_cancel, Real.rpow_zero]
  calc
    C * dirichletPrebalanceCore s1 s2 k E1 E2 Y = C * A := by rfl
    _ = (C * Real.rpow delta (-vartheta) * A) *
        Real.rpow delta vartheta := by
      symm
      calc
        (C * Real.rpow delta (-vartheta) * A) * Real.rpow delta vartheta =
            C * A * (Real.rpow delta (-vartheta) *
              Real.rpow delta vartheta) := by ring
        _ = C * A := by rw [hcancel, mul_one]
    _ ≤ Z * Real.rpow delta vartheta :=
      mul_le_mul_of_nonneg_right hnormalized hpower
    _ = dirichletRandomFactor C delta vartheta s1 s2 k
          (fun _ : Unit ↦ E1) (fun _ : Unit ↦ E2) (fun _ : Unit ↦ Y) () *
        Real.rpow delta vartheta := by rfl

/-- A nonnegative datum factor may be appended to the balanced prebalance
bound without changing the random variable. -/
theorem mul_dirichletPrebalanceCore_mul_le_randomFactor_mul_rpow_mul
    {C delta vartheta s1 s2 E1 E2 Y D : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hE1 : 0 ≤ E1) (hY : 0 ≤ Y) (hD : 0 ≤ D) :
    C * dirichletPrebalanceCore s1 s2 k E1 E2 Y * D ≤
      dirichletRandomFactor C delta vartheta s1 s2 k
          (fun _ : Unit ↦ E1) (fun _ : Unit ↦ E2) (fun _ : Unit ↦ Y) () *
        Real.rpow delta vartheta * D :=
  mul_le_mul_of_nonneg_right
    (mul_dirichletPrebalanceCore_le_dirichletRandomFactor_mul_rpow
      hC hdelta hE1 hY) hD

/-- The linear response term used when the forcing vanishes is paid by the
last summand of the same common random factor.  The displayed `3^s1` is the
fixed loss from reapplying prebalance at `k = 1`. -/
theorem mul_growth_one_mul_response_le_growth_one_mul_randomFactor_mul_delta
    {C delta vartheta s1 s2 E1 E2 Y : ℝ}
    (hC : 0 ≤ C) (hdelta : 0 < delta)
    (hE1 : 0 ≤ E1) (hY : 0 ≤ Y) :
    C * Real.rpow 3 s1 * E1 * Y ≤
      Real.rpow 3 s1 *
        dirichletRandomFactor C delta vartheta s1 s2 1
          (fun _ : Unit ↦ E1) (fun _ : Unit ↦ E2) (fun _ : Unit ↦ Y) () * delta := by
  let Z := dirichletRandomFactor C delta vartheta s1 s2 1
    (fun _ : Unit ↦ E1) (fun _ : Unit ↦ E2) (fun _ : Unit ↦ Y) ()
  have hcore : 0 ≤ dirichletPrebalanceCore s1 s2 1 E1 E2 Y :=
    dirichletPrebalanceCore_nonneg hE1 hY
  have hnormalized : C * Real.rpow delta (-1) * E1 * Y ≤ Z := by
    dsimp only [Z]
    unfold dirichletRandomFactor
    change C * Real.rpow delta (-1) * E1 * Y ≤
      1 + C * Real.rpow delta (-vartheta) *
          dirichletPrebalanceCore s1 s2 1 E1 E2 Y +
        C * Real.rpow delta (-1) * E1 * Y
    have hmiddle : 0 ≤ C * Real.rpow delta (-vartheta) *
        dirichletPrebalanceCore s1 s2 1 E1 E2 Y :=
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
  calc
    C * Real.rpow 3 s1 * E1 * Y =
        Real.rpow 3 s1 * (C * E1 * Y) := by ring
    _ ≤ Real.rpow 3 s1 * (Z * delta) :=
      mul_le_mul_of_nonneg_left hlinear hgrowth
    _ = Real.rpow 3 s1 * Z * delta := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
