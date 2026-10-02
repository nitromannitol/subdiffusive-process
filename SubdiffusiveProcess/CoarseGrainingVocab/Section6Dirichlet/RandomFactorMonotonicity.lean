import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FinalRandomFactor

/-!
# Monotonicity of the cutoff Dirichlet random factor

These adapters allow independently obtained deterministic coefficients to be
merged into one coefficient-measurable random factor.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- The raw random factor is monotone in its deterministic coefficient. -/
theorem dirichletRandomFactor_mono_coefficient
    {Omega : Type*}
    {C₁ C₂ delta vartheta s1 s2 : ℝ} {k : ℕ}
    {E1 E2 Y : Omega → ℝ} {omega : Omega}
    (hC : C₁ ≤ C₂) (hdelta : 0 ≤ delta)
    (hE1 : 0 ≤ E1 omega) (hY : 0 ≤ Y omega) :
    dirichletRandomFactor C₁ delta vartheta s1 s2 k E1 E2 Y omega ≤
      dirichletRandomFactor C₂ delta vartheta s1 s2 k E1 E2 Y omega := by
  have hcore : 0 ≤
      Real.rpow 3 (s1 * k) * E1 omega * Y omega +
        Real.rpow 3 (-s2 * k) *
          (1 + Real.rpow 3 (s1 * k) * (E2 omega) ^ 2) := by
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hE1) hY)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (add_nonneg zero_le_one
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _))))
  let A := Real.rpow delta (-vartheta) *
      (Real.rpow 3 (s1 * k) * E1 omega * Y omega +
        Real.rpow 3 (-s2 * k) *
          (1 + Real.rpow 3 (s1 * k) * (E2 omega) ^ 2))
  let B := Real.rpow delta (-1) * E1 omega * Y omega
  have hA : 0 ≤ A :=
    mul_nonneg (Real.rpow_nonneg hdelta _) hcore
  have hB : 0 ≤ B :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hdelta _) hE1) hY
  unfold dirichletRandomFactor
  calc
    _ = 1 + C₁ * A + C₁ * B := by dsimp only [A, B]; ring
    _ ≤ 1 + C₂ * A + C₂ * B :=
      add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hC hA))
        (mul_le_mul_of_nonneg_right hC hB)
    _ = _ := by dsimp only [A, B]; ring

/-- Specialized monotonicity for the concrete response/coefficient factor. -/
theorem dirichletUniversalRandomFactor_mono_coefficient
    {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    {C₁ C₂ delta vartheta s1 s2 : ℝ} {k : ℕ}
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hC : C₁ ≤ C₂) (hdelta : 0 ≤ delta) :
    dirichletUniversalRandomFactor M L N C₁ delta vartheta s1 s2 k omega ≤
      dirichletUniversalRandomFactor M L N C₂ delta vartheta s1 s2 k omega := by
  unfold dirichletUniversalRandomFactor
  exact dirichletRandomFactor_mono_coefficient hC hdelta
    (dirichletFullResponseOne_nonneg M L N s1 omega)
    (zero_le_one.trans (one_le_dirichletEllipticityEnvelope M L N s1 omega))

/-- Monotonicity survives the deterministic final-readout enlargement. -/
theorem cutoffDirichletRandomFactor_mono_coefficient
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    {C₁ C₂ vartheta : ℝ}
    (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hC : C₁ ≤ C₂) :
    cutoffDirichletRandomFactor M L N C₁ vartheta hvartheta omega ≤
      cutoffDirichletRandomFactor M L N C₂ vartheta hvartheta omega := by
  unfold cutoffDirichletRandomFactor dirichletReadoutRandomFactor
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (dirichletUniversalRandomFactor_mono_coefficient M L N omega hC
      M.shellPrefix.delta_pos.le) ENNReal.toReal_nonneg)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
