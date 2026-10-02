import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHarmonicLocalization

/-!
# Normalizing one Hessian row

This is the carrier-free scale algebra used after the normalized first-child
Hessian estimate.  Isolating it keeps the dependent weak-Hessian witness out
of the arithmetic proof.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- A normalized total Hessian estimate on the first central child controls
each row, with the explicit factor three coming from the child side length. -/
theorem hessian_row_normalized_bound_of_total {d : ℕ}
    (Q : TriadicCube d) (hess : Fin d → Fin d → Vec d → ℝ)
    (A E : ℝ)
    (henergy : cubeScaleFactor (CubeCalderonZygmund.centralChild Q) *
      (∑ a : Fin d, ∑ b : Fin d,
        cubeLpNorm (CubeCalderonZygmund.centralChild Q) 2 (hess a b)) ≤
      A * E) (i : Fin d) :
    ∑ k : Fin d,
        cubeLpNorm (CubeCalderonZygmund.centralChild Q) 2 (hess i k) ≤
      3 * A * (cubeScaleFactor Q)⁻¹ * E := by
  let P : TriadicCube d := CubeCalderonZygmund.centralChild Q
  have hnonneg : ∀ a ∈ (Finset.univ : Finset (Fin d)),
      0 ≤ ∑ b : Fin d, cubeLpNorm P 2 (hess a b) := by
    intro a ha
    exact Finset.sum_nonneg fun b hb => cubeLpNorm_nonneg P 2 (hess a b)
  have hrow : ∑ k : Fin d, cubeLpNorm P 2 (hess i k) ≤
      ∑ a : Fin d, ∑ b : Fin d, cubeLpNorm P 2 (hess a b) :=
    Finset.single_le_sum hnonneg (Finset.mem_univ i)
  have hscaleP : cubeScaleFactor P = cubeScaleFactor Q / 3 := by
    simpa [P] using cubeScaleFactor_childCube Q (fun _ => (1 : Fin 3))
  have hscaleQpos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      zpow_pos (by norm_num : (0 : ℝ) < 3) Q.scale
  have hscalePpos : 0 < cubeScaleFactor P := by
    simpa [cubeScaleFactor] using
      zpow_pos (by norm_num : (0 : ℝ) < 3) P.scale
  have henergy' : cubeScaleFactor P *
      (∑ a : Fin d, ∑ b : Fin d, cubeLpNorm P 2 (hess a b)) ≤
      A * E := by
    simpa [P] using henergy
  have hdiv := (le_div_iff₀ hscalePpos).2
    (calc
      (∑ k : Fin d, cubeLpNorm P 2 (hess i k)) * cubeScaleFactor P ≤
          (∑ a : Fin d, ∑ b : Fin d, cubeLpNorm P 2 (hess a b)) *
            cubeScaleFactor P :=
        mul_le_mul_of_nonneg_right hrow hscalePpos.le
      _ = cubeScaleFactor P *
          (∑ a : Fin d, ∑ b : Fin d, cubeLpNorm P 2 (hess a b)) := by ring
      _ ≤ _ := henergy')
  rw [hscaleP] at hdiv
  calc
    ∑ k : Fin d, cubeLpNorm (CubeCalderonZygmund.centralChild Q) 2 (hess i k) =
        ∑ k : Fin d, cubeLpNorm P 2 (hess i k) := by rfl
    _ ≤ (A * E) / (cubeScaleFactor Q / 3) := hdiv
    _ = 3 * A * (cubeScaleFactor Q)⁻¹ * E := by
      field_simp [hscaleQpos.ne']

end


end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
