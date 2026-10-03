module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.TriadicMeanTelescope
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubunitGeometry

@[expose] public section

/-!
# Theta ladder: target-cube Campanato readout

The point-centred triadic telescope is compared to one common target mean.
This is the deterministic conversion from the stopped centered rows to the
two affine-safe carriers used by the bounded-multiplier conclusion.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ}

/-- Every scale-`n` cube centred at a point of a scale-`n` cube is contained
in the concentric scale-`n+1` enlargement of the latter. -/
theorem translatedCube_point_subset_target_succ
    {n : ℕ} {z' x : Vec d}
    (hx : x ∈ translatedCube d (n : ℤ) z') :
    translatedCube d (n : ℤ) x ⊆
      translatedCube d ((n + 1 : ℕ) : ℤ) z' := by
  rw [translatedCube_eq_metricBall] at hx
  rw [Metric.mem_ball, zpow_natCast] at hx
  rw [translatedCube_eq_metricBall (d := d) (n : ℤ) x]
  rw [translatedCube_eq_metricBall (d := d)
    ((n + 1 : ℕ) : ℤ) z']
  apply Metric.ball_subset_ball'
  have hpow : (3 : ℝ) ^ ((n + 1 : ℕ) : ℤ) =
      3 * (3 : ℝ) ^ n := by
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega,
      zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    ring
  rw [zpow_natCast, hpow]
  have hscale : 0 < (3 : ℝ) ^ n := by positivity
  nlinarith

/-- Join the point-centred finite telescope to the common mean on the
one-scale enlargement of the target cube. -/
theorem abs_point_sub_targetSuccMean_le_of_halfDecay
    {n : ℕ} {z' x : Vec d} {f fRep : Vec d → ℝ} {A E Aouter : ℝ}
    (hx : x ∈ translatedCube d (n : ℤ) z')
    (hA : 0 ≤ A)
    (hf : IntegrableOn f
      (translatedCube d ((n + 1 : ℕ) : ℤ) z'))
    (hf2 : IntegrableOn (fun y ↦ f y ^ 2)
      (translatedCube d ((n + 1 : ℕ) : ℤ) z'))
    (hdecay : ∀ s : ℕ, s ≤ n →
      normalizedL2On (translatedCube d (s : ℤ) x)
          (fun y ↦ f y - averageOn (translatedCube d (s : ℤ) x) f) ≤
        A * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * ((n : ℝ) - (s : ℝ))))
    (hpoint : |fRep x - averageOn (translatedCube d 0 x) f| ≤ E)
    (houter : normalizedL2On
        (translatedCube d ((n + 1 : ℕ) : ℤ) z')
        (fun y ↦ f y - averageOn
          (translatedCube d ((n + 1 : ℕ) : ℤ) z') f) ≤ Aouter) :
    |fRep x - averageOn
        (translatedCube d ((n + 1 : ℕ) : ℤ) z') f| ≤
      E + 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * A +
        Real.sqrt ((3 : ℝ) ^ d) * Aouter := by
  have hsub := translatedCube_point_subset_target_succ hx
  have hfInner : IntegrableOn f (translatedCube d (n : ℤ) x) :=
    hf.mono_set hsub
  have hf2Inner : IntegrableOn (fun y ↦ f y ^ 2)
      (translatedCube d (n : ℤ) x) := hf2.mono_set hsub
  have hpointMean := abs_point_sub_triadicMean_le_of_halfDecay
    hA hfInner hf2Inner hdecay hpoint
  have hmean := abs_averageOn_translatedCube_pred_sub_le_of_subset
    (ell := ((n + 1 : ℕ) : ℤ)) (zInner := x) (zOuter := z')
    (f := f) (by
      have hncast : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
      rw [hncast]
      exact hsub) hf hf2
  have hncast : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
  rw [hncast] at hmean
  have hmean' : |averageOn (translatedCube d (n : ℤ) x) f -
        averageOn (translatedCube d ((n + 1 : ℕ) : ℤ) z') f| ≤
      Real.sqrt ((3 : ℝ) ^ d) * Aouter := hmean.trans
        (mul_le_mul_of_nonneg_left houter (Real.sqrt_nonneg _))
  have htri := abs_sub_le (fRep x)
    (averageOn (translatedCube d (n : ℤ) x) f)
    (averageOn (translatedCube d ((n + 1 : ℕ) : ℤ) z') f)
  exact htri.trans (by linarith [hpointMean, hmean'])

/-- Final deterministic pair of readouts.  The first is the decaying literal
oscillation row.  The second is the undecayed point-to-parent-mean `sSup`
row; only the common target-to-parent mean increment is added. -/
theorem targetOscillation_and_pointToParentMean_of_commonMean
    {S : Set (Vec d)} {fRep : Vec d → ℝ}
    {targetMean parentMean K P : ℝ}
    (hS : S.Nonempty)
    (hpoint : ∀ x ∈ S, |fRep x - targetMean| ≤ K)
    (hmean : |targetMean - parentMean| ≤ P) :
    oscillationOn S fRep ≤ 2 * K ∧
      sSup {r : ℝ | ∃ x ∈ S, r = |fRep x - parentMean|} ≤ K + P := by
  refine ⟨oscillationOn_le_two_mul_of_point_sub_common hS hpoint, ?_⟩
  apply sSup_point_sub_common_le hS
  intro x hx
  exact (abs_sub_le (fRep x) targetMean parentMean).trans
    (by linarith [hpoint x hx, hmean])

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
