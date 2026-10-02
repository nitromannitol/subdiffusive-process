import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ScaleZeroPointEndpoint
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.TriadicTargetReadout

/-!
# Theta ladder: finite Campanato readout

This is the complete deterministic telescope once a point-centred half-decay
row is available.  It returns both affine-safe consumer rows: literal target
oscillation and the undecayed point-to-parent-mean supremum.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ}

/-- Complete finite triadic readout from a uniform point-centred row family.
The scale-zero point price is kept explicit here; the next numerical layer
absorbs its polynomial parent-scale growth into the half-exponent reserve. -/
theorem finiteCampanato_targetOscillation_and_parentMean
    {n top : ℕ} (hntop : n + 1 ≤ top)
    {z' : Vec d} {S : Set (Vec d)}
    (hS : S = translatedCube d (n : ℤ) z')
    {f fRep : Vec d → ℝ} {A P0 Pparent : ℝ}
    (hA : 0 ≤ A) (hP0 : 0 ≤ P0)
    (hInt : ∀ x ∈ S, ∀ s : ℕ, s ≤ top →
      IntegrableOn f (translatedCube d (s : ℤ) x) ∧
      IntegrableOn (fun y ↦ f y ^ 2) (translatedCube d (s : ℤ) x))
    (hrows : ∀ x ∈ S, ∀ s : ℕ, s ≤ top →
      normalizedL2On (translatedCube d (s : ℤ) x)
          (fun y ↦ f y - averageOn (translatedCube d (s : ℤ) x) f) ≤
        A * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * ((top : ℝ) - (s : ℝ))))
    (hpoint0 : ∀ x ∈ S,
      |fRep x - averageOn (translatedCube d 0 x) f| ≤
        P0 * normalizedL2On (translatedCube d 0 x)
          (fun y ↦ f y - averageOn (translatedCube d 0 x) f))
    (htopMean : |averageOn (translatedCube d (top : ℤ) z') f -
        Pparent| ≤ A) :
    let Ktarget :=
      P0 * (A * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (top : ℝ))) +
        5 / 2 * Real.sqrt ((3 : ℝ) ^ d) *
          (A * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ)))) +
        Real.sqrt ((3 : ℝ) ^ d) *
          (A * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((top : ℝ) - ((n + 1 : ℕ) : ℝ))))
    oscillationOn S fRep ≤ 2 * Ktarget ∧
      sSup {r : ℝ | ∃ x ∈ S, r = |fRep x - Pparent|} ≤
        Ktarget + 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * A + A := by
  dsimp only
  let An := A * (3 : ℝ) ^
    (-(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ)))
  let Anext := A * (3 : ℝ) ^
    (-(1 / 2 : ℝ) * ((top : ℝ) - ((n + 1 : ℕ) : ℝ)))
  let E := P0 * (A * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (top : ℝ)))
  let K := E + 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * An +
    Real.sqrt ((3 : ℝ) ^ d) * Anext
  have hSnonempty : S.Nonempty := by
    refine ⟨z', ?_⟩
    rw [hS, translatedCube_eq_metricBall]
    exact Metric.mem_ball_self (by positivity)
  have hAn : 0 ≤ An :=
    mul_nonneg hA (Real.rpow_nonneg (by norm_num) _)
  have hAnext : 0 ≤ Anext :=
    mul_nonneg hA (Real.rpow_nonneg (by norm_num) _)
  have hE : 0 ≤ E := by
    exact mul_nonneg hP0
      (mul_nonneg hA (Real.rpow_nonneg (by norm_num) _))
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hpointTarget : ∀ x ∈ S,
      |fRep x - averageOn
        (translatedCube d ((n + 1 : ℕ) : ℤ) z') f| ≤ K := by
    intro x hx
    have hxTarget : x ∈ translatedCube d (n : ℤ) z' := by
      rwa [← hS]
    have hIntOuter := hInt z' (by
      rw [hS, translatedCube_eq_metricBall]
      exact Metric.mem_ball_self (by positivity)) (n + 1) hntop
    have hdecay : ∀ s : ℕ, s ≤ n →
        normalizedL2On (translatedCube d (s : ℤ) x)
            (fun y ↦ f y - averageOn (translatedCube d (s : ℤ) x) f) ≤
          An * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((n : ℝ) - (s : ℝ))) := by
      intro s hsn
      have hsTop : s ≤ top := hsn.trans (Nat.le_trans (Nat.le_succ n) hntop)
      have hrow := hrows x hx s hsTop
      have hsplit :
          -(1 / 2 : ℝ) * ((top : ℝ) - (s : ℝ)) =
            -(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ)) +
              -(1 / 2 : ℝ) * ((n : ℝ) - (s : ℝ)) := by ring
      dsimp only [An]
      rw [hsplit, Real.rpow_add (by norm_num : (0 : ℝ) < 3)] at hrow
      simpa only [mul_assoc] using hrow
    have hpoint : |fRep x - averageOn (translatedCube d 0 x) f| ≤ E := by
      have hzero := hrows x hx 0 (Nat.zero_le top)
      have hmul := mul_le_mul_of_nonneg_left hzero hP0
      have hraw := (hpoint0 x hx).trans hmul
      simpa only [E, Nat.cast_zero, sub_zero] using hraw
    have houter : normalizedL2On
        (translatedCube d ((n + 1 : ℕ) : ℤ) z')
          (fun y ↦ f y - averageOn
            (translatedCube d ((n + 1 : ℕ) : ℤ) z') f) ≤ Anext := by
      have hrow := hrows z' (by
        rw [hS, translatedCube_eq_metricBall]
        exact Metric.mem_ball_self (by positivity)) (n + 1) hntop
      simpa only [Anext] using hrow
    have hout := abs_point_sub_targetSuccMean_le_of_halfDecay
      hxTarget hAn hIntOuter.1 hIntOuter.2 hdecay hpoint houter
    simpa only [K, E, An, Anext] using hout
  have hosc := oscillationOn_le_two_mul_of_point_sub_common
    hSnonempty hpointTarget
  have hIntTop := hInt z' (by
    rw [hS, translatedCube_eq_metricBall]
    exact Metric.mem_ball_self (by positivity)) top le_rfl
  have hmeanTargetTop := abs_averageOn_translatedCube_nat_sub_le_of_halfDecay
    (d := d) (top := top) (n := n + 1) hntop hA hIntTop.1 hIntTop.2
    (fun s hs hst ↦ hrows z' (by
      rw [hS, translatedCube_eq_metricBall]
      exact Metric.mem_ball_self (by positivity)) s hst)
  have htargetParent :
      |averageOn (translatedCube d ((n + 1 : ℕ) : ℤ) z') f - Pparent| ≤
        5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * A + A := by
    exact (abs_sub_le
      (averageOn (translatedCube d ((n + 1 : ℕ) : ℤ) z') f)
      (averageOn (translatedCube d (top : ℤ) z') f) Pparent).trans
        (add_le_add hmeanTargetTop htopMean)
  have hsup := sSup_point_sub_common_le hSnonempty (fun x hx ↦
    (abs_sub_le (fRep x)
      (averageOn (translatedCube d ((n + 1 : ℕ) : ℤ) z') f)
      Pparent).trans (add_le_add (hpointTarget x hx) htargetParent))
  refine ⟨?_, ?_⟩
  · simpa only [K, E, An, Anext] using hosc
  · simpa only [K, E, An, Anext, add_assoc] using hsup

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
