module

public import SubdiffusiveProcess.Static.CoercivityCover
public import SubdiffusiveProcess.Static.CubeCoercivityComparison
public import SubdiffusiveProcess.Static.FractionalReadout

@[expose] public section

/-! # Native coercivity assembled from a finite near-pair cover -/

open MeasureTheory Homogenization SubdiffusiveProcess.Static
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The deterministic price of the far-pair contribution. -/
def farPairPrice (d : ℕ) (s t : ℝ) : ℝ := 4 * (4 / t) ^ ((d : ℝ) + 3 / 2) * s ^ d

/-- Finite local `H¹` inequalities control the global literal fractional
norm. Native a.e. representatives are handled without changing gradients. -/
theorem H1_coercivity_of_nearPair_cover {d : ℕ} (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (A : Vec d → ℝ) (Y : Finset (Vec d)) (K : Vec d → ℝ)
    (hK : ∀ y ∈ Y, 0 ≤ K y)
    (hsub : ∀ y ∈ Y, Metric.ball y (t / 2) ⊆ Metric.ball (0 : Vec d) (s / 2))
    (hcov : ∀ x ∈ Metric.ball (0 : Vec d) (s / 2),
      ∀ z ∈ Metric.ball (0 : Vec d) (s / 2), ‖x - z‖ < t / 4 →
        ∃ y ∈ Y, x ∈ Metric.ball y (t / 2) ∧ z ∈ Metric.ball y (t / 2))
    (hcoer : ∀ y ∈ Y, ∀ H : H1Function (Metric.ball y (t / 2)),
      fractionalSqNorm (Metric.ball y (t / 2)) H.toFun ≤ ENNReal.ofReal (K y) *
        (energy (Metric.ball y (t / 2)) A H.grad +
          ∫⁻ x in Metric.ball y (t / 2), ENNReal.ofReal (H.toFun x ^ 2))) :
    ∀ H : H1Function (Metric.ball (0 : Vec d) (s / 2)),
      fractionalSqNorm (Metric.ball (0 : Vec d) (s / 2)) H.toFun ≤
        ENNReal.ofReal ((∑ y ∈ Y, K y) + farPairPrice d s t + 1) *
          (energy (Metric.ball (0 : Vec d) (s / 2)) A H.grad +
            ∫⁻ x in Metric.ball (0 : Vec d) (s / 2), ENNReal.ofReal (H.toFun x ^ 2)) := by
  classical
  intro H
  obtain ⟨W, hW, hWgrad, hHW⟩ := exists_measurable_H1Function H
  have hL2 : (∫⁻ x in Metric.ball (0 : Vec d) (s / 2), ENNReal.ofReal (H.toFun x ^ 2)) =
      ∫⁻ x in Metric.ball (0 : Vec d) (s / 2), ENNReal.ofReal (W.toFun x ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards [hHW] with x hx
    rw [hx]
  rw [fractionalSqNorm_congr_ae hHW, hL2, ← hWgrad]
  let U := Metric.ball (0 : Vec d) (s / 2)
  let L2 := ∫⁻ x in U, ENNReal.ofReal (W.toFun x ^ 2)
  let Q := energy U A W.grad + L2
  have hcover := fractionalCover_bound W.toFun hW s t hs ht Y hcov
  have hlocal : ∀ y ∈ Y,
      fractionalCoverIntegral W.toFun (Metric.ball y (t / 2)) ≤ ENNReal.ofReal (K y) * Q := by
    intro y hy
    let V := Metric.ball y (t / 2)
    let W' := W.restrict Metric.isOpen_ball (hsub y hy)
    have hbound := hcoer y hy W'
    have he : energy V A W.grad ≤ energy U A W.grad :=
      lintegral_mono' (Measure.restrict_mono (hsub y hy) le_rfl) le_rfl
    have hl : (∫⁻ x in V, ENNReal.ofReal (W.toFun x ^ 2)) ≤ L2 :=
      lintegral_mono' (Measure.restrict_mono (hsub y hy) le_rfl) le_rfl
    exact (le_add_of_nonneg_right zero_le).trans
      (hbound.trans (mul_le_mul_right (add_le_add he hl) _))
  have hsum : (∑ y ∈ Y, fractionalCoverIntegral W.toFun (Metric.ball y (t / 2))) ≤
      ENNReal.ofReal (∑ y ∈ Y, K y) * Q := by
    refine (Finset.sum_le_sum hlocal).trans_eq ?_
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg hK]
  have hF : 0 ≤ farPairPrice d s t := by unfold farPairPrice; positivity
  have hS : 0 ≤ ∑ y ∈ Y, K y := Finset.sum_nonneg hK
  have hLQ : L2 ≤ Q := le_add_of_nonneg_left zero_le
  change fractionalCoverIntegral W.toFun U + L2 ≤ _
  calc
    fractionalCoverIntegral W.toFun U + L2 ≤
        ENNReal.ofReal (∑ y ∈ Y, K y) * Q + ENNReal.ofReal (farPairPrice d s t) * L2 + L2 :=
      add_le_add ((hcover.trans (add_le_add hsum le_rfl))) le_rfl
    _ = ENNReal.ofReal (∑ y ∈ Y, K y) * Q +
        ENNReal.ofReal (farPairPrice d s t + 1) * L2 := by
      rw [ENNReal.ofReal_add hF zero_le_one, ENNReal.ofReal_one, add_mul, one_mul, add_assoc]
    _ ≤ ENNReal.ofReal (∑ y ∈ Y, K y) * Q +
        ENNReal.ofReal (farPairPrice d s t + 1) * Q :=
      add_le_add le_rfl (mul_le_mul_right hLQ _)
    _ = _ := by
      rw [← add_mul, ← ENNReal.ofReal_add hS (add_nonneg hF zero_le_one)]
      congr 2
      ring

end SubdiffusiveProcess.Static
