module

public import SubdiffusiveProcess.Static.HarmonicCellEnergySplit
public import SubdiffusiveProcess.Static.Comparison

@[expose] public section

/-! # Local original-cell correction budgets before reflection -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The squared native gradient has the measurable lower-integral carrier. -/
theorem aemeasurable_ofReal_grad_sq {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    AEMeasurable (fun x => ENNReal.ofReal (vecNormSq (u.grad x))) (volume.restrict U) := by
  have h := (memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2).norm.aestronglyMeasurable
  have hh : AEStronglyMeasurable (fun x => euclideanNorm (u.grad x)) (volume.restrict U) := by
    simpa only [hilbertifyVecField, ← euclideanNorm_eq_norm_ofVec] using h
  simp_rw [← euclideanNorm_sq]
  exact (hh.pow 2).aemeasurable.ennreal_ofReal

/-- Ellipticity and the original macroscopic energy bound give an unweighted
local correction budget, with the literal smooth-datum volume contribution. -/
theorem local_boundaryCorrection_budget {d : ℕ}
    (u h : H1Function (openCubeSet (originCube d 0))) (a : Vec d → ℝ)
    {R H E rho : ℝ} (hR : 0 < R) (hH : 0 ≤ H) (hE : 0 ≤ E) (hrho : 0 < rho)
    (hacoef : ∀ y ∈ openCubeSet (originCube d 0), R⁻¹ ≤ a y)
    (hhgrad : ∀ y, euclideanNorm (h.grad y) ≤ H)
    (x : Vec d)
    (hbudget : ∫⁻ y in Metric.ball x rho ∩ openCubeSet (originCube d 0),
      ENNReal.ofReal (a y * vecNormSq (u.grad y)) ≤ ENNReal.ofReal E) :
    ∫⁻ y in Metric.ball x rho ∩ openCubeSet (originCube d 0),
      ENNReal.ofReal (vecNormSq (u.grad y - h.grad y)) ≤
      ENNReal.ofReal (2 * (R * E + H ^ 2 * (2 * rho) ^ d)) := by
  let W := Metric.ball x rho ∩ openCubeSet (originCube d 0)
  have hW : MeasurableSet W := measurableSet_ball.inter (isOpen_openCubeSet _).measurableSet
  have hm : volume.restrict W ≤ volume.restrict (openCubeSet (originCube d 0)) :=
    Measure.restrict_mono Set.inter_subset_right le_rfl
  have hUsm := (aemeasurable_ofReal_grad_sq u).mono_measure hm
  have hHsm := (aemeasurable_ofReal_grad_sq h).mono_measure hm
  have hnegative : AEMeasurable (fun y => ENNReal.ofReal (vecNormSq (-h.grad y)))
      (volume.restrict W) := by
    simpa only [vecNormSq, vecDot_neg_left, vecDot_neg_right, neg_neg] using hHsm
  have hsplit := lintegral_energy_add_le W (fun _ => 1) u.grad (fun y => -h.grad y)
    (fun _ => zero_le_one) (by simpa only [one_mul] using hUsm)
    (by simpa only [one_mul] using hnegative)
  simp only [one_mul, ← sub_eq_add_neg, vecNormSq, vecDot_neg_left, vecDot_neg_right, neg_neg] at hsplit
  have hU : ∫⁻ y in W, ENNReal.ofReal (vecNormSq (u.grad y)) ≤ ENNReal.ofReal (R * E) := by
    refine (SubdiffusiveProcess.Static.lintegral_ofReal_le_mul volume hW
      (g := fun y => a y * vecNormSq (u.grad y)) hR.le ?_).trans ?_
    · intro y hy
      have hr := (inv_le_iff_one_le_mul₀' hR).mp (hacoef y hy.2)
      have hn := vecNormSq_nonneg (u.grad y)
      nlinarith only [mul_le_mul_of_nonneg_right hr hn]
    · exact (mul_le_mul_right hbudget _).trans_eq (ENNReal.ofReal_mul hR.le).symm
  have hHenergy : ∫⁻ y in W, ENNReal.ofReal (vecNormSq (h.grad y)) ≤
      ENNReal.ofReal (H ^ 2 * (2 * rho) ^ d) := by
    calc
      _ ≤ ∫⁻ _y in W, ENNReal.ofReal (H ^ 2) := by
        apply lintegral_mono
        intro y
        apply ENNReal.ofReal_le_ofReal
        rw [← euclideanNorm_sq]
        exact (sq_le_sq₀ (euclideanNorm_nonneg _) hH).mpr (hhgrad y)
      _ = ENNReal.ofReal (H ^ 2) * volume W := by
        simp only [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal (H ^ 2) * volume (Metric.ball x rho) :=
        mul_le_mul_right (measure_mono Set.inter_subset_left) _
      _ = _ := by
        rw [Real.volume_pi_ball x hrho, Fintype.card_fin, ← ENNReal.ofReal_mul (sq_nonneg H)]
  refine hsplit.trans ((mul_le_mul_right (add_le_add hU hHenergy) _).trans_eq ?_)
  rw [← ENNReal.ofReal_add (mul_nonneg hR.le hE) (by positivity),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]

end SubdiffusiveProcess.Static
