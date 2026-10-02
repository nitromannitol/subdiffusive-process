import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Paper.inputs_classical_e2_morrey

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_inputs_W_morrey_norm_le_euclidean {d : ℕ}
    (x y : SpatialCoordinates d) :
    ‖x - y‖ ≤ Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) := by
  have hsum : 0 ≤ ∑ i : Fin d, (x i - y i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  have hterm : (x i - y i) ^ 2 ≤ ∑ j : Fin d, (x j - y j) ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin d => (x j - y j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  simpa only [sq_abs, Real.sq_sqrt hsum] using hterm

theorem inputs_W_morrey (d : ℕ) :
    ∀ (p1 : ℝ), 2 ≤ p1 → ∀ (alpha : ℝ), 0 < alpha → alpha < 1 - (d : ℝ) / p1 →
      ∃ C : ℝ, 0 < C ∧ ∀ (x0 : SpatialCoordinates d) (l : ℝ) (hl : (0 : ℝ) < 4 * l)
      (u : weakSobolevGraph (centeredCube x0 (4 * l) hl)),
      MemLp (fun y => Real.sqrt (∑ i : Fin d,
            ((sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl))) i y) ^ 2))
          (ENNReal.ofReal p1)
          ((volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d))).restrict
            (Metric.ball x0 l)) →
      ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
        ((u : SobolevData (centeredCube x0 (4 * l) hl)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[(volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d))).restrict
              (Metric.ball x0 l)] U ∧
        IsHolderOn alpha (Metric.closedBall x0 l) U ∧
        holderSeminorm alpha (Metric.closedBall x0 l) U ≤
          C * l ^ (1 - alpha) *
            normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x0 l)
              (sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl))) := by
  intro p1 hp alpha halpha hpa
  obtain ⟨C, hC, hMorrey⟩ :=
    inputs_classical_e2_morrey d p1 alpha hp halpha hpa
  refine ⟨C, hC, ?_⟩
  intro x0 l hl u hmem
  have hlpos : 0 < l := by nlinarith
  have hball : Metric.ball x0 l ⊆ (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d)) := by
    intro y hy
    change dist y x0 < (4 * l) / 2
    change dist y x0 < l at hy
    nlinarith
  have hμ :
      (volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d))).restrict
          (Metric.ball x0 l) = volume.restrict (Metric.ball x0 l) :=
    Measure.restrict_restrict_of_subset hball
  obtain ⟨v, hvfun, hvgrad⟩ :=
    SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph u
  let vBall : Homogenization.H1Function (Metric.ball x0 l) :=
    v.restrict Metric.isOpen_ball hball
  have hgradBall :
      MemLp (fun y => Real.sqrt (∑ i : Fin d, (vBall.grad y i) ^ 2))
        (ENNReal.ofReal p1) (volume.restrict (Metric.ball x0 l)) := by
    rw [← hμ]
    simpa only [vBall, Homogenization.H1Function.restrict, hvgrad] using hmem
  obtain ⟨U, hUcont, hUae, hUbound⟩ :=
    hMorrey x0 l hlpos vBall hgradBall
  have hfun :
      (fun z => Real.sqrt (∑ i : Fin d,
        ((sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl))) i z) ^ 2)) =
      (fun z => Real.sqrt (∑ i : Fin d, (vBall.grad z i) ^ 2)) := by
    funext z
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hproj :
        (sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl))).ofLp i =
          (u : SobolevData (centeredCube x0 (4 * l) hl)).2 i := rfl
    rw [hproj]
    simp only [vBall, Homogenization.H1Function.restrict]
    rw [← congrFun (congrFun hvgrad z) i]
  have hnorm :
      normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x0 l)
        (sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl))) =
      (eLpNorm (fun y => Real.sqrt (∑ i : Fin d, (vBall.grad y i) ^ 2))
          (ENNReal.ofReal p1) (volume.restrict (Metric.ball x0 l))).toReal /
        (volume.real (Metric.ball x0 l)) ^ (1 / p1) := by
    unfold normalizedGradientLpNorm
    rw [hμ, hfun, ENNReal.toReal_ofReal (by linarith : 0 ≤ p1)]
  have hUaeTarget :
      ((u : SobolevData (centeredCube x0 (4 * l) hl)).1 : SpatialCoordinates d → ℝ) =ᵐ[
        (volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d))).restrict
          (Metric.ball x0 l)] U := by
    rw [hμ]
    filter_upwards [hUae] with y hy
    rw [← congrFun hvfun y]
    exact hy
  let A := C * l ^ (1 - alpha) *
    normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x0 l)
      (sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl)))
  have hratio : ∀ q ∈ holderRatioSet alpha (Metric.closedBall x0 l) U, q ≤ A := by
    intro q hq
    change q ∈ {q : ℝ | ∃ x ∈ Metric.closedBall x0 l, ∃ y ∈ Metric.closedBall x0 l,
      x ≠ y ∧ q = |U x - U y| /
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha} at hq
    rcases hq with ⟨x, hx, y, hy, hxy, hq⟩
    rw [hq]
    let D := Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)
    have hsum : 0 < ∑ i : Fin d, (x i - y i) ^ 2 := by
      have hnonneg : 0 ≤ ∑ i : Fin d, (x i - y i) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      by_contra hn
      have hzero : ∑ i : Fin d, (x i - y i) ^ 2 = 0 := by linarith
      have heq : x = y := by
        funext i
        have hi : (x i - y i) ^ 2 ≤ ∑ j : Fin d, (x j - y j) ^ 2 :=
          Finset.single_le_sum (f := fun j : Fin d => (x j - y j) ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        have hizero : (x i - y i) ^ 2 = 0 := by
          nlinarith [sq_nonneg (x i - y i)]
        have hcoord : x i - y i = 0 := by nlinarith
        exact sub_eq_zero.mp hcoord
      exact hxy heq
    have hDpos : 0 < D := by
      dsimp [D]
      exact Real.sqrt_pos.2 hsum
    have hDpow : 0 < D ^ alpha := Real.rpow_pos_of_pos hDpos alpha
    have hdist : ‖x - y‖ ≤ D := by
      simpa [D] using aux_inputs_W_morrey_norm_le_euclidean x y
    have hpow : ‖x - y‖ ^ alpha ≤ D ^ alpha :=
      Real.rpow_le_rpow (norm_nonneg _) hdist halpha.le
    have hcoef_nonneg : 0 ≤ C * l ^ (1 - alpha) *
        ((eLpNorm (fun z => Real.sqrt (∑ i : Fin d, (vBall.grad z i) ^ 2))
            (ENNReal.ofReal p1) (volume.restrict (Metric.ball x0 l))).toReal /
          (volume.real (Metric.ball x0 l)) ^ (1 / p1)) := by
      positivity
    have hpoint := hUbound x hx y hy
    have hpoint' : |U x - U y| ≤ A * D ^ alpha := by
      calc
        |U x - U y| ≤
            (C * l ^ (1 - alpha) *
              ((eLpNorm (fun z => Real.sqrt (∑ i : Fin d, (vBall.grad z i) ^ 2))
                    (ENNReal.ofReal p1) (volume.restrict (Metric.ball x0 l))).toReal /
                (volume.real (Metric.ball x0 l)) ^ (1 / p1))) * ‖x - y‖ ^ alpha := hpoint
        _ ≤ (C * l ^ (1 - alpha) *
              ((eLpNorm (fun z => Real.sqrt (∑ i : Fin d, (vBall.grad z i) ^ 2))
                    (ENNReal.ofReal p1) (volume.restrict (Metric.ball x0 l))).toReal /
                (volume.real (Metric.ball x0 l)) ^ (1 / p1))) * D ^ alpha := by
          exact mul_le_mul_of_nonneg_left hpow hcoef_nonneg
        _ = A * D ^ alpha := by
          dsimp [A]
          rw [hnorm]
    have hquot : |U x - U y| / D ^ alpha ≤ A :=
      (div_le_iff₀ hDpow).2 (by simpa [mul_comm] using hpoint')
    simpa [D] using hquot
  have hIsHolder : IsHolderOn alpha (Metric.closedBall x0 l) U := by
    unfold IsHolderOn
    exact ⟨A, hratio⟩
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    rw [hnorm]
    positivity
  have hseminorm : holderSeminorm alpha (Metric.closedBall x0 l) U ≤ A := by
    unfold holderSeminorm
    by_cases hne : (holderRatioSet alpha (Metric.closedBall x0 l) U).Nonempty
    · exact csSup_le hne hratio
    · have hempty : holderRatioSet alpha (Metric.closedBall x0 l) U = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty, Real.sSup_empty]
      exact hAnonneg
  refine ⟨U, hUcont, hUaeTarget, hIsHolder, ?_⟩
  simpa [A] using hseminorm

end Paper

