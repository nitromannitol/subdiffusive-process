module

public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Main.MeasureTraceCharacterization
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff
noncomputable section

namespace SubdiffusiveProcess

theorem measureTrace_unique_of_smoothDensity
    {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (ν : Measure (SpatialCoordinates d)) (K C : ℝ)
    (T₁ T₂ : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder → Lp ℝ 2 ν)
    (hT₁ : MeasureTraceCharacterization hd Q hr ν K C T₁)
    (hT₂ : MeasureTraceCharacterization hd Q hr ν K C T₂)
    (hdense : ∀ u : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder,
      ∃ (a : ℕ → CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
            (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder)
        (f : ℕ → SpatialCoordinates d → ℝ)
        (w : ℕ → CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
            (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder),
        (∀ n, ContDiff ℝ ∞ (f n)) ∧
        (∀ n, MemLp (f n) 2 ν) ∧
        (∀ n, (a n).val 0 =ᵐ[volume.restrict
            (centeredCube (Homogenization.cubeCenter Q)
              (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d))] f n) ∧
        (∀ n, (w n).val 0 = u.val 0 - (a n).val 0) ∧
        Filter.Tendsto
          (fun n => cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
            (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (w n))
          Filter.atTop (nhds 0)) :
    T₁ = T₂ := by
  rcases hT₁ with ⟨hT₁_exists, hT₁_bound, hT₁_trace⟩
  rcases hT₂ with ⟨hT₂_exists, hT₂_bound, hT₂_trace⟩
  funext u
  obtain ⟨a, f, w, hfcont, hfmem, hfae, hwdiff, hlim⟩ := hdense u
  have haeq : ∀ n, T₁ (a n) = T₂ (a n) := by
    intro n
    exact (hT₁_trace (f n) (hfcont n) (a n) (hfae n) (hfmem n)).trans
      (hT₂_trace (f n) (hfcont n) (a n) (hfae n) (hfmem n)).symm
  let A : ℝ := C * (K + (ν (closure (Homogenization.openCubeSet Q))).toReal)
  have hnorm₁ : Filter.Tendsto (fun n => ‖T₁ u - T₁ (a n)‖) Filter.atTop (nhds 0) := by
    have hsq : ∀ n, ‖T₁ u - T₁ (a n)‖ ^ 2 ≤
        A * (cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (w n)) ^ 2 := by
      intro n
      exact hT₁_bound u (a n) (w n) (hwdiff n)
    have harg : Filter.Tendsto
        (fun n => A * (cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (w n)) ^ 2)
        Filter.atTop (nhds 0) := by
      have hpow := hlim.pow 2
      have hmul := hpow.const_mul A
      simpa [A] using hmul
    have hsqrt : Filter.Tendsto
        (fun n => Real.sqrt (A * (cubeFractionalL2Norm hd
          (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr
          halfFractionalOrder (w n)) ^ 2)) Filter.atTop (nhds 0) := by
      have hs := Real.continuous_sqrt.continuousAt.tendsto.comp harg
      simpa only [Function.comp_def, Real.sqrt_zero] using hs
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n => norm_nonneg _
    · exact Filter.Eventually.of_forall fun n => Real.le_sqrt_of_sq_le (hsq n)
    · exact hsqrt
  have hnorm₂ : Filter.Tendsto (fun n => ‖T₂ (a n) - T₂ u‖) Filter.atTop (nhds 0) := by
    have hsq : ∀ n, ‖T₂ (a n) - T₂ u‖ ^ 2 ≤
        A * (cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (w n)) ^ 2 := by
      intro n
      simpa only [norm_sub_rev] using hT₂_bound u (a n) (w n) (hwdiff n)
    have harg : Filter.Tendsto
        (fun n => A * (cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder (w n)) ^ 2)
        Filter.atTop (nhds 0) := by
      have hpow := hlim.pow 2
      have hmul := hpow.const_mul A
      simpa [A] using hmul
    have hsqrt : Filter.Tendsto
        (fun n => Real.sqrt (A * (cubeFractionalL2Norm hd
          (Homogenization.cubeCenter Q) (Homogenization.cubeScaleFactor Q) hr
          halfFractionalOrder (w n)) ^ 2)) Filter.atTop (nhds 0) := by
      have hs := Real.continuous_sqrt.continuousAt.tendsto.comp harg
      simpa only [Function.comp_def, Real.sqrt_zero] using hs
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n => norm_nonneg _
    · exact Filter.Eventually.of_forall fun n => Real.le_sqrt_of_sq_le (hsq n)
    · exact hsqrt
  have hsum : Filter.Tendsto
      (fun n => ‖T₁ u - T₁ (a n)‖ + ‖T₂ (a n) - T₂ u‖)
      Filter.atTop (nhds 0) := by
    simpa only [add_zero] using hnorm₁.add hnorm₂
  have hfixed : ‖T₁ u - T₂ u‖ ≤ 0 := by
    apply ge_of_tendsto hsum
    exact Filter.Eventually.of_forall fun n => by
      calc
        ‖T₁ u - T₂ u‖ =
            ‖(T₁ u - T₁ (a n)) + (T₁ (a n) - T₂ u)‖ := by
          congr 1 ; abel
        _ ≤ ‖T₁ u - T₁ (a n)‖ + ‖T₁ (a n) - T₂ u‖ :=
          norm_add_le _ _
        _ ≤ ‖T₁ u - T₁ (a n)‖ +
            (‖T₁ (a n) - T₂ (a n)‖ + ‖T₂ (a n) - T₂ u‖) := by
          gcongr
          calc
            ‖T₁ (a n) - T₂ u‖ =
                ‖(T₁ (a n) - T₂ (a n)) + (T₂ (a n) - T₂ u)‖ := by
              congr 1 ; abel
            _ ≤ ‖T₁ (a n) - T₂ (a n)‖ + ‖T₂ (a n) - T₂ u‖ :=
              norm_add_le _ _
        _ = ‖T₁ u - T₁ (a n)‖ + ‖T₂ (a n) - T₂ u‖ := by
          rw [haeq n]
          simp only [sub_self, norm_zero, zero_add]
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hfixed (norm_nonneg _)))

end SubdiffusiveProcess
