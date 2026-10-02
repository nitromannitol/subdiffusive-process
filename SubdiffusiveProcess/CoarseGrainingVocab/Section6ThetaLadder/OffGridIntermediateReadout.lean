import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.AmbientOscillationEnergy
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.OffGridCampanatoRows

/-!
# Theta ladder: off-grid readout of an intermediate stopped row

This is the deterministic composition needed at each rung of the finite
mean telescope.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ}

/-- A uniform intermediate row on the selected grid centre becomes the
point-centred row, with its top energy read against the literal ambient
oscillation. -/
theorem pointCenteredRow_le_ambientOscillation_of_intermediate
    {m s : ℕ} (hsm : s + 4 ≤ m) {z x : Vec d}
    (hx : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {h : H1Function (translatedCube d (m : ℤ) z)}
    {hRep : Vec d → ℝ}
    (hRepCont : ContinuousOn hRep (translatedCube d (m : ℤ) z))
    (hRepAE : hRep =ᵐ[volume.restrict (translatedCube d (m : ℤ) z)] h.toFun)
    {K : ℝ} (hK : 0 ≤ K)
    (hrow : ∀ q : Vec d, OnTriadicGrid s q → q ∈ cube d (m : ℤ) →
      translatedCube d ((m : ℤ) - 2) (z + q) ⊆
          {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ (m : ℤ) / 8} →
      normalizedL2On (translatedCube d ((s : ℤ) + 1) (z + q))
          (fun y ↦ h.toFun y - averageOn
            (translatedCube d ((s : ℤ) + 1) (z + q)) h.toFun) ≤
        K * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * (((m : ℝ) - 2) - ((s : ℝ) + 1))) *
          normalizedL2On (translatedCube d ((m : ℤ) - 2) (z + q))
            (fun y ↦ h.toFun y - averageOn
              (translatedCube d ((m : ℤ) - 2) (z + q)) h.toFun)) :
    normalizedL2On (translatedCube d (s : ℤ) x)
        (fun y ↦ h.toFun y - averageOn
          (translatedCube d (s : ℤ) x) h.toFun) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        (K * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * (((m : ℝ) - 2) - ((s : ℝ) + 1))) *
        oscillationOn {y : Vec d | ‖y - z‖ ≤
          3 * (3 : ℝ) ^ (m : ℤ) / 8} hRep) := by
  obtain ⟨q, hqgrid, hqmem, hinner, htop⟩ :=
    exists_relativeGridCentre_with_campanatoWindows
      (by omega : s + 3 ≤ m) hx
  let Q := translatedCube d ((s : ℤ) + 1) (z + q)
  let T := translatedCube d ((m : ℤ) - 2) (z + q)
  have hQsubT : Q ⊆ T := by
    dsimp only [Q, T]
    exact translatedCube_subset_translatedCube_sameCenter (by omega) (z + q)
  have hTparent : T ⊆ translatedCube d (m : ℤ) z := by
    exact htop.trans (by
      intro y hy
      have hpowEq : (3 : ℝ) ^ (m : ℤ) = (3 : ℝ) ^ m := zpow_natCast _ _
      rw [translatedCube_eq_metricBall, Metric.mem_ball, dist_eq_norm, hpowEq]
      rw [hpowEq] at hy
      have hp : 0 < (3 : ℝ) ^ m := by positivity
      exact lt_of_le_of_lt hy (by nlinarith))
  have hmemT : MemLp h.toFun 2 (volume.restrict T) :=
    h.memL2.mono_measure (Measure.restrict_mono hTparent le_rfl)
  letI : IsFiniteMeasure (volume.restrict T) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_top_iff_ne_top.mpr
          (volume_translatedCube_ne_top ((m : ℤ) - 2) (z + q))⟩
  have hfT : IntegrableOn h.toFun T := hmemT.integrable one_le_two
  have hf2T : IntegrableOn (fun y ↦ h.toFun y ^ 2) T := hmemT.integrable_sq
  have htopEnergy : normalizedL2On T
        (fun y ↦ h.toFun y - averageOn T h.toFun) ≤
      oscillationOn {y : Vec d | ‖y - z‖ ≤
        3 * (3 : ℝ) ^ (m : ℤ) / 8} hRep := by
    apply normalizedL2On_centered_le_ambientOscillation
      (by rw [translatedCube_eq_metricBall]; exact measurableSet_ball)
      (volume_translatedCube_toReal_pos ((m : ℤ) - 2) (z + q))
      (volume_translatedCube_ne_top ((m : ℤ) - 2) (z + q))
    · refine ⟨z + q, ?_⟩
      rw [translatedCube_eq_metricBall]
      exact Metric.mem_ball_self (by positivity)
    · exact htop
    · exact hRepCont
    · exact hRepAE
  have hQrow := hrow q hqgrid hqmem htop
  have hQbound : normalizedL2On Q
        (fun y ↦ h.toFun y - averageOn Q h.toFun) ≤
      K * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * (((m : ℝ) - 2) - ((s : ℝ) + 1))) *
        oscillationOn {y : Vec d | ‖y - z‖ ≤
          3 * (3 : ℝ) ^ (m : ℤ) / 8} hRep := by
    exact hQrow.trans (mul_le_mul_of_nonneg_left htopEnergy
      (mul_nonneg hK (Real.rpow_nonneg (by norm_num) _)))
  have hrestrict := normalizedL2On_centered_le_sqrt_three_of_subset_succ
    (ell := (s : ℤ)) (zInner := x) (zOuter := z + q) (f := h.toFun)
    (by simpa only using hinner) (hfT.mono_set hQsubT) (hf2T.mono_set hQsubT)
  exact hrestrict.trans
    (mul_le_mul_of_nonneg_left hQbound (Real.sqrt_nonneg _))

/-- The parallel off-grid row used by the undecayed mean telescope.  Here the
moving top energy is read against the centered parent energy with the fixed
two-scale volume price. -/
theorem pointCenteredRow_le_parentCentered_of_intermediate
    {m s : ℕ} (hsm : s + 4 ≤ m) {z x : Vec d}
    (hx : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {h : H1Function (translatedCube d (m : ℤ) z)}
    {K : ℝ} (hK : 0 ≤ K)
    (hrow : ∀ q : Vec d, OnTriadicGrid s q → q ∈ cube d (m : ℤ) →
      translatedCube d ((m : ℤ) - 2) (z + q) ⊆
          {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ (m : ℤ) / 8} →
      normalizedL2On (translatedCube d ((s : ℤ) + 1) (z + q))
          (fun y ↦ h.toFun y - averageOn
            (translatedCube d ((s : ℤ) + 1) (z + q)) h.toFun) ≤
        K * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * (((m : ℝ) - 2) - ((s : ℝ) + 1))) *
          normalizedL2On (translatedCube d ((m : ℤ) - 2) (z + q))
            (fun y ↦ h.toFun y - averageOn
              (translatedCube d ((m : ℤ) - 2) (z + q)) h.toFun)) :
    normalizedL2On (translatedCube d (s : ℤ) x)
        (fun y ↦ h.toFun y - averageOn
          (translatedCube d (s : ℤ) x) h.toFun) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        (K * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * (((m : ℝ) - 2) - ((s : ℝ) + 1))) *
        (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          normalizedL2On (translatedCube d (m : ℤ) z)
            (fun y ↦ h.toFun y - averageOn
              (translatedCube d (m : ℤ) z) h.toFun))) := by
  obtain ⟨q, hqgrid, hqmem, hinner, htop⟩ :=
    exists_relativeGridCentre_with_campanatoWindows
      (by omega : s + 3 ≤ m) hx
  let Q := translatedCube d ((s : ℤ) + 1) (z + q)
  let T := translatedCube d ((m : ℤ) - 2) (z + q)
  let P := translatedCube d (m : ℤ) z
  have hQsubT : Q ⊆ T := by
    dsimp only [Q, T]
    exact translatedCube_subset_translatedCube_sameCenter (by omega) (z + q)
  have hTparent : T ⊆ P := by
    exact htop.trans (by
      intro y hy
      have hpowEq : (3 : ℝ) ^ (m : ℤ) = (3 : ℝ) ^ m := zpow_natCast _ _
      dsimp only [P]
      rw [translatedCube_eq_metricBall, Metric.mem_ball, dist_eq_norm, hpowEq]
      rw [hpowEq] at hy
      have hp : 0 < (3 : ℝ) ^ m := by positivity
      exact lt_of_le_of_lt hy (by nlinarith))
  have hmemP : MemLp h.toFun 2 (volume.restrict P) := by
    simpa only [P] using h.memL2
  letI : IsFiniteMeasure (volume.restrict P) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_top_iff_ne_top.mpr
          (volume_translatedCube_ne_top (m : ℤ) z)⟩
  have hfP : IntegrableOn h.toFun P := hmemP.integrable one_le_two
  have hf2P : IntegrableOn (fun y ↦ h.toFun y ^ 2) P := hmemP.integrable_sq
  have htopEnergy : normalizedL2On T
        (fun y ↦ h.toFun y - averageOn T h.toFun) ≤
      Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
        normalizedL2On P
          (fun y ↦ h.toFun y - averageOn P h.toFun) := by
    simpa only [T, P] using normalizedL2On_predTwo_centered_le_parent
      hTparent hfP hf2P
  have hQrow := hrow q hqgrid hqmem htop
  have hQbound : normalizedL2On Q
        (fun y ↦ h.toFun y - averageOn Q h.toFun) ≤
      K * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * (((m : ℝ) - 2) - ((s : ℝ) + 1))) *
        (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          normalizedL2On P
            (fun y ↦ h.toFun y - averageOn P h.toFun)) := by
    exact hQrow.trans (mul_le_mul_of_nonneg_left htopEnergy
      (mul_nonneg hK (Real.rpow_nonneg (by norm_num) _)))
  have hfT : IntegrableOn h.toFun T := hfP.mono_set hTparent
  have hf2T : IntegrableOn (fun y ↦ h.toFun y ^ 2) T :=
    hf2P.mono_set hTparent
  have hrestrict := normalizedL2On_centered_le_sqrt_three_of_subset_succ
    (ell := (s : ℤ)) (zInner := x) (zOuter := z + q) (f := h.toFun)
    (by simpa only using hinner) (hfT.mono_set hQsubT) (hf2T.mono_set hQsubT)
  exact hrestrict.trans
    (mul_le_mul_of_nonneg_left hQbound (Real.sqrt_nonneg _))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
