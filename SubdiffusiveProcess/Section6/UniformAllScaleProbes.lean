import SubdiffusiveProcess.Section6.UniformQuenchedDecay
import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.AllScaleProbeMoment

/-! A law-uniform probe bound at all integer scales. -/
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab hiding TriadicCube Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

noncomputable section
namespace SubdiffusiveProcess.Section6

theorem exists_law_uniform_allScale_probe_bound (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 / 16 ∧
      ∀ L : ℕ, ∀ delta : ℝ, ∃ Cst : ℝ → ℝ, (∀ xi : ℝ, 0 ≤ Cst xi) ∧
          ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta = delta →
          ∀ xi : ℝ, 2 ≤ xi → ∀ R : TriadicCube d,
            lpMoment M.P.toMeasure xi
                (fun omega => finiteProbeSum M L (ahom M L) R omega) ≤
              Cst xi * Real.rpow (3 : ℝ) (-rho * ((R.scale : ℤ) : ℝ)) := by
  classical
  obtain ⟨rho0, hrho0, hdecay⟩ := exists_law_uniform_lpMoment_probe_decay d hd
  refine ⟨min rho0 (1 / 16), lt_min hrho0 (by norm_num), min_le_right _ _, ?_⟩
  set rho : ℝ := min rho0 (1 / 16) with hrhodef
  have hrhopos : 0 < rho := lt_min hrho0 (by norm_num)
  have hrhole : rho ≤ rho0 := min_le_left _ _
  intro L delta
  obtain ⟨m₀, Cst0, hCst0⟩ := hdecay L delta
  have hBex : ∀ xi : ℝ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta = delta →
        2 ≤ xi → ∀ R : TriadicCube d,
          lpMoment M.P.toMeasure xi
            (fun omega => finiteProbeSum M L (ahom M L) R omega) ≤ B := by
    intro xi
    by_cases hxi : 2 ≤ xi
    · obtain ⟨B, hB0, hB⟩ := exists_law_uniform_finite_probe_moment (d := d) L delta
        (le_trans (by norm_num) hxi)
      exact ⟨B, hB0, fun M hdelta _ => hB M hdelta⟩
    · exact ⟨0, le_rfl, fun _ _ h => absurd h hxi⟩
  choose B hB0 hB using hBex
  refine ⟨fun xi => max (Cst0 xi) (B xi * Real.rpow (3 : ℝ) (rho * (m₀ : ℝ))), ?_, ?_⟩
  · intro xi
    refine le_trans ?_ (le_max_right (Cst0 xi) _)
    have : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (rho * (m₀ : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg (hB0 xi) this
  · intro M hdelta xi hxi R
    rw [lpMoment_finiteProbeSum_eq_originCube M L (ahom M L) R xi]
    have hpow : (0 : ℝ) < Real.rpow (3 : ℝ) (-rho * ((R.scale : ℤ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rcases le_or_gt ((m₀ : ℤ)) R.scale with hcase | hcase
    · -- large positive scale: use the decay
      have hnn : (0 : ℤ) ≤ R.scale := le_trans (Int.natCast_nonneg m₀) hcase
      set m : ℕ := R.scale.toNat with hm
      have hmz : ((m : ℕ) : ℤ) = R.scale := Int.toNat_of_nonneg hnn
      have hm0 : m₀ ≤ m := by omega
      have hbound := hCst0 M hdelta xi hxi m hm0
      have hcubeeq : originCube d ((m : ℕ) : ℤ) = originCube d R.scale := by
        rw [hmz]
      rw [hcubeeq] at hbound
      have hCst0nonneg : 0 ≤ Cst0 xi := by
        by_contra hneg
        push_neg at hneg
        have hp : (0 : ℝ) < Real.rpow (3 : ℝ) (-rho0 * (m : ℝ)) :=
          Real.rpow_pos_of_pos (by norm_num) _
        have : Cst0 xi * Real.rpow (3 : ℝ) (-rho0 * (m : ℝ)) < 0 :=
          mul_neg_of_neg_of_pos hneg hp
        have hge := lpMoment_nonneg M.P.toMeasure xi
          (fun omega => finiteProbeSum M L (ahom M L) (originCube d R.scale) omega)
        linarith
      have hexp : Real.rpow (3 : ℝ) (-rho0 * (m : ℝ)) ≤
          Real.rpow (3 : ℝ) (-rho * ((R.scale : ℤ) : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hmr : ((R.scale : ℤ) : ℝ) = (m : ℝ) := by
          rw [← hmz]; push_cast; ring
        rw [hmr]
        nlinarith [Nat.cast_nonneg (α := ℝ) m, hrhole]
      refine le_trans hbound ?_
      refine le_trans (mul_le_mul_of_nonneg_left hexp hCst0nonneg) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
    · -- small or negative scale: use the uniform bound
      have hstep := hB xi M hdelta hxi (originCube d R.scale)
      refine le_trans hstep ?_
      have hone : (1 : ℝ) ≤ Real.rpow (3 : ℝ)
          (rho * (m₀ : ℝ) + -rho * ((R.scale : ℤ) : ℝ)) := by
        have hlt : ((R.scale : ℤ) : ℝ) ≤ (m₀ : ℝ) := by
          have : R.scale ≤ (m₀ : ℤ) := le_of_lt hcase
          exact_mod_cast this
        have hnonneg : (0 : ℝ) ≤ rho * (m₀ : ℝ) + -rho * ((R.scale : ℤ) : ℝ) := by
          nlinarith [hrhopos]
        have := Real.rpow_le_rpow_of_exponent_le
          (x := (3 : ℝ)) (by norm_num) hnonneg
        simpa using this
      have hsplit : Real.rpow (3 : ℝ) (rho * (m₀ : ℝ)) *
          Real.rpow (3 : ℝ) (-rho * ((R.scale : ℤ) : ℝ)) =
          Real.rpow (3 : ℝ) (rho * (m₀ : ℝ) + -rho * ((R.scale : ℤ) : ℝ)) :=
        (Real.rpow_add (by norm_num) _ _).symm
      have hchain : B xi ≤ (B xi * Real.rpow (3 : ℝ) (rho * (m₀ : ℝ))) *
          Real.rpow (3 : ℝ) (-rho * ((R.scale : ℤ) : ℝ)) := by
        rw [mul_assoc, hsplit]
        nlinarith [hB0 xi, hone]
      refine le_trans hchain ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpow.le


end SubdiffusiveProcess.Section6
