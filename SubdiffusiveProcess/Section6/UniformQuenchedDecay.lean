module

public import SubdiffusiveProcess.Section6.UniformEntryScale
public import SubdiffusiveProcess.Section6.UniformProbeMoments

@[expose] public section

/-! Quenched probe decay with a common entry scale and moment constants. -/
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab hiding TriadicCube Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

noncomputable section
namespace SubdiffusiveProcess.Section6

theorem exists_law_uniform_lpMoment_probe_decay (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ L : ℕ, ∀ delta : ℝ, ∃ (m₀ : ℕ) (Cst : ℝ → ℝ),
          ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta = delta → ∀ xi : ℝ, 2 ≤ xi → ∀ m : ℕ, m₀ ≤ m →
            lpMoment M.P.toMeasure xi
                (fun omega =>
                  finiteProbeSum M L (ahom M L) (originCube d (m : ℤ)) omega) ≤
              Cst xi * Real.rpow (3 : ℝ) (-rho * (m : ℝ)) := by
  classical
  obtain ⟨alpha, halpha0, hannUniform⟩ :=
    exists_law_uniform_annealed_probe_decay d hd
  obtain ⟨C, hC, hstep⟩ := lpMoment_finiteProbeSum_le d
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : d ≠ 0 := NeZero.ne d
    positivity
  refine ⟨min (alpha / 2) ((d : ℝ) / 4), lt_min (by positivity) (by positivity), ?_⟩
  intro L delta
  obtain ⟨k₀, hann⟩ := hannUniform L delta
  have hunitex : ∀ xi : ℝ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta = delta →
        2 ≤ xi → probeSumUnitConst M L (ahom M L) xi ≤ B := by
    intro xi
    by_cases hxi : 2 ≤ xi
    · obtain ⟨B, hB0, hB⟩ := exists_law_uniform_probe_unit_constant (d := d) L delta
        (le_trans (by norm_num) hxi)
      exact ⟨B, hB0, fun M hdelta _ => hB M hdelta⟩
    · exact ⟨0, le_rfl, fun _ _ h => absurd h hxi⟩
  choose B hB0 hB using hunitex
  refine ⟨2 * (max L k₀ + 1),
    fun xi => 3 * (d : ℝ) ^ 2 *
        Real.rpow (3 : ℝ) (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ))) +
      C * xi * B xi, ?_⟩
  intro M hdelta xi hxi m hm
  have halpha := ahom_pos M L
  set n : ℕ := m / 2 with hn
  have hNn : max L k₀ ≤ n := by omega
  have hLn : L ≤ n := le_trans (le_max_left _ _) hNn
  have hk₀n : k₀ ≤ n := le_trans (le_max_right _ _) hNn
  have hnm : n ≤ m := by omega
  have hmain0 := hstep M L n m hLn hnm halpha xi hxi
  have hmain := hmain0.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hB xi M hdelta hxi)
      (mul_nonneg hC.le (by linarith : 0 ≤ xi)))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)))
  have hcube : originCube d ((k₀ + (n - k₀) : ℕ) : ℤ) = originCube d (n : ℤ) := by
    congr 2
    omega
  have hannbound : (∫ eta, finiteProbeSum M L (ahom M L)
      (originCube d (n : ℤ)) eta ∂M.P.toMeasure) ≤
      3 * (d : ℝ) ^ 2 * Real.rpow (3 : ℝ) (-alpha * ((n - k₀ : ℕ) : ℝ)) := by
    have := hann M hdelta (n - k₀)
    rwa [hcube] at this
  have h3 : (1 : ℝ) ≤ 3 := by norm_num
  have hnreal : (m : ℝ) / 2 - 1 / 2 ≤ (n : ℝ) := by
    have h2 : 2 * n + 1 ≥ m := by omega
    have hcast : (2 : ℝ) * (n : ℝ) + 1 ≥ (m : ℝ) := by exact_mod_cast h2
    linarith
  have hsub : ((n - k₀ : ℕ) : ℝ) = (n : ℝ) - (k₀ : ℝ) := by
    push_cast [Nat.cast_sub hk₀n]
    ring
  have hexp1 : -alpha * ((n - k₀ : ℕ) : ℝ) ≤
      alpha * ((1 : ℝ) / 2 + (k₀ : ℝ)) + (-(alpha / 2) * (m : ℝ)) := by
    rw [hsub]
    nlinarith [hnreal, halpha0]
  have hterm1 : Real.rpow (3 : ℝ) (-alpha * ((n - k₀ : ℕ) : ℝ)) ≤
      Real.rpow (3 : ℝ) (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ))) *
        Real.rpow (3 : ℝ) (-(alpha / 2) * (m : ℝ)) := by
    have heq : Real.rpow (3 : ℝ) (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ))) *
        Real.rpow (3 : ℝ) (-(alpha / 2) * (m : ℝ)) =
        Real.rpow (3 : ℝ)
          (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ)) + (-(alpha / 2) * (m : ℝ))) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le h3 hexp1
  have hmn : ((m - n : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    push_cast [Nat.cast_sub hnm]
    ring
  have hnhalf : (n : ℝ) ≤ (m : ℝ) / 2 := by
    have h2 : 2 * n ≤ m := by omega
    have : (2 : ℝ) * (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2
    linarith
  have hexp2 : -((d : ℝ) / 2) * ((m - n : ℕ) : ℝ) ≤
      -((d : ℝ) / 4) * (m : ℝ) := by
    rw [hmn]
    nlinarith [hnhalf, hdpos]
  have hterm2 : Real.rpow (3 : ℝ) (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) ≤
      Real.rpow (3 : ℝ) (-((d : ℝ) / 4) * (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le h3 hexp2
  set rho : ℝ := min (alpha / 2) ((d : ℝ) / 4) with hrho
  have hrho1 : Real.rpow (3 : ℝ) (-(alpha / 2) * (m : ℝ)) ≤
      Real.rpow (3 : ℝ) (-rho * (m : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le h3 ?_
    have : rho ≤ alpha / 2 := min_le_left _ _
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hrho2 : Real.rpow (3 : ℝ) (-((d : ℝ) / 4) * (m : ℝ)) ≤
      Real.rpow (3 : ℝ) (-rho * (m : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le h3 ?_
    have : rho ≤ (d : ℝ) / 4 := min_le_right _ _
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hA : (0 : ℝ) ≤ 3 * (d : ℝ) ^ 2 := by positivity
  have hB : (0 : ℝ) ≤ C * xi * B xi := by
    have hxi0 : (0 : ℝ) ≤ xi := by linarith
    have := hB0 xi
    positivity
  have hchain1 : (∫ eta, finiteProbeSum M L (ahom M L)
      (originCube d (n : ℤ)) eta ∂M.P.toMeasure) ≤
      3 * (d : ℝ) ^ 2 * Real.rpow (3 : ℝ) (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ))) *
        Real.rpow (3 : ℝ) (-rho * (m : ℝ)) := by
    refine hannbound.trans ?_
    have := (hterm1.trans (mul_le_mul_of_nonneg_left hrho1
      (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _)))
    calc 3 * (d : ℝ) ^ 2 * Real.rpow (3 : ℝ) (-alpha * ((n - k₀ : ℕ) : ℝ))
        ≤ 3 * (d : ℝ) ^ 2 *
            (Real.rpow (3 : ℝ) (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ))) *
              Real.rpow (3 : ℝ) (-rho * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left this hA
      _ = _ := by ring
  have hchain2 : C * xi * B xi *
      Real.rpow (3 : ℝ) (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) ≤
      C * xi * B xi *
        Real.rpow (3 : ℝ) (-rho * (m : ℝ)) :=
    mul_le_mul_of_nonneg_left (hterm2.trans hrho2) hB
  have hfinal := hmain.trans (add_le_add hchain1 hchain2)
  refine hfinal.trans (le_of_eq ?_)
  ring


end SubdiffusiveProcess.Section6
