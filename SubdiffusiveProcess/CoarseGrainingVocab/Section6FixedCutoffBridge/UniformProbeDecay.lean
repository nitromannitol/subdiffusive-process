module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.QuenchedProbeStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.ProbeMomentNonpos

@[expose] public section

/-!
# A dimension-only decay rate for the quenched probe moments

`QuenchedProbeStep.lean` produces, for each model `M` and cutoff level `L`, an
exponent `rho > 0` with

    `‖finiteProbeSum M L (ahom M L) (originCube d m)‖_{L^xi} ≤ Cst xi * 3^{-rho m}`.

The supply interface `FixedCutoffResponseSupply d` quantifies its exponent
`theta` **before** `M` and `L`, so the rate has to be dimension-only.  It is:
`rho = min (alpha / 2) (d / 4)` where `alpha` comes from
`Ch05.Section51.annealedConvergence_homogenizationScale`, whose constants are
"selected from the quantitative ellipticity parameter record before the
probability law".  For the GMC cutoff that record is
`aCutoffP4Params d hd` — **dimension-only**.  This file hoists the two
quantifiers accordingly, and combines the resulting decay with the all-cube
uniform bound of `ProbeMomentNonpos.lean` into a single bound valid at every
integer scale.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- **The annealed contrast decay at a dimension-only rate.**  Same statement as
`exists_annealed_contrast_decay_normalizedCutoffLaw`, with `C` and `alpha`
quantified before the model and the cutoff level. -/
theorem exists_uniform_annealed_contrast_decay (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C alpha : ℝ, 0 < C ∧ 0 < alpha ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (n : ℕ),
        Ch05.thetaAtScale (normalizedCutoffLaw_lawCarrier M L)
            (normalizedCutoffLaw_structuralLaw M L)
            ((Ch05.annealedAlgebraicEntryScale (normalizedCutoffLaw M L)
                (normalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L) C
              + n : ℕ) : ℤ) ≤
          1 + Real.rpow (3 : ℝ) (-alpha * (n : ℝ)) := by
  obtain ⟨C, alpha, hC, halpha, hmain⟩ :=
    Ch05.Section51.annealedConvergence_homogenizationScale
      (d := d) (aCutoffP4Params d hd)
  refine ⟨C, alpha, hC, halpha, ?_⟩
  intro M L
  exact hmain (normalizedCutoffLaw_lawCarrier M L)
    (normalizedCutoffLaw_structuralLaw M L)
    (normalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L) rfl

/-- **The annealed probe-sum decay at a dimension-only rate.** -/
theorem exists_uniform_annealed_finiteProbeSum_decay (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ), ∃ k₀ : ℕ,
        ∀ n : ℕ,
          (∫ omega, finiteProbeSum M L (ahom M L)
              (originCube d ((k₀ + n : ℕ) : ℤ)) omega ∂M.P.toMeasure) ≤
            3 * (d : ℝ) ^ 2 * Real.rpow (3 : ℝ) (-alpha * (n : ℝ)) := by
  obtain ⟨C, alpha, _hC, halpha, hdecay⟩ :=
    exists_uniform_annealed_contrast_decay d hd
  refine ⟨alpha, halpha, ?_⟩
  intro M L
  set e : ℕ := Ch05.annealedAlgebraicEntryScale (normalizedCutoffLaw M L)
    (normalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L) C with he
  refine ⟨aCutoffNormalizationDepth d L + e, ?_⟩
  intro n
  have hindex := thetaAtScale_normalizedCutoffLaw_eq_annealedContrast M L (e + n)
  have hdec := hdecay M L n
  rw [hindex] at hdec
  have hassoc : aCutoffNormalizationDepth d L + (e + n) =
      aCutoffNormalizationDepth d L + e + n := by omega
  rw [hassoc] at hdec
  have hcontrast :
      abarScalarReadout M L (aCutoffNormalizationDepth d L + e + n) *
          oneStepAnnealedDualReadout M L
            (aCutoffNormalizationDepth d L + e + n) - 1 ≤
        Real.rpow (3 : ℝ) (-alpha * (n : ℝ)) := by linarith
  have hbase :=
    integral_finiteProbeSum_le M L (aCutoffNormalizationDepth d L + e + n)
  refine hbase.trans ?_
  refine mul_le_mul_of_nonneg_left hcontrast ?_
  positivity

/-- **The quenched `L^xi` decay at a dimension-only rate.**

Identical to `exists_lpMoment_finiteProbeSum_decay` except that the exponent
`rho` is produced before the model and the cutoff level. -/
theorem exists_uniform_lpMoment_finiteProbeSum_decay (d : ℕ) [NeZero d]
    (hd : 2 ≤ d) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ),
        ∃ (m₀ : ℕ) (Cst : ℝ → ℝ),
          ∀ xi : ℝ, 2 ≤ xi → ∀ m : ℕ, m₀ ≤ m →
            lpMoment M.P.toMeasure xi
                (fun omega =>
                  finiteProbeSum M L (ahom M L) (originCube d (m : ℤ)) omega) ≤
              Cst xi * Real.rpow (3 : ℝ) (-rho * (m : ℝ)) := by
  classical
  obtain ⟨alpha, halpha0, hannUniform⟩ :=
    exists_uniform_annealed_finiteProbeSum_decay d hd
  obtain ⟨C, hC, hstep⟩ := lpMoment_finiteProbeSum_le d
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : d ≠ 0 := NeZero.ne d
    positivity
  refine ⟨min (alpha / 2) ((d : ℝ) / 4), lt_min (by positivity) (by positivity), ?_⟩
  intro M L
  have halpha : 0 < ahom M L :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M L)
  obtain ⟨k₀, hann⟩ := hannUniform M L
  refine ⟨2 * (max L k₀ + 1),
    fun xi => 3 * (d : ℝ) ^ 2 *
        Real.rpow (3 : ℝ) (alpha * ((1 : ℝ) / 2 + (k₀ : ℝ))) +
      C * xi * probeSumUnitConst M L (ahom M L) xi, ?_⟩
  intro xi hxi m hm
  set n : ℕ := m / 2 with hn
  have hNn : max L k₀ ≤ n := by omega
  have hLn : L ≤ n := le_trans (le_max_left _ _) hNn
  have hk₀n : k₀ ≤ n := le_trans (le_max_right _ _) hNn
  have hnm : n ≤ m := by omega
  have hmain := hstep M L n m hLn hnm halpha xi hxi
  have hcube : originCube d ((k₀ + (n - k₀) : ℕ) : ℤ) = originCube d (n : ℤ) := by
    congr 2
    omega
  have hannbound : (∫ eta, finiteProbeSum M L (ahom M L)
      (originCube d (n : ℤ)) eta ∂M.P.toMeasure) ≤
      3 * (d : ℝ) ^ 2 * Real.rpow (3 : ℝ) (-alpha * ((n - k₀ : ℕ) : ℝ)) := by
    have := hann (n - k₀)
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
  have hB : (0 : ℝ) ≤ C * xi * probeSumUnitConst M L (ahom M L) xi := by
    have hxi0 : (0 : ℝ) ≤ xi := by linarith
    have := probeSumUnitConst_nonneg M L (ahom M L) xi
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
  have hchain2 : C * xi * probeSumUnitConst M L (ahom M L) xi *
      Real.rpow (3 : ℝ) (-((d : ℝ) / 2) * ((m - n : ℕ) : ℝ)) ≤
      C * xi * probeSumUnitConst M L (ahom M L) xi *
        Real.rpow (3 : ℝ) (-rho * (m : ℝ)) :=
    mul_le_mul_of_nonneg_left (hterm2.trans hrho2) hB
  have hfinal := hmain.trans (add_le_add hchain1 hchain2)
  refine hfinal.trans (le_of_eq ?_)
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
