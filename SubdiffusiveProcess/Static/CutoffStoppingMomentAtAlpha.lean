module

public import SubdiffusiveProcess.Frozen.Section6.CutoffHolderRegularity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceScale
public import SubdiffusiveProcess.Analysis.GeometricTailMomentBound

@[expose] public section

/-! # Uniform moments of the finite-cutoff Hölder stopping scale

The exponent is selectable below one, so a strictly stronger macroscopic
energy exponent leaves a margin for microscopic coefficient extremes.
The deterministic threshold is chosen before the cutoff, domain scale,
and arbitrary real translation. The geometric moment is bounded uniformly
as disorder decreases to zero.
-/

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

private theorem stoppingTail_constant_mono {c C A D E k : ℝ}
    (hc : 0 < c) (hcC : c ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    c * Real.exp (-(A * max (k - c) 0) / (c * D * E)) ≤
      C * Real.exp (-(A * max (k - C) 0 / (C * D * E))) := by
  have hC : 0 < C := hc.trans_le hcC
  refine mul_le_mul hcC (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hC.le
  rw [neg_div]
  refine neg_le_neg ?_
  have hB : 0 ≤ D * E := mul_nonneg hD hE
  rw [mul_assoc, mul_assoc]
  rcases hB.lt_or_eq with hB | hB
  · have hm : max (k - C) 0 ≤ max (k - c) 0 := max_le_max (by linarith) le_rfl
    exact div_le_div₀ (mul_nonneg hA (le_max_right _ _))
      (mul_le_mul_of_nonneg_left hm hA) (mul_pos hc hB)
      (mul_le_mul_of_nonneg_right hcC hB.le)
  · rw [← hB, mul_zero, mul_zero, div_zero, div_zero]

/-- The existing Hölder supplier with its scale premises and stopping-scale
moment premises fully discharged. -/
theorem exists_uniform_cutoffStopping_moment_bound_at_alpha (d : ℕ) (alpha t q : ℝ)
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1) (ht : 0 ≤ t) (hq : 1 ≤ q) :
    ∃ δ0 C B : ℝ, 0 < δ0 ∧ 0 < C ∧ 0 ≤ B ∧
      ∀ M : GMCModel d, M.delta ≤ δ0 → ∀ L m : ℕ, ∀ z : Vec d,
        ∃ X : PotentialSample d → ℕ,
          Measurable X ∧ (∀ ω, 0 < X ω) ∧
          MemLp (fun ω => (3 : ℝ) ^ (t * (X ω : ℝ))) (ENNReal.ofReal q) M.P.toMeasure ∧
          eLpNorm (fun ω => (3 : ℝ) ^ (t * (X ω : ℝ)))
              (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal B ∧
          ∀ ω, ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
              (g : Vec d → Vec d),
            IsDirichletSolutionOn (aCutoff M L (translatePotentialSample z ω))
              (originCube d (m : ℤ)) u h g →
            MemHolder (cube d (m : ℤ)) (1 / 2) g →
            MemHolder (cube d (m : ℤ)) (1 / 2) h.grad →
            HolderRegularityConclusions M C L (translatePotentialSample z ω)
              alpha m (X ω) u h g := by
  obtain ⟨C, hC, hholder⟩ := SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity d
  let Ct : ℝ := 1 + C
  have hCt : 1 ≤ Ct := by dsimp only [Ct]; linarith
  obtain ⟨δt, B, hδt, hB, hmoment⟩ :=
    SubdiffusiveProcess.exists_uniform_prefixLen_pow_eLpNorm_bound
      Ct alpha t q hCt ht hq halpha.2
  have hgap : 0 < 1 - alpha := by linarith [halpha.2]
  let δ0 : ℝ := min δt (min C⁻¹ ((1 - alpha) ^ 2 / C ^ 2))
  have hδ0 : 0 < δ0 := by dsimp only [δ0]; positivity
  refine ⟨δ0, C, B, hδ0, hC, hB, ?_⟩
  intro M hM L m z
  have hδpos := M.shellPrefix.delta_pos
  have hMC : M.delta ≤ C⁻¹ :=
    hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMsq : M.delta ≤ ((1 - alpha) ^ 2 / C ^ 2) :=
    hM.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) ≤ 1 - alpha := by
    have hlog := Section5Support.delta_sq_mul_abs_log_le_self
      hδpos (M.shellPrefix.delta_le_half.trans (by norm_num))
    have hsqrt : (|Real.log M.delta| ^ (1 / 2 : ℝ)) ^ 2 = |Real.log M.delta| := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (abs_nonneg _)]
    have hbound : M.delta * C ^ 2 ≤ (1 - alpha) ^ 2 := by
      exact (le_div_iff₀ (sq_pos_of_pos hC)).mp hMsq
    have hscaled := mul_le_mul_of_nonneg_left hlog (sq_nonneg C)
    have hfactor : 0 ≤ C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) := by positivity
    apply (sq_le_sq₀ hfactor hgap.le).mp
    calc
      (C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)) ^ 2 =
          C ^ 2 * (M.delta ^ 2 * |Real.log M.delta|) := by
            rw [mul_pow, mul_pow, hsqrt]
            ring
      _ ≤ C ^ 2 * M.delta := hscaled
      _ ≤ (1 - alpha) ^ 2 := by nlinarith only [hbound]
  obtain ⟨X, hX, hXpos, htail, hgrowth⟩ :=
    ((hholder M hMC alpha ⟨halpha.1, by linarith⟩ L m).2.2 z).1
  have htail' : ∀ k : ℕ, M.P.toMeasure {ω | k < X ω} ≤
      ENNReal.ofReal (Ct * Real.exp (-((1 - alpha) ^ 2 *
        max ((k : ℝ) - Ct) 0 / (Ct * M.delta ^ 2 * |Real.log M.delta|)))) := by
    intro k
    cases k with
    | zero =>
        have heq : Ct * Real.exp (-((1 - alpha) ^ 2 *
            max ((0 : ℝ) - Ct) 0 / (Ct * M.delta ^ 2 * |Real.log M.delta|))) = Ct := by
          rw [max_eq_right (by linarith)]
          simp
        rw [Nat.cast_zero, heq]
        exact (measure_mono (Set.subset_univ _)).trans (by simpa using ENNReal.ofReal_le_ofReal hCt)
    | succ k =>
        refine (htail (k + 1) (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
        exact stoppingTail_constant_mono hC (by dsimp only [Ct]; linarith)
          (sq_nonneg _) (sq_nonneg _) (abs_nonneg _)
  obtain ⟨hmem, hnorm⟩ := hmoment M.P.toMeasure X hX M.delta M.shellPrefix.delta_pos
    (hM.trans (min_le_left _ _)) htail'
  exact ⟨X, hX, hXpos, hmem, hnorm, hgrowth⟩

end SubdiffusiveProcess.Static
