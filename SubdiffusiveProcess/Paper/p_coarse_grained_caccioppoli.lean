module

public import SubdiffusiveProcess.Caccioppoli.SourceInterior
public import SubdiffusiveProcess.Frozen.Section2.CoarseGrainedCaccioppoli



@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The open range `1/4 < t < 1/2` of the coarse-grained Caccioppoli inequality. -/
theorem aux_p_coarse_grained_caccioppoli_gap {d : ℕ} :
    2 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ (s t : ℝ), 0 < s → s < 1 → (1 / 4 : ℝ) < t → t < (1 / 2 : ℝ) → s + t < 1 →
        ∀ (a : Ch02.TriadicCoeffFamily d),
          (∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) →
          ∀ u : Homogenization.H1Function
              (Homogenization.openCubeSet (Homogenization.originCube d 0)),
            ∀ f : PaperPositiveSobolevField
                (Homogenization.originCube d 0) (2 * t)
                Homogenization.FiniteLpExponent.two,
              Homogenization.Book.Ch03.ABK26.IsForcedEquation
                (Homogenization.originCube d 0)
                (a.coeffOn (Homogenization.originCube d 0)) u f.toField →
              coefficientEnergyNorm (Homogenization.originCube d (-1)) a u.grad ^ 2 ≤
                Real.rpow (C / (1 - s - t))
                    (2 + 4 * s / (1 - s - t)) *
                  Real.rpow
                    (LambdaDefault (Homogenization.originCube d 0) s a /
                      lambdaDefault (Homogenization.originCube d 0) t a)
                    (s / (1 - s - t)) *
                  LambdaDefault (Homogenization.originCube d 0) s a *
                  Homogenization.cubeLpNorm (Homogenization.originCube d 0)
                    (2 : ℝ≥0∞) u.toFun ^ 2 +
                t ^ (-11 : ℤ) *
                  Real.rpow (C / (1 - s - t))
                    (2 + 4 * s / (1 - s - t)) *
                  Real.rpow
                    (LambdaDefault (Homogenization.originCube d 0) s a /
                      lambdaDefault (Homogenization.originCube d 0) t a)
                    ((1 - t) / (1 - s - t)) *
                  (lambdaDefault (Homogenization.originCube d 0) t a)⁻¹ *
                  f.norm.toReal ^ 2 := by
  intro hd
  obtain ⟨C, hC, hfull⟩ :=
    SubdiffusiveProcess.Caccioppoli.source_interior_caccioppoli (d := d) hd
  refine ⟨C, hC, ?_⟩
  intro s t hs hs1 ht4 ht2 hst a hsymm u f hf
  exact hfull s t hs hs1 (by linarith only [ht4]) ht2 hst a hsymm u f hf

theorem p_coarse_grained_caccioppoli {d : ℕ} :
    2 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ (s t : ℝ), 0 < s → s < 1 → 0 < t → t < (1 / 2 : ℝ) → s + t < 1 →
        ∀ (a : Ch02.TriadicCoeffFamily d),
          (∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) →
          ∀ u : Homogenization.H1Function
              (Homogenization.openCubeSet (Homogenization.originCube d 0)),
            ∀ f : PaperPositiveSobolevField
                (Homogenization.originCube d 0) (2 * t)
                Homogenization.FiniteLpExponent.two,
              Homogenization.Book.Ch03.ABK26.IsForcedEquation
                (Homogenization.originCube d 0)
                (a.coeffOn (Homogenization.originCube d 0)) u f.toField →
              coefficientEnergyNorm (Homogenization.originCube d (-1)) a u.grad ^ 2 ≤
                Real.rpow (C / (1 - s - t))
                    (2 + 4 * s / (1 - s - t)) *
                  Real.rpow
                    (LambdaDefault (Homogenization.originCube d 0) s a /
                      lambdaDefault (Homogenization.originCube d 0) t a)
                    (s / (1 - s - t)) *
                  LambdaDefault (Homogenization.originCube d 0) s a *
                  Homogenization.cubeLpNorm (Homogenization.originCube d 0)
                    (2 : ℝ≥0∞) u.toFun ^ 2 +
                t ^ (-11 : ℤ) *
                  Real.rpow (C / (1 - s - t))
                    (2 + 4 * s / (1 - s - t)) *
                  Real.rpow
                    (LambdaDefault (Homogenization.originCube d 0) s a /
                      lambdaDefault (Homogenization.originCube d 0) t a)
                    ((1 - t) / (1 - s - t)) *
                  (lambdaDefault (Homogenization.originCube d 0) t a)⁻¹ *
                  f.norm.toReal ^ 2 := by
  intro hd
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C₀, hC₀, h₀⟩ := SubdiffusiveProcess.Frozen.Section2.coarse_grained_caccioppoli (d := d) hd
  obtain ⟨C₁, hC₁, h₁⟩ := aux_p_coarse_grained_caccioppoli_gap (d := d) hd
  refine ⟨max C₀ C₁, lt_max_of_lt_left hC₀, ?_⟩
  intro s t hs hs1 ht ht2 hst a hsymm u f hf
  have hσ : 0 < 1 - s - t := by linarith
  have hLam : 0 ≤ LambdaDefault (Homogenization.originCube d 0) s a :=
    Ch02.LambdaSq_nonneg _ a hs (by simp [Ch02.MultiscaleExponent.IsAdmissible])
  have hlam : 0 ≤ lambdaDefault (Homogenization.originCube d 0) t a :=
    Ch02.lambdaSq_nonneg _ a ht (by simp [Ch02.MultiscaleExponent.IsAdmissible])
  have hlinv : 0 ≤ (lambdaDefault (Homogenization.originCube d 0) t a)⁻¹ := inv_nonneg.mpr hlam
  have ht11 : 0 ≤ t ^ (-11 : ℤ) := by positivity
  set σ : ℝ := 1 - s - t with hσdef
  have hexp : 0 ≤ 2 + 4 * s / σ := by positivity
  by_cases h4 : t ≤ 1 / 4
  · refine (h₀ s t hs hs1 ht h4 hst a hsymm u f hf).trans ?_
    have hle : C₀ / σ ≤ max C₀ C₁ / σ :=
      div_le_div_of_nonneg_right (le_max_left _ _) hσ.le
    have hpow : Real.rpow (C₀ / σ) (2 + 4 * s / σ) ≤ Real.rpow (max C₀ C₁ / σ) (2 + 4 * s / σ) :=
      Real.rpow_le_rpow (by positivity) hle hexp
    have hR1 : 0 ≤ Real.rpow (LambdaDefault (Homogenization.originCube d 0) s a /
        lambdaDefault (Homogenization.originCube d 0) t a) (s / σ) := Real.rpow_nonneg (by positivity) _
    have hR2 : 0 ≤ Real.rpow (LambdaDefault (Homogenization.originCube d 0) s a /
        lambdaDefault (Homogenization.originCube d 0) t a) ((1 - t) / σ) := Real.rpow_nonneg (by positivity) _
    gcongr
  · have h4' : 1 / 4 < t := not_le.mp h4
    refine (h₁ s t hs hs1 h4' ht2 hst a hsymm u f hf).trans ?_
    have hle : C₁ / σ ≤ max C₀ C₁ / σ :=
      div_le_div_of_nonneg_right (le_max_right _ _) hσ.le
    have hpow : Real.rpow (C₁ / σ) (2 + 4 * s / σ) ≤ Real.rpow (max C₀ C₁ / σ) (2 + 4 * s / σ) :=
      Real.rpow_le_rpow (by positivity) hle hexp
    have hR1 : 0 ≤ Real.rpow (LambdaDefault (Homogenization.originCube d 0) s a /
        lambdaDefault (Homogenization.originCube d 0) t a) (s / σ) := Real.rpow_nonneg (by positivity) _
    have hR2 : 0 ≤ Real.rpow (LambdaDefault (Homogenization.originCube d 0) s a /
        lambdaDefault (Homogenization.originCube d 0) t a) ((1 - t) / σ) := Real.rpow_nonneg (by positivity) _
    gcongr

end SubdiffusiveProcess.Paper
