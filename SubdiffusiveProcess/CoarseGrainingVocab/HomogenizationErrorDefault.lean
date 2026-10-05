module

public import SubdiffusiveProcess.Frozen.Vocab.PaperHomogenizationError

@[expose] public section

open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization.Book

/-- The paper's omitted-`q` convention is `q = 1`. -/
noncomputable abbrev paperHomogenizationErrorDefault {d : ℕ}
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (p : Ch02.MultiscaleExponent)
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) : ℝ≥0∞ :=
  paperHomogenizationError Q n s p (.finite 1) a alpha

/-- The paper homogenization error is certificate-independent. -/
theorem paperHomogenizationError_toTriadicCoeffFamily_eq {d : ℕ}
    {a : Vec d → ℝ} (h₁ h₂ : ScalarTriadicCoeffData a)
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (p q : Ch02.MultiscaleExponent)
    (alpha : ℝ) :
    paperHomogenizationError Q n s p q h₁.toTriadicCoeffFamily alpha =
      paperHomogenizationError Q n s p q h₂.toTriadicCoeffFamily alpha := by
  have hprobe : ∀ (R : TriadicCube d) (e : Vec d),
      paperScalarProbe R h₁.toTriadicCoeffFamily alpha e =
        paperScalarProbe R h₂.toTriadicCoeffFamily alpha e := by
    intro R e
    exact Ch02.responseJ_eq_ofAEEq
      ((h₁.onCube R).toCoeffOn_aeEq (h₂.onCube R)) _ _
  unfold paperHomogenizationError paperHomogenizationErrorFinite
    paperHomogenizationErrorInfinity paperScaleResponseAtScale
    paperMaxDescendantProbeAtScale paperScalarProbeMax
  split <;> simp_rw [hprobe]

end SubdiffusiveProcess.CoarseGrainingVocab
