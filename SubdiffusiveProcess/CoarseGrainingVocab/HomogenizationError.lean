import SubdiffusiveProcess.Frozen.Vocab.PaperScalarProbeMax

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section

/-- Maximum paper probe over descendants at one scale. -/
noncomputable def paperMaxDescendantProbeAtScale {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) : ℝ≥0∞ :=
  ⨆ R : {R : TriadicCube d // R ∈ Homogenization.descendantsAtScale Q k},
    paperScalarProbeMax R a alpha

/-- The paper's `p` aggregation at one scale. -/
noncomputable def paperScaleResponseAtScale {d : ℕ} (Q : TriadicCube d)
    (k : ℤ) (p : Ch02.MultiscaleExponent) (a : Ch02.TriadicCoeffFamily d)
    (alpha : ℝ) : ℝ≥0∞ :=
  match p with
  | .finite p =>
      (((Homogenization.descendantsAtScale Q k).card : ℝ≥0∞)⁻¹ *
          ∑ R ∈ Homogenization.descendantsAtScale Q k,
            (paperScalarProbeMax R a alpha) ^ (p / 2)) ^ (1 / p)
  | .infinity => (paperMaxDescendantProbeAtScale Q k a alpha) ^ (1 / 2 : ℝ)

/-- Finite-`q` paper homogenization error. -/
noncomputable def paperHomogenizationErrorFinite {d : ℕ} (Q : TriadicCube d)
    (n : ℤ) (s : ℝ) (p : Ch02.MultiscaleExponent) (q : ℝ)
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) : ℝ≥0∞ :=
  (∑' l : ℕ,
    ENNReal.ofReal (Ch02.geometricWeight s q l) *
      (paperScaleResponseAtScale Q (n - (l : ℤ)) p a alpha) ^ q) ^ (1 / q)

/-- Endpoint-`q` paper homogenization error. -/
noncomputable def paperHomogenizationErrorInfinity {d : ℕ} (Q : TriadicCube d)
    (n : ℤ) (s : ℝ) (p : Ch02.MultiscaleExponent)
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) : ℝ≥0∞ :=
  ⨆ l : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ) (-s * (l : ℝ))) *
    paperScaleResponseAtScale Q (n - (l : ℤ)) p a alpha

end

end SubdiffusiveProcess.CoarseGrainingVocab
