module

public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness

@[expose] public section

/-!
# Clauses (A) and (B) of the interior harmonic anchor

`SubdiffusiveProcess.Section6.harmonic_approximation_good_scales_interior` has three clauses:

* (A) existence of the constant-coefficient harmonic replacement on the
  replacement cube `y + 𝔠_{n-2}`;
* (B) almost-everywhere uniqueness of that replacement, in value and in weak
  gradient;
* (C) the harmonic-approximation comparison estimate itself.

(A) and (B) mention neither the coefficient, nor the datum, nor the good event:
they depend only on `uD`.  They are therefore **unconditional**, and this file
discharges them from the committed Dirichlet theory
(`SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness`).

This is the same pair of clauses that
`SubdiffusiveProcess.Providers.Section6.harmonicApproximationGoodScales_wellPosed` discharges
for the interior harmonic estimates. The proof is repeated under a distinct name.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}



theorem interiorHarmonic_wellPosed (d : ℕ) [NeZero d] (n : ℕ) (y : Vec d)
    (uD : H1Function (translatedCube d ((n : ℤ) - 2) y)) :
    (∃ v : H1Function (translatedCube d ((n : ℤ) - 2) y),
      IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d ((n : ℤ) - 2) y) v ∧
        HasZeroTraceDifferenceOn (translatedCube d ((n : ℤ) - 2) y) v uD) ∧
    (∀ v v' : H1Function (translatedCube d ((n : ℤ) - 2) y),
      (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d ((n : ℤ) - 2) y) v ∧
          HasZeroTraceDifferenceOn (translatedCube d ((n : ℤ) - 2) y) v uD) →
      (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d ((n : ℤ) - 2) y) v' ∧
          HasZeroTraceDifferenceOn (translatedCube d ((n : ℤ) - 2) y) v' uD) →
      v.toFun =ᵐ[volume.restrict (translatedCube d ((n : ℤ) - 2) y)] v'.toFun ∧
        v.grad =ᵐ[volume.restrict (translatedCube d ((n : ℤ) - 2) y)] v'.grad) := by
  refine ⟨exists_isWeaklyHarmonicOn_one_translatedCube ((n : ℤ) - 2) y uD, ?_⟩
  intro v v' hv hv'
  exact ae_eq_of_isWeaklyHarmonicOn_one_translatedCube ((n : ℤ) - 2) y
    hv.1 hv.2 hv'.1 hv'.2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
