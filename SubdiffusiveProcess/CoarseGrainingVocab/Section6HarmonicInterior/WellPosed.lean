import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness




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
