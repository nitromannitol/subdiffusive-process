module

public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffNormalization

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book

noncomputable section



noncomputable def normalizedCutoffLaw {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) : Ch04.RestrictionCoeffLaw d :=
  Ch04.restrictionScaleNormalizedLaw (aCutoffNormalizationDepth d L)
    (aCutoffRestrictionLaw M L)

/-- The Chapter 4 probability / local-ellipticity carrier of the normalized
cutoff law. -/
theorem normalizedCutoffLaw_lawCarrier {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    Ch04.RestrictionLawCarrier (normalizedCutoffLaw M L) :=
  (aCutoffRestrictionLaw_lawCarrier M L).scaleNormalized
    (aCutoffNormalizationDepth d L)

/-- The Chapter 4 structural package (stationary, unit range, isotropic,
adjoint invariant) of the normalized cutoff law. -/
theorem normalizedCutoffLaw_structuralLaw {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    Ch04.RestrictionStructuralLaw (normalizedCutoffLaw M L) :=
  aCutoffNormalization_structuralLaw M L

/-- The normalized cutoff law is a probability law. -/
theorem normalizedCutoffLaw_isProbabilityMeasure {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    IsProbabilityMeasure (normalizedCutoffLaw M L) :=
  (normalizedCutoffLaw_lawCarrier M L).isProbability

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
