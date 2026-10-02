import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.FiniteCutoffSpecialization
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.PositiveRescaling




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}



theorem finite_cutoff_holder_displays
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {C : ℝ} {L m X : ℕ} {gamma : ℝ}
    {ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d}
    {u : H1Function (openCubeSet (originCube d m))}
    (hconc : HolderRegularityConclusions M C L ω.1 gamma m X u u
      (fun _ ↦ (0 : Vec d))) :
    ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X : ℤ) →
      ∀ z : Vec d, OnTriadicGrid n z →
        translatedCube d n z ⊆ cube d ((m : ℤ) - 1) →
          normalizedL2On (translatedCube d (n : ℤ) z)
              (fun x ↦ u.toFun x -
                averageOn (translatedCube d (n : ℤ) z) u.toFun) ≤
            C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) *
              normalizedL2On (cube d m)
                (fun x ↦ u.toFun x - averageOn (cube d m) u.toFun) ∧
          vectorNormalizedL2On (translatedCube d (n : ℤ) z)
              (fun x ↦ Real.sqrt (coefficientAt M (L : WithTop ℕ) ω x) •
                u.grad x) ≤
            C * (3 : ℝ) ^ ((1 - gamma) * ((m : ℝ) - (n : ℝ))) *
              vectorNormalizedL2On (cube d m)
                (fun x ↦ Real.sqrt (coefficientAt M (L : WithTop ℕ) ω x) •
                  u.grad x) := by
  intro n hn z hgrid hsub
  refine ⟨normalizedL2On_translatedCube_le_of_holderRegularityConclusions
      hconc hn hgrid hsub, ?_⟩
  -- At a finite cutoff the frozen coefficient is the conclusion package's.
  rw [coefficientAt_natCast]
  exact vectorNormalizedL2On_translatedCube_le_of_holderRegularityConclusions
    hconc hn hsub



theorem finite_cutoff_holder_displays_of_conclusions
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {C : ℝ} {L m X : ℕ} {gamma : ℝ}
    {ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d}
    (hconc : ∀ u : H1Function (openCubeSet (originCube d m)),
      IsWeaklyHarmonicOn (coefficientAt M (L : WithTop ℕ) ω) (cube d m) u →
      HolderRegularityConclusions M C L ω.1 gamma m X u u
        (fun _ ↦ (0 : Vec d))) :
    ∀ u : H1Function (openCubeSet (originCube d m)),
      IsWeaklyHarmonicOn (coefficientAt M (L : WithTop ℕ) ω) (cube d m) u →
      ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X : ℤ) →
        ∀ z : Vec d, OnTriadicGrid n z →
          translatedCube d n z ⊆ cube d ((m : ℤ) - 1) →
            normalizedL2On (translatedCube d (n : ℤ) z)
                (fun x ↦ u.toFun x -
                  averageOn (translatedCube d (n : ℤ) z) u.toFun) ≤
              C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) *
                normalizedL2On (cube d m)
                  (fun x ↦ u.toFun x - averageOn (cube d m) u.toFun) ∧
            vectorNormalizedL2On (translatedCube d (n : ℤ) z)
                (fun x ↦ Real.sqrt (coefficientAt M (L : WithTop ℕ) ω x) •
                  u.grad x) ≤
              C * (3 : ℝ) ^ ((1 - gamma) * ((m : ℝ) - (n : ℝ))) *
                vectorNormalizedL2On (cube d m)
                  (fun x ↦ Real.sqrt (coefficientAt M (L : WithTop ℕ) ω x) •
                    u.grad x) :=
  fun u hu ↦ finite_cutoff_holder_displays (hconc u hu)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
