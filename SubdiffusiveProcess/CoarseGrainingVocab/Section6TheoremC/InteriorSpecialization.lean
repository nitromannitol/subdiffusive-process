import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.HolderHalfAssembly
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CubeGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.ZeroDatum
import SubdiffusiveProcess.Frozen.Section6.Defs.InteriorHolderRegularityConclusions




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **S3.**  The interior conclusion package yields Theorem C's two displays,
with no boundary-datum regularity anywhere. -/
theorem theoremCDisplays_of_interiorConclusions
    {M : GMCModel d} {C : ℝ} {L m X : ℕ} {gamma : ℝ}
    {ω : AnchoredC11Sample d}
    {u : H1Function (openCubeSet (originCube d m))}
    (hconc : InteriorHolderRegularityConclusions M C L ω.1 gamma m X u
      (fun _ ↦ (0 : Vec d))) :
    TheoremCDisplays M C (L : WithTop ℕ) gamma m X ω u := by
  intro n hn z hgrid hsub
  have hzm : z ∈ cube d (m : ℤ) := mem_cube_of_translatedCube_subset_pred hsub
  have hzpred : z ∈ cube d ((m : ℤ) - 1) :=
    mem_cube_pred_of_translatedCube_subset hsub
  have hwin : truncatedCube d (m : ℤ) (n : ℤ) z = translatedCube d (n : ℤ) z :=
    truncatedCube_eq_translatedCube_of_subset_pred hsub
  have hmem : z ∈ truncatedCube d (m : ℤ) (n : ℤ) z :=
    Section6ExcessDecay.mem_truncatedCube_self (n : ℤ) hzm
  refine ⟨?_, ?_⟩
  · have hmain := hconc.1 n hn z hzpred n le_rfl z hgrid hmem
    rw [show gamma * ((n : ℝ) - (n : ℝ)) = 0 by ring, Real.rpow_zero,
      one_mul, hwin] at hmain
    rw [holderSeminormOn_zero, mul_zero, add_zero] at hmain
    exact hmain
  · rw [coefficientAt_natCast]
    have hmain := hconc.2.1 n hn z hzpred
    rw [hwin] at hmain
    rw [holderSeminormOn_zero, mul_zero, add_zero] at hmain
    exact hmain

/-- The datum side: a weakly harmonic function meets both hypotheses of the
interior anchor, with the zero divergence datum. -/
theorem interior_hypotheses_of_isWeaklyHarmonicOn
    {a : Vec d → ℝ} {m : ℕ} {u : H1Function (openCubeSet (originCube d m))}
    (hu : IsWeaklyHarmonicOn a (cube d m) u) :
    IsDivFormWeakSolutionOn a (cube d m) u (fun _ ↦ (0 : Vec d)) ∧
      MemHolder (cube d m) (1 / 2) (fun _ ↦ (0 : Vec d)) :=
  ⟨(isDivFormWeakSolutionOn_zero_iff a _ u).2 hu, memHolder_zero _ _⟩

/-- **The finite-cutoff inner conclusion, from the interior anchor's base
clause.**  Hypothesis-shaped on the byte-exact conclusion of
`p.cutoff.Holder.regularity.interior` (DRAFT); everything else is discharged. -/
theorem theoremCInner_of_interiorAnchor
    {M : GMCModel d} {C : ℝ} {L m : ℕ} {gamma : ℝ}
    {X : PotentialSample d → ℕ}
    (hanchor : ∀ ω : PotentialSample d,
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn (aCutoff M L ω) (cube d m) u g →
        MemHolder (cube d m) (1 / 2) g →
        InteriorHolderRegularityConclusions M C L ω gamma m (X ω) u g)
    (ω : AnchoredC11Sample d) :
    TheoremCInner M C (L : WithTop ℕ) gamma m
      (Section6TheoremC.liftToAnchored X) ω := by
  intro u hu
  have hcoef : IsWeaklyHarmonicOn (aCutoff M L ω.1) (cube d m) u := by
    rwa [coefficientAt_natCast] at hu
  obtain ⟨hdiv, hg⟩ := interior_hypotheses_of_isWeaklyHarmonicOn hcoef
  exact theoremCDisplays_of_interiorConclusions
    (hanchor ω.1 u (fun _ ↦ (0 : Vec d)) hdiv hg)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
