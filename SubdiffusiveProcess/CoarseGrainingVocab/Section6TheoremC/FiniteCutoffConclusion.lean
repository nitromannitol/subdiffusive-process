module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.FiniteCutoffSpecialization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.PositiveRescaling

@[expose] public section

/-!
# The finite-cutoff half of Theorem C, in provider shape

This assembles the part of Theorem C's `C^{0,γ}` clause that elaborates
from the stated regularity conclusions of `p.cutoff.Holder.regularity`.

`HolderRegularityConclusions` is a definition.  So the entire
interior harmonic specialization  -- the `ℓ = n`
gain-factor collapse, the `x = y = z` window collapse, and the vanishing of the
datum and boundary terms -- is a theorem about that definition, proved here.

`finite_cutoff_holder_displays` below is stated so that its conclusion is
*syntactically* the inner body of the statement
(`SubdiffusiveProcess/Section6/LargeScaleHolderMultifractal.lean`) at a finite cutoff
`L = (L : ℕ)`, with `coefficientAt M (L : WithTop ℕ) ω` as the coefficient and
`ω : AnchoredC11Sample d` as the sample.  The eventual provider therefore
applies it as a term rather than re-deriving anything.

This support theorem consumes the `HolderRegularityConclusions` instance supplied by `p.cutoff.Holder.regularity`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The finite-cutoff `C^{0,γ}` displays of Theorem C.**

Given the conclusion package of `p.cutoff.Holder.regularity` at the zero
divergence datum and at the boundary datum `h = u`, this produces both displays
`e.large.scale.Holder.multifractal`  and
`e.large.scale.energy.multifractal`  in the
statement's own shape, on the untruncated window `z + 𝔠_n`.

The coefficient is written `coefficientAt M (L : WithTop ℕ) ω`, matching the
statement; at a finite cutoff this is definitionally
`aCutoff M L ω.1`, which is the coefficient the conclusion package uses. -/
theorem finite_cutoff_holder_displays
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {C : ℝ} {L m X : ℕ} {gamma : ℝ}
    {ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d}
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
  -- At a finite cutoff the coefficient is the conclusion package's.
  rw [coefficientAt_natCast]
  exact vectorNormalizedL2On_translatedCube_le_of_holderRegularityConclusions
    hconc hn hsub

/-- The same statement with the harmonicity hypothesis in front, in the exact
order the statement uses.  The Dirichlet presentation with `g = 0` and
`h = u` is supplied by `ZeroDatum`; what is *not* supplied -- and is the content
of the regularity condition -- is the `C^{1,1/2}` regularity of the boundary datum that
`p.cutoff.Holder.regularity` additionally requires, which is why the
conclusion package is taken as a hypothesis here rather than derived. -/
theorem finite_cutoff_holder_displays_of_conclusions
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {C : ℝ} {L m X : ℕ} {gamma : ℝ}
    {ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d}
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
