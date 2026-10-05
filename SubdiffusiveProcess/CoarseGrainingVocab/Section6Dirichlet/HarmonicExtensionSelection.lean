module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BoundaryDataStability

@[expose] public section

/-!
# Canonical selection of scalar harmonic Dirichlet extensions

This module packages the variational existence theorem for scalar harmonic
extensions as a deterministic choice.  It then combines that choice with the
Dirichlet stability theorem, supplying the comparison-solution sequence used
when passing locally uniformly convergent coefficients to the limit.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- A selected weakly harmonic extension of an `H¹` boundary datum for a
uniformly elliptic scalar coefficient. -/
noncomputable def weakHarmonicDirichletExtension
    [NeZero d] {W : Set (Vec d)} {a : Vec d → ℝ} {lambda Lambda : ℝ}
    (hW : IsOpenBoundedConvexDomain W) (hne : W.Nonempty)
    (hEll : IsEllipticFieldOn lambda Lambda W (scalarCoeffField a))
    (h : H1Function W) : H1Function W :=
  Classical.choose
    (exists_isWeaklyHarmonicOn_and_hasZeroTraceDifferenceOn hW hne hEll h)

/-- The selected extension solves the scalar weak equation. -/
theorem isWeaklyHarmonicOn_weakHarmonicDirichletExtension
    [NeZero d] {W : Set (Vec d)} {a : Vec d → ℝ} {lambda Lambda : ℝ}
    (hW : IsOpenBoundedConvexDomain W) (hne : W.Nonempty)
    (hEll : IsEllipticFieldOn lambda Lambda W (scalarCoeffField a))
    (h : H1Function W) :
    IsWeaklyHarmonicOn a W
      (weakHarmonicDirichletExtension hW hne hEll h) :=
  (Classical.choose_spec
    (exists_isWeaklyHarmonicOn_and_hasZeroTraceDifferenceOn hW hne hEll h)).1

/-- The selected extension has the prescribed trace. -/
theorem hasZeroTraceDifferenceOn_weakHarmonicDirichletExtension
    [NeZero d] {W : Set (Vec d)} {a : Vec d → ℝ} {lambda Lambda : ℝ}
    (hW : IsOpenBoundedConvexDomain W) (hne : W.Nonempty)
    (hEll : IsEllipticFieldOn lambda Lambda W (scalarCoeffField a))
    (h : H1Function W) :
    HasZeroTraceDifferenceOn W
      (weakHarmonicDirichletExtension hW hne hEll h) h :=
  (Classical.choose_spec
    (exists_isWeaklyHarmonicOn_and_hasZeroTraceDifferenceOn hW hne hEll h)).2

/-- Locally uniformly convergent scalar coefficients admit selected harmonic
extensions with a common datum which converge strongly in both components of
the witness-based `H¹` carrier. -/
theorem exists_dirichletSolutionSequence_tendsto_H1_of_tendstoUniformlyOn
    [NeZero d] {W K : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    (hne : W.Nonempty) {a : ℕ → Vec d → ℝ} {alim : Vec d → ℝ}
    {lambda LambdaLim : ℝ} {Lambda : ℕ → ℝ}
    (hWK : W ⊆ K) (hlambda : 0 < lambda)
    (halow : ∀ n x, x ∈ W → lambda ≤ a n x)
    (haEll : ∀ n,
      IsEllipticFieldOn lambda (Lambda n) W (scalarCoeffField (a n)))
    (halimEll : IsEllipticFieldOn lambda LambdaLim W (scalarCoeffField alim))
    (haLim : TendstoUniformlyOn a alim Filter.atTop K)
    (h : H1Function W) :
    ∃ u : ℕ → H1Function W, ∃ ulim : H1Function W,
      (∀ n, IsWeaklyHarmonicOn (a n) W (u n)) ∧
      IsWeaklyHarmonicOn alim W ulim ∧
      (∀ n, HasZeroTraceDifferenceOn W (u n) h) ∧
      HasZeroTraceDifferenceOn W ulim h ∧
      Filter.Tendsto (fun n ↦ ‖((u n) - ulim).toScalarL2‖)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n ↦ ‖((u n) - ulim).gradToHilbertVectorL2‖)
        Filter.atTop (nhds 0) := by
  let u : ℕ → H1Function W := fun n ↦
    weakHarmonicDirichletExtension hW hne (haEll n) h
  let ulim : H1Function W :=
    weakHarmonicDirichletExtension hW hne halimEll h
  have huHarm : ∀ n, IsWeaklyHarmonicOn (a n) W (u n) := fun n ↦
    isWeaklyHarmonicOn_weakHarmonicDirichletExtension hW hne (haEll n) h
  have hulimHarm : IsWeaklyHarmonicOn alim W ulim :=
    isWeaklyHarmonicOn_weakHarmonicDirichletExtension hW hne halimEll h
  have huTrace : ∀ n, HasZeroTraceDifferenceOn W (u n) h := fun n ↦
    hasZeroTraceDifferenceOn_weakHarmonicDirichletExtension hW hne (haEll n) h
  have hulimTrace : HasZeroTraceDifferenceOn W ulim h :=
    hasZeroTraceDifferenceOn_weakHarmonicDirichletExtension hW hne halimEll h
  obtain ⟨hvalue, hgrad⟩ :=
    tendsto_dirichletSolution_H1_of_tendstoUniformlyOn hW hWK hlambda
      halow haEll halimEll haLim huTrace hulimTrace huHarm hulimHarm
  exact ⟨u, ulim, huHarm, hulimHarm, huTrace, hulimTrace, hvalue, hgrad⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
