/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EquationTranslation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ForcedReplacement
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FullWspTransport
public import Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingForcing
public import Homogenization.Deterministic.CoarsePoincareRHS.TerminalBounds

@[expose] public section

/-!
# The local harmonic-approximation comparison datum

This is the PDE-carrier assembly immediately before applying finite-`p`
coarse graining.  It restricts and recenters the v5 force, recenters the weak
equation, and constructs the source-sign scalar replacement with the same
boundary trace.

PROVENANCE: mirrors the division between `ForceTransport.lean`,
`TranslationTransport.lean`, and `ReplacementDatum.lean` in
`Algsuperdiff/Section4/Provider/ExcessDecay/`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The local equation and v5 membership produce every PDE-side premise of
the finite-`p` comparison on the recentered cube. -/
theorem exists_localSourceComparisonDatum
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q P : TriadicCube d) (z : Vec d) (s : FractionalOrder)
    (g : Vec d → Vec d) (u : H1Function (translateSet z (openCubeSet Q)))
    (hsub : translateSet z (openCubeSet Q) ⊆ openCubeSet P)
    (hg : Ch03.ABK26.MemCubeEuclideanFullWsp P s FiniteLpExponent.two g)
    (hu : IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (translateSet z (openCubeSet Q)) u g)
    (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ g0 : Vec d → Vec d,
      Ch03.ABK26.MemCubeEuclideanFullWsp Q s FiniteLpExponent.two g0 ∧
      ∃ u0 v0 : H1Function (openCubeSet Q),
        Ch03.ABK26.IsForcedEquation Q
          ((aCutoffFamily M L (translatePotentialSample z omega)).coeffOn Q) u0 g0 ∧
        Ch03.ABK26.IsScalarForcedEquation Q sigma v0 g0 ∧
        Ch03.ABK26.HasH10Difference Q u0 v0 := by
  let g0 : Vec d → Vec d := fun x => g (x + z)
  have hg0 : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two g0 :=
    memCubeEuclideanFullWsp_translate_of_subset Q P z s FiniteLpExponent.two g hsub hg
  have hg0Two : MemLp g0 2 (normalizedCubeMeasure Q) :=
    Ch03.ABK26.MemCubeEuclideanFullWsp.memLpTwo (by norm_num) hg0
  have hg0Cube : MemVectorL2 (cubeSet Q) g0 :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hg0Two
  have hg0Open : MemVectorL2 (openCubeSet Q) g0 := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using hg0Cube
  let u0 : H1Function (openCubeSet Q) := H1Function.untranslate z u
  let v0 : H1Function (openCubeSet Q) :=
    sourceForcedReplacement (scalarConstantCoeffMatrix (d := d) hsigma) u0 hg0Open
  refine ⟨g0, hg0, u0, v0, ?_, ?_, ?_⟩
  · exact isForcedEquation_aCutoff_untranslate M L omega Q z hu
  · exact isScalarForcedEquation_sourceForcedReplacement hsigma u0 hg0Open
  · exact hasH10Difference_sourceForcedReplacement
      (scalarConstantCoeffMatrix (d := d) hsigma) u0 hg0Open

/-- Anchor-facing form: restrict the ambient Dirichlet equation to the local
translated cube and replace its restriction by the supplied exact `uD`
representative. -/
theorem exists_localSourceComparisonDatum_of_dirichlet
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (m : ℕ) (k : ℤ) (y : Vec d) (s : FractionalOrder)
    (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d)
    (hdir : IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (originCube d (m : ℤ)) u h g)
    (hg : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d (m : ℤ)) s FiniteLpExponent.two g)
    (hsub : translatedCube d k y ⊆ openCubeSet (originCube d (m : ℤ)))
    (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ g0 : Vec d → Vec d,
      Ch03.ABK26.MemCubeEuclideanFullWsp
        (originCube d k) s FiniteLpExponent.two g0 ∧
      ∃ u0 v0 : H1Function (openCubeSet (originCube d k)),
        Ch03.ABK26.IsForcedEquation (originCube d k)
          ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
            (originCube d k)) u0 g0 ∧
        Ch03.ABK26.IsScalarForcedEquation (originCube d k) sigma v0 g0 ∧
        Ch03.ABK26.HasH10Difference (originCube d k) u0 v0 := by
  have hD : translatedCube d k y =
      translateSet y (openCubeSet (originCube d k)) := by
    rw [translatedCube, cube,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet]
  have hDopen : IsOpen (translatedCube d k y) := by
    rw [hD]
    exact (isOpenBoundedConvexDomain_openCubeSet (originCube d k)).translateSet y |>.isOpen
  have hsubt : translateSet y (openCubeSet (originCube d k)) ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    rw [← hD]
    exact hsub
  have hDtOpen : IsOpen (translateSet y (openCubeSet (originCube d k))) := by
    rw [← hD]
    exact hDopen
  let uDt : H1Function (translateSet y (openCubeSet (originCube d k))) :=
    u.restrict hDtOpen hsubt
  have huDt : IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (translateSet y (openCubeSet (originCube d k))) uDt g :=
    isDivFormWeakSolutionOn_restrict
      (isOpenBoundedConvexDomain_openCubeSet (originCube d (m : ℤ))).isOpen
      hDtOpen hsubt hdir.2
  exact exists_localSourceComparisonDatum M L omega
    (originCube d k) (originCube d (m : ℤ)) y s g uDt hsubt hg huDt sigma hsigma

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
