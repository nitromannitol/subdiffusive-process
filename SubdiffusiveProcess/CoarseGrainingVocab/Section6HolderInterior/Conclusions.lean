module

public import SubdiffusiveProcess.Frozen.Section6.Defs.InteriorHolderRegularityConclusions
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.Geometry

@[expose] public section

/-!
# Interior Hölder regularity: the conclusion package

Two facts about the frozen interior package
`InteriorHolderRegularityConclusions` (D-061) are recorded here.

* `interiorHolderRegularityConclusions_of_rows` is its exact three-row
  constructor, the interior mirror of
  `Section6Holder.holderRegularityConclusions_of_rows`.
* `interiorHolderRegularityConclusions_of_conclusions` shows the interior
  package is a *weakening* of the boundary package: whenever a Dirichlet datum
  happens to exist, the boundary conclusions imply the interior ones, because
  every printed `h`-term sits inside the indicator `if x ∈ cube d (m-1)`, which
  is `0` on the interior branch.  This is the machine form of the D-060 remark
  that the deleted summands "vanish for interior solutions"; it is *not* a route
  to the interior anchor, whose hypotheses supply no datum at all.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Exact constructor for the three frozen interior rows. -/
theorem interiorHolderRegularityConclusions_of_rows
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C : ℝ) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (alpha : ℝ) (m X : ℕ)
    (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
    (hcampanato :
      ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X : ℤ) →
        ∀ x ∈ cube d ((m : ℤ) - 1), ∀ ell : ℕ, ell ≤ n →
        ∀ y : Vec d, OnTriadicGrid ell y → y ∈ truncatedCube d m n x →
          (3 : ℝ) ^ (alpha * ((n : ℝ) - (ell : ℝ))) *
              normalizedL2On (truncatedCube d m ell y)
                (fun z ↦ u.toFun z - averageOn (truncatedCube d m ell y) u.toFun) ≤
            C * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
              (normalizedL2On (cube d m)
                  (fun z ↦ u.toFun z - averageOn (cube d m) u.toFun) +
                (tailAverage M L m ω (cube d m))⁻¹ * (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
                  holderSeminormOn (cube d m) (1 / 2) g))
    (henergy :
      ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X : ℤ) → ∀ x ∈ cube d ((m : ℤ) - 1),
        vectorNormalizedL2On (truncatedCube d m n x)
            (fun z ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω z) • u.grad z) ≤
          C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
            (vectorNormalizedL2On (cube d m)
                (fun z ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω z) • u.grad z) +
              (tailAverage M L m ω (cube d m)) ^ (-1 / 2 : ℝ) *
                (3 : ℝ) ^ ((m : ℝ) / 2) *
                holderSeminormOn (cube d m) (1 / 2) g))
    (hexcess :
      ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
        (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
        ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → ∀ x ∈ cube d ((m : ℤ) - 1),
          excess n (truncatedCube d m n x) u.toFun ≤
            C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) *
                excess ell (truncatedCube d m ell x) u.toFun +
              C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) *
                normalizedL2On (truncatedCube d m ell x)
                  (fun z ↦ u.toFun z - averageOn (truncatedCube d m ell x) u.toFun) +
              C * (tailAverage M L m ω (cube d m))⁻¹ *
                (3 : ℝ) ^ ((ell : ℝ) / 2) *
                holderSeminormOn (cube d m) (1 / 2) g) :
    InteriorHolderRegularityConclusions M C L ω alpha m X u g :=
  ⟨hcampanato, henergy, hexcess⟩

/-- The interior package is implied by the boundary package with any datum:
the deleted summands are exactly the ones the frozen indicator switches off at
interior base points. -/
theorem interiorHolderRegularityConclusions_of_conclusions
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C : ℝ) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (alpha : ℝ) (m X : ℕ)
    (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
    (hconcl : HolderRegularityConclusions M C L ω alpha m X u h g) :
    InteriorHolderRegularityConclusions M C L ω alpha m X u g := by
  obtain ⟨hcampanato, henergy, hexcess⟩ := hconcl
  refine interiorHolderRegularityConclusions_of_rows M C L ω alpha m X u g
    ?_ ?_ ?_
  · intro n hn x hx ell hell y hgrid hy
    have := hcampanato n hn x (mem_cube_of_mem_cube_sub_one hx) ell hell y hgrid hy
    rwa [if_pos hx, add_zero] at this
  · intro n hn x hx
    have := henergy n hn x (mem_cube_of_mem_cube_sub_one hx)
    rwa [if_pos hx, add_zero] at this
  · intro n hn hwindow ell hnell hellm x hx
    have := hexcess n hn hwindow ell hnell hellm x (mem_cube_of_mem_cube_sub_one hx)
    rwa [if_pos hx, add_zero] at this

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
