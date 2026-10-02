import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.InnerHalfNestedFamily
import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.ExtendByZero

/-!
# Coverage of the shared-parent family

The fixed-concentric-interior family of `NestedFamilyComplete.lean` reaches
only the fraction `(3 ^ d) ^ -(depth)` of the source cells inside a retained
overlap centre (`nfNestedIndex_card_mul_le_descendantsAtDepth_card`).  The
shared-parent family of `InnerHalfNestedFamily.lean` reaches **all** of them:
its cells attached to a retained overlap centre `S` are exactly the depth-`(N
- 1)` descendants of `S`, i.e. every source-scale cell inside `S`.

This module proves that surjectivity, and the resulting exactness of
`nfExtendByZero` on those cells.
-/

open MeasureTheory Homogenization
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

noncomputable section

variable {d : ℕ}

/-- The cells of the shared-parent family attached to a retained overlap
centre `S` are the depth-`(N - 1)` descendants of `S`, translated from the
origin cube one scale below the parent. -/
theorem nfInnerHalfCell_eq_translate
    (N : ℕ) (S R₀ : TriadicCube d) :
    translateCube
        (descendantTranslationShift (N - 1) (fun i ↦ (3 : ℤ) ^ (1 - 1) *
          S.index i)) R₀ =
      translateCube (nfCellShift S N) R₀ := by
  congr 1
  funext i
  simp only [descendantTranslationShift, nfCellShift]
  ring

/-- **Coverage.**  Every depth-`(N - 1)` descendant of a retained overlap
centre is a cell of the shared-parent family. -/
theorem exists_nfInnerHalfIndex_cell_eq
    {K : ℤ} {j N : ℕ}
    {S : TriadicCube d} (hS : S ∈ overlapCentersAtDepth (originCube d K) j)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth S (N - 1)) :
    ∃ q : NFInnerHalfIndex d K j N, nfNestedCell N q = R := by
  classical
  have hT := translateCube_originCube_eq_centralDescendant (K := K) (j := j)
    (a := 1) le_rfl hS
  rw [CubeCalderonZygmund.centralDescendant_zero] at hT
  rw [← hT, descendantsAtDepth_translateCube] at hR
  obtain ⟨R₀, hR₀, hR₀eq⟩ := Finset.mem_image.mp hR
  refine ⟨(⟨S, hS⟩, ⟨R₀, hR₀⟩), ?_⟩
  rw [nfNestedCell]
  rw [← nfInnerHalfCell_eq_translate N S R₀]
  exact hR₀eq

/-- **Exactness of the zero extension on the covered cells.**  On every
depth-`(N - 1)` descendant of a retained overlap centre, the extension of a
family observable is that observable at some index over the cell. -/
theorem exists_nfExtendByZero_innerHalf_eq {Omega : Type*}
    {K : ℤ} {j N : ℕ}
    {S : TriadicCube d} (hS : S ∈ overlapCentersAtDepth (originCube d K) j)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth S (N - 1))
    (G : NFInnerHalfIndex d K j N → Omega → ℝ) :
    ∃ q : NFInnerHalfIndex d K j N, nfNestedCell N q = R ∧
      ∀ omega, nfExtendByZero (nfNestedCell N) G R omega = G q omega :=
  exists_nfExtendByZero_eq (exists_nfInnerHalfIndex_cell_eq hS hR)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
