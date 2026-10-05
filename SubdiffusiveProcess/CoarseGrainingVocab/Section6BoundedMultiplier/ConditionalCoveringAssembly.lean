module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.LocalPointMajorant

@[expose] public section

/-!
# Cover geometry and common-reference readout

Only geometry and the general common-reference lemma remain here.  The former
cell-mean consumer has been removed: an off-center unit-cell mean cannot carry
target-depth decay, as witnessed by affine harmonic functions.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open _root_.SubdiffusiveProcess.Model

noncomputable section

private abbrev Sample (d : ℕ) := PotentialSample d

/-- On the covering good event, the cell containing a requested point carries
explicit positive ellipticity bounds with controlled ratio. -/
theorem exists_coverCell_ellipticity_of_good {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) {omega : Sample d}
    (hgood : omega ∈ coveringCoefficientRatioGood M L m z)
    {x : Vec d} (hx : x ∈ translatedCube d m z) :
    ∃ p ∈ shellCoverShifts d m,
      x ∈ boundedMultiplierCoverCell d m z p ∧
      ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
        Lam ≤ Real.exp (boundedMultiplierCoverOscillationThreshold M m) ^ 2 * lam ∧
        ∀ y ∈ boundedMultiplierCoverCell d m z p,
          lam ≤ aCutoff M L omega y ∧ aCutoff M L omega y ≤ Lam := by
  obtain ⟨p, hpS, hxcell⟩ := exists_mem_boundedMultiplierCoverCell m z hx
  refine ⟨p, hpS, hxcell, ?_⟩
  exact exists_bounds_of_coefficientRatioGood_aCutoff M L
    ⟨x, hxcell⟩ (mem_coveringCoefficientRatioGood_iff.1 hgood p hpS)

/-- For an interior covering cube, clipping disappears and the same event
supplies ellipticity on the full translated unit cube. -/
theorem exists_unitCube_ellipticity_of_coveringGood {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) {omega : Sample d}
    (hgood : omega ∈ coveringCoefficientRatioGood M L m z)
    (p : Fin d → ℤ) (hp : p ∈ shellCoverShifts d m)
    (hinterior : translatedCube d 0 (z + physicalShellCoverCenter 0 p) ⊆
      translatedCube d m z) :
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      Lam ≤ Real.exp (boundedMultiplierCoverOscillationThreshold M m) ^ 2 * lam ∧
      ∀ y ∈ translatedCube d 0 (z + physicalShellCoverCenter 0 p),
        lam ≤ aCutoff M L omega y ∧ aCutoff M L omega y ≤ Lam := by
  have hcell : boundedMultiplierCoverCell d m z p =
      translatedCube d 0 (z + physicalShellCoverCenter 0 p) :=
    Set.inter_eq_right.mpr hinterior
  have hpGood := mem_coveringCoefficientRatioGood_iff.1 hgood p hp
  rw [hcell] at hpGood
  exact exists_bounds_of_coefficientRatioGood_aCutoff M L
    (by
      refine ⟨z + physicalShellCoverCenter 0 p, ?_⟩
      refine ⟨0, ?_, by simp⟩
      change (0 : Vec d) ∈ openCubeSet (originCube d 0)
      rw [mem_openCubeSet_originCube_iff]
      intro i
      norm_num)
    hpGood

/-- A pointwise estimate relative to one common reference value bounds the
literal oscillation and supremum used by the frozen target. -/
theorem pointwiseConclusions_of_commonReference {d : ℕ}
    {B' : Set (Vec d)} (hB' : B'.Nonempty) (f : Vec d → ℝ)
    (a R D E : ℝ)
    (hpoint : ∀ x ∈ B', |f x - a| ≤ R)
    (hdecay : 2 * R ≤ D) (henergy : R ≤ E) :
    oscillationOn B' f ≤ D ∧
      sSup {r : ℝ | ∃ x ∈ B', r = |f x - a|} ≤ E := by
  constructor
  · unfold oscillationOn
    apply (csSup_le ?_ fun r hr ↦ ?_).trans hdecay
    · obtain ⟨x, hx⟩ := hB'
      exact ⟨0, x, hx, x, hx, by simp⟩
    · rcases hr with ⟨x, hx, y, hy, rfl⟩
      have htri := abs_sub_le (f x) a (f y)
      have htri' : |f x - f y| ≤ |f x - a| + |f y - a| := by
        simpa only [abs_sub_comm a] using htri
      exact htri'.trans (by linarith [hpoint x hx, hpoint y hy])
  · apply (csSup_le ?_ fun r hr ↦ ?_).trans henergy
    · obtain ⟨x, hx⟩ := hB'
      exact ⟨|f x - a|, x, hx, rfl⟩
    · rcases hr with ⟨x, hx, rfl⟩
      exact hpoint x hx

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
