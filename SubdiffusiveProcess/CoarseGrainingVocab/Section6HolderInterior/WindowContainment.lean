module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OffGridOscillation

@[expose] public section

/-!
# The containment criterion for truncated windows

`Section6Holder.truncatedCube_subset_succ_of_holderGridCentre` is the special
case `ell = j + 1` of a general criterion: a scale-`j` window at `x` sits inside
a scale-`ell` window at `z` exactly when the centres are within
`(3^ell - 3^j)/2` in every coordinate.

Stating it in that generality is what makes the scale bookkeeping of the
off-grid transfer checkable, and it is the geometric core any covering
construction will need.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

variable {d : ℕ}

/-- **The containment criterion.**  `U_{m,j}(x) ⊆ U_{m,ell}(z)` as soon as the
centres are within `(3^ell - 3^j)/2` coordinatewise. -/
theorem truncatedCube_subset_of_dist {m j ell : ℤ} {x z : Vec d}
    (hdist : ∀ i : Fin d, |x i - z i| ≤ ((3 : ℝ) ^ ell - (3 : ℝ) ^ j) / 2) :
    truncatedCube d m j x ⊆ truncatedCube d m ell z := by
  intro p hp
  refine ⟨?_, hp.2⟩
  rw [mem_translatedCube_iff, cube, mem_openCubeSet_originCube_iff]
  intro i
  have hpx := (mem_openCubeSet_originCube_iff.mp
    (mem_translatedCube_iff.mp hp.1)) i
  have hxz := abs_le.mp (hdist i)
  simp only [Pi.sub_apply] at hpx ⊢
  constructor <;> linarith only [hpx.1, hpx.2, hxz.1, hxz.2]

/-- **The scale obstruction.**  A grid centre at scale `g` is only guaranteed to
be within `3^g / 2` of `x`, so the criterion is available only when
`3^g + 3^j ≤ 3^ell`.  That forces `g < ell` — for *every* `j`, since `3^j > 0`:
an off-grid window is **never** contained in a same-scale window of its own grid
centre, at any scale.

This is the arithmetic reason row 1 — whose binder ties the grid scale to
the window scale, `OnTriadicGrid ell y` with the window `U_{m,ell}(y)` — cannot
be reached from an off-grid base point by a single containment, and why a
covering argument is required. -/
theorem grid_scale_lt_of_containment_criterion {g j ell : ℤ}
    (hcrit : (3 : ℝ) ^ g + (3 : ℝ) ^ j ≤ (3 : ℝ) ^ ell) :
    g < ell := by
  by_contra hcon
  push Not at hcon
  have hge : (3 : ℝ) ^ ell ≤ (3 : ℝ) ^ g :=
    zpow_le_zpow_right₀ (by norm_num) hcon
  have hjpos : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
