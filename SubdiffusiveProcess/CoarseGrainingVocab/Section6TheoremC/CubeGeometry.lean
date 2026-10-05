module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows

@[expose] public section

/-!
# Window geometry for the Theorem C specialization

The proof of Theorem C (`t.large.scale.Holder.multifractal`) reads, at
`t.large.scale.Holder.multifractal` and `p.cutoff.Holder.regularity` and `e.Holder.estimate.boxes.local` and `e.energy.density.estimate` and `e.large.scale.Holder.multifractal` and `e.large.scale.energy.multifractal`:

> For finite `L`, the two estimates are the interior, harmonic specialization
> of Proposition `p.cutoff.Holder.regularity`: take `g = 0`, `x = z`, and
> `ℓ = n` in `e.Holder.estimate.boxes.local`, and use
> `e.energy.density.estimate`.

The windows of `p.cutoff.Holder.regularity` are the *truncated* cubes
`truncatedCube d m n x = (x + 𝔠_n) ∩ 𝔠_m` (`t.large.scale.Holder.multifractal` and `p.cutoff.Holder.regularity` and `e.Holder.estimate.boxes.local` and `e.energy.density.estimate` and `e.large.scale.Holder.multifractal` and `e.large.scale.energy.multifractal`), while
Theorem C's displays `e.large.scale.Holder.multifractal` and
`e.large.scale.energy.multifractal` are stated on the untruncated translate
`translatedCube d n z = z + 𝔠_n`.  Theorem C carries the interior hypothesis
`z + 𝔠_n ⊆ 𝔠_{m-1}` (`t.large.scale.Holder.multifractal` and `p.cutoff.Holder.regularity` and `e.Holder.estimate.boxes.local` and `e.energy.density.estimate` and `e.large.scale.Holder.multifractal` and `e.large.scale.energy.multifractal`), which collapses the
truncation.

This file proves that collapse and the two membership facts it needs: `x = z`
is an admissible base point for `p.cutoff.Holder.regularity`, and it lies in
`𝔠_{m-1}`, so the boundary indicator `𝟙_{x ∉ 𝔠_{m-1}}` carrying the `∇h` terms
of `e.Holder.estimate.boxes.local` and `e.energy.density.estimate` vanishes.

The scale-monotonicity and origin-membership facts are reused from
`SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay` rather than reproved.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open Homogenization SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

variable {d : ℕ}

/-! ### The base point of the translated window -/

/-- The translation base point lies in its own translated cube: this is the
admissibility of the choice `x = z`, `y = z` at `t.C`. -/
theorem mem_translatedCube_self (d : ℕ) (n : ℤ) (z : Vec d) :
    z ∈ translatedCube d n z := by
  rw [mem_translatedCube_iff, sub_self]
  exact zero_mem_cube d n

/-- If a translated window sits inside a centered cube, its base point does. -/
theorem mem_cube_of_translatedCube_subset {n k : ℤ} {z : Vec d}
    (h : translatedCube d n z ⊆ cube d k) : z ∈ cube d k :=
  h (mem_translatedCube_self d n z)

/-! ### Collapse of the truncation -/

/-- Under the interior hypothesis of Theorem C the truncated window of
`p.cutoff.Holder.regularity` *is* the translated window of
`e.large.scale.Holder.multifractal`. -/
theorem truncatedCube_eq_translatedCube {m n : ℤ} {z : Vec d}
    (h : translatedCube d n z ⊆ cube d m) :
    truncatedCube d m n z = translatedCube d n z :=
  Set.inter_eq_self_of_subset_left h

/-- The form in which the collapse is applied: Theorem C supplies containment
in `𝔠_{m-1}`, one scale below the outer cube `𝔠_m` carrying the estimate. -/
theorem truncatedCube_eq_translatedCube_of_subset_pred {m n : ℤ} {z : Vec d}
    (h : translatedCube d n z ⊆ cube d (m - 1)) :
    truncatedCube d m n z = translatedCube d n z :=
  truncatedCube_eq_translatedCube
    (h.trans (cube_subset_cube_of_le (by omega)))

/-- Under the same hypothesis the base point lies in `𝔠_{m-1}`, so the boundary
indicator `𝟙_{x ∉ 𝔠_{m-1}}` of `e.Holder.estimate.boxes.local` and
`e.energy.density.estimate` vanishes. -/
theorem mem_cube_pred_of_translatedCube_subset {m n : ℤ} {z : Vec d}
    (h : translatedCube d n z ⊆ cube d (m - 1)) : z ∈ cube d (m - 1) :=
  mem_cube_of_translatedCube_subset h

/-- The base point also lies in the outer cube `𝔠_m`, as
`p.cutoff.Holder.regularity` requires of its parameter `x`. -/
theorem mem_cube_of_translatedCube_subset_pred {m n : ℤ} {z : Vec d}
    (h : translatedCube d n z ⊆ cube d (m - 1)) : z ∈ cube d m :=
  cube_subset_cube_of_le (by omega : m - 1 ≤ m)
    (mem_cube_pred_of_translatedCube_subset h)

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
