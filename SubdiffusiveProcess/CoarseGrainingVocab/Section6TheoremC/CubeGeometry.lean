module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open Homogenization SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

variable {d : ℕ}

/-! ### The base point of the translated window -/



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
