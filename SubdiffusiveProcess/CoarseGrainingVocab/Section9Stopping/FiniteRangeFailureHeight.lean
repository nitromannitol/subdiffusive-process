module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolation
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# Finite failure heights and local stopping envelopes

This file gives the finite combinatorial core of the stopping field constructed in Section 9:
one plus the last failed level, a local lattice maximum, and its exponential readout.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

/-- One plus the supremum of all failed levels, valued in `WithTop ℕ` so an unbounded set of
failures remains visible.  Taking the supremum of successors makes the empty-set value zero,
which is exactly the source convention `1 + sup ∅ = 0` without representing `-1` in `ℕ`.
-/
def extendedFailureHeight (failed : Set ℕ) : WithTop ℕ :=
  ⨆ h : {h // h ∈ failed}, ((h.1 + 1 : ℕ) : WithTop ℕ)

/-- The extended height of the empty failure set is zero.

Source: the `sup ∅ = -1` convention.
-/
@[simp]
theorem extendedFailureHeight_empty : extendedFailureHeight ∅ = 0 := by
  simp [extendedFailureHeight]

/-- Every failed level contributes its successor to the extended height.
-/
theorem coe_succ_le_extendedFailureHeight {failed : Set ℕ} {h : ℕ}
    (hh : h ∈ failed) :
    (↑(h + 1) : WithTop ℕ) ≤ extendedFailureHeight failed := by
  exact le_iSup (fun k : {k // k ∈ failed} ↦
    ((k.1 + 1 : ℕ) : WithTop ℕ)) ⟨h, hh⟩

/-- Enlarging the failure set can only increase its extended height.

Source: the nested failure tests used.
-/
theorem extendedFailureHeight_mono {failed failed' : Set ℕ}
    (hsub : failed ⊆ failed') :
    extendedFailureHeight failed ≤ extendedFailureHeight failed' := by
  apply iSup_le
  rintro ⟨h, hh⟩
  exact le_iSup_of_le ⟨h, hsub hh⟩ le_rfl

/-- One plus the last failed level, with value zero when no level fails.

This is the finite analogue of the convention `1 + sup ∅ = 0` in the source.
-/
def finiteFailureHeight (failed : Finset ℕ) : ℕ :=
  if h : failed.Nonempty then failed.max' h + 1 else 0

/-- No failed levels give height zero.

Source: the `sup ∅ = -1` convention.
-/
@[simp]
theorem finiteFailureHeight_empty : finiteFailureHeight ∅ = 0 := by
  simp [finiteFailureHeight]

/-- Every failed level lies strictly below the resulting height.
-/
theorem lt_finiteFailureHeight_of_mem {failed : Finset ℕ} {h : ℕ}
    (hh : h ∈ failed) : h < finiteFailureHeight failed := by
  have hne : failed.Nonempty := ⟨h, hh⟩
  simp only [finiteFailureHeight, dite_eq_left hne]
  exact Nat.lt_succ_of_le (failed.le_max' h hh)

/-- Adding possible failures can only increase the last-failure height.

Source: the nested failure tests used for monotonicity -/
theorem finiteFailureHeight_mono {failed failed' : Finset ℕ}
    (hsub : failed ⊆ failed') :
    finiteFailureHeight failed ≤ finiteFailureHeight failed' := by
  by_cases hne : failed.Nonempty
  · have hne' : failed'.Nonempty := hne.mono hsub
    simp only [finiteFailureHeight, dite_eq_left hne, dite_eq_left hne']
    exact Nat.add_le_add_right
      (failed'.le_max' (failed.max' hne) (hsub (failed.max'_mem hne))) 1
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, finiteFailureHeight_empty,
      Nat.zero_le]

/-- On a finite failure set, the extended construction agrees with the natural-valued last
failure height.
-/
theorem extendedFailureHeight_coe_finset (failed : Finset ℕ) :
    extendedFailureHeight (failed : Set ℕ) =
      (finiteFailureHeight failed : WithTop ℕ) := by
  by_cases hne : failed.Nonempty
  · apply le_antisymm
    · apply iSup_le
      rintro ⟨h, hh⟩
      simp only [finiteFailureHeight, dite_eq_left hne]
      exact_mod_cast Nat.succ_le_succ (failed.le_max' h hh)
    · simp only [finiteFailureHeight, dite_eq_left hne]
      exact le_iSup_of_le ⟨failed.max' hne, failed.max'_mem hne⟩ le_rfl
  · have hempty : failed = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hempty, Finset.coe_empty, extendedFailureHeight_empty,
      finiteFailureHeight_empty, Nat.cast_zero]

/-- The local maximum of the lattice failure heights in a closed `ℓ∞` ball.

At radius four this is `h_m(x)` on lattice centers..
-/
def localFailureHeight {d : ℕ} (height : Lattice d → ℕ)
    (z : Lattice d) (R : ℕ) : ℕ :=
  (latticeBallFinset z R).sup height

/-- A lattice point in the local ball has height at most the local maximum.
-/
theorem le_localFailureHeight_of_latticeDist_le {d : ℕ}
    (height : Lattice d → ℕ) {z w : Lattice d} {R : ℕ}
    (hw : latticeDist z w ≤ R) :
    height w ≤ localFailureHeight height z R := by
  exact Finset.le_sup (mem_latticeBallFinset_iff.mpr hw)

/-- Pointwise larger failure heights have larger local envelopes.

Source: the first implication.
-/
theorem localFailureHeight_mono_height {d : ℕ}
    {height height' : Lattice d → ℕ} (hmono : ∀ z, height z ≤ height' z)
    (z : Lattice d) (R : ℕ) :
    localFailureHeight height z R ≤ localFailureHeight height' z R := by
  exact Finset.sup_mono_fun fun w _hw ↦ hmono w

/-- Enlarging the lattice radius can only increase the local envelope.

Source: the local maximum construction.
-/
theorem localFailureHeight_mono_radius {d : ℕ} (height : Lattice d → ℕ)
    (z : Lattice d) {R S : ℕ} (hRS : R ≤ S) :
    localFailureHeight height z R ≤ localFailureHeight height z S := by
  apply Finset.sup_mono
  intro w hw
  apply mem_latticeBallFinset_iff.mpr
  exact (mem_latticeBallFinset_iff.mp hw).trans hRS

/-- Exponential readout of a local failure height.
-/
def stoppingFactor (C : ℝ) (height : ℕ) : ℝ :=
  Real.exp (C * height)

/-- The stopping factor is at least one for a nonnegative dimensional constant.
-/
theorem one_le_stoppingFactor {C : ℝ} (hC : 0 ≤ C) (height : ℕ) :
    1 ≤ stoppingFactor C height := by
  rw [stoppingFactor, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  positivity

/-- Monotonicity of the height passes to its exponential stopping factor.
-/
theorem stoppingFactor_mono {C : ℝ} (hC : 0 ≤ C) {height height' : ℕ}
    (hh : height ≤ height') :
    stoppingFactor C height ≤ stoppingFactor C height' := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hh) hC

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
