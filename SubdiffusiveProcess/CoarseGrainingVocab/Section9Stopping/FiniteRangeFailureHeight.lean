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



def extendedFailureHeight (failed : Set ℕ) : WithTop ℕ :=
  ⨆ h : {h // h ∈ failed}, ((h.1 + 1 : ℕ) : WithTop ℕ)



@[simp]
theorem extendedFailureHeight_empty : extendedFailureHeight ∅ = 0 := by
  simp [extendedFailureHeight]



theorem coe_succ_le_extendedFailureHeight {failed : Set ℕ} {h : ℕ}
    (hh : h ∈ failed) :
    (↑(h + 1) : WithTop ℕ) ≤ extendedFailureHeight failed := by
  exact le_iSup (fun k : {k // k ∈ failed} ↦
    ((k.1 + 1 : ℕ) : WithTop ℕ)) ⟨h, hh⟩



theorem extendedFailureHeight_mono {failed failed' : Set ℕ}
    (hsub : failed ⊆ failed') :
    extendedFailureHeight failed ≤ extendedFailureHeight failed' := by
  apply iSup_le
  rintro ⟨h, hh⟩
  exact le_iSup_of_le ⟨h, hsub hh⟩ le_rfl



def finiteFailureHeight (failed : Finset ℕ) : ℕ :=
  if h : failed.Nonempty then failed.max' h + 1 else 0



@[simp]
theorem finiteFailureHeight_empty : finiteFailureHeight ∅ = 0 := by
  simp [finiteFailureHeight]



theorem lt_finiteFailureHeight_of_mem {failed : Finset ℕ} {h : ℕ}
    (hh : h ∈ failed) : h < finiteFailureHeight failed := by
  have hne : failed.Nonempty := ⟨h, hh⟩
  simp only [finiteFailureHeight, dif_pos hne]
  exact Nat.lt_succ_of_le (failed.le_max' h hh)



theorem finiteFailureHeight_mono {failed failed' : Finset ℕ}
    (hsub : failed ⊆ failed') :
    finiteFailureHeight failed ≤ finiteFailureHeight failed' := by
  by_cases hne : failed.Nonempty
  · have hne' : failed'.Nonempty := hne.mono hsub
    simp only [finiteFailureHeight, dif_pos hne, dif_pos hne']
    exact Nat.add_le_add_right
      (failed'.le_max' (failed.max' hne) (hsub (failed.max'_mem hne))) 1
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, finiteFailureHeight_empty,
      Nat.zero_le]



theorem extendedFailureHeight_coe_finset (failed : Finset ℕ) :
    extendedFailureHeight (failed : Set ℕ) =
      (finiteFailureHeight failed : WithTop ℕ) := by
  by_cases hne : failed.Nonempty
  · apply le_antisymm
    · apply iSup_le
      rintro ⟨h, hh⟩
      simp only [finiteFailureHeight, dif_pos hne]
      exact_mod_cast Nat.succ_le_succ (failed.le_max' h hh)
    · simp only [finiteFailureHeight, dif_pos hne]
      exact le_iSup_of_le ⟨failed.max' hne, failed.max'_mem hne⟩ le_rfl
  · have hempty : failed = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hempty, Finset.coe_empty, extendedFailureHeight_empty,
      finiteFailureHeight_empty, Nat.cast_zero]



def localFailureHeight {d : ℕ} (height : Lattice d → ℕ)
    (z : Lattice d) (R : ℕ) : ℕ :=
  (latticeBallFinset z R).sup height



theorem le_localFailureHeight_of_latticeDist_le {d : ℕ}
    (height : Lattice d → ℕ) {z w : Lattice d} {R : ℕ}
    (hw : latticeDist z w ≤ R) :
    height w ≤ localFailureHeight height z R := by
  exact Finset.le_sup (mem_latticeBallFinset_iff.mpr hw)



theorem localFailureHeight_mono_height {d : ℕ}
    {height height' : Lattice d → ℕ} (hmono : ∀ z, height z ≤ height' z)
    (z : Lattice d) (R : ℕ) :
    localFailureHeight height z R ≤ localFailureHeight height' z R := by
  exact Finset.sup_mono_fun fun w _hw ↦ hmono w



theorem localFailureHeight_mono_radius {d : ℕ} (height : Lattice d → ℕ)
    (z : Lattice d) {R S : ℕ} (hRS : R ≤ S) :
    localFailureHeight height z R ≤ localFailureHeight height z S := by
  apply Finset.sup_mono
  intro w hw
  apply mem_latticeBallFinset_iff.mpr
  exact (mem_latticeBallFinset_iff.mp hw).trans hRS



def stoppingFactor (C : ℝ) (height : ℕ) : ℝ :=
  Real.exp (C * height)



theorem one_le_stoppingFactor {C : ℝ} (hC : 0 ≤ C) (height : ℕ) :
    1 ≤ stoppingFactor C height := by
  rw [stoppingFactor, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  positivity



theorem stoppingFactor_mono {C : ℝ} (hC : 0 ≤ C) {height height' : ℕ}
    (hh : height ≤ height') :
    stoppingFactor C height ≤ stoppingFactor C height' := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hh) hC

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
