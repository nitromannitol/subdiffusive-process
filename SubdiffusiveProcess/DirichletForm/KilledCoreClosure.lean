module

public import Mathlib.Tactic
public import SubdiffusiveProcess.DirichletForm.Killed

@[expose] public section

/-! Deterministic lib data extracted upstream of process convergence.
This module does not assert concentration or invoke the process-convergence theorem. -/

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
namespace DirichletForm.ClosedForm
noncomputable section

variable {X : Type*} [MeasurableSpace X] {mu : Measure X}

/-- Extracted energyNormSq add le argument from the pre-convergence deterministic proof. -/
theorem energyNormSq_add_le_two_mul
    (E : DirichletForm.ClosedForm mu) {u v : Lp ℝ 2 mu}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.energyNormSq (u + v) ≤ 2 * E.energyNormSq u + 2 * E.energyNormSq v := by
  have hp := E.energyNormSq_add_smul_self 1 hu hv
  have hm := E.energyNormSq_add_smul_self (-1) hu hv
  have hn := E.energyNormSq_nonneg (E.domain.sub_mem hu hv)
  simp only [one_smul, mul_one, one_pow, one_mul] at hp
  simp only [neg_smul, one_smul, neg_one_sq, one_mul, ← sub_eq_add_neg] at hm
  linarith only [hp, hm, hn]

/-- Extracted energyNormSq smul argument from the pre-convergence deterministic proof. -/
theorem energyNormSq_smul_eq
    (E : DirichletForm.ClosedForm mu) (c : ℝ) {u : Lp ℝ 2 mu} (hu : u ∈ E.domain) :
    E.energyNormSq (c • u) = c ^ 2 * E.energyNormSq u := by
  unfold DirichletForm.ClosedForm.energyNormSq
  rw [E.form_smul_left c u hu (c • u) (E.domain.smul_mem c hu),
    E.form_smul_right c hu hu, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

variable [TopologicalSpace X]

/-- Extracted killed domain argument from the pre-convergence deterministic proof. -/
def killedCoreClosure (E : DirichletForm.ClosedForm mu) (U : Set X) :
    Submodule ℝ (Lp ℝ 2 mu) where
  carrier := {u | u ∈ E.domain ∧ ∀ eps : ℝ, 0 < eps →
    ∃ w : Lp ℝ 2 mu, E.MemCoreOn U w ∧ E.energyNormSq (u - w) < eps}
  zero_mem' := by
    refine ⟨E.domain.zero_mem, fun eps heps => ⟨0, DirichletForm.ClosedForm.memCoreOn_zero E U, ?_⟩⟩
    simpa only [DirichletForm.ClosedForm.energyNormSq, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), E.form_zero_left E.domain.zero_mem, add_zero] using heps
  add_mem' := by
    rintro u v ⟨hu, hau⟩ ⟨hv, hav⟩
    refine ⟨E.domain.add_mem hu hv, fun eps heps => ?_⟩
    obtain ⟨w, hw, hwu⟩ := hau (eps / 4) (by positivity)
    obtain ⟨z, hz, hzv⟩ := hav (eps / 4) (by positivity)
    refine ⟨w + z, hw.add hz, ?_⟩
    have heq : u + v - (w + z) = (u - w) + (v - z) := by abel
    rw [heq]
    have hbound := DirichletForm.ClosedForm.energyNormSq_add_le_two_mul E
      (E.domain.sub_mem hu hw.1) (E.domain.sub_mem hv hz.1)
    linarith only [hbound, hwu, hzv]
  smul_mem' := by
    rintro c u ⟨hu, hau⟩
    refine ⟨E.domain.smul_mem c hu, fun eps heps => ?_⟩
    obtain ⟨w, hw, hwu⟩ := hau (eps / (c ^ 2 + 1)) (by positivity)
    refine ⟨c • w, hw.smul c, ?_⟩
    rw [← smul_sub, DirichletForm.ClosedForm.energyNormSq_smul_eq E c (E.domain.sub_mem hu hw.1)]
    have hh := (lt_div_iff₀ (by positivity : 0 < c ^ 2 + 1)).mp hwu
    have hn := E.energyNormSq_nonneg (E.domain.sub_mem hu hw.1)
    nlinarith only [hh, hn]

/-- Extracted isKilledDomain argument from the pre-convergence deterministic proof. -/
theorem isKilledDomain_killedCoreClosure
    (E : DirichletForm.ClosedForm mu) (U : Set X) :
    DirichletForm.IsKilledDomain E U (DirichletForm.ClosedForm.killedCoreClosure E U) := by
  refine ⟨fun _ hu => hu.1, ?_, fun _ hu => hu.2, ?_⟩
  · intro u hu
    refine ⟨hu.1, fun eps heps => ⟨u, hu, ?_⟩⟩
    simpa only [DirichletForm.ClosedForm.energyNormSq, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), E.form_zero_left E.domain.zero_mem, add_zero] using heps
  · intro u w hu hw hlim
    refine ⟨hw, fun eps heps => ?_⟩
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (by positivity : 0 < eps / 4))).exists
    obtain ⟨z, hz, hzn⟩ := (hu n).2 (eps / 4) (by positivity)
    refine ⟨z, hz, ?_⟩
    have heq : w - z = (w - u n) + (u n - z) := by abel
    have hbound := DirichletForm.ClosedForm.energyNormSq_add_le_two_mul E
      (E.domain.sub_mem hw (hu n).1) (E.domain.sub_mem (hu n).1 hz.1)
    rw [← heq, E.energyNormSq_sub_comm hw (hu n).1] at hbound
    linarith only [hbound, hn, hzn]

end
end DirichletForm.ClosedForm
