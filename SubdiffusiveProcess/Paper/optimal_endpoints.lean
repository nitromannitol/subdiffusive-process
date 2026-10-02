import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Lane2.LimitForm
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace Paper



theorem optimal_endpoints
    (d : ℕ) (hd : 2 ≤ d)
    (Q : ℕ → Opens (SpatialCoordinates d))
    (hQ : ∀ n, ∃ z r, ∃ (hr : 0 < r), Q n = centeredCube z r hr)
    (GE GF : (n : ℕ) → DomainL2 (Q n) →L[ℝ] DomainL2 (Q n))
    (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hdom : ∀ n, limitFormDomain (GE n) = limitFormDomain (GF n))
    (hcompare : ∀ n (u : DomainL2 (Q n)), u ∈ limitFormDomain (GE n) →
      C0⁻¹ * (limitFormEnergy (GE n) u).toReal ≤ (limitFormEnergy (GF n) u).toReal ∧
      (limitFormEnergy (GF n) u).toReal ≤ C0 * (limitFormEnergy (GE n) u).toReal)
    (hnonzero : ∃ n, ∃ (u : DomainL2 (Q n)), u ∈ limitFormDomain (GE n) ∧
      0 < (limitFormEnergy (GE n) u).toReal) :
    let lower : Set ℝ := {a | ∀ n (u : DomainL2 (Q n)),
      u ∈ limitFormDomain (GE n) →
      a * (limitFormEnergy (GE n) u).toReal ≤ (limitFormEnergy (GF n) u).toReal}
    let upper : Set ℝ := {a | ∀ n (u : DomainL2 (Q n)),
      u ∈ limitFormDomain (GE n) →
      (limitFormEnergy (GF n) u).toReal ≤ a * (limitFormEnergy (GE n) u).toReal}
    let m := sSup lower
    let M := sInf upper
    IsLUB lower m ∧ IsGLB upper M ∧
      (C0⁻¹ ≤ m ∧ m ≤ M ∧ M ≤ C0) ∧ (m ∈ lower ∧ M ∈ upper) := by
  let lower : Set ℝ := {a | ∀ n (u : DomainL2 (Q n)),
    u ∈ limitFormDomain (GE n) →
    a * (limitFormEnergy (GE n) u).toReal ≤ (limitFormEnergy (GF n) u).toReal}
  let upper : Set ℝ := {a | ∀ n (u : DomainL2 (Q n)),
    u ∈ limitFormDomain (GE n) →
    (limitFormEnergy (GF n) u).toReal ≤ a * (limitFormEnergy (GE n) u).toReal}
  let m := sSup lower
  let M := sInf upper
  change IsLUB lower m ∧ IsGLB upper M ∧
    (C0⁻¹ ≤ m ∧ m ≤ M ∧ M ≤ C0) ∧ (m ∈ lower ∧ M ∈ upper)

  have hE_nonneg (n : ℕ) (u : DomainL2 (Q n)) :
      0 ≤ (limitFormEnergy (GE n) u).toReal :=
    EReal.toReal_nonneg (limitFormEnergy_nonneg (GE n) u)

  have hLower_mem : C0⁻¹ ∈ lower := by
    change ∀ n (u : DomainL2 (Q n)),
      u ∈ limitFormDomain (GE n) →
        C0⁻¹ * (limitFormEnergy (GE n) u).toReal ≤
          (limitFormEnergy (GF n) u).toReal
    intro n u hu
    exact (hcompare n u hu).1

  have hUpper_mem : C0 ∈ upper := by
    change ∀ n (u : DomainL2 (Q n)),
      u ∈ limitFormDomain (GE n) →
        (limitFormEnergy (GF n) u).toReal ≤
          C0 * (limitFormEnergy (GE n) u).toReal
    intro n u hu
    exact (hcompare n u hu).2

  have hLower_nonempty : lower.Nonempty := ⟨C0⁻¹, hLower_mem⟩
  have hUpper_nonempty : upper.Nonempty := ⟨C0, hUpper_mem⟩

  have hLower_bddAbove : BddAbove lower := by
    refine ⟨C0, ?_⟩
    intro a ha
    rcases hnonzero with ⟨n, u, hu, he⟩
    have ha' := ha n u hu
    have hC0' := (hcompare n u hu).2
    exact le_of_mul_le_mul_right (ha'.trans hC0') he

  have hUpper_bddBelow : BddBelow upper := by
    refine ⟨C0⁻¹, ?_⟩
    intro a ha
    rcases hnonzero with ⟨n, u, hu, he⟩
    have hC0' := (hcompare n u hu).1
    have ha' := ha n u hu
    exact le_of_mul_le_mul_right (hC0'.trans ha') he

  have hLUB : IsLUB lower m :=
    isLUB_csSup hLower_nonempty hLower_bddAbove
  have hGLB : IsGLB upper M :=
    isGLB_csInf hUpper_nonempty hUpper_bddBelow
  have hm_lower : C0⁻¹ ≤ m := le_csSup hLower_bddAbove hLower_mem
  have hM_upper : M ≤ C0 := csInf_le hUpper_bddBelow hUpper_mem

  have hcross : ∀ a ∈ lower, ∀ b ∈ upper, a ≤ b := by
    intro a ha b hb
    rcases hnonzero with ⟨n, u, hu, he⟩
    have ha' := ha n u hu
    have hb' := hb n u hu
    exact le_of_mul_le_mul_right (ha'.trans hb') he

  have hmM : m ≤ M := by
    refine csSup_le hLower_nonempty ?_
    intro a ha
    exact le_csInf hUpper_nonempty (fun b hb => hcross a ha b hb)

  have hm_mem : m ∈ lower := by
    change ∀ n (u : DomainL2 (Q n)),
      u ∈ limitFormDomain (GE n) →
        m * (limitFormEnergy (GE n) u).toReal ≤
          (limitFormEnergy (GF n) u).toReal
    intro n u hu
    let e : ℝ := (limitFormEnergy (GE n) u).toReal
    let f : ℝ := (limitFormEnergy (GF n) u).toReal
    change m * e ≤ f
    have hcomp : C0⁻¹ * e ≤ f ∧ f ≤ C0 * e := by
      simpa only [e, f] using hcompare n u hu
    have he0 : 0 ≤ e := by
      dsimp [e]
      exact hE_nonneg n u
    by_cases he : e = 0
    · have hf : 0 ≤ f := by simpa [he] using hcomp.1
      simpa [he] using hf
    · have hepos : 0 < e := lt_of_le_of_ne he0 (Ne.symm he)
      have hmdiv : m ≤ f / e := by
        refine csSup_le hLower_nonempty ?_
        intro a ha
        exact (le_div_iff₀ hepos).2 (ha n u hu)
      exact (le_div_iff₀ hepos).1 hmdiv

  have hM_mem : M ∈ upper := by
    change ∀ n (u : DomainL2 (Q n)),
      u ∈ limitFormDomain (GE n) →
        (limitFormEnergy (GF n) u).toReal ≤
          M * (limitFormEnergy (GE n) u).toReal
    intro n u hu
    let e : ℝ := (limitFormEnergy (GE n) u).toReal
    let f : ℝ := (limitFormEnergy (GF n) u).toReal
    change f ≤ M * e
    have hcomp : C0⁻¹ * e ≤ f ∧ f ≤ C0 * e := by
      simpa only [e, f] using hcompare n u hu
    have he0 : 0 ≤ e := by
      dsimp [e]
      exact hE_nonneg n u
    by_cases he : e = 0
    · have hf : f ≤ 0 := by simpa [he] using hcomp.2
      simpa [he] using hf
    · have hepos : 0 < e := lt_of_le_of_ne he0 (Ne.symm he)
      have hdivM : f / e ≤ M := by
        refine le_csInf hUpper_nonempty ?_
        intro a ha
        exact (div_le_iff₀ hepos).2 (ha n u hu)
      exact (div_le_iff₀ hepos).1 hdivM

  exact ⟨hLUB, hGLB, ⟨hm_lower, hmM, hM_upper⟩, ⟨hm_mem, hM_mem⟩⟩

end Paper
