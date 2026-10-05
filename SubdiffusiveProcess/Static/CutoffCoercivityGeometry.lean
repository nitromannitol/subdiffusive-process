module

public import SubdiffusiveProcess.Static.DyadicCoercivityAssembly
public import SubdiffusiveProcess.Static.AnchoredLawTransport
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Fixed geometry and dyadic side bounds for local coercivity -/

open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Static

theorem exists_coercivity_geometry {p : ℕ} (hp : 0 < p) (s0 s1 : Fin p → ℝ)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ (∀ i, a ≤ s0 i) ∧ (∀ i, s1 i ≤ b) := by
  classical
  let i0 : Fin p := ⟨0, hp⟩
  have hu : (Finset.univ : Finset (Fin p)).Nonempty := ⟨i0, Finset.mem_univ _⟩
  let a := (Finset.univ : Finset (Fin p)).inf' hu s0
  let b := (Finset.univ : Finset (Fin p)).sup' hu s1
  have ha : 0 < a := (Finset.lt_inf'_iff hu).mpr fun i _ => (hs i).1
  have h0 : ∀ i, a ≤ s0 i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have h1 : ∀ i, s1 i ≤ b := fun i => Finset.le_sup' _ (Finset.mem_univ i)
  exact ⟨a, b, ha, (h0 i0).trans ((hs i0).2.le.trans (h1 i0)), h0, h1⟩

theorem exists_coercivity_chart_scale {a b : ℝ} (ha : 0 < a) :
    ∃ J : ℕ, ((3 : ℝ) ^ J)⁻¹ < a ∧ b ≤ (3 : ℝ) ^ J := by
  obtain ⟨J, hJ⟩ := ((tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 3)).eventually (Filter.eventually_gt_atTop (max b a⁻¹))).exists
  refine ⟨J, ?_, ((le_max_left _ _).trans hJ.le)⟩
  have hi := (le_max_right b a⁻¹).trans_lt hJ
  exact (inv_lt_comm₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ J) ha).mpr hi

theorem dyadic_side_bounds {s0 s1 : ℝ} (hs : s0 ≤ s1) (n : ℕ)
    (k : Fin (2 ^ n + 1)) :
    s0 ≤ (1 - ((k : ℕ) : ℝ) / 2 ^ n) * s0 + (((k : ℕ) : ℝ) / 2 ^ n) * s1 ∧
      (1 - ((k : ℕ) : ℝ) / 2 ^ n) * s0 + (((k : ℕ) : ℝ) / 2 ^ n) * s1 ≤ s1 := by
  have hk : (k : ℕ) ≤ 2 ^ n := Nat.le_of_lt_succ k.isLt
  have hk' : ((k : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hk
  have hp : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hr0 : 0 ≤ (((k : ℕ) : ℝ) / 2 ^ n) := by positivity
  have hr1 : (((k : ℕ) : ℝ) / 2 ^ n) ≤ 1 := (div_le_one hp).mpr hk'
  constructor <;> nlinarith

end SubdiffusiveProcess.Static
