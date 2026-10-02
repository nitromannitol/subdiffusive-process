import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lane3.Forms
import Mathlib.Algebra.Order.Group.Bounds
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- paragraph "A near-extremal member", paper lines 3837-3841 (inventory row
35): for each `k` a member `i_k` with `f_{i_k}(4k) >= F_{4k} - 1/k`, and the
consequence that on the window `k <= n <= 4k` the member's defect is within
`F_k - F_{4k} + 1/k` of its value at `4k`, which tends to zero.

This is the supplier of the hypothesis `hnear` of `mfd:thm-eta` and of the
trace bound used in `mfd:lem-conc`. -/
theorem near_extremal_member
    (f : ℕ → ℕ → ℝ) (Fk : ℕ → ℝ)
    (hmono : ∀ i k : ℕ, f i (k + 1) ≤ f i k)
    (hFk : ∀ k : ℕ, IsLUB (Set.range fun i => f i k) (Fk k))
    (hFmono : Antitone Fk) (eta : ℝ)
    (hFconv : Tendsto Fk atTop (𝓝 eta)) :
    ∃ idx : ℕ → ℕ,
      (∀ n : ℕ, 1 ≤ n → Fk (4 * n) - (n : ℝ)⁻¹ ≤ f (idx n) (4 * n)) ∧
      (∀ (n m : ℕ), 1 ≤ n → n ≤ m → m ≤ 4 * n →
        0 ≤ f (idx n) m - f (idx n) (4 * n) ∧
          f (idx n) m - f (idx n) (4 * n) ≤
            Fk m - Fk (4 * n) + (n : ℝ)⁻¹ ∧ Fk m - Fk (4 * n) + (n : ℝ)⁻¹ ≤ Fk n - Fk (4 * n) + (n : ℝ)⁻¹) ∧
      Tendsto (fun n : ℕ => Fk n - Fk (4 * n) + (n : ℝ)⁻¹) atTop (𝓝 0) := by
  have hnear : ∀ n : ℕ, 1 ≤ n →
      ∃ i : ℕ, Fk (4 * n) - (n : ℝ)⁻¹ ≤ f i (4 * n) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    obtain ⟨x, hx, hxlower, _⟩ :=
      (hFk (4 * n)).exists_between_sub_self (inv_pos.mpr hnpos)
    rcases hx with ⟨i, rfl⟩
    exact ⟨i, hxlower.le⟩
  let idx : ℕ → ℕ := fun n =>
    if hn : 1 ≤ n then Classical.choose (hnear n hn) else 0
  have hidx : ∀ n : ℕ, 1 ≤ n →
      Fk (4 * n) - (n : ℝ)⁻¹ ≤ f (idx n) (4 * n) := by
    intro n hn
    dsimp [idx]
    rw [dif_pos hn]
    exact Classical.choose_spec (hnear n hn)
  have hfantitone : ∀ i : ℕ, Antitone (f i) := by
    intro i
    exact antitone_nat_of_succ_le (hmono i)
  refine ⟨idx, ?_, ?_, ?_⟩
  · exact hidx
  · intro n m hn hnm hm4
    have hlow : f (idx n) (4 * n) ≤ f (idx n) m :=
      hfantitone (idx n) hm4
    have hupp : f (idx n) m ≤ Fk m :=
      (hFk m).1 ⟨idx n, rfl⟩
    have hsel := hidx n hn
    have hFm : Fk m ≤ Fk n := hFmono hnm
    constructor
    · linarith
    constructor
    · linarith
    · linarith
  · have hfour : Tendsto (fun n : ℕ => 4 * n) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [eventually_ge_atTop b] with n hn
      omega
    have hF4 : Tendsto (fun n : ℕ => Fk (4 * n)) atTop (𝓝 eta) :=
      hFconv.comp hfour
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using (hFconv.sub hF4).add hinv

end Paper
