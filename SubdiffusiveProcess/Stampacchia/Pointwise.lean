module

public import Mathlib

@[expose] public section

/-!
# Stampacchia: a limit of scalar multiples of a vector is a scalar multiple of it
-/

open Filter Topology
noncomputable section
namespace SubdiffusiveProcess.Stampacchia

theorem pointwise_theta {ι : Type*} [Fintype ι] (g ξ : ι → ℝ) (θ : ℕ → ℝ)
    (hθ : ∀ j, |θ j| ≤ 1) (hlim : ∀ i, Tendsto (fun j => θ j * g i) atTop (𝓝 (ξ i))) :
    |(if ∑ i, g i ^ 2 = 0 then 0 else (∑ i, ξ i * g i) / (∑ i, g i ^ 2))| ≤ 1 ∧
      ∀ i, ξ i = (if ∑ i, g i ^ 2 = 0 then 0 else (∑ i, ξ i * g i) / (∑ i, g i ^ 2)) * g i := by
  classical
  by_cases hz : ∑ i, g i ^ 2 = 0
  · have hg : ∀ i, g i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (g i))).1 hz i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    rw [if_pos hz]
    refine ⟨by simp, fun i => ?_⟩
    have h1 := hlim i
    simp only [hg i, mul_zero] at h1
    have := tendsto_nhds_unique h1 tendsto_const_nhds
    rw [hg i, mul_zero]; exact this.symm ▸ rfl
  · rw [if_neg hz]
    have hpos : 0 < ∑ i, g i ^ 2 := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Ne.symm hz)
    set t := (∑ i, ξ i * g i) / (∑ i, g i ^ 2) with ht
    have hθt : Tendsto θ atTop (𝓝 t) := by
      have hs : Tendsto (fun j => ∑ i, (θ j * g i) * g i) atTop (𝓝 (∑ i, ξ i * g i)) :=
        tendsto_finset_sum _ fun i _ => (hlim i).mul_const (g i)
      have := hs.div_const (∑ i, g i ^ 2)
      refine this.congr fun j => ?_
      have : ∑ i, (θ j * g i) * g i = θ j * ∑ i, g i ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]; field_simp
    refine ⟨le_of_tendsto (hθt.abs) (Eventually.of_forall hθ), fun i => ?_⟩
    exact tendsto_nhds_unique (hlim i) (hθt.mul_const (g i))

end SubdiffusiveProcess.Stampacchia
