module

public import Mathlib
public import SubdiffusiveProcess.Gluing.CutoffDeriv
public import SubdiffusiveProcess.Gluing.Vanishing

@[expose] public section

/-!
# Gluing: the sum of the cutoffs of pairwise disjoint cubes
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section
namespace SubdiffusiveProcess.Gluing

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cube data: centres and half-side lengths. -/
abbrev gcCell (c : ι → Fin d → ℝ) (h : ι → ℝ) (i : ι) : Set (Fin d → ℝ) :=
  Metric.ball (c i) (h i)

/-- The sum of the cell cutoffs at relative width `δ`. -/
def gcS (c : ι → Fin d → ℝ) (h : ι → ℝ) (δ : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, gcTheta (c i) (h i) δ x

section
variable {c : ι → Fin d → ℝ} {h : ι → ℝ}

theorem gcTheta_eq_zero_of_notMem_cell (hh : ∀ i, 0 < h i) {δ : ℝ} (hδ : 0 < δ) {i : ι}
    {x : Fin d → ℝ} (hx : x ∉ gcCell c h i) : gcTheta (c i) (h i) δ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hxt => hx (tsupport_gcTheta_subset (hh i) hδ hxt)

/-- At a point of the cell `i` only the cutoff of the cell `i` is nonzero. -/
theorem gcS_eq_of_mem (hh : ∀ i, 0 < h i)
    (hdisj : Pairwise fun i k => Disjoint (gcCell c h i) (gcCell c h k)) {δ : ℝ} (hδ : 0 < δ)
    {i : ι} {x : Fin d → ℝ} (hx : x ∈ gcCell c h i) :
    gcS c h δ x = gcTheta (c i) (h i) δ x := by
  unfold gcS
  refine Finset.sum_eq_single i (fun k _ hki => ?_) (fun hi => absurd (Finset.mem_univ i) hi)
  exact gcTheta_eq_zero_of_notMem_cell hh hδ fun hk => (Set.disjoint_left.1 (hdisj hki.symm)) hx hk

theorem gcS_eq_zero_of_notMem (hh : ∀ i, 0 < h i) {δ : ℝ} (hδ : 0 < δ) {x : Fin d → ℝ}
    (hx : ∀ i, x ∉ gcCell c h i) : gcS c h δ x = 0 :=
  Finset.sum_eq_zero fun i _ => gcTheta_eq_zero_of_notMem_cell hh hδ (hx i)

theorem gcS_nonneg (x : Fin d → ℝ) (δ : ℝ) : 0 ≤ gcS c h δ x :=
  Finset.sum_nonneg fun i _ => gcTheta_nonneg _ _ _ _

theorem gcS_le_one (hh : ∀ i, 0 < h i)
    (hdisj : Pairwise fun i k => Disjoint (gcCell c h i) (gcCell c h k)) {δ : ℝ} (hδ : 0 < δ)
    (x : Fin d → ℝ) : gcS c h δ x ≤ 1 := by
  by_cases hx : ∃ i, x ∈ gcCell c h i
  · obtain ⟨i, hi⟩ := hx
    rw [gcS_eq_of_mem hh hdisj hδ hi]
    exact gcTheta_le_one _ _ _ _
  · push_neg at hx
    rw [gcS_eq_zero_of_notMem hh hδ hx]; exact zero_le_one

theorem gcS_contDiff (δ : ℝ) : ContDiff ℝ ∞ (gcS c h δ) := by
  unfold gcS
  exact ContDiff.sum fun i _ => gcTheta_contDiff _ _ _

theorem hasCompactSupport_gcS (hh : ∀ i, 0 < h i) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (gcS c h δ) := by
  unfold gcS
  refine HasCompactSupport.intro (K := ⋃ i, gcBox (c i) (h i) δ)
    (isCompact_iUnion fun i => isCompact_univ_pi fun k => isCompact_Icc) ?_
  intro x hx
  exact Finset.sum_eq_zero fun i _ =>
    gcTheta_eq_zero_of_notMem (hh i) hδ fun hxi => hx (mem_iUnion.2 ⟨i, hxi⟩)

theorem fderiv_gcS (δ : ℝ) (x v : Fin d → ℝ) :
    fderiv ℝ (gcS c h δ) x v = ∑ i, fderiv ℝ (gcTheta (c i) (h i) δ) x v := by
  unfold gcS
  rw [fderiv_fun_sum (fun i _ => ((gcTheta_contDiff (c i) (h i) δ).differentiable (by simp)) x)]
  simp

/-- Sequence version: the relative widths `1/(n+2)`. -/
def gcDelta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem gcDelta_pos (n : ℕ) : 0 < gcDelta n := by unfold gcDelta; positivity

theorem tendsto_gcDelta : Tendsto gcDelta atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall gcDelta_pos⟩
  unfold gcDelta
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (fun n => by positivity) (fun n => ?_)
  show 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1)
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem tendsto_gcS (hh : ∀ i, 0 < h i)
    (hdisj : Pairwise fun i k => Disjoint (gcCell c h i) (gcCell c h k))
    {x : Fin d → ℝ} (hx : ∃ i, x ∈ gcCell c h i) :
    Tendsto (fun n => gcS c h (gcDelta n) x) atTop (𝓝 1) := by
  obtain ⟨i, hi⟩ := hx
  have hev : ∀ᶠ n in atTop, gcTheta (c i) (h i) (gcDelta n) x = 1 :=
    tendsto_gcDelta.eventually (eventually_gcTheta_eq_one (hh i) hi)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with n hn
  rw [gcS_eq_of_mem hh hdisj (gcDelta_pos n) hi, hn]

/-- The uniform `L¹` bound of the partial derivatives of `gcS`. -/
theorem exists_integral_abs_fderiv_gcS_le (hh : ∀ i, 0 < h i) :
    ∃ C : ℝ, ∀ (δ : ℝ), 0 < δ → ∀ j : Fin d,
      ∫ x, |fderiv ℝ (gcS c h δ) x (Pi.single j 1)| ≤ C := by
  obtain ⟨T, hT0, hT⟩ := exists_deriv_st_bound
  refine ⟨∑ i, 2 * T * (2 * h i) ^ (d - 1), fun δ hδ j => ?_⟩
  have hint : ∀ i, Integrable fun x => |fderiv ℝ (gcTheta (c i) (h i) δ) x (Pi.single j 1)| := by
    intro i
    have hc : Continuous fun x => fderiv ℝ (gcTheta (c i) (h i) δ) x (Pi.single j 1) :=
      ((gcTheta_contDiff _ _ _).continuous_fderiv (by simp)).clm_apply continuous_const
    have hcs : HasCompactSupport fun x => fderiv ℝ (gcTheta (c i) (h i) δ) x (Pi.single j 1) :=
      (hasCompactSupport_gcTheta (hh i) hδ).fderiv_apply (𝕜 := ℝ) (Pi.single j 1)
    exact (hc.integrable_of_hasCompactSupport hcs).abs
  calc ∫ x, |fderiv ℝ (gcS c h δ) x (Pi.single j 1)|
      ≤ ∫ x, ∑ i, |fderiv ℝ (gcTheta (c i) (h i) δ) x (Pi.single j 1)| := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
          (integrable_finset_sum _ fun i _ => hint i) (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [fderiv_gcS]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∫ x, |fderiv ℝ (gcTheta (c i) (h i) δ) x (Pi.single j 1)| :=
        integral_finset_sum _ fun i _ => hint i
    _ ≤ ∑ i, 2 * T * (2 * h i) ^ (d - 1) :=
        Finset.sum_le_sum fun i _ => integral_abs_fderiv_gcTheta_le hT (hh i) hδ j

end

end SubdiffusiveProcess.Gluing
