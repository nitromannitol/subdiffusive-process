module

public import Mathlib
public import Homogenization.Sobolev.H1.Definitions
public import SubdiffusiveProcess.Gluing.CellIdentity
public import SubdiffusiveProcess.Gluing.CutoffSum

@[expose] public section

/-!
# Gluing: summing the cell identities

`∫ W S ∂_jφ + ∫ W φ ∂_jS = - ∫ G S φ` for the sum `S = ∑ θ_i` of the cell cutoffs, where the glued
gradient `G` is the sum of the cell gradients extended by zero.
-/

open MeasureTheory Set Filter Topology Homogenization
open scoped ContDiff
noncomputable section
namespace SubdiffusiveProcess.Gluing

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `j`-th component of the glued gradient: cell gradients, extended by zero. -/
def gluedGrad (c : ι → Fin d → ℝ) (h : ι → ℝ) (u : ∀ i, H1Function (gcCell c h i)) (j : Fin d)
    (x : Fin d → ℝ) : ℝ :=
  ∑ i, (gcCell c h i).indicator (fun y => (u i).grad y j) x

section
variable {c : ι → Fin d → ℝ} {h : ι → ℝ}

omit [DecidableEq ι] in
theorem gluedGrad_eq_of_mem [_instPreserved0 : DecidableEq ι] {c : ι → Fin d → ℝ} {h : ι → ℝ} (hdisj : Pairwise fun i k => Disjoint (gcCell c h i) (gcCell c h k))
    (u : ∀ i, H1Function (gcCell c h i)) (j : Fin d) {i : ι} {x : Fin d → ℝ}
    (hx : x ∈ gcCell c h i) : gluedGrad c h u j x = (u i).grad x j := by
  unfold gluedGrad
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hx]
  · intro k _ hki
    exact Set.indicator_of_notMem (fun hk => (Set.disjoint_left.1 (hdisj hki.symm)) hx hk) _
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [DecidableEq ι] in
theorem gluedGrad_eq_zero_of_notMem [_instPreserved0 : DecidableEq ι] {c : ι → Fin d → ℝ} {h : ι → ℝ} (u : ∀ i, H1Function (gcCell c h i)) (j : Fin d)
    {x : Fin d → ℝ} (hx : ∀ i, x ∉ gcCell c h i) : gluedGrad c h u j x = 0 :=
  Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (hx i) _

/-- The pointwise identity `G · S = ∑ g_i θ_i`. -/
theorem gluedGrad_mul_gcS (hh : ∀ i, 0 < h i)
    (hdisj : Pairwise fun i k => Disjoint (gcCell c h i) (gcCell c h k))
    (u : ∀ i, H1Function (gcCell c h i)) (j : Fin d) {δ : ℝ} (hδ : 0 < δ) (x : Fin d → ℝ) :
    gluedGrad c h u j x * gcS c h δ x = ∑ i, (u i).grad x j * gcTheta (c i) (h i) δ x := by
  by_cases hx : ∃ i, x ∈ gcCell c h i
  · obtain ⟨i, hi⟩ := hx
    rw [gluedGrad_eq_of_mem hdisj u j hi, gcS_eq_of_mem hh hdisj hδ hi]
    rw [Finset.sum_eq_single i]
    · intro k _ hki
      rw [gcTheta_eq_zero_of_notMem_cell hh hδ (fun hk => (Set.disjoint_left.1 (hdisj hki.symm)) hi hk),
        mul_zero]
    · intro hi'; exact absurd (Finset.mem_univ i) hi'
  · push Not at hx
    rw [gluedGrad_eq_zero_of_notMem u j hx, zero_mul]
    exact (Finset.sum_eq_zero fun i _ => by
      rw [gcTheta_eq_zero_of_notMem_cell hh hδ (hx i), mul_zero]).symm

/-- **The summed cell identity.** -/
theorem sum_identity (hh : ∀ i, 0 < h i)
    (hdisj : Pairwise fun i k => Disjoint (gcCell c h i) (gcCell c h k))
    (u : ∀ i, H1Function (gcCell c h i)) {W : (Fin d → ℝ) → ℝ} (hWc : Continuous W)
    (hW : ∀ i, ∀ x ∈ gcCell c h i, W x = (u i).toFun x)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (j : Fin d)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ x, W x * (gcS c h δ x * fderiv ℝ φ x (Pi.single j 1))) +
      (∫ x, W x * (φ x * fderiv ℝ (gcS c h δ) x (Pi.single j 1))) =
      -∫ x, gluedGrad c h u j x * (gcS c h δ x * φ x) := by
  have hcφ' : Continuous fun x => fderiv ℝ φ x (Pi.single j 1) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs' : HasCompactSupport fun x => fderiv ℝ φ x (Pi.single j 1) :=
    hφc.fderiv_apply (𝕜 := ℝ) (Pi.single j 1)
  have hθc : ∀ i, HasCompactSupport (gcTheta (c i) (h i) δ) := fun i =>
    hasCompactSupport_gcTheta (hh i) hδ
  have hθ : ∀ i, ContDiff ℝ ∞ (gcTheta (c i) (h i) δ) := fun i => gcTheta_contDiff _ _ _
  have hcθ' : ∀ i, Continuous fun x => fderiv ℝ (gcTheta (c i) (h i) δ) x (Pi.single j 1) :=
    fun i => ((hθ i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hcsθ' : ∀ i, HasCompactSupport fun x => fderiv ℝ (gcTheta (c i) (h i) δ) x (Pi.single j 1) :=
    fun i => (hθc i).fderiv_apply (𝕜 := ℝ) (Pi.single j 1)
  -- integrability of the pieces
  have iA : ∀ i, Integrable fun x => W x * (gcTheta (c i) (h i) δ x * fderiv ℝ φ x (Pi.single j 1)) :=
    fun i => (hWc.mul ((hθ i).continuous.mul hcφ')).integrable_of_hasCompactSupport
      ((hθc i).mul_right.mul_left)
  have iB : ∀ i, Integrable fun x => W x * (φ x * fderiv ℝ (gcTheta (c i) (h i) δ) x (Pi.single j 1)) :=
    fun i => (hWc.mul (hφ.continuous.mul (hcθ' i))).integrable_of_hasCompactSupport
      ((hcsθ' i).mul_left.mul_left)
  have iC : ∀ i, Integrable fun x => (u i).grad x j * (gcTheta (c i) (h i) δ x * φ x) := by
    intro i
    have hind : (fun x => (u i).grad x j * (gcTheta (c i) (h i) δ x * φ x)) =
        (gcCell c h i).indicator (fun x => (u i).grad x j * (gcTheta (c i) (h i) δ x * φ x)) := by
      funext x
      by_cases hx : x ∈ gcCell c h i
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, gcTheta_eq_zero_of_notMem_cell hh hδ hx]; simp
    rw [hind, integrable_indicator_iff Metric.isOpen_ball.measurableSet]
    have : IsFiniteMeasure (volume.restrict (gcCell c h i)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hgi : Integrable (fun x => (u i).grad x j) (volume.restrict (gcCell c h i)) :=
      ((u i).gradMemL2 j).integrable one_le_two
    have hbd : Continuous fun x => gcTheta (c i) (h i) δ x * φ x := (hθ i).continuous.mul hφ.continuous
    obtain ⟨B, hB⟩ := hbd.bounded_above_of_compact_support (hθc i).mul_right
    exact hgi.mul_bdd hbd.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using hB x)
  have hcell := fun i => cell_identity (hh i) hδ (u i) hWc (hW i) hφ hφc j
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset ι) = Finset.univ) fun i _ => hcell i
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hsum
  rw [← integral_finsetSum _ (fun i _ => iA i), ← integral_finsetSum _ (fun i _ => iB i),
    ← integral_finsetSum _ (fun i _ => iC i)] at hsum
  have e1 : (fun x => ∑ i, W x * (gcTheta (c i) (h i) δ x * fderiv ℝ φ x (Pi.single j 1))) =
      fun x => W x * (gcS c h δ x * fderiv ℝ φ x (Pi.single j 1)) := by
    funext x; unfold gcS; rw [Finset.sum_mul, Finset.mul_sum]
  have e2 : (fun x => ∑ i, W x * (φ x * fderiv ℝ (gcTheta (c i) (h i) δ) x (Pi.single j 1))) =
      fun x => W x * (φ x * fderiv ℝ (gcS c h δ) x (Pi.single j 1)) := by
    funext x; rw [fderiv_gcS, Finset.mul_sum, Finset.mul_sum]
  have e3 : (fun x => ∑ i, (u i).grad x j * (gcTheta (c i) (h i) δ x * φ x)) =
      fun x => gluedGrad c h u j x * (gcS c h δ x * φ x) := by
    funext x
    have hG := gluedGrad_mul_gcS hh hdisj u j hδ x
    calc ∑ i, (u i).grad x j * (gcTheta (c i) (h i) δ x * φ x)
        = (∑ i, (u i).grad x j * gcTheta (c i) (h i) δ x) * φ x := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = gluedGrad c h u j x * (gcS c h δ x * φ x) := by rw [← hG]; ring
  rw [e1, e2, e3] at hsum
  exact hsum

end

end SubdiffusiveProcess.Gluing
