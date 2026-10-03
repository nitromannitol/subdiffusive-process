module

public import SubdiffusiveProcess.Static.AffineChart
public import SubdiffusiveProcess.Static.CutoffUnitCoercivity
public import SubdiffusiveProcess.Static.CutoffBlockComparison
public import SubdiffusiveProcess.Static.CubeCoercivityComparison
public import SubdiffusiveProcess.Frozen.Section3.AnnealedMatrixBounds
public import SubdiffusiveProcess.Static.InfraredComparison

@[expose] public section

/-! # Unit coercivity a bounded number of scales below a finite cutoff -/

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Static
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

private theorem ahom_antitone {d : ℕ} (M : GMCModel d) {j L : ℕ} (hjL : j ≤ L) :
    ahom M L ≤ ahom M j := by
  rcases hjL.eq_or_lt with h | h
  · exact h ▸ le_rfl
  · exact (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds.2 M L j h).1

/-- If the observation scale is at most J steps below the cutoff, the
matched-prefix coercivity and shell-block factor control the same unit cube. -/
theorem cutoff_unit_coercivity_with_block {d : ℕ} {M : GMCModel d} {L k : ℕ}
    (z : Vec d) (ω : PotentialSample d) {K : ℝ} (hK : 0 ≤ K)
    (h : cubeCoercivityEstimates
      (fun x => (ahom M (min L k))⁻¹ * aCutoff M (min L k)
        (translatePotentialSample z ω) ((3 : ℝ) ^ k • x)) 0 1 K) :
    cubeCoercivityEstimates
      (fun x => (ahom M L)⁻¹ * aCutoff M L
        (translatePotentialSample z ω) ((3 : ℝ) ^ k • x)) 0 1
      (K * cutoffBlockFactor M L (min L k) z ω) := by
  apply cubeCoercivityEstimates_of_comparison hK (one_le_cutoffBlockFactor _ _ _ _ _) _ h
  intro x hx
  rw [← unitCube_eq_ball] at hx
  have hjL : min L k ≤ L := min_le_left _ _
  have hhom := (inv_le_inv₀ (ahom_pos M (min L k)) (ahom_pos M L)).mpr
    (ahom_antitone M hjL)
  by_cases hLk : L ≤ k
  · rw [min_eq_left hLk]
    simp only [cutoffBlockFactor, lt_self_iff_false, ↓reduceIte, one_mul, le_refl]
  · have hkL : k ≤ L := le_of_lt (lt_of_not_ge hLk)
    rw [min_eq_right hkL] at hhom ⊢
    have hpoint : z + (3 : ℝ) ^ k • x - z ∈ openCubeSet (originCube d (k : ℤ)) := by
      rw [add_sub_cancel_left]
      rw [mem_openCubeSet_originCube_iff] at hx ⊢
      intro i
      have hxi := hx i
      simp only [Pi.smul_apply, smul_eq_mul, zpow_natCast]
      constructor <;> nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) k]
    have hb := (cutoffBlockFactor_comparison M hkL z ω hpoint).2
    simp only [aCutoff_translatePotentialSample]
    rw [add_comm ((3 : ℝ) ^ k • x) z]
    calc
      (ahom M k)⁻¹ * aCutoff M k ω (z + (3 : ℝ) ^ k • x) ≤
          (ahom M L)⁻¹ * aCutoff M k ω (z + (3 : ℝ) ^ k • x) :=
        mul_le_mul_of_nonneg_right hhom (aCutoff_pos M k ω _).le
      _ ≤ (ahom M L)⁻¹ * (cutoffBlockFactor M L k z ω *
          aCutoff M L ω (z + (3 : ℝ) ^ k • x)) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (ahom_pos M L).le)
      _ = _ := by ring

end SubdiffusiveProcess.Static
