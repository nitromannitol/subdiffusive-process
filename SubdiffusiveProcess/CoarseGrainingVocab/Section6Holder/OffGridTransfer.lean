module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.OffGridWindows
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Triangle

@[expose] public section

/-!
# Hölder Step 7: off-grid norm transfer

This file supplies the normalized-volume and affine-excess comparisons for
the cross-centre window sandwich.  The constants are the literal
dimension-only ratios coming from the established truncated-cube volume
bounds.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

/-- The usual truncated-cube volume ratio does not depend on the two window
centres. -/
theorem volume_ratio_truncatedCube_crossCentre_le
    {d : ℕ} {m j ell : ℤ} {x z : Vec d}
    (hx : x ∈ cube d m) (hz : z ∈ cube d m)
    (hjm : j - 1 ≤ m) (hellm : ell - 1 ≤ m) :
    (volume (truncatedCube d m ell z)).toReal /
        (volume (truncatedCube d m j x)).toReal ≤
      ((3 : ℝ) ^ (ell - j + 2)) ^ d := by
  obtain ⟨_, hhi⟩ := volume_toReal_truncatedCube_bounds z hz hellm
  obtain ⟨hlo, _⟩ := volume_toReal_truncatedCube_bounds x hx hjm
  have hjpos : (0 : ℝ) < ((3 : ℝ) ^ (j - 2)) ^ d := by positivity
  have hden : 0 < (volume (truncatedCube d m j x)).toReal :=
    lt_of_lt_of_le hjpos hlo
  have hquot : ((3 : ℝ) ^ ell) ^ d / ((3 : ℝ) ^ (j - 2)) ^ d =
      ((3 : ℝ) ^ (ell - j + 2)) ^ d := by
    rw [← div_pow, ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 2
    ring
  rw [← hquot, div_le_div_iff₀ hden hjpos]
  calc
    (volume (truncatedCube d m ell z)).toReal * ((3 : ℝ) ^ (j - 2)) ^ d ≤
        ((3 : ℝ) ^ ell) ^ d * ((3 : ℝ) ^ (j - 2)) ^ d :=
      mul_le_mul_of_nonneg_right hhi hjpos.le
    _ ≤ ((3 : ℝ) ^ ell) ^ d *
        (volume (truncatedCube d m j x)).toReal :=
      mul_le_mul_of_nonneg_left hlo (by positivity)

/-- Cross-centre normalized `L²` restriction along nested truncated windows. -/
theorem normalizedL2On_truncatedCube_crossCentre_le
    {d : ℕ} {m j ell : ℤ} {x z : Vec d} {f : Vec d → ℝ}
    (hx : x ∈ cube d m) (hz : z ∈ cube d m)
    (hjm : j - 1 ≤ m) (hellm : ell - 1 ≤ m)
    (hsub : truncatedCube d m j x ⊆ truncatedCube d m ell z)
    (hint : IntegrableOn (fun y ↦ f y ^ 2) (truncatedCube d m ell z)) :
    normalizedL2On (truncatedCube d m j x) f ≤
      Real.sqrt (((3 : ℝ) ^ (ell - j + 2)) ^ d) *
        normalizedL2On (truncatedCube d m ell z) f := by
  have hW : 0 < (volume (truncatedCube d m ell z)).toReal :=
    volume_toReal_truncatedCube_pos z hz hellm
  have hW' : 0 < (volume (truncatedCube d m j x)).toReal :=
    volume_toReal_truncatedCube_pos x hx hjm
  refine (normalizedL2On_le_of_subset hsub hW hW' hint).trans ?_
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt
      (volume_ratio_truncatedCube_crossCentre_le hx hz hjm hellm))
    (normalizedL2On_nonneg _ _)

/-- Cross-centre affine-excess restriction along nested truncated windows. -/
theorem excess_truncatedCube_crossCentre_le
    {d : ℕ} {m j ell : ℤ} {x z : Vec d}
    (hx : x ∈ cube d m) (hz : z ∈ cube d m)
    (hjm : j - 1 ≤ m) (hellm : ell - 1 ≤ m)
    (hsub : truncatedCube d m j x ⊆ truncatedCube d m ell z)
    {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedCube d m ell z))) :
    excess j (truncatedCube d m j x) u ≤
      (3 : ℝ) ^ (ell - j) *
        Real.sqrt (((3 : ℝ) ^ (ell - j + 2)) ^ d) *
          excess ell (truncatedCube d m ell z) u := by
  have hW : 0 < (volume (truncatedCube d m ell z)).toReal :=
    volume_toReal_truncatedCube_pos z hz hellm
  have hW' : 0 < (volume (truncatedCube d m j x)).toReal :=
    volume_toReal_truncatedCube_pos x hx hjm
  have hraw := affineExcessRaw_le_of_subset (u := u) hsub hW hW'
    (fun c g ↦ by
      exact (integrableOn_sub_affineEval_sq_truncatedCube z hu c g))
  have hratio : Real.sqrt
      ((volume (truncatedCube d m ell z)).toReal /
        (volume (truncatedCube d m j x)).toReal) ≤
      Real.sqrt (((3 : ℝ) ^ (ell - j + 2)) ^ d) :=
    Real.sqrt_le_sqrt
      (volume_ratio_truncatedCube_crossCentre_le hx hz hjm hellm)
  have hchain : affineExcessRaw (truncatedCube d m j x) u ≤
      Real.sqrt (((3 : ℝ) ^ (ell - j + 2)) ^ d) *
        affineExcessRaw (truncatedCube d m ell z) u :=
    hraw.trans (mul_le_mul_of_nonneg_right hratio
      (affineExcessRaw_nonneg _ _))
  have hzpow : (3 : ℝ) ^ (-j) =
      (3 : ℝ) ^ (ell - j) * (3 : ℝ) ^ (-ell) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  rw [excess_eq_affineExcessScaled, excess_eq_affineExcessScaled,
    affineExcessScaled, affineExcessScaled, hzpow]
  have hpos : 0 ≤ (3 : ℝ) ^ (ell - j) * (3 : ℝ) ^ (-ell) := by positivity
  calc
    (3 : ℝ) ^ (ell - j) * (3 : ℝ) ^ (-ell) *
        affineExcessRaw (truncatedCube d m j x) u ≤
      (3 : ℝ) ^ (ell - j) * (3 : ℝ) ^ (-ell) *
        (Real.sqrt (((3 : ℝ) ^ (ell - j + 2)) ^ d) *
          affineExcessRaw (truncatedCube d m ell z) u) :=
      mul_le_mul_of_nonneg_left hchain hpos
    _ = (3 : ℝ) ^ (ell - j) *
        Real.sqrt (((3 : ℝ) ^ (ell - j + 2)) ^ d) *
          ((3 : ℝ) ^ (-ell) *
            affineExcessRaw (truncatedCube d m ell z) u) := by ring

/-- The complete deterministic off-grid composition used in Step 7.  A grid
estimate from scale `n+1` to `ell-1` is transported to the literal
windows at scales `n` and `ell`; the middle oscillation is re-centered at the
outer window before restriction. -/
theorem exists_holderOffGridExcessTransfer
    {d m n ell : ℕ} {x : Vec d} {u : Vec d → ℝ} {A B D : ℝ}
    (hx : x ∈ cube d m) (hnell : n + 2 < ell) (hellm : ell ≤ m)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : MemLp u 2 (volume.restrict (truncatedCube d m ell x)))
    (hgrid : ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
      truncatedCube d m n x ⊆ truncatedCube d m (n + 1) z →
      truncatedCube d m ((ell : ℤ) - 1) z ⊆ truncatedCube d m ell x →
      excess (n + 1) (truncatedCube d m (n + 1) z) u ≤
        A * excess ((ell : ℤ) - 1) (truncatedCube d m ((ell : ℤ) - 1) z) u +
          B * normalizedL2On (truncatedCube d m ((ell : ℤ) - 1) z)
            (fun y ↦ u y - averageOn (truncatedCube d m ((ell : ℤ) - 1) z) u) + D) :
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
      excess n (truncatedCube d m n x) u ≤
        (3 * Real.sqrt (27 ^ d)) *
          (A * ((3 * Real.sqrt (27 ^ d)) *
                excess ell (truncatedCube d m ell x) u) +
            B * (Real.sqrt (27 ^ d) *
              normalizedL2On (truncatedCube d m ell x)
                (fun y ↦ u y - averageOn (truncatedCube d m ell x) u)) + D) := by
  obtain ⟨z, hzgrid, hz, hsubN, hsubMid, hsubEll⟩ :=
    exists_holderOffGridWindowSandwich hx (by omega) hnell
  refine ⟨z, hzgrid, hz, ?_⟩
  have hnm : (n : ℤ) - 1 ≤ (m : ℤ) := by omega
  have hn1m : ((n + 1 : ℕ) : ℤ) - 1 ≤ (m : ℤ) := by omega
  have hellPredM : ((ell : ℤ) - 1) - 1 ≤ (m : ℤ) := by omega
  have hellM : (ell : ℤ) - 1 ≤ (m : ℤ) := by omega
  have huPred : MemLp u 2
      (volume.restrict (truncatedCube d m ((ell : ℤ) - 1) z)) :=
    hu.mono_measure (Measure.restrict_mono hsubEll le_rfl)
  have huSucc : MemLp u 2
      (volume.restrict (truncatedCube d m (n + 1) z)) :=
    huPred.mono_measure (Measure.restrict_mono hsubMid le_rfl)
  have hinner := excess_truncatedCube_crossCentre_le hx hz hnm hn1m hsubN huSucc
  have houter := excess_truncatedCube_crossCentre_le hz hx hellPredM hellM
    hsubEll hu
  have hOuterSq : IntegrableOn
      (fun y ↦ (u y - averageOn (truncatedCube d m ell x) u) ^ 2)
      (truncatedCube d m ell x) :=
    integrableOn_sub_const_sq_truncatedCube x hu _
  have hrestrict := normalizedL2On_truncatedCube_crossCentre_le hz hx
    hellPredM hellM hsubEll hOuterSq
  have hpredPos : 0 <
      (volume (truncatedCube d m ((ell : ℤ) - 1) z)).toReal :=
    volume_toReal_truncatedCube_pos z hz hellPredM
  have hpredTop : volume (truncatedCube d m ((ell : ℤ) - 1) z) ≠ ⊤ :=
    ne_of_lt (volume_truncatedCube_lt_top d m ((ell : ℤ) - 1) z)
  have hmean : normalizedL2On (truncatedCube d m ((ell : ℤ) - 1) z)
        (fun y ↦ u y - averageOn (truncatedCube d m ((ell : ℤ) - 1) z) u) ≤
      normalizedL2On (truncatedCube d m ((ell : ℤ) - 1) z)
        (fun y ↦ u y - averageOn (truncatedCube d m ell x) u) := by
    exact normalizedL2On_sub_volumeAverage_le
      (measurableSet_truncatedCube d m ((ell : ℤ) - 1) z) hpredPos hpredTop
      (integrableOn_truncatedCube z huPred)
      (integrableOn_sub_const_sq_truncatedCube z huPred 0 |>.congr_fun
        (fun y ↦ by simp) (measurableSet_truncatedCube d m ((ell : ℤ) - 1) z)) _
  have hosc := hmean.trans hrestrict
  have hgrid' := hgrid z hzgrid hz hsubN hsubEll
  have hmiddle :
      A * excess ((ell : ℤ) - 1) (truncatedCube d m ((ell : ℤ) - 1) z) u +
          B * normalizedL2On (truncatedCube d m ((ell : ℤ) - 1) z)
            (fun y ↦ u y - averageOn (truncatedCube d m ((ell : ℤ) - 1) z) u) + D ≤
        A * ((3 * Real.sqrt (27 ^ d)) *
              excess ell (truncatedCube d m ell x) u) +
          B * (Real.sqrt (27 ^ d) *
            normalizedL2On (truncatedCube d m ell x)
              (fun y ↦ u y - averageOn (truncatedCube d m ell x) u)) + D := by
    have hfirst := mul_le_mul_of_nonneg_left (by
        simpa only [show (ell : ℤ) - ((ell : ℤ) - 1) = 1 by ring,
          show (ell : ℤ) - ((ell : ℤ) - 1) + 2 = 3 by ring] using houter) hA
    have hsecond := mul_le_mul_of_nonneg_left (by
        simpa only [show (ell : ℤ) - ((ell : ℤ) - 1) + 2 = 3 by ring]
          using hosc) hB
    norm_num at hfirst
    norm_num at hsecond
    exact add_le_add (add_le_add hfirst hsecond) le_rfl
  have hfactor : 0 ≤ 3 * Real.sqrt (27 ^ d) := by positivity
  calc
    excess n (truncatedCube d m n x) u ≤
        (3 * Real.sqrt (27 ^ d)) *
          excess (n + 1) (truncatedCube d m (n + 1) z) u := by
      rw [show ((n + 1 : ℕ) : ℤ) - (n : ℤ) = 1 by omega] at hinner
      norm_num at hinner
      exact hinner
    _ ≤ (3 * Real.sqrt (27 ^ d)) *
        (A * excess ((ell : ℤ) - 1) (truncatedCube d m ((ell : ℤ) - 1) z) u +
          B * normalizedL2On (truncatedCube d m ((ell : ℤ) - 1) z)
            (fun y ↦ u y - averageOn (truncatedCube d m ((ell : ℤ) - 1) z) u) + D) :=
      mul_le_mul_of_nonneg_left hgrid' hfactor
    _ ≤ _ := mul_le_mul_of_nonneg_left hmiddle hfactor

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
