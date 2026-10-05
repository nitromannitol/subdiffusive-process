module

public import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovDescendantMass

@[expose] public section

/-!
# One-cube cutoff-ratio negative-Besov estimate

This module performs the source shell split: coarse shells are reindexed by
their descendant gap and summed geometrically, while the retained fine shells
are counted by the descendant depth.
-/

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section


noncomputable def negativeBesovOneCubeConst (d : ℕ) : ℝ :=
  1 + negativeBesovFreshShellFinalConst d +
    16 * negativeBesovFreshShellFinalConst d *
    (negativeBesovMinGeomSumConst + 1) * (Real.log 2)⁻¹

noncomputable def negativeBesovOneCubeSmallConst (d : ℕ) : ℝ :=
  min (Real.log 2) (Real.log (3 / 2 : ℝ) ^ 2) /
    (negativeBesovFreshShellFinalConst d + 1)

theorem negativeBesovOneCubeConst_pos (d : ℕ) : 0 < negativeBesovOneCubeConst d := by
  unfold negativeBesovOneCubeConst
  have hC := negativeBesovFreshShellFinalConst_pos d
  have hK := negativeBesovMinGeomSumConst_pos
  have hb := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

theorem negativeBesovOneCubeSmallConst_pos (d : ℕ) : 0 < negativeBesovOneCubeSmallConst d := by
  unfold negativeBesovOneCubeSmallConst
  have hC := negativeBesovFreshShellFinalConst_pos d
  have hb := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha := Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)
  positivity

theorem negativeBesov_oneCube_smallness {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {p : ℝ} (hp : 2 ≤ p)
    (hsmall : p * M.delta ^ 2 * Real.log (2 + p) ≤ negativeBesovOneCubeSmallConst d) :
    let eps := negativeBesovFreshShellFinalConst d * p * M.delta ^ 2
    0 ≤ eps ∧
    eps ≤ Real.log 3 - Real.log (3 / 2 : ℝ) ∧
    eps * Real.log p ≤ Real.log (3 / 2 : ℝ) ^ 2 := by
  dsimp only
  let C := negativeBesovFreshShellFinalConst d
  let b := Real.log 2
  let a := Real.log (3 / 2 : ℝ)
  have hC : 0 < C := negativeBesovFreshShellFinalConst_pos d
  have hb : 0 < b := by dsimp [b]; exact Real.log_pos (by norm_num)
  have ha : 0 < a := by dsimp [a]; exact Real.log_pos (by norm_num)
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hlogp : 0 < Real.log p := Real.log_pos (lt_of_lt_of_le (by norm_num) hp)
  have hlogmono : Real.log p ≤ Real.log (2 + p) := by
    apply Real.log_le_log hp0
    linarith
  have hloglarge : 1 ≤ Real.log (2 + p) := by
    have h4 : (4 : ℝ) ≤ 2 + p := by linarith
    have hlog4 : Real.log 4 ≤ Real.log (2 + p) :=
      Real.log_le_log (by norm_num) h4
    have : (1 : ℝ) ≤ Real.log 4 := by
      rw [← Real.exp_le_exp]
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      exact (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 4)).le
    exact this.trans hlog4
  have ht : p * M.delta ^ 2 ≤ negativeBesovOneCubeSmallConst d := by
    calc
      p * M.delta ^ 2 ≤ p * M.delta ^ 2 * Real.log (2 + p) := by
        have : 0 ≤ p * M.delta ^ 2 := by positivity
        nlinarith
      _ ≤ _ := hsmall
  have hcC : C * negativeBesovOneCubeSmallConst d ≤ min b (a ^ 2) := by
    dsimp [negativeBesovOneCubeSmallConst]
    have hmin0 : 0 ≤ min b (a ^ 2) := by positivity
    calc
      C * (min b (a ^ 2) / (C + 1)) ≤
          (C + 1) * (min b (a ^ 2) / (C + 1)) := by
        gcongr
        linarith
      _ = min b (a ^ 2) := by field_simp [ne_of_gt (by linarith : 0 < C + 1)]
  have heps0 : 0 ≤ C * p * M.delta ^ 2 := by positivity
  refine ⟨heps0, ?_, ?_⟩
  · have hCb : C * p * M.delta ^ 2 ≤ b := by
      calc
        _ ≤ C * negativeBesovOneCubeSmallConst d := by
          have h := mul_le_mul_of_nonneg_left ht hC.le
          simpa [mul_assoc] using! h
        _ ≤ min b (a ^ 2) := hcC
        _ ≤ b := min_le_left _ _
    have hlog : b = Real.log 3 - Real.log (3 / 2 : ℝ) := by
      dsimp [b]
      rw [← Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
      norm_num
    rwa [← hlog]
  · have hprod : (C * p * M.delta ^ 2) * Real.log p ≤
        C * negativeBesovOneCubeSmallConst d := by
      calc
        _ ≤ C * (p * M.delta ^ 2 * Real.log (2 + p)) := by
          have hCp : 0 ≤ C * (p * M.delta ^ 2) := by positivity
          simpa [mul_assoc] using! mul_le_mul_of_nonneg_left hlogmono hCp
        _ ≤ C * negativeBesovOneCubeSmallConst d := by gcongr
    exact hprod.trans (hcC.trans (min_le_right _ _))

theorem negativeBesov_cutoffRatio_oneCube_moment {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {p : ℝ} (hp : 2 ≤ p)
    (hsmall : p * M.delta ^ 2 * Real.log (2 + p) ≤ negativeBesovOneCubeSmallConst d)
    (m : ℕ) (n : ℤ) (hn : -1 ≤ n) (hnm : n < (m : ℤ))
    (depth : ℕ) (R : TriadicCube d)
    (hR : R ∈ descendantsAtDepth (originCube d (m : ℤ)) depth) :
    paperLpNorm M.P.toMeasure p (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
        exactCircBlockMean R (cutoffRatioMinusOne M m n omega)
          ((cutoffRatioExactCircIntegrable M m n omega).block depth R hR)) ≤
      ENNReal.ofReal
        (negativeBesovOneCubeConst d * M.delta * Real.sqrt p * Real.log p *
          (1 + depth : ℕ) *
          Real.exp (negativeBesovOneCubeConst d * p * M.delta ^ 2 * (depth : ℝ))) := by
  let C := negativeBesovFreshShellFinalConst d
  let K := negativeBesovMinGeomSumConst
  let B := negativeBesovOneCubeConst d
  let eps := C * p * M.delta ^ 2
  let shells := cutoffShellIndices m n
  let coarse := shells.filter fun r : ℕ ↦ (r : ℤ) - 1 ≤ R.scale
  let fine := shells.filter fun r : ℕ ↦ R.scale < (r : ℤ) - 1
  let gap : ℕ → ℕ := fun r ↦ (R.scale - ((r : ℤ) - 1)).toNat
  have hC : 0 < C := negativeBesovFreshShellFinalConst_pos d
  have hK : 0 < K := negativeBesovMinGeomSumConst_pos
  have hB : 0 < B := negativeBesovOneCubeConst_pos d
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hlogp : 0 < Real.log p := Real.log_pos (lt_of_lt_of_le (by norm_num) hp)
  have hscale : R.scale = (m : ℤ) - (depth : ℤ) := by
    simpa only [originCube] using! scale_eq_sub_of_mem_descendantsAtDepth hR
  obtain ⟨heps0, hepsDecay, hepsLog⟩ := negativeBesov_oneCube_smallness M hp hsmall
  have hsplits : shells = coarse ∪ fine := by
    ext r
    simp only [Finset.mem_union]
    change r ∈ shells ↔
      r ∈ shells.filter (fun r : ℕ ↦ (r : ℤ) - 1 ≤ R.scale) ∨
      r ∈ shells.filter (fun r : ℕ ↦ R.scale < (r : ℤ) - 1)
    simp only [Finset.mem_filter]
    constructor
    · intro hrs
      by_cases h : (r : ℤ) - 1 ≤ R.scale
      · exact Or.inl ⟨hrs, h⟩
      · exact Or.inr ⟨hrs, lt_of_not_ge h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  have hdisj : Disjoint coarse fine := by
    rw [Finset.disjoint_left]
    intro r hrc hrf
    simp [coarse] at hrc
    simp [fine] at hrf
    omega
  have hshell_le (r : ℕ) (hr : r ∈ shells) : r ≤ m := by
    have h := (by simpa [shells, cutoffShellIndices] using! hr :
      (n + 1).toNat ≤ r ∧ r ≤ m)
    exact h.2
  have hcoarse_shell (r : ℕ) (hr : r ∈ coarse) : r ∈ shells := by
    change r ∈ shells.filter (fun r : ℕ ↦ (r : ℤ) - 1 ≤ R.scale) at hr
    exact (Finset.mem_filter.mp hr).1
  have hcoarse_pred (r : ℕ) (hr : r ∈ coarse) : (r : ℤ) - 1 ≤ R.scale := by
    change r ∈ shells.filter (fun r : ℕ ↦ (r : ℤ) - 1 ≤ R.scale) at hr
    exact (Finset.mem_filter.mp hr).2
  have hfine_shell (r : ℕ) (hr : r ∈ fine) : r ∈ shells := by
    change r ∈ shells.filter (fun r : ℕ ↦ R.scale < (r : ℤ) - 1) at hr
    exact (Finset.mem_filter.mp hr).1
  have hfine_pred (r : ℕ) (hr : r ∈ fine) : R.scale < (r : ℤ) - 1 := by
    change r ∈ shells.filter (fun r : ℕ ↦ R.scale < (r : ℤ) - 1) at hr
    exact (Finset.mem_filter.mp hr).2
  have hgapCast (r : ℕ) (hr : r ∈ coarse) :
      ((gap r : ℕ) : ℝ) = ((R.scale - ((r : ℤ) - 1) : ℤ) : ℝ) := by
    have hnonneg : 0 ≤ R.scale - ((r : ℤ) - 1) := by
      exact sub_nonneg.mpr (hcoarse_pred r hr)
    dsimp [gap]
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  have hage (r : ℕ) (hr : r ∈ coarse) :
      m + 1 - r = depth + gap r := by
    have hrs : r ∈ shells := hcoarse_shell r hr
    have hrm := hshell_le r hrs
    have hnonneg : 0 ≤ R.scale - ((r : ℤ) - 1) := by
      exact sub_nonneg.mpr (hcoarse_pred r hr)
    have hgapZ : (gap r : ℤ) = R.scale - ((r : ℤ) - 1) := by
      dsimp [gap]
      exact Int.toNat_of_nonneg hnonneg
    rw [hscale] at hgapZ
    omega
  have hgap_lt (r : ℕ) (hr : r ∈ coarse) : gap r < m + 2 := by
    have hr0 : (0 : ℤ) ≤ r := by exact_mod_cast Nat.zero_le r
    have hRm : R.scale ≤ (m : ℤ) := by rw [hscale]; omega
    have hnonneg : 0 ≤ R.scale - ((r : ℤ) - 1) := by
      exact sub_nonneg.mpr (hcoarse_pred r hr)
    have hgapZ : (gap r : ℤ) = R.scale - ((r : ℤ) - 1) := by
      dsimp [gap]
      exact Int.toNat_of_nonneg hnonneg
    omega
  have hgapInj : Set.InjOn gap (↑coarse : Set ℕ) := by
    intro r hr q hq heq
    have hrc := hcoarse_pred r hr
    have hqc := hcoarse_pred q hq
    have heqZ : (gap r : ℤ) = gap q := by exact_mod_cast heq
    have hgr : (gap r : ℤ) = R.scale - ((r : ℤ) - 1) := by
      dsimp [gap]
      exact Int.toNat_of_nonneg (by omega)
    have hgq : (gap q : ℤ) = R.scale - ((q : ℤ) - 1) := by
      dsimp [gap]
      exact Int.toNat_of_nonneg (by omega)
    omega
  have hkernelSum :
      ∑ r ∈ coarse,
          Real.exp (eps * gap r) *
            (Real.rpow 3 (-((d : ℝ) / 2) * (gap r : ℝ)) +
              min (p * Real.rpow 3
                (-(d : ℝ) * (1 - p⁻¹) * (gap r : ℝ))) 1) ≤
        4 * K * Real.log p := by
    let F : ℕ → ℝ := fun l ↦
      Real.exp (eps * l) *
        (Real.rpow 3 (-((d : ℝ) / 2) * (l : ℝ)) +
          min (p * Real.rpow 3
            (-(d : ℝ) * (1 - p⁻¹) * (l : ℝ))) 1)
    have himage : ∑ r ∈ coarse, F (gap r) =
        ∑ l ∈ coarse.image gap, F l := by
      rw [Finset.sum_image hgapInj]
    rw [show (∑ r ∈ coarse, Real.exp (eps * gap r) *
        (Real.rpow 3 (-((d : ℝ) / 2) * (gap r : ℝ)) +
          min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) * (gap r : ℝ))) 1)) =
        ∑ r ∈ coarse, F (gap r) by rfl, himage]
    calc
      ∑ l ∈ coarse.image gap, F l ≤ ∑ l ∈ Finset.range (m + 2), F l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro l hl
          simp only [Finset.mem_image] at hl
          obtain ⟨r, hr, rfl⟩ := hl
          exact Finset.mem_range.mpr (hgap_lt r hr)
        · intro l hl hli
          dsimp [F]
          positivity
      _ ≤ 4 * K * Real.log p := by
        exact sum_range_negativeBesov_sourceKernel_le_log
          M.shellPrefix.dimension hp heps0 hepsDecay hepsLog (m + 2)
  have hcoarseReal :
      ∑ r ∈ coarse,
          C * M.delta * Real.sqrt p *
            (Real.rpow 3 (-((d : ℝ) / 2) *
                ((R.scale - ((r : ℤ) - 1) : ℤ) : ℝ)) +
              min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) *
                ((R.scale - ((r : ℤ) - 1) : ℤ) : ℝ))) 1) *
            Real.exp (C * p * M.delta ^ 2 * ((m + 1 - r : ℕ) : ℝ)) ≤
        C * M.delta * Real.sqrt p * Real.exp (eps * depth) *
          (4 * K * Real.log p) := by
    calc
      _ = C * M.delta * Real.sqrt p * Real.exp (eps * depth) *
          ∑ r ∈ coarse,
            Real.exp (eps * gap r) *
              (Real.rpow 3 (-((d : ℝ) / 2) * (gap r : ℝ)) +
                min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) *
                  (gap r : ℝ))) 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        rw [hgapCast r hr, hage r hr]
        have hexparg : C * p * M.delta ^ 2 * ((depth + gap r : ℕ) : ℝ) =
            eps * (depth : ℝ) + eps * (gap r : ℝ) := by
          push_cast
          dsimp [eps]
          ring
        rw [hexparg, Real.exp_add]
        rw [← hgapCast r hr]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hkernelSum
        exact mul_nonneg
          (mul_nonneg (mul_nonneg hC.le M.shellPrefix.delta_pos.le)
            (Real.sqrt_nonneg p)) (Real.exp_pos _).le
  have hcoarse :
      ∑ r ∈ coarse,
          paperLpNorm M.P.toMeasure p (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
            ∫ x, cutoffFreshShellTerm M m r omega x
              ∂normalizedCubeMeasure R) ≤
        ENNReal.ofReal (C * M.delta * Real.sqrt p * Real.exp (eps * depth) *
          (4 * K * Real.log p)) := by
    calc
      _ ≤ ∑ r ∈ coarse, ENNReal.ofReal
          (C * M.delta * Real.sqrt p *
            (Real.rpow 3 (-((d : ℝ) / 2) *
                ((R.scale - ((r : ℤ) - 1) : ℤ) : ℝ)) +
              min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) *
                ((R.scale - ((r : ℤ) - 1) : ℤ) : ℝ))) 1) *
            Real.exp (C * p * M.delta ^ 2 * ((m + 1 - r : ℕ) : ℝ))) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrs : r ∈ shells := hcoarse_shell r hr
        have hrc : (r : ℤ) - 1 ≤ R.scale := hcoarse_pred r hr
        exact negativeBesov_freshShell_block_paperLpNorm_source
          M hp m r R (hshell_le r hrs) hrc (by rw [hscale]; omega)
      _ = ENNReal.ofReal (∑ r ∈ coarse,
          C * M.delta * Real.sqrt p *
            (Real.rpow 3 (-((d : ℝ) / 2) *
                ((R.scale - ((r : ℤ) - 1) : ℤ) : ℝ)) +
              min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) *
                ((R.scale - ((r : ℤ) - 1) : ℤ) : ℝ))) 1) *
            Real.exp (C * p * M.delta ^ 2 * ((m + 1 - r : ℕ) : ℝ))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro r hr
        have hpre : 0 ≤ C * M.delta * Real.sqrt p :=
          mul_nonneg (mul_nonneg hC.le M.shellPrefix.delta_pos.le)
            (Real.sqrt_nonneg p)
        have hshape : 0 ≤ Real.rpow 3 (-((d : ℝ) / 2) *
              ((R.scale - ((r : ℤ) - 1) : ℤ) : ℝ)) +
            min (p * Real.rpow 3 (-(d : ℝ) * (1 - p⁻¹) *
              ((R.scale - ((r : ℤ) - 1) : ℤ) : ℝ))) 1 := by
          apply add_nonneg (Real.rpow_nonneg (by norm_num) _)
          apply le_min
          · exact mul_nonneg hp0.le (Real.rpow_nonneg (by norm_num) _)
          · norm_num
        exact mul_nonneg (mul_nonneg hpre hshape) (Real.exp_pos _).le
      _ ≤ _ := ENNReal.ofReal_le_ofReal hcoarseReal
  have hfineAge (r : ℕ) (hr : r ∈ fine) : m + 1 - r ≤ depth := by
    have hrs : r ∈ shells := hfine_shell r hr
    have hrf : R.scale < (r : ℤ) - 1 := hfine_pred r hr
    have hrm := hshell_le r hrs
    rw [hscale] at hrf
    omega
  have hfineCard : fine.card ≤ depth + 1 := by
    let band := Finset.Icc (m + 1 - depth) m
    have hsub : fine ⊆ band := by
      intro r hr
      have hrs : r ∈ shells := hfine_shell r hr
      have hrm := hshell_le r hrs
      have hage := hfineAge r hr
      simp only [band, Finset.mem_Icc]
      omega
    calc
      fine.card ≤ band.card := Finset.card_le_card hsub
      _ ≤ depth + 1 := by
        dsimp [band]
        rw [Nat.card_Icc]
        omega
  have hfine :
      ∑ r ∈ fine,
          paperLpNorm M.P.toMeasure p (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
            ∫ x, cutoffFreshShellTerm M m r omega x
              ∂normalizedCubeMeasure R) ≤
        ENNReal.ofReal ((depth + 1 : ℕ) *
          (C * M.delta * Real.sqrt p * Real.exp (eps * depth))) := by
    calc
      _ ≤ ∑ _r ∈ fine, ENNReal.ofReal
          (C * M.delta * Real.sqrt p * Real.exp (eps * depth)) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrs : r ∈ shells := hfine_shell r hr
        have hraw := negativeBesov_freshShell_block_paperLpNorm_crude_source
          M R m r (hshell_le r hrs) hp
        apply hraw.trans
        apply ENNReal.ofReal_le_ofReal
        have hCcrude : negativeBesovFreshShellConst d ≤ C := by
          dsimp [C, negativeBesovFreshShellFinalConst]
          have hprod : 0 ≤ Real.rpow 3 ((d : ℝ) / 2) *
              freshShellSourceMomentConst :=
            mul_nonneg (Real.rpow_nonneg (by norm_num) _)
              freshShellSourceMomentConst_pos.le
          have htail : 0 ≤ Real.rpow 3 ((d : ℝ) / 2) *
              freshShellSourceMomentConst + 1 := by linarith
          change negativeBesovFreshShellConst d ≤
            negativeBesovFreshShellConst d +
              Real.rpow 3 ((d : ℝ) / 2) * freshShellSourceMomentConst + 1
          linarith
        have hexp : Real.exp (negativeBesovFreshShellConst d * p * M.delta ^ 2 *
            ((m + 1 - r : ℕ) : ℝ)) ≤ Real.exp (eps * depth) := by
          apply Real.exp_le_exp.mpr
          have ht0 : 0 ≤ p * M.delta ^ 2 := by positivity
          calc
            negativeBesovFreshShellConst d * p * M.delta ^ 2 *
                ((m + 1 - r : ℕ) : ℝ) ≤
              C * p * M.delta ^ 2 * ((m + 1 - r : ℕ) : ℝ) := by gcongr
            _ ≤ C * p * M.delta ^ 2 * (depth : ℝ) := by
              gcongr
              exact_mod_cast hfineAge r hr
            _ = eps * depth := by dsimp [eps]
        have hpref : negativeBesovFreshShellConst d * M.delta * Real.sqrt p ≤
            C * M.delta * Real.sqrt p := by
          have htail : 0 ≤ M.delta * Real.sqrt p :=
            mul_nonneg M.shellPrefix.delta_pos.le (Real.sqrt_nonneg p)
          simpa [mul_assoc] using! mul_le_mul_of_nonneg_right hCcrude htail
        exact mul_le_mul hpref hexp (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg hC.le M.shellPrefix.delta_pos.le)
            (Real.sqrt_nonneg p))
      _ = ENNReal.ofReal (∑ _r ∈ fine,
          (C * M.delta * Real.sqrt p * Real.exp (eps * depth))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro r hr
        exact mul_nonneg (mul_nonneg (mul_nonneg hC.le M.shellPrefix.delta_pos.le)
          (Real.sqrt_nonneg p)) (Real.exp_pos _).le
      _ = ENNReal.ofReal (fine.card *
          (C * M.delta * Real.sqrt p * Real.exp (eps * depth))) := by
        congr 1
        simp
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hconst : 0 ≤ C * M.delta * Real.sqrt p * Real.exp (eps * depth) :=
          mul_nonneg (mul_nonneg (mul_nonneg hC.le M.shellPrefix.delta_pos.le)
            (Real.sqrt_nonneg p)) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfineCard) hconst
  have hMink := paperLpNorm_exactCircBlockMean_cutoffRatio_le_sum_freshShell
    M m n hn hnm R hp (fun omega ↦
      (cutoffRatioExactCircIntegrable M m n omega).block depth R hR)
  change _ ≤ ∑ r ∈ shells,
    paperLpNorm M.P.toMeasure p (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
      ∫ x, cutoffFreshShellTerm M m r omega x
        ∂normalizedCubeMeasure R) at hMink
  rw [hsplits, Finset.sum_union hdisj] at hMink
  apply hMink.trans
  calc
    (∑ r ∈ coarse, paperLpNorm M.P.toMeasure p (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
        ∫ x, cutoffFreshShellTerm M m r omega x ∂normalizedCubeMeasure R)) +
      ∑ r ∈ fine, paperLpNorm M.P.toMeasure p (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
        ∫ x, cutoffFreshShellTerm M m r omega x ∂normalizedCubeMeasure R) ≤
      ENNReal.ofReal (C * M.delta * Real.sqrt p * Real.exp (eps * depth) *
          (4 * K * Real.log p)) +
        ENNReal.ofReal ((depth + 1 : ℕ) *
          (C * M.delta * Real.sqrt p * Real.exp (eps * depth))) :=
      add_le_add hcoarse hfine
    _ = ENNReal.ofReal
        (C * M.delta * Real.sqrt p * Real.exp (eps * depth) *
            (4 * K * Real.log p) +
          (depth + 1 : ℕ) *
            (C * M.delta * Real.sqrt p * Real.exp (eps * depth))) := by
      have hcommon : 0 ≤ C * M.delta * Real.sqrt p * Real.exp (eps * depth) :=
        mul_nonneg
          (mul_nonneg (mul_nonneg hC.le M.shellPrefix.delta_pos.le)
            (Real.sqrt_nonneg p)) (Real.exp_pos _).le
      rw [← ENNReal.ofReal_add]
      exact mul_nonneg hcommon
        (mul_nonneg (mul_nonneg (by norm_num) hK.le) hlogp.le)
      exact mul_nonneg (Nat.cast_nonneg _) hcommon
    _ ≤ ENNReal.ofReal
        (B * M.delta * Real.sqrt p * Real.log p * (1 + depth : ℕ) *
          Real.exp (B * p * M.delta ^ 2 * (depth : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      have hCB : C ≤ B := by
        dsimp [C, B, negativeBesovOneCubeConst]
        have htail : 0 ≤ 16 * negativeBesovFreshShellFinalConst d *
            (negativeBesovMinGeomSumConst + 1) * (Real.log 2)⁻¹ :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
            (negativeBesovFreshShellFinalConst_pos d).le) (by linarith [hK]))
            (inv_nonneg.mpr (Real.log_pos (by norm_num)).le)
        linarith
      have hlog2p : Real.log 2 ≤ Real.log p :=
        Real.log_le_log (by norm_num) hp
      have hfac : 4 * K + (Real.log 2)⁻¹ ≤
          16 * (K + 1) * (Real.log 2)⁻¹ := by
        have hb : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hb1 : Real.log 2 ≤ 1 := by
          have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          norm_num at h ⊢
          exact h
        have hbi : 1 ≤ (Real.log 2)⁻¹ := by
          rw [← one_div]
          apply (le_div_iff₀ hb).2
          simpa using! hb1
        nlinarith [hK]
      have hsum : 4 * K * Real.log p + (depth + 1 : ℕ) ≤
          (4 * K + (Real.log 2)⁻¹) * Real.log p * (1 + depth : ℕ) := by
        have hd0 : 0 ≤ (depth : ℝ) := Nat.cast_nonneg _
        have hone : 1 ≤ (1 + depth : ℕ) := by omega
        have hunit : (1 : ℝ) ≤ (Real.log 2)⁻¹ * Real.log p := by
          have hb : 0 < Real.log 2 := Real.log_pos (by norm_num)
          rw [← div_eq_inv_mul]
          apply (le_div_iff₀ hb).2
          simpa using! hlog2p
        push_cast at hone ⊢
        nlinarith [mul_nonneg hK.le hlogp.le]
      have hexp : Real.exp (eps * depth) ≤
          Real.exp (B * p * M.delta ^ 2 * (depth : ℝ)) := by
        apply Real.exp_le_exp.mpr
        dsimp [eps]
        gcongr
      have hcoef : C * (4 * K + (Real.log 2)⁻¹) ≤ B := by
        calc
          _ ≤ C * (16 * (K + 1) * (Real.log 2)⁻¹) := by gcongr
          _ ≤ 1 + 16 * C * (K + 1) * (Real.log 2)⁻¹ := by linarith
          _ ≤ B := by
            dsimp [B, negativeBesovOneCubeConst]
            linarith [hC]
      calc
        C * M.delta * Real.sqrt p * Real.exp (eps * depth) *
              (4 * K * Real.log p) +
            (depth + 1 : ℕ) *
              (C * M.delta * Real.sqrt p * Real.exp (eps * depth)) =
          C * M.delta * Real.sqrt p * Real.exp (eps * depth) *
            (4 * K * Real.log p + (depth + 1 : ℕ)) := by ring
        _ ≤ C * M.delta * Real.sqrt p * Real.exp (eps * depth) *
            ((4 * K + (Real.log 2)⁻¹) * Real.log p *
              (1 + depth : ℕ)) := by
          apply mul_le_mul_of_nonneg_left hsum
          exact mul_nonneg
            (mul_nonneg (mul_nonneg hC.le M.shellPrefix.delta_pos.le)
              (Real.sqrt_nonneg p)) (Real.exp_pos _).le
        _ = (C * (4 * K + (Real.log 2)⁻¹)) * M.delta * Real.sqrt p *
            Real.exp (eps * depth) * (Real.log p * (1 + depth : ℕ)) := by ring
        _ ≤ B * M.delta * Real.sqrt p * Real.exp (eps * depth) *
            (Real.log p * (1 + depth : ℕ)) := by
          have htail : 0 ≤ M.delta * Real.sqrt p * Real.exp (eps * depth) *
              (Real.log p * ((1 + depth : ℕ) : ℝ)) := by
            exact mul_nonneg
              (mul_nonneg (mul_nonneg M.shellPrefix.delta_pos.le
                (Real.sqrt_nonneg p)) (Real.exp_pos _).le)
              (mul_nonneg hlogp.le (Nat.cast_nonneg _))
          simpa [mul_assoc] using! mul_le_mul_of_nonneg_right hcoef htail
        _ ≤ B * M.delta * Real.sqrt p *
            Real.exp (B * p * M.delta ^ 2 * (depth : ℝ)) *
              (Real.log p * (1 + depth : ℕ)) := by
          have hpre : 0 ≤ B * M.delta * Real.sqrt p :=
            mul_nonneg (mul_nonneg hB.le M.shellPrefix.delta_pos.le)
              (Real.sqrt_nonneg p)
          have hpost : 0 ≤ Real.log p * ((1 + depth : ℕ) : ℝ) := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hexp hpre) le_rfl hpost
            (mul_nonneg hpre (Real.exp_pos _).le)
        _ = B * M.delta * Real.sqrt p * Real.log p *
            (1 + depth : ℕ) *
              Real.exp (B * p * M.delta ^ 2 * (depth : ℝ)) := by ring

end
end SubdiffusiveProcess.CoarseGrainingVocab
