module

public import SubdiffusiveProcess.Paper.lfgc_chart_compare

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Homogenization-error comparison for close charts

With `aux_lfgc_chart_compare_ChartsClose F F' κ ε` and `ε ≥ 0`, the finite-`q` paper homogenization error
(`q = 2`, `p = ∞`, discount `s`) satisfies, in `ℝ≥0∞`,
`E(F', κα)^2 ≤ e^ε · E(F, α)^2 + (e^ε - 1)`.
The proof compares the scalar probes cube by cube (`responseJ_scalar_compare`) and uses
that the geometric weights sum to one.  Deterministic.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02
open scoped ENNReal

namespace Paper
variable {d : ℕ}

theorem aux_lfgc_err_compare_originCube_scale_zero : (originCube d 0).scale = 0 := by
  simp [originCube]

/-- One-cube probe comparison. -/
theorem aux_lfgc_chart_compare_ChartsClose.probeMax_le {F F' : TriadicCoeffFamily d} {κ ε : ℝ} (hκ : 0 < κ)
    (hε : 0 ≤ ε) (h : aux_lfgc_chart_compare_ChartsClose F F' κ ε) (R : TriadicCube d)
    (hR : openCubeSet R ⊆ openCubeSet (originCube d 0)) (α : ℝ) (hα : 0 < α) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F' (κ * α) ≤
      ENNReal.ofReal (Real.exp ε) * SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F α +
        ENNReal.ofReal (Real.exp ε - 1) := by
  obtain ⟨hs, hs', hhi, hlo⟩ := h R hR
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax
  refine iSup_le fun e => ?_
  have hJ := responseJ_scalar_compare (U := cubeDomain R) (F'.coeffOn R) (F.coeffOn R) hs' hs
    κ ε hκ hε hhi hlo α hα e.1
  have hee : vecDot e.1 e.1 = 1 := e.2
  rw [hee, mul_one] at hJ
  have hexp : 0 ≤ Real.exp ε := (Real.exp_pos ε).le
  calc ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe R F' (κ * α) e.1)
      ≤ ENNReal.ofReal (Real.exp ε *
          SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe R F α e.1 + (Real.exp ε - 1)) :=
        ENNReal.ofReal_le_ofReal hJ
    _ ≤ ENNReal.ofReal (Real.exp ε * SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe R F α e.1) +
          ENNReal.ofReal (Real.exp ε - 1) := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (Real.exp ε) *
          ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe R F α e.1) +
          ENNReal.ofReal (Real.exp ε - 1) := by rw [ENNReal.ofReal_mul hexp]
    _ ≤ ENNReal.ofReal (Real.exp ε) * (⨆ e' : {e : SubdiffusiveProcess.CoarseGrainingVocab.Vec d //
            Homogenization.vecNormSq e = 1},
            ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe R F α e'.1)) +
          ENNReal.ofReal (Real.exp ε - 1) := by
        gcongr
        exact le_iSup (fun e' : {e : SubdiffusiveProcess.CoarseGrainingVocab.Vec d //
            Homogenization.vecNormSq e = 1} =>
          ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe R F α e'.1)) e

theorem aux_lfgc_err_compare_iSup_le_mul_add {ι : Sort*} (f g : ι → ℝ≥0∞) (c b : ℝ≥0∞)
    (h : ∀ i, f i ≤ c * g i + b) : (⨆ i, f i) ≤ c * (⨆ i, g i) + b := by
  refine iSup_le fun i => (h i).trans ?_
  gcongr
  exact le_iSup g i

theorem aux_lfgc_err_compare_rpow_half_rpow_two (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]; norm_num

theorem lfgc_err_compare (s : ℝ) (hs : 0 < s) :
    ∑' l : ℕ, ENNReal.ofReal (Book.Ch02.geometricWeight s 2 l) = 1 := by
  have h := Paper.aux_lem_band_U2_gw_tsum s hs
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => Paper.aux_lem_band_U2_gw_nonneg s hs.le n)
    h.summable, h.tsum_eq, ENNReal.ofReal_one]

/-- Squared homogenization-error comparison. -/
theorem aux_lfgc_chart_compare_ChartsClose.err_sq_le {F F' : TriadicCoeffFamily d} {κ ε : ℝ} (hκ : 0 < κ)
    (hε : 0 ≤ ε) (h : aux_lfgc_chart_compare_ChartsClose F F' κ ε) (s : ℝ) (hs : 0 < s) (α : ℝ) (hα : 0 < α) :
    (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite (originCube d 0) 0 s
        MultiscaleExponent.infinity 2 F' (κ * α)) ^ (2 : ℝ) ≤
      ENNReal.ofReal (Real.exp ε) *
        (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite (originCube d 0) 0 s
          MultiscaleExponent.infinity 2 F α) ^ (2 : ℝ) + ENNReal.ofReal (Real.exp ε - 1) := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
    SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale
  simp only [aux_lfgc_err_compare_rpow_half_rpow_two]
  set c := ENNReal.ofReal (Real.exp ε)
  set b := ENNReal.ofReal (Real.exp ε - 1)
  have hdesc : ∀ l : ℕ,
      SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale (originCube d 0) (0 - (l : ℤ)) F'
          (κ * α) ≤
        c * SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale (originCube d 0)
          (0 - (l : ℤ)) F α + b := by
    intro l
    unfold SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
    refine aux_lfgc_err_compare_iSup_le_mul_add _ _ c b fun R => ?_
    have hR : openCubeSet (R : TriadicCube d) ⊆ openCubeSet (originCube d 0) := by
      refine Paper.aux_lem_band_U2_desc_sub l R.1 ?_
      rw [aux_lfgc_err_compare_originCube_scale_zero]; exact R.2
    exact h.probeMax_le hκ hε R hR α hα
  have hsum : ∑' l : ℕ, ENNReal.ofReal (Book.Ch02.geometricWeight s 2 l) *
      SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale (originCube d 0) (0 - (l : ℤ)) F'
        (κ * α) ≤
      ∑' l : ℕ, (c * (ENNReal.ofReal (Book.Ch02.geometricWeight s 2 l) *
        SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale (originCube d 0) (0 - (l : ℤ)) F α) +
        ENNReal.ofReal (Book.Ch02.geometricWeight s 2 l) * b) := by
    refine ENNReal.tsum_le_tsum fun l => ?_
    calc ENNReal.ofReal (Book.Ch02.geometricWeight s 2 l) * _
        ≤ ENNReal.ofReal (Book.Ch02.geometricWeight s 2 l) * (c * _ + b) := by
          gcongr; exact hdesc l
      _ = _ := by ring
  refine hsum.trans ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
    lfgc_err_compare s hs, one_mul]

end Paper
