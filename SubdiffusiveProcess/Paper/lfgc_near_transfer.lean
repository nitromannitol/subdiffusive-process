module

public import SubdiffusiveProcess.Paper.lfgc_near_tests

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Transfer of nearness between close charts, and the single-point tests

`aux_lfgc_near_tests_NearChart.transfer`: if `aux_lfgc_chart_compare_ChartsClose F F' κ ε` then `aux_lfgc_near_tests_NearChart σ F ref θ` implies
`aux_lfgc_near_tests_NearChart σ F' (κ * ref) (aux_lfgc_near_tests_tolTransfer ε θ)`.
`aux_lfgc_near_tests_NearChart.tests`: for `θ ≤ 1/(4d)` the chart passes the ellipticity window `[2/3, 3/2]`,
the coercivity test with constant `1/(2d)`, and the error bound.  Deterministic.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02
open scoped ENNReal

namespace Paper
variable {d : ℕ}

theorem aux_lfgc_near_transfer_le_tolTransfer_left (ε θ : ℝ) : Real.exp ε * (1 + θ) - 1 ≤ aux_lfgc_near_tests_tolTransfer ε θ :=
  le_max_left _ _

theorem aux_lfgc_near_transfer_le_tolTransfer_right (ε θ : ℝ) :
    Real.sqrt (Real.exp ε * θ ^ 2 + (Real.exp ε - 1)) ≤ aux_lfgc_near_tests_tolTransfer ε θ :=
  le_max_right _ _

/-- The error part of the transfer, in real numbers. -/
theorem lfgc_near_transfer {F F' : TriadicCoeffFamily d} {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε)
    (h : aux_lfgc_chart_compare_ChartsClose F F' κ ε) (σ : ℝ) (hσ : 0 < σ) (ref : ℝ) (href : 0 < ref)
    (hfin : SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite (originCube d 0) 0 σ
      MultiscaleExponent.infinity 2 F ref < ⊤)
    (hfin' : SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite (originCube d 0) 0 σ
      MultiscaleExponent.infinity 2 F' (κ * ref) < ⊤) {θ : ℝ} (hθ : 0 ≤ θ)
    (hE : Paper.aux_lem_band_U2_errF σ F ref ≤ θ) :
    Paper.aux_lem_band_U2_errF σ F' (κ * ref) ≤
      Real.sqrt (Real.exp ε * θ ^ 2 + (Real.exp ε - 1)) := by
  have hsq := h.err_sq_le hκ hε σ hσ ref href
  set E := SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite (originCube d 0) 0 σ
      MultiscaleExponent.infinity 2 F ref with hEdef
  set E' := SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite (originCube d 0) 0 σ
      MultiscaleExponent.infinity 2 F' (κ * ref) with hE'def
  have hEt : E ≠ ⊤ := hfin.ne
  have hE't : E' ≠ ⊤ := hfin'.ne
  have hexp : 0 ≤ Real.exp ε - 1 := by linarith [Real.one_le_exp hε]
  have hr := ENNReal.toReal_mono (by
      refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
        ENNReal.ofReal_ne_top⟩
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hEt) hsq
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hEt)) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos ε).le, ENNReal.toReal_ofReal hexp,
    ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at hr
  have h2 : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := fun x => by norm_cast
  rw [h2, h2] at hr
  have hE0 : 0 ≤ E.toReal := ENNReal.toReal_nonneg
  have hEθ : E.toReal ≤ θ := hE
  have hsqθ : E.toReal ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hE0 hEθ 2
  have hfinal : E'.toReal ^ 2 ≤ Real.exp ε * θ ^ 2 + (Real.exp ε - 1) := by
    have := mul_le_mul_of_nonneg_left hsqθ (Real.exp_pos ε).le
    linarith
  show E'.toReal ≤ _
  exact Real.le_sqrt_of_sq_le hfinal

/-- Nearness transfers between close charts. -/
theorem aux_lfgc_near_tests_NearChart.transfer {F F' : TriadicCoeffFamily d} {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε)
    (h : aux_lfgc_chart_compare_ChartsClose F F' κ ε) (σ : ℝ) (hσ : 0 < σ) (ref : ℝ) (href : 0 < ref)
    (hlam : 0 < Paper.aux_lem_band_U2_lamF σ F) (hlam' : 0 < Paper.aux_lem_band_U2_lamF σ F')
    (hLam : 0 < Paper.aux_lem_band_U2_LamF σ F) (hLam' : 0 < Paper.aux_lem_band_U2_LamF σ F')
    (hfin : SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite (originCube d 0) 0 σ
      MultiscaleExponent.infinity 2 F ref < ⊤)
    (hfin' : SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite (originCube d 0) 0 σ
      MultiscaleExponent.infinity 2 F' (κ * ref) < ⊤) {θ : ℝ} (hθ : 0 ≤ θ)
    (hn : aux_lfgc_near_tests_NearChart σ F ref θ) : aux_lfgc_near_tests_NearChart σ F' (κ * ref) (aux_lfgc_near_tests_tolTransfer ε θ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hn
  have hkr : 0 < κ * ref := mul_pos hκ href
  have hlo := h.lamF_ge hκ σ hσ hlam hlam'
  have hhi := h.lamF_le hκ σ hσ hlam hlam'
  have hLo := h.LamF_ge hκ σ hσ hLam'
  have hLhi := h.LamF_le hκ σ hσ hLam
  have hen := Real.exp_pos (-ε)
  have he := Real.exp_pos ε
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (aux_lfgc_near_tests_ratio_transfer hε hθ ?_ ?_ h1).trans (aux_lfgc_near_transfer_le_tolTransfer_left ε θ)
    · -- `e^{-ε} ref/lam ≤ κ ref / lam'`
      rw [le_div_iff₀ hlam']
      calc Real.exp (-ε) * (ref / Paper.aux_lem_band_U2_lamF σ F) *
            Paper.aux_lem_band_U2_lamF σ F'
          ≤ Real.exp (-ε) * (ref / Paper.aux_lem_band_U2_lamF σ F) *
            (Real.exp ε * κ * Paper.aux_lem_band_U2_lamF σ F) := by gcongr
        _ = κ * ref := by
            have : Real.exp (-ε) * Real.exp ε = 1 := by rw [← Real.exp_add]; simp
            rw [show Real.exp (-ε) * (ref / Paper.aux_lem_band_U2_lamF σ F) *
                (Real.exp ε * κ * Paper.aux_lem_band_U2_lamF σ F) =
                (Real.exp (-ε) * Real.exp ε) * (κ * ref) *
                (Paper.aux_lem_band_U2_lamF σ F / Paper.aux_lem_band_U2_lamF σ F) by ring,
              this, div_self hlam.ne']
            ring
    · rw [div_le_iff₀ hlam']
      calc κ * ref = Real.exp ε * (ref / Paper.aux_lem_band_U2_lamF σ F) *
            (Real.exp (-ε) * κ * Paper.aux_lem_band_U2_lamF σ F) := by
            have : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
            rw [show Real.exp ε * (ref / Paper.aux_lem_band_U2_lamF σ F) *
                (Real.exp (-ε) * κ * Paper.aux_lem_band_U2_lamF σ F) =
                (Real.exp ε * Real.exp (-ε)) * (κ * ref) *
                (Paper.aux_lem_band_U2_lamF σ F / Paper.aux_lem_band_U2_lamF σ F) by ring,
              this, div_self hlam.ne']
            ring
        _ ≤ Real.exp ε * (ref / Paper.aux_lem_band_U2_lamF σ F) *
            (Real.exp (-ε) * κ * Paper.aux_lem_band_U2_lamF σ F) := le_rfl
        _ ≤ Real.exp ε * (ref / Paper.aux_lem_band_U2_lamF σ F) *
            Paper.aux_lem_band_U2_lamF σ F' := by gcongr
  · refine (aux_lfgc_near_tests_ratio_transfer hε hθ ?_ ?_ h2).trans (aux_lfgc_near_transfer_le_tolTransfer_left ε θ)
    · rw [le_div_iff₀ hkr]
      calc Real.exp (-ε) * (Paper.aux_lem_band_U2_LamF σ F / ref) * (κ * ref)
          = Real.exp (-ε) * κ * Paper.aux_lem_band_U2_LamF σ F := by field_simp
        _ ≤ Paper.aux_lem_band_U2_LamF σ F' := hLo
    · rw [div_le_iff₀ hkr]
      calc Paper.aux_lem_band_U2_LamF σ F' ≤ Real.exp ε * κ * Paper.aux_lem_band_U2_LamF σ F := hLhi
        _ = Real.exp ε * (Paper.aux_lem_band_U2_LamF σ F / ref) * (κ * ref) := by field_simp
  · intro i j
    obtain ⟨hs1, hs2⟩ := h.sigma_top hκ
    set S := Book.Ch02.sigmaCoarse (cubeDomain (originCube d 0)) (F.coeffOn (originCube d 0))
    set S' := Book.Ch02.sigmaCoarse (cubeDomain (originCube d 0)) (F'.coeffOn (originCube d 0))
    set A : Mat d := ref⁻¹ • S
    set A' : Mat d := (κ * ref)⁻¹ • S'
    have hSs : S.IsSymm := Book.Ch02.sigmaCoarse_isSymm _ _
    have hS's : S'.IsSymm := Book.Ch02.sigmaCoarse_isSymm _ _
    have hAs : A.IsSymm := hSs.smul _
    have hA's : A'.IsSymm := hS's.smul _
    have hApos : ∀ v, 0 ≤ vecDot v (matVecMul A v) := by
      intro v; rw [quad_smul]
      exact mul_nonneg (inv_pos.mpr href).le (sigma_quad_nonneg _ v)
    have hAhi : ∀ v, vecDot v (matVecMul A' v) ≤ Real.exp ε * vecDot v (matVecMul A v) := by
      intro v
      have q := quad_le_of_loewner hs1 v
      rw [quad_smul, quad_smul] at q
      rw [quad_smul, quad_smul]
      rw [mul_inv]
      calc κ⁻¹ * ref⁻¹ * vecDot v (matVecMul S' v)
          ≤ κ⁻¹ * ref⁻¹ * (Real.exp ε * (κ * vecDot v (matVecMul S v))) := by
            gcongr
        _ = Real.exp ε * (ref⁻¹ * vecDot v (matVecMul S v)) := by field_simp
    have hAlo : ∀ v, Real.exp (-ε) * vecDot v (matVecMul A v) ≤ vecDot v (matVecMul A' v) := by
      intro v
      have q := quad_le_of_loewner hs2 v
      rw [quad_smul, quad_smul] at q
      rw [quad_smul, quad_smul]
      rw [mul_inv]
      calc Real.exp (-ε) * (ref⁻¹ * vecDot v (matVecMul S v))
          = κ⁻¹ * ref⁻¹ * (Real.exp (-ε) * (κ * vecDot v (matVecMul S v))) := by field_simp
        _ ≤ κ⁻¹ * ref⁻¹ * vecDot v (matVecMul S' v) := by gcongr
    have hAnear : ∀ i j, |A i j - (if i = j then (1 : ℝ) else 0)| ≤ θ := by
      intro i j
      have := h3 i j
      simpa [A, S, Paper.aux_lem_band_U2_sigF, Matrix.smul_apply, div_eq_inv_mul] using this
    have := lfgc_near_tests A A' hAs hA's hApos hε hθ hAhi hAlo hAnear i j
    refine le_trans ?_ ((aux_lfgc_near_transfer_le_tolTransfer_left ε θ).trans' this)
    simp [A', S', Paper.aux_lem_band_U2_sigF, Matrix.smul_apply, div_eq_inv_mul]
  · exact (lfgc_near_transfer hκ hε h σ hσ ref href hfin hfin' hθ h4).trans (aux_lfgc_near_transfer_le_tolTransfer_right ε θ)

end Paper
