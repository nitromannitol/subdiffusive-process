module

public import SubdiffusiveProcess.Paper.lem_band
public import SubdiffusiveProcess.Lfgc.CubeCompare

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Comparison of multiscale quantities of two close charts

`aux_lfgc_chart_compare_ChartsClose F F' κ ε`: on every triadic subcube of the unit root both charts are symmetric
and `e^{-ε} κ F ≤ F' ≤ e^{ε} κ F` in the Loewner order, almost everywhere.  Then
`lamF`, `LamF` of `F'` lie within `e^{±ε} κ` of those of `F`, the top-cube `σ` is sandwiched,
and the homogenization error satisfies `E(F', κα)² ≤ e^ε E(F, α)² + (e^ε - 1)`.
Deterministic; no law is used.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02
open scoped ENNReal

namespace SubdiffusiveProcess.Paper
variable {d : ℕ}

/-- Two triadic charts are multiplicatively `ε`-close after scaling by `κ`. -/
def aux_lfgc_chart_compare_ChartsClose (F F' : TriadicCoeffFamily d) (κ ε : ℝ) : Prop :=
  ∀ Q : TriadicCube d, openCubeSet Q ⊆ openCubeSet (originCube d 0) →
    CoeffOn.IsSymmetric (F.coeffOn Q) ∧ CoeffOn.IsSymmetric (F'.coeffOn Q) ∧
    (∀ᵐ x ∂ volume.restrict (openCubeSet Q),
      MatLoewnerLE ((F'.coeffOn Q).toCoeffField x)
        (Real.exp ε • (κ • (F.coeffOn Q).toCoeffField x))) ∧
    (∀ᵐ x ∂ volume.restrict (openCubeSet Q),
      MatLoewnerLE (Real.exp (-ε) • (κ • (F.coeffOn Q).toCoeffField x))
        ((F'.coeffOn Q).toCoeffField x))

theorem aux_lfgc_chart_compare_loewner_smul {A B : Mat d} (h : MatLoewnerLE A B) {c : ℝ} (hc : 0 ≤ c) :
    MatLoewnerLE (c • A) (c • B) := by
  intro v
  have := h v
  rw [quad_smul, quad_smul]
  nlinarith

theorem aux_lfgc_chart_compare_ChartsClose.symm {F F' : TriadicCoeffFamily d} {κ ε : ℝ} (hκ : 0 < κ)
    (h : aux_lfgc_chart_compare_ChartsClose F F' κ ε) : aux_lfgc_chart_compare_ChartsClose F' F κ⁻¹ ε := by
  intro Q hQ
  obtain ⟨hs, hs', hhi, hlo⟩ := h Q hQ
  refine ⟨hs', hs, ?_, ?_⟩
  · filter_upwards [hlo] with x hx
    have := aux_lfgc_chart_compare_loewner_smul hx (c := Real.exp ε * κ⁻¹) (by positivity)
    have e1 : (Real.exp ε * κ⁻¹) • (Real.exp (-ε) • (κ • (F.coeffOn Q).toCoeffField x)) =
        (F.coeffOn Q).toCoeffField x := by
      rw [smul_smul, smul_smul]
      have : Real.exp ε * κ⁻¹ * Real.exp (-ε) * κ = 1 := by
        rw [Real.exp_neg]; field_simp
      rw [this, one_smul]
    rw [e1] at this
    simpa [smul_smul, mul_comm] using this
  · filter_upwards [hhi] with x hx
    have := aux_lfgc_chart_compare_loewner_smul hx (c := Real.exp (-ε) * κ⁻¹) (by positivity)
    have e1 : (Real.exp (-ε) * κ⁻¹) • (Real.exp ε • (κ • (F.coeffOn Q).toCoeffField x)) =
        (F.coeffOn Q).toCoeffField x := by
      rw [smul_smul, smul_smul]
      have : Real.exp (-ε) * κ⁻¹ * Real.exp ε * κ = 1 := by
        rw [Real.exp_neg]; field_simp
      rw [this, one_smul]
    rw [e1] at this
    simpa [smul_smul, mul_comm] using this

theorem aux_lfgc_chart_compare_desc_sub' (n : ℕ) (R : TriadicCube d)
    (hR : R ∈ _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_D (d := d) n) :
    openCubeSet R ⊆ openCubeSet (originCube d 0) :=
  _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_desc_sub n R hR

/-- Cube-level norm comparisons from chart closeness. -/
theorem aux_lfgc_chart_compare_ChartsClose.norms {F F' : TriadicCoeffFamily d} {κ ε : ℝ} (hκ : 0 < κ)
    (h : aux_lfgc_chart_compare_ChartsClose F F' κ ε) (Q : TriadicCube d)
    (hQ : openCubeSet Q ⊆ openCubeSet (originCube d 0)) :
    coarseSigmaStarInvMatrixNorm Q F' ≤ Real.exp ε * κ⁻¹ * coarseSigmaStarInvMatrixNorm Q F ∧
    coarseBMatrixNorm Q F' ≤ Real.exp ε * κ * coarseBMatrixNorm Q F := by
  obtain ⟨hs, hs', hhi, hlo⟩ := h Q hQ
  have hn := sigma_norm_compare (U := cubeDomain Q) (F'.coeffOn Q) (F.coeffOn Q) hs' hs κ ε hκ
    hhi hlo
  have hb : ∀ G : TriadicCoeffFamily d, CoeffOn.IsSymmetric (G.coeffOn Q) →
      coarseBMatrixNorm Q G = matrixNorm (Book.Ch02.sigmaCoarse (cubeDomain Q) (G.coeffOn Q)) := by
    intro G hG
    unfold coarseBMatrixNorm
    rw [(responseSymmetricDirichletNeumannTheory (cubeDomain Q) (G.coeffOn Q) hG).derived_matrices.2.2]
  refine ⟨hn.2, ?_⟩
  rw [hb F' hs', hb F hs]
  exact hn.1

theorem aux_lfgc_chart_compare_sup'_le_mul_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f g : ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hfg : ∀ i ∈ s, f i ≤ c * g i) :
    s.sup' hs f ≤ c * s.sup' hs g := by
  refine Finset.sup'_le hs f fun i hi => (hfg i hi).trans ?_
  exact mul_le_mul_of_nonneg_left (Finset.le_sup' g hi) hc

theorem aux_lfgc_chart_compare_sup'_nonneg_of {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ s.sup' hs f := by
  obtain ⟨i, hi⟩ := hs
  exact (hf i hi).trans (Finset.le_sup' f hi)

/-- Series comparison with a summable dominating series. -/
theorem lfgc_chart_compare {f g : ℕ → ℝ} {c : ℝ} (_hc : 0 ≤ c) (hf : ∀ n, 0 ≤ f n)
    (hfg : ∀ n, f n ≤ c * g n) (hg : Summable g) :
    Summable f ∧ ∑' n, f n ≤ c * ∑' n, g n := by
  have hs : Summable f := Summable.of_nonneg_of_le hf hfg (hg.mul_left c)
  refine ⟨hs, ?_⟩
  rw [← tsum_mul_left]
  exact hs.tsum_le_tsum hfg (hg.mul_left c)

theorem aux_lfgc_chart_compare_summable_of_tsum_ne_zero {f : ℕ → ℝ} (h : ∑' n, f n ≠ 0) : Summable f := by
  by_contra hns
  exact h (tsum_eq_zero_of_not_summable hns)

/-- `lamF` lower comparison. -/
theorem aux_lfgc_chart_compare_ChartsClose.lamF_ge {F F' : TriadicCoeffFamily d} {κ ε : ℝ} (hκ : 0 < κ)
    (h : aux_lfgc_chart_compare_ChartsClose F F' κ ε) (sigma : ℝ) (hsigma : 0 < sigma)
    (hpos : 0 < _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F)
    (hpos' : 0 < _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F') :
    Real.exp (-ε) * κ * _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F ≤
      _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F' := by
  set g : ℕ → ℝ := fun n => Book.Ch02.geometricWeight sigma 2 n *
    (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_D (d := d) n).sup' (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_D_nonempty n)
      (fun R => coarseSigmaStarInvMatrixNorm R F) with hg
  set f : ℕ → ℝ := fun n => Book.Ch02.geometricWeight sigma 2 n *
    (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_D (d := d) n).sup' (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_D_nonempty n)
      (fun R => coarseSigmaStarInvMatrixNorm R F') with hf
  have hS := _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF_inv_eq sigma F
  have hS' := _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF_inv_eq sigma F'
  have hgs : Summable g := aux_lfgc_chart_compare_summable_of_tsum_ne_zero (by
    rw [← hS]; exact (inv_pos.mpr hpos).ne')
  have hc : 0 ≤ Real.exp ε * κ⁻¹ := by positivity
  have hcmp := lfgc_chart_compare hc (f := f) (g := g)
    (fun n => mul_nonneg (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_gw_nonneg sigma hsigma.le n)
      (aux_lfgc_chart_compare_sup'_nonneg_of _ _ _ fun R _ => norm_nonneg _))
    (fun n => by
      have hw := _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_gw_nonneg sigma hsigma.le n
      have := aux_lfgc_chart_compare_sup'_le_mul_sup' _ (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_D_nonempty n)
        (fun R => coarseSigmaStarInvMatrixNorm R F')
        (fun R => coarseSigmaStarInvMatrixNorm R F) hc
        (fun R hR => (h.norms hκ R (aux_lfgc_chart_compare_desc_sub' n R hR)).1)
      calc f n = Book.Ch02.geometricWeight sigma 2 n * _ := rfl
        _ ≤ Book.Ch02.geometricWeight sigma 2 n * (Real.exp ε * κ⁻¹ * _) :=
            mul_le_mul_of_nonneg_left this hw
        _ = Real.exp ε * κ⁻¹ * g n := by simp only [hg]; ring) hgs
  have h1 : (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F')⁻¹ ≤
      Real.exp ε * κ⁻¹ * (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F)⁻¹ := by
    rw [hS, hS']; exact hcmp.2
  have h2 := inv_anti₀ (inv_pos.mpr hpos') h1
  rw [inv_inv] at h2
  calc Real.exp (-ε) * κ * _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F
      = (Real.exp ε * κ⁻¹ * (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F)⁻¹)⁻¹ := by
        rw [Real.exp_neg]; field_simp
    _ ≤ _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F' := h2

/-- `lamF` upper comparison. -/
theorem aux_lfgc_chart_compare_ChartsClose.lamF_le {F F' : TriadicCoeffFamily d} {κ ε : ℝ} (hκ : 0 < κ)
    (h : aux_lfgc_chart_compare_ChartsClose F F' κ ε) (sigma : ℝ) (hsigma : 0 < sigma)
    (hpos : 0 < _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F)
    (hpos' : 0 < _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F') :
    _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F' ≤
      Real.exp ε * κ * _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F := by
  have := (h.symm hκ).lamF_ge (inv_pos.mpr hκ) sigma hsigma hpos' hpos
  have hk : 0 < Real.exp (-ε) * κ⁻¹ := by positivity
  calc _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F'
      = (Real.exp (-ε) * κ⁻¹)⁻¹ * (Real.exp (-ε) * κ⁻¹ * _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F') := by
        field_simp
    _ ≤ (Real.exp (-ε) * κ⁻¹)⁻¹ * _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F :=
        mul_le_mul_of_nonneg_left this (inv_pos.mpr hk).le
    _ = Real.exp ε * κ * _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma F := by
        rw [Real.exp_neg]; field_simp

/-- `LamF` upper comparison. -/
theorem aux_lfgc_chart_compare_ChartsClose.LamF_le {F F' : TriadicCoeffFamily d} {κ ε : ℝ} (hκ : 0 < κ)
    (h : aux_lfgc_chart_compare_ChartsClose F F' κ ε) (sigma : ℝ) (hsigma : 0 < sigma)
    (hpos : 0 < _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma F) :
    _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma F' ≤
      Real.exp ε * κ * _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma F := by
  rw [_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF_eq, _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF_eq]
  have hS := _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF_eq sigma F
  have hgs := aux_lfgc_chart_compare_summable_of_tsum_ne_zero (by rw [← hS]; exact hpos.ne')
  have hc : 0 ≤ Real.exp ε * κ := by positivity
  refine (lfgc_chart_compare hc
    (fun n => mul_nonneg (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_gw_nonneg sigma hsigma.le n)
      (aux_lfgc_chart_compare_sup'_nonneg_of _ _ _ fun R _ => norm_nonneg _))
    (fun n => ?_) hgs).2
  have hw := _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_gw_nonneg sigma hsigma.le n
  have := aux_lfgc_chart_compare_sup'_le_mul_sup' _ (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_D_nonempty n)
    (fun R => coarseBMatrixNorm R F') (fun R => coarseBMatrixNorm R F) hc
    (fun R hR => (h.norms hκ R (aux_lfgc_chart_compare_desc_sub' n R hR)).2)
  calc Book.Ch02.geometricWeight sigma 2 n * _ ≤ Book.Ch02.geometricWeight sigma 2 n * (Real.exp ε * κ * _) :=
        mul_le_mul_of_nonneg_left this hw
    _ = Real.exp ε * κ * (Book.Ch02.geometricWeight sigma 2 n * _) := by ring

/-- `LamF` lower comparison. -/
theorem aux_lfgc_chart_compare_ChartsClose.LamF_ge {F F' : TriadicCoeffFamily d} {κ ε : ℝ} (hκ : 0 < κ)
    (h : aux_lfgc_chart_compare_ChartsClose F F' κ ε) (sigma : ℝ) (hsigma : 0 < sigma)
    (hpos' : 0 < _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma F') :
    Real.exp (-ε) * κ * _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma F ≤
      _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma F' := by
  have := (h.symm hκ).LamF_le (inv_pos.mpr hκ) sigma hsigma hpos'
  have hk : 0 < Real.exp (-ε) * κ := by positivity
  calc Real.exp (-ε) * κ * _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma F
      ≤ Real.exp (-ε) * κ * (Real.exp ε * κ⁻¹ * _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma F') :=
        mul_le_mul_of_nonneg_left this hk.le
    _ = _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma F' := by
        rw [Real.exp_neg]; field_simp

/-- Top-cube `σ` sandwich. -/
theorem aux_lfgc_chart_compare_ChartsClose.sigma_top {F F' : TriadicCoeffFamily d} {κ ε : ℝ} (hκ : 0 < κ)
    (h : aux_lfgc_chart_compare_ChartsClose F F' κ ε) :
    MatLoewnerLE (Book.Ch02.sigmaCoarse (cubeDomain (originCube d 0)) (F'.coeffOn (originCube d 0)))
      (Real.exp ε • (κ • Book.Ch02.sigmaCoarse (cubeDomain (originCube d 0))
        (F.coeffOn (originCube d 0)))) ∧
    MatLoewnerLE (Real.exp (-ε) • (κ • Book.Ch02.sigmaCoarse (cubeDomain (originCube d 0))
        (F.coeffOn (originCube d 0))))
      (Book.Ch02.sigmaCoarse (cubeDomain (originCube d 0)) (F'.coeffOn (originCube d 0))) := by
  obtain ⟨hs, hs', hhi, hlo⟩ := h (originCube d 0) subset_rfl
  obtain ⟨h1, h2, -, -⟩ := coarse_sandwich (U := cubeDomain (originCube d 0))
    (F'.coeffOn (originCube d 0)) (F.coeffOn (originCube d 0)) hs' hs κ ε hκ hhi hlo
  exact ⟨h1, h2⟩

end SubdiffusiveProcess.Paper
