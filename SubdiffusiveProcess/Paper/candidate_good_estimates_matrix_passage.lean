import SubdiffusiveProcess.Paper.in_deterministic
import SubdiffusiveProcess.Paper.candidate_good_estimates_finite_bank_support
import SubdiffusiveProcess.Main.CutoffCoefficient

/-! Limiting chart matrices retain the finite ellipticity inequalities.
This module does not assert the analytic source or harmonic comparison estimates.
-/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- A normalized finite chart satisfies the spectral and quadratic bounds. -/
lemma aux_candidate_good_estimates_matrix_passage_chart_bounds
    {d : ℕ} [NeZero d] (I : Paper.in_J d) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (sNv : ℝ) (hsNv : 0 < sNv) :
    let lo := I.lam z r hr a z r sigma 2 / sNv
    let hi := I.Lam z r hr a z r sigma 2 / sNv
    let A := sNv⁻¹ • Homogenization.Book.Ch02.sigmaCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((I.chart z r hr a z r).coeffOn (Homogenization.originCube d 0))
    lo ≤ hi ∧ Matrix.trace A ≤ (d : ℝ) * hi ∧
      ∀ x : Fin d → ℝ, lo * (x ⬝ᵥ x) ≤ x ⬝ᵥ A.mulVec x := by
  dsimp only
  have hq : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have htr := aux_in_deterministic_matrix_bounds_trace_le (originCube d 0)
    (I.chart z r hr a z r) hsigma.1 aux_in_deterministic_matrix_bounds_two_admissible
  have hqd := aux_in_deterministic_matrix_bounds_quad_ge (originCube d 0)
    (I.chart z r hr a z r) hsigma.1 aux_in_deterministic_matrix_bounds_two_admissible
  rw [← I.Lam_eq z r hr a z r hr subset_rfl sigma hsigma 2 hq] at htr
  simp only [← I.lam_eq z r hr a z r hr subset_rfl sigma hsigma 2 hq] at hqd
  refine ⟨div_le_div_of_nonneg_right
    (aux_in_deterministic_matrix_bounds_chart_lam_le_Lam I sigma hsigma z r hr a)
    hsNv.le, ?_, ?_⟩
  · rw [Matrix.trace_smul, smul_eq_mul]
    calc sNv⁻¹ * _ ≤ sNv⁻¹ * ((d : ℝ) * I.Lam z r hr a z r sigma 2) :=
          mul_le_mul_of_nonneg_left htr (inv_nonneg.mpr hsNv.le)
      _ = _ := by ring
  · intro x
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    calc (I.lam z r hr a z r sigma 2 / sNv) * (x ⬝ᵥ x) =
        sNv⁻¹ * (I.lam z r hr a z r sigma 2 * (x ⬝ᵥ x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hqd x) (inv_nonneg.mpr hsNv.le)

/-- Convergent normalized charts retain their spectral and quadratic inequalities. -/
lemma aux_candidate_good_estimates_matrix_passage_chart_limit
    {d : ℕ} [NeZero d] (I : Paper.in_J d) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr)) (sNv lo hi : ℕ → ℝ)
    (A : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hlo : ∀ n, lo n = I.lam z r hr (a n) z r sigma 2 / sNv n)
    (hhi : ∀ n, hi n = I.Lam z r hr (a n) z r sigma 2 / sNv n)
    (hA : ∀ n, A n = (sNv n)⁻¹ • Homogenization.Book.Ch02.sigmaCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((I.chart z r hr (a n) z r).coeffOn (Homogenization.originCube d 0)))
    (loLim hiLim : ℝ) (ALim : Matrix (Fin d) (Fin d) ℝ)
    (hloLim : Tendsto lo atTop (𝓝 loLim))
    (hhiLim : Tendsto hi atTop (𝓝 hiLim))
    (hALim : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (ALim i j)))
    (hpos : 0 < loLim) :
    loLim ≤ hiLim ∧ Matrix.trace ALim ≤ (d : ℝ) * hiLim ∧
      ∀ x : Fin d → ℝ, loLim * (x ⬝ᵥ x) ≤ x ⬝ᵥ ALim.mulVec x := by
  have hposN : ∀ᶠ n in atTop, 0 < lo n := hloLim.eventually (lt_mem_nhds hpos)
  have hbounds : ∀ᶠ n in atTop,
      lo n ≤ hi n ∧ Matrix.trace (A n) ≤ (d : ℝ) * hi n ∧
        ∀ x : Fin d → ℝ, lo n * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A n).mulVec x := by
    filter_upwards [hposN] with n hn
    have hs : 0 < sNv n := by
      by_contra h
      have hle := div_nonpos_of_nonneg_of_nonpos
        (I.lam_pos z r hr (a n) z r sigma 2).le (le_of_not_gt h)
      rw [← hlo n] at hle
      exact (not_lt_of_ge hle) hn
    simpa only [← hlo n, ← hhi n, ← hA n] using
      aux_candidate_good_estimates_matrix_passage_chart_bounds I sigma hsigma z r hr (a n) (sNv n) hs
  have htrace : Tendsto (fun n => Matrix.trace (A n)) atTop (𝓝 (Matrix.trace ALim)) := by
    exact tendsto_finset_sum _ (fun i _ => hALim i i)
  refine ⟨le_of_tendsto_of_tendsto hloLim hhiLim (hbounds.mono fun n h => h.1),
    le_of_tendsto_of_tendsto htrace (tendsto_const_nhds.mul hhiLim)
      (hbounds.mono fun n h => h.2.1), ?_⟩
  intro x
  have hquad : Tendsto (fun n => x ⬝ᵥ (A n).mulVec x) atTop
      (𝓝 (x ⬝ᵥ ALim.mulVec x)) := by
    simp only [Matrix.mulVec, dotProduct]
    exact tendsto_finset_sum _ (fun i _ => tendsto_const_nhds.mul
      (tendsto_finset_sum _ (fun j _ => (hALim i j).mul tendsto_const_nhds)))
  exact le_of_tendsto_of_tendsto (hloLim.mul tendsto_const_nhds) hquad
    (hbounds.mono fun n h => h.2.2 x)

/-- Convergence in measure of finite chart entries yields almost sure limiting inequalities. -/
lemma aux_candidate_good_estimates_matrix_passage_chart_limit_ae
    {d : ℕ} [NeZero d] {Om : Type*} [MeasurableSpace Om] (P : Measure Om)
    (I : Paper.in_J d) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : ℕ → Om → PositiveCoefficient (centeredCube z r hr))
    (sNv lo hi : ℕ → Om → ℝ) (A : ℕ → Om → Matrix (Fin d) (Fin d) ℝ)
    (hlo : ∀ n omega, lo n omega = I.lam z r hr (a n omega) z r sigma 2 / sNv n omega)
    (hhi : ∀ n omega, hi n omega = I.Lam z r hr (a n omega) z r sigma 2 / sNv n omega)
    (hA : ∀ n omega, A n omega = (sNv n omega)⁻¹ • Homogenization.Book.Ch02.sigmaCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((I.chart z r hr (a n omega) z r).coeffOn (Homogenization.originCube d 0)))
    (loLim hiLim : Om → ℝ) (ALim : Om → Matrix (Fin d) (Fin d) ℝ)
    (hloLim : TendstoInMeasure P lo atTop loLim)
    (hhiLim : TendstoInMeasure P hi atTop hiLim)
    (hALim : ∀ i j, TendstoInMeasure P (fun n omega => A n omega i j) atTop
      (fun omega => ALim omega i j)) :
    ∀ᵐ omega ∂P, 0 < loLim omega →
      loLim omega ≤ hiLim omega ∧ Matrix.trace (ALim omega) ≤ (d : ℝ) * hiLim omega ∧
        ∀ x : Fin d → ℝ, loLim omega * (x ⬝ᵥ x) ≤
          x ⬝ᵥ (ALim omega).mulVec x := by
  let X : (Unit ⊕ (Unit ⊕ (Fin d × Fin d))) → ℕ → Om → ℝ := fun idx n omega =>
    Sum.elim (fun _ => lo n omega)
      (Sum.elim (fun _ => hi n omega) (fun ij => A n omega ij.1 ij.2)) idx
  let XL : (Unit ⊕ (Unit ⊕ (Fin d × Fin d))) → Om → ℝ := fun idx omega =>
    Sum.elim (fun _ => loLim omega)
      (Sum.elim (fun _ => hiLim omega) (fun ij => ALim omega ij.1 ij.2)) idx
  have hconv : ∀ idx, TendstoInMeasure P (X idx) atTop (XL idx) := by
    intro idx
    rcases idx with v | idx
    · exact hloLim
    · rcases idx with v | ij
      · exact hhiLim
      · exact hALim ij.1 ij.2
  obtain ⟨ns, _, hae⟩ := aux_candidate_good_estimates_finite_bank_support_finite_ae_subseq_fintype P X XL hconv
  filter_upwards [hae] with omega hlim
  intro hpos
  exact aux_candidate_good_estimates_matrix_passage_chart_limit I sigma hsigma z r hr
    (fun n => a (ns n) omega) (fun n => sNv (ns n) omega)
    (fun n => lo (ns n) omega) (fun n => hi (ns n) omega)
    (fun n => A (ns n) omega)
    (fun n => hlo (ns n) omega) (fun n => hhi (ns n) omega) (fun n => hA (ns n) omega)
    (loLim omega) (hiLim omega) (ALim omega)
    (hlim (Sum.inl ())) (hlim (Sum.inr (Sum.inl ())))
    (fun i j => hlim (Sum.inr (Sum.inr (i, j)))) hpos

/-- A calibrated constant converts the spectral chart bounds into trace coercivity. -/
lemma aux_candidate_good_estimates_matrix_passage_good_matrix_bounds
    {d : ℕ} (cell C lo hi : ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hcell : 0 < cell) (hC : 0 < C) (hCdim : (d : ℝ) ≤ C * cell ^ 2)
    (hlo : cell ≤ lo) (hhi : hi ≤ cell⁻¹)
    (htrace : Matrix.trace A ≤ (d : ℝ) * hi)
    (hquad : ∀ x : Fin d → ℝ, lo * (x ⬝ᵥ x) ≤ x ⬝ᵥ A.mulVec x) :
    ∀ x : Fin d → ℝ, C⁻¹ * Matrix.trace A * (x ⬝ᵥ x) ≤ x ⬝ᵥ A.mulVec x := by
  have htrace' : Matrix.trace A ≤ C * cell := by
    calc
      Matrix.trace A ≤ (d : ℝ) * hi := htrace
      _ ≤ (d : ℝ) * cell⁻¹ := mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg d)
      _ ≤ C * cell := by
        rw [← div_eq_mul_inv, div_le_iff₀ hcell]
        simpa only [pow_two, mul_assoc] using hCdim
  have hinv : C⁻¹ * Matrix.trace A ≤ cell := by
    calc
      _ ≤ C⁻¹ * (C * cell) := mul_le_mul_of_nonneg_left htrace' (inv_nonneg.mpr hC.le)
      _ = cell := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
  intro x
  have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  exact (mul_le_mul_of_nonneg_right (hinv.trans hlo) hxx).trans (hquad x)

/-- The upper chart scalar is comparable to the positive reference scale. -/
lemma aux_candidate_good_estimates_matrix_passage_good_normalization
    (cell C lo hi sE : ℝ) (hClo : C⁻¹ ≤ cell) (hChi : cell⁻¹ ≤ C)
    (hlo : cell ≤ lo) (hhi : hi ≤ cell⁻¹) (hlohi : lo ≤ hi) (hsE : 0 ≤ sE) :
    ∃ Uq : ℝ, Uq = hi * sE ∧ C⁻¹ * sE ≤ Uq ∧ Uq ≤ C * sE := by
  exact ⟨hi * sE, rfl, mul_le_mul_of_nonneg_right (hClo.trans (hlo.trans hlohi)) hsE,
    mul_le_mul_of_nonneg_right (hhi.trans hChi) hsE⟩

/-- Every represented root retains the normalized spectral and quadratic bounds almost surely. -/
theorem candidate_good_estimates_matrix_passage
  (d : ℕ)
  [NeZero d]
  (I : Paper.in_J d)
  (sigma : ℝ)
  (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
  (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
  (H : BilateralField d → C(SpatialCoordinates d, ℝ))
  (Ω : Type)
  [MeasurableSpace Ω]
  (P : Measure Ω)
  (env : PUnit → ℕ → Ω → BilateralField d)
  (Enl Shift : Type)
  (rootLevel : Enl × Shift → ℤ)
  (rootSide : Enl × Shift → ℝ)
  (rootCentre : Enl × Shift → SpatialCoordinates d)
  (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
  (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
  (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
  (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
        ellLoN N U omega =
          I.lam (rootCentre U) (rootSide U) (rootPos U)
            (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H omega N
              (rootCentre U) (rootPos U))
            (rootCentre U) (rootSide U) sigma 2 /
            sN N (rootLevel U) (rootCentre U) omega)
  (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
        ellHiN N U omega =
          I.Lam (rootCentre U) (rootSide U) (rootPos U)
            (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H omega N
              (rootCentre U) (rootPos U))
            (rootCentre U) (rootSide U) sigma 2 /
            sN N (rootLevel U) (rootCentre U) omega)
  (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
  (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
        AEN N U omega =
          (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
            Homogenization.Book.Ch02.sigmaCoarse
              (Homogenization.Book.Ch02.cubeDomain
                (Homogenization.originCube d 0))
              ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H omega N
                  (rootCentre U) (rootPos U))
                (rootCentre U) (rootSide U)).coeffOn
                (Homogenization.originCube d 0)))
  (phi : ℕ → ℕ)
  (ellLoLim ellHiLim : (Enl × Shift) → Ω → ℝ)
  (AE_Lim : (Enl × Shift) → Ω → Matrix (Fin d) (Fin d) ℝ)
  (hEllLoLim : ∀ (U : Enl × Shift),
        TendstoInMeasure P
          (fun n omega => ellLoN (phi n) U (env PUnit.unit n omega)) atTop (ellLoLim U))
  (hEllHiLim : ∀ (U : Enl × Shift),
        TendstoInMeasure P
          (fun n omega => ellHiN (phi n) U (env PUnit.unit n omega)) atTop (ellHiLim U))
  (hAELim : ∀ (U : Enl × Shift) (i j : Fin d),
        TendstoInMeasure P
          (fun n omega => AEN (phi n) U (env PUnit.unit n omega) i j) atTop
          (fun omega => AE_Lim U omega i j)) : ∀ Uroot : Enl × Shift, ∀ᵐ omega ∂P,
    0 < ellLoLim Uroot omega →
      ellLoLim Uroot omega ≤ ellHiLim Uroot omega ∧
      Matrix.trace (AE_Lim Uroot omega) ≤ (d : ℝ) * ellHiLim Uroot omega ∧
      ∀ x : Fin d → ℝ,
        ellLoLim Uroot omega * (x ⬝ᵥ x) ≤
          x ⬝ᵥ (AE_Lim Uroot omega).mulVec x := by
  intro Uroot
  exact aux_candidate_good_estimates_matrix_passage_chart_limit_ae P I sigma hsigma
    (rootCentre Uroot) (rootSide Uroot) (rootPos Uroot)
    (fun n omega => SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M H
      (env PUnit.unit n omega) (phi n) (rootCentre Uroot) (rootPos Uroot))
    (fun n omega => sN (phi n) (rootLevel Uroot) (rootCentre Uroot)
      (env PUnit.unit n omega))
    (fun n omega => ellLoN (phi n) Uroot (env PUnit.unit n omega))
    (fun n omega => ellHiN (phi n) Uroot (env PUnit.unit n omega))
    (fun n omega => AEN (phi n) Uroot (env PUnit.unit n omega))
    (fun n omega => hEllLoN (phi n) Uroot (env PUnit.unit n omega))
    (fun n omega => hEllHiN (phi n) Uroot (env PUnit.unit n omega))
    (fun n omega => hAEN (phi n) Uroot (env PUnit.unit n omega))
    (ellLoLim Uroot) (ellHiLim Uroot) (fun omega => AE_Lim Uroot omega)
    (hEllLoLim Uroot) (hEllHiLim Uroot)
    (fun i j => hAELim Uroot i j)

/-- Algebraic consequences of the limiting chart, independent of the analytic event. -/
lemma aux_candidate_good_estimates_matrix_passage_algebraic_ae
    {d : ℕ} {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (cell C : ℝ) (hcell : 0 < cell) (hC : 0 < C)
    (hClo : C⁻¹ ≤ cell) (hChi : cell⁻¹ ≤ C) (hCdim : (d : ℝ) ≤ C * cell ^ 2)
    (lo hi : ι → Ω → ℝ) (A : ι → Ω → Matrix (Fin d) (Fin d) ℝ)
    (s : Ω → ℝ) (qRoot : ι)
    (hChart : ∀ i, ∀ᵐ omega ∂P, 0 < lo i omega →
      lo i omega ≤ hi i omega ∧ Matrix.trace (A i omega) ≤ (d : ℝ) * hi i omega ∧
      ∀ x : Fin d → ℝ, lo i omega * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A i omega).mulVec x)
    (hs : ∀ᵐ omega ∂P, 0 ≤ s omega) :
    ∀ᵐ omega ∂P, (∀ i, cell ≤ lo i omega ∧ hi i omega ≤ cell⁻¹) →
      (∀ (i : ι) (x : Fin d → ℝ),
        C⁻¹ * Matrix.trace (A i omega) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A i omega).mulVec x) ∧
      (∃ Uq : ℝ, Uq = hi qRoot omega * s omega ∧
        C⁻¹ * s omega ≤ Uq ∧ Uq ≤ C * s omega) := by
  have hAll : ∀ᵐ omega ∂P, ∀ i, 0 < lo i omega →
      lo i omega ≤ hi i omega ∧ Matrix.trace (A i omega) ≤ (d : ℝ) * hi i omega ∧
      ∀ x : Fin d → ℝ, lo i omega * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A i omega).mulVec x :=
    ae_all_iff.2 hChart
  filter_upwards [hAll, hs] with omega hchart hs0
  intro hBounds
  constructor
  · intro i x
    have hLocal := hchart i (hcell.trans_le (hBounds i).1)
    exact aux_candidate_good_estimates_matrix_passage_good_matrix_bounds cell C
      (lo i omega) (hi i omega) (A i omega) hcell hC hCdim
      (hBounds i).1 (hBounds i).2 hLocal.2.1 hLocal.2.2 x
  · have hLocal := hchart qRoot (hcell.trans_le (hBounds qRoot).1)
    exact aux_candidate_good_estimates_matrix_passage_good_normalization cell C
      (lo qRoot omega) (hi qRoot omega) (s omega) hClo hChi
      (hBounds qRoot).1 (hBounds qRoot).2 hLocal.1 hs0

end Paper
