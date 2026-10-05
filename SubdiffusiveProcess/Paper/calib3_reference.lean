module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib3_HT
public import SubdiffusiveProcess.Paper.prop_growth_trunc_energy_assembly
public import SubdiffusiveProcess.Paper.prop_growth_trunc_bank

@[expose] public section

/-! Stage 3 (calibration): the reference factor `exp ‖HT_j|_K‖` of the top-block-removed potential on the unit cube is measurable
and has every finite moment (`HT_j = -log(ahom_{j-1} A^0_{j-1}) - jτ²`, so it is dominated by the envelope
`Mx_{j-1}` of `aux_prop_growth_trunc_energy_assembly_root_extremes` at `L0 = 0`).  Analogue of
`aux_prop_growth_trunc_bank_reference`. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Pointwise: `|HT_j(x)| ≤ log Mx + |log ahom_{j-1}| + j|τ²|` when `Mx⁻¹ ≤ A^0_{j-1}(x) ≤ Mx`. -/
theorem aux_calib3_reference_sup_bound {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (hj : 0 < j)
    (om : BilateralField d) (x : SpatialCoordinates d) (Mx : ℝ) (hMx : 0 < Mx)
    (hb : Mx⁻¹ ≤ cutoffCoefficient M (fun om' => infraredPartialSum om' 0) om (j - 1) x ∧
      cutoffCoefficient M (fun om' => infraredPartialSum om' 0) om (j - 1) x ≤ Mx) :
    |calib3_HT d j om x| ≤
      Real.log Mx + |Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (j - 1))| + (j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P| := by
  have hle : Mx⁻¹ ≤ Mx := hb.1.trans hb.2
  have hMx1 : 1 ≤ Mx := by
    by_contra h
    push Not at h
    have hlt : 1 < Mx⁻¹ := (one_lt_inv₀ hMx).2 h
    linarith
  set S : ℝ := ∑ i ∈ Finset.range j, om (-(Int.ofNat i)) x with hSdef
  set A : ℝ := cutoffCoefficient M (fun om' => infraredPartialSum om' 0) om (j - 1) x with hA
  have hApos : 0 < A := lt_of_lt_of_le (inv_pos.mpr hMx) hb.1
  have hlogA_le : Real.log A ≤ Real.log Mx := Real.log_le_log hApos hb.2
  have hlogA_ge : -Real.log Mx ≤ Real.log A := by
    have h := Real.log_le_log (inv_pos.mpr hMx) hb.1
    rwa [Real.log_inv] at h
  have habs_logA : |Real.log A| ≤ Real.log Mx := abs_le.2 ⟨hlogA_ge, hlogA_le⟩
  have hj1 : j - 1 + 1 = j := by omega
  have hcast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
    have h := Nat.cast_pred (R := ℝ) hj
    rw [h]; ring
  have hcp : cutoffPotential (fun om' : BilateralField d => infraredPartialSum om' 0) om (j - 1) x = S := by
    rw [cutoffPotential, hj1]
    simp [infraredPartialSum, hSdef]
  have hlogA : Real.log A = -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (j - 1)) +
      (S - (j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
    rw [hA, cutoffCoefficient,
      Real.log_mul (inv_ne_zero (ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (j - 1)))) (Real.exp_ne_zero _),
      Real.log_inv, Real.log_exp, hcp, hcast]
  have hht : calib3_HT d j om x = -S := by
    rw [calib3_HT]
    simp only [ContinuousMap.neg_apply, ContinuousMap.coe_sum, Finset.sum_apply]
    rw [hSdef]
  have hS_eq : S = Real.log A + Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (j - 1)) +
      (j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P := by linarith
  rw [hht, abs_neg]
  calc |S| = |Real.log A + Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (j - 1)) +
        (j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P| := by rw [hS_eq]
    _ ≤ |Real.log A + Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (j - 1))| +
        |(j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P| := abs_add_le _ _
    _ ≤ (|Real.log A| + |Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (j - 1))|) +
        |(j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P| := by
        linarith [abs_add_le (Real.log A) (Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (j - 1)))]
    _ ≤ (Real.log Mx + |Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (j - 1))|) +
        (j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P| := by
        have h2 : |(j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P| =
            (j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P| := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
        linarith [habs_logA, le_of_eq h2]

/-- The exponentiated sup norm of `HT_j` on the closed unit cube is measurable. -/
theorem aux_calib3_reference_measurable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (j : ℕ) (z : SpatialCoordinates d) :
    Measurable (fun om : BilateralField d =>
      aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) z 1 one_pos) := by
  unfold aux_prop_growth_trunc_bank_refFactor calib3_HT
  have hc : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
      Real.exp ‖f.restrict (closedCube z 1 one_pos : Set (SpatialCoordinates d))‖) :=
    Real.continuous_exp.comp (continuous_norm.comp
      (ContinuousMap.continuous_restrict (closedCube z 1 one_pos : Set (SpatialCoordinates d))))
  have hcont : Continuous (fun om : BilateralField d =>
      -(∑ i ∈ Finset.range j, om (-(Int.ofNat i)))) :=
    continuous_neg.comp (continuous_finsetSum (Finset.range j) (fun i _ => continuous_apply _))
  exact hc.measurable.comp hcont.measurable

/-- The exponential of the sup norm is dominated by `e^{b} · Mx` whenever `|HT_j| ≤ log Mx + b` on the cube. -/
theorem aux_calib3_reference_dom {d : ℕ} (f : C(SpatialCoordinates d, ℝ)) (z : SpatialCoordinates d) (Mx b : ℝ)
    (hMx : 1 ≤ Mx) (hb : 0 ≤ b)
    (h : ∀ x ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)), |f x| ≤ Real.log Mx + b) :
    aux_prop_growth_trunc_bank_refFactor f z 1 one_pos ≤ Real.exp b * Mx := by
  unfold aux_prop_growth_trunc_bank_refFactor
  have hlog : (0 : ℝ) ≤ Real.log Mx + b :=
    add_nonneg (Real.log_nonneg hMx) hb
  have hnorm : ‖f.restrict (closedCube z 1 one_pos : Set (SpatialCoordinates d))‖ ≤
      Real.log Mx + b := by
    rw [ContinuousMap.norm_le (f.restrict (closedCube z 1 one_pos : Set (SpatialCoordinates d))) hlog]
    intro x
    rw [ContinuousMap.restrict_apply, Real.norm_eq_abs]
    exact h x x.2
  calc Real.exp ‖f.restrict (closedCube z 1 one_pos : Set (SpatialCoordinates d))‖
      ≤ Real.exp (Real.log Mx + b) := Real.exp_le_exp.2 hnorm
    _ = Real.exp b * Mx := by
        rw [Real.exp_add, Real.exp_log (lt_of_lt_of_le one_pos hMx), mul_comm]

/-- **Reference factor of the top-block-removed potential.** -/
theorem calib3_reference (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ cd : ℝ, 0 < cd ∧ ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ cd →
      ∀ (j : ℕ), 0 < j → ∀ (z : SpatialCoordinates d),
        Measurable (fun om => aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) z 1 one_pos) ∧
        (∀ om, ∀ x ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)),
          Real.exp |calib3_HT d j om x| ≤ aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) z 1 one_pos) ∧
        MemLp (fun om => aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) z 1 one_pos)
          (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure := by
  obtain ⟨Cp, Cd, cd, hCp, hCd, hcd, hroot⟩ :=
    aux_prop_growth_trunc_energy_assembly_root_extremes d hd Q hQ
  refine ⟨cd / (2 * Q), by positivity, ?_⟩
  intro M hδ j hj z
  obtain ⟨D0, Mx0, CD0, CE0, hCD0, hCE0, h0, hae, hmem, hDm, hMm⟩ :=
    hroot M 0 hδ z 1 one_pos le_rfl
  refine ⟨aux_calib3_reference_measurable j z, ?_, ?_⟩
  · intro om x hx
    refine Real.exp_le_exp.2 ?_
    have h := ContinuousMap.norm_coe_le_norm
      ((calib3_HT d j om).restrict (closedCube z 1 one_pos : Set (SpatialCoordinates d))) ⟨x, hx⟩
    have heq : ‖((calib3_HT d j om).restrict (closedCube z 1 one_pos : Set (SpatialCoordinates d))) ⟨x, hx⟩‖ =
        |calib3_HT d j om x| := Real.norm_eq_abs _
    rw [heq] at h
    exact h
  · obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = |Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (j - 1))| +
        (j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P| := ⟨_, rfl⟩
    have hb0 : 0 ≤ b := by rw [hbdef]; positivity
    refine MemLp.mono' ((hmem (j - 1)).2.const_mul (Real.exp b))
      (aux_calib3_reference_measurable j z).aestronglyMeasurable ?_
    filter_upwards [hae] with om h
    obtain ⟨hp, hbd, -⟩ := h (j - 1)
    have hz : z ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)) :=
      Metric.mem_closedBall_self (by norm_num)
    have hMx1 : 1 ≤ Mx0 (j - 1) om := by
      have h1 := (hbd z hz).1.trans (hbd z hz).2
      by_contra hlt
      push Not at hlt
      have h2 : 1 < (Mx0 (j - 1) om)⁻¹ := (one_lt_inv₀ hp).2 hlt
      linarith
    have hdom := aux_calib3_reference_dom (calib3_HT d j om) z (Mx0 (j - 1) om) b hMx1 hb0
      (fun x hx => by
        have := aux_calib3_reference_sup_bound M j hj om x _ hp (hbd x hx)
        rw [hbdef]; linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold aux_prop_growth_trunc_bank_refFactor; positivity)]
    exact hdom

end SubdiffusiveProcess.Paper
