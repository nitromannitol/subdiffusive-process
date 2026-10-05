module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.RowSumBound
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.SupplyInterface

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section

private abbrev S8 (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

variable {d : ℕ}

/-! ## A weighted `p`-power sum of a decaying family -/

theorem lintegral_tsum_weighted_rpow_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (D : ℕ → Omega → ℝ≥0∞) (hD : ∀ j, Measurable (D j))
    {a p v : ℝ} (hp : 0 < p) (c : ℝ≥0∞)
    (hDb : ∀ j : ℕ, (∫⁻ omega, (D j omega) ^ p ∂mu) ≤
      c * ENNReal.ofReal (Real.rpow (3 : ℝ) (-v * (j : ℝ)))) :
    (∫⁻ omega, ∑' j : ℕ,
        (ENNReal.ofReal (Real.rpow (3 : ℝ) (a * (j : ℝ))) * D j omega) ^ p ∂mu) ≤
      c * ∑' j : ℕ,
        ENNReal.ofReal (Real.rpow (3 : ℝ) (-(v - a * p) * (j : ℝ))) := by
  have hterm : ∀ j : ℕ,
      (∫⁻ omega,
        (ENNReal.ofReal (Real.rpow (3 : ℝ) (a * (j : ℝ))) * D j omega) ^ p ∂mu) ≤
        c * ENNReal.ofReal (Real.rpow (3 : ℝ) (-(v - a * p) * (j : ℝ))) := by
    intro j
    have hsplit : ∀ omega : Omega,
        (ENNReal.ofReal (Real.rpow (3 : ℝ) (a * (j : ℝ))) * D j omega) ^ p =
          ENNReal.ofReal (Real.rpow (3 : ℝ) (a * (j : ℝ) * p)) *
            (D j omega) ^ p := by
      intro omega
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ofReal_rpow3_rpow _ _ hp.le]
    simp only [hsplit]
    rw [lintegral_const_mul _ ((hD j).pow_const _)]
    refine le_trans (mul_le_mul_right (hDb j) _) (le_of_eq ?_)
    rw [← mul_assoc, mul_comm (ENNReal.ofReal (Real.rpow (3 : ℝ) (a * (j : ℝ) * p))) c,
      mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (rpow3_nonneg _), rpow3_add]
    congr 1
    ring_nf
  rw [lintegral_tsum fun j => (((hD j).const_mul _).pow_const _).aemeasurable]
  refine le_trans (ENNReal.tsum_le_tsum hterm) (le_of_eq ?_)
  rw [ENNReal.tsum_mul_left]

/-! ## The supply -/

/-- **The AK.HC supply interface is met by the GMC fixed cutoff.**

This discharges the single named hypothesis of `SupplyInterface.lean`. -/
theorem fixedCutoffResponseSupply (d : ℕ) [NeZero d] :
    FixedCutoffResponseSupply d := by
  classical
  by_cases hd : 2 ≤ d
  swap
  · exact ⟨1, one_pos, fun M _ _ _ => absurd M.shellPrefix.dimension hd⟩
  obtain ⟨rho, hrho0, hrho16, hbound⟩ :=
    exists_allScale_lpMoment_finiteProbeSum_bound d hd
  refine ⟨rho / 2, by positivity, ?_⟩
  intro M L q hq
  set theta : ℝ := rho / 2 with hthetadef
  have htheta0 : 0 < theta := by positivity
  set xi : ℝ := max (2 * q) (6 * (d : ℝ) + 2) with hxidef
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_of_lt hd
  have hxi2 : (2 : ℝ) ≤ xi := le_trans (by linarith) (le_max_right _ _)
  have hxi1 : (1 : ℝ) ≤ xi := by linarith
  have hxi0 : (0 : ℝ) < xi := by linarith
  have hxibig : 6 * (d : ℝ) + 2 ≤ xi := le_max_right _ _
  set p : ℝ := 2 * xi with hpdef
  have hp0 : (0 : ℝ) < p := by rw [hpdef]; linarith
  have hp4q : 4 * q ≤ p := by
    have := le_max_left (2 * q) (6 * (d : ℝ) + 2)
    rw [hpdef]; linarith [this]
  -- the per-cube moment bound
  obtain ⟨Cst, hCst0, hCst⟩ := hbound M L
  have hmom := hCst xi hxi2
  -- the two union-bound conditions
  have hs1 : Section6Dirichlet.fixedCutoffDirichletS1 = 1 / 2 := rfl
  have hgamma1 : 0 < Section6Dirichlet.fixedCutoffDirichletS1 * xi -
      (d : ℝ) - rho * xi := by
    rw [hs1]
    nlinarith [hrho16, hrho0, hxibig, hxi0, hd1]
  have hgamma2 : 0 < (Section6Dirichlet.fixedCutoffDirichletS1 / 2) * xi -
      (d : ℝ) - rho * xi := by
    rw [hs1]
    nlinarith [hrho16, hrho0, hxibig, hxi0, hd1]
  have hs1pos : 0 < Section6Dirichlet.fixedCutoffDirichletS1 := by
    rw [hs1]; norm_num
  obtain ⟨c1, hc1top, hC1⟩ :=
    exists_lintegral_paperHomogenizationError_rpow_le M L
      (s := Section6Dirichlet.fixedCutoffDirichletS1) (r := 1) (xi := xi)
      (rho := rho) (Cst := Cst xi) hs1pos one_pos hxi1 (hCst0 xi) hmom hgamma1
  obtain ⟨c2, hc2top, hC2⟩ :=
    exists_lintegral_paperHomogenizationError_rpow_le M L
      (s := Section6Dirichlet.fixedCutoffDirichletS1 / 2) (r := 2) (xi := xi)
      (rho := rho) (Cst := Cst xi) (by rw [hs1]; norm_num) two_pos hxi1
      (hCst0 xi) hmom hgamma2
  -- the two shifted families
  set D1 : ℕ → S8 d → ℝ≥0∞ := fun j omega =>
    paperHomogenizationError (originCube d (((L + j : ℕ) : ℤ)))
      (((L + j : ℕ) : ℤ)) Section6Dirichlet.fixedCutoffDirichletS1 .infinity
      (.finite 1) (aCutoffFamily M L omega) (ahom M L) with hD1
  set D2 : ℕ → S8 d → ℝ≥0∞ := fun j omega =>
    paperHomogenizationError (originCube d (((L + j : ℕ) : ℤ)))
      (((L + j : ℕ) : ℤ)) (Section6Dirichlet.fixedCutoffDirichletS1 / 2)
      .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L) with hD2
  have hD1meas : ∀ j, Measurable (D1 j) := fun j =>
    measurable_paperHomogenizationError_ambient M L _ _ _ _
  have hD2meas : ∀ j, Measurable (D2 j) := fun j =>
    measurable_paperHomogenizationError_ambient M L _ _ _ _
  -- the shifted decay
  set cL1 : ℝ≥0∞ := c1 * ENNReal.ofReal (Real.rpow (3 : ℝ) (-(rho * xi) * (L : ℝ)))
    with hcL1
  set cL2 : ℝ≥0∞ := c2 * ENNReal.ofReal (Real.rpow (3 : ℝ) (-(rho * xi) * (L : ℝ)))
    with hcL2
  have hshift : ∀ (c : ℝ≥0∞) (j : ℕ),
      c * ENNReal.ofReal (Real.rpow (3 : ℝ) (-(rho * xi) * ((L + j : ℕ) : ℝ))) =
        (c * ENNReal.ofReal (Real.rpow (3 : ℝ) (-(rho * xi) * (L : ℝ)))) *
          ENNReal.ofReal (Real.rpow (3 : ℝ) (-(rho * xi) * (j : ℝ))) := by
    intro c j
    rw [mul_assoc, ← ENNReal.ofReal_mul (rpow3_nonneg _), rpow3_add]
    congr 2
    push_cast
    ring_nf
  have hDb1 : ∀ j : ℕ, (∫⁻ omega, (D1 j omega) ^ p ∂M.P.toMeasure) ≤
      cL1 * ENNReal.ofReal (Real.rpow (3 : ℝ) (-(rho * xi) * (j : ℝ))) := by
    intro j
    have := hC1 (L + j)
    rw [hpdef]
    rw [hcL1, ← hshift c1 j]
    exact this
  have hDb2 : ∀ j : ℕ, (∫⁻ omega, (D2 j omega) ^ p ∂M.P.toMeasure) ≤
      cL2 * ENNReal.ofReal (Real.rpow (3 : ℝ) (-(rho * xi) * (j : ℝ))) := by
    intro j
    have := hC2 (L + j)
    rw [hpdef]
    rw [hcL2, ← hshift c2 j]
    exact this
  -- the prefactor
  set wgt : ℕ → ℝ≥0∞ := fun j =>
    ENNReal.ofReal (Real.rpow (3 : ℝ) ((theta / 2) * (j : ℝ))) with hwgt
  set G : S8 d → ℝ≥0∞ := fun omega =>
    (∑' j : ℕ, (wgt j * D1 j omega) ^ p) +
      ∑' j : ℕ, (wgt j * D2 j omega) ^ p with hG
  have hGmeas : Measurable G := by
    refine Measurable.add ?_ ?_
    · exact Measurable.tsum fun j =>
        (((hD1meas j).const_mul _).pow_const _)
    · exact Measurable.tsum fun j =>
        (((hD2meas j).const_mul _).pow_const _)
  -- finiteness of the `p`-th moment
  have hgap : (0 : ℝ) < rho * xi - (theta / 2) * p := by
    rw [hthetadef, hpdef]
    nlinarith [hrho0, hxi0]
  have hgeo : (∑' j : ℕ, ENNReal.ofReal (Real.rpow (3 : ℝ)
      (-(rho * xi - (theta / 2) * p) * (j : ℝ)))) ≠ ⊤ :=
    tsum_ofReal_rpow3_geometric_ne_top hgap
  have hint1 := lintegral_tsum_weighted_rpow_le (mu := M.P.toMeasure) D1 hD1meas
    (a := theta / 2) (p := p) (v := rho * xi) hp0 cL1 hDb1
  have hint2 := lintegral_tsum_weighted_rpow_le (mu := M.P.toMeasure) D2 hD2meas
    (a := theta / 2) (p := p) (v := rho * xi) hp0 cL2 hDb2
  have hGint : (∫⁻ omega, G omega ∂M.P.toMeasure) ≠ ⊤ := by
    have hsplit : (∫⁻ omega, G omega ∂M.P.toMeasure) =
        (∫⁻ omega, ∑' j : ℕ, (wgt j * D1 j omega) ^ p ∂M.P.toMeasure) +
          ∫⁻ omega, ∑' j : ℕ, (wgt j * D2 j omega) ^ p ∂M.P.toMeasure := by
      rw [hG]
      exact lintegral_add_left (Measurable.tsum fun j =>
        (((hD1meas j).const_mul _).pow_const _)) _
    rw [hsplit]
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · refine ne_top_of_le_ne_top ?_ hint1
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hc1top ENNReal.ofReal_ne_top) hgeo
    · refine ne_top_of_le_ne_top ?_ hint2
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hc2top ENNReal.ofReal_ne_top) hgeo
  set W : S8 d → ℝ := fun omega => ((G omega) ^ p⁻¹).toReal with hW
  set B : ℝ := ((∫⁻ omega, G omega ∂M.P.toMeasure) ^ p⁻¹).toReal with hB
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hW0 : ∀ omega, 0 ≤ W omega := fun _ => ENNReal.toReal_nonneg
  -- coefficient measurability
  have hGcoeff : @Measurable (S8 d) ℝ≥0∞
      (coefficientSigma (fun omega => _root_.SubdiffusiveProcess.Model.aCutoff M L omega))
      inferInstance G := by
    let : MeasurableSpace (S8 d) :=
      coefficientSigma (fun omega => _root_.SubdiffusiveProcess.Model.aCutoff M L omega)
    refine Measurable.add ?_ ?_
    · refine Measurable.tsum fun j => ?_
      exact (ENNReal.continuous_rpow_const.measurable.comp
        (((measurable_paperHomogenizationError_infinity_finite_aCutoffFamily_coefficientSigma
          M L _ _ _ _)).const_mul _))
    · refine Measurable.tsum fun j => ?_
      exact (ENNReal.continuous_rpow_const.measurable.comp
        (((measurable_paperHomogenizationError_infinity_finite_aCutoffFamily_coefficientSigma
          M L _ _ _ _)).const_mul _))
  have hWmeas : CoefficientMeasurable
      (fun omega => _root_.SubdiffusiveProcess.Model.aCutoff M L omega) W :=
    (ENNReal.continuous_rpow_const.measurable.comp hGcoeff).ennreal_toReal
  -- the `L^{4q}` bound
  have hofRealW : ∀ omega, ENNReal.ofReal (W omega) ≤ (G omega) ^ p⁻¹ := fun omega =>
    ENNReal.ofReal_toReal_le
  have hWp : ∀ omega, (ENNReal.ofReal (W omega)) ^ p ≤ G omega := by
    intro omega
    refine le_trans (ENNReal.rpow_le_rpow (hofRealW omega) hp0.le) (le_of_eq ?_)
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  have hWAES : AEStronglyMeasurable W M.P.toMeasure := by
    simpa only [W, Function.comp_def] using! ((ENNReal.continuous_rpow_const.measurable.comp hGmeas).ennreal_toReal).aestronglyMeasurable
  have hnormp : eLpNorm W (ENNReal.ofReal p) M.P.toMeasure ≤ ENNReal.ofReal B := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by simpa using (ENNReal.ofReal_pos.mpr hp0).ne') ENNReal.ofReal_ne_top
      hWAES,
      ENNReal.toReal_ofReal hp0.le]
    have henorm : ∀ omega : S8 d, ‖W omega‖ₑ ^ p ≤ G omega := by
      intro omega
      have : ‖W omega‖ₑ = ENNReal.ofReal (W omega) := by
        rw [← Real.enorm_eq_ofReal (hW0 omega)]
      rw [this]
      exact hWp omega
    have hle := lintegral_mono (μ := M.P.toMeasure) henorm
    have hfinal := ENNReal.rpow_le_rpow hle (by positivity : (0 : ℝ) ≤ 1 / p)
    rw [hB, ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg
      (by positivity) hGint)]
    simpa only [one_div] using hfinal
  have hnorm4q : eLpNorm W (ENNReal.ofReal (4 * q)) M.P.toMeasure ≤
      ENNReal.ofReal B := by
    refine le_trans ?_ hnormp
    exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hp4q)
  refine ⟨W, B, hB0, hW0, hWmeas, hnorm4q, ?_⟩
  -- the pathwise envelope, on the full-measure set where `G` is finite
  have hGfin : ∀ᵐ omega ∂M.P.toMeasure, G omega < ⊤ := ae_lt_top hGmeas hGint
  filter_upwards [hGfin] with omega hfin
  intro N hLN
  set j : ℕ := N - L with hj
  have hjN : L + j = N := by omega
  have hGrpow : (G omega) ^ p⁻¹ = ENNReal.ofReal (W omega) := by
    rw [hW]
    exact (ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg
      (by positivity) hfin.ne)).symm
  have hkey : ∀ (E : ℕ → S8 d → ℝ≥0∞),
      (∀ k, (wgt k * E k omega) ^ p ≤ G omega) →
      E j omega ≤ ENNReal.ofReal (W omega *
        Section6Dirichlet.fixedCutoffDirichletResponseWeight theta j) := by
    intro E hE
    have hstep : wgt j * E j omega ≤ ENNReal.ofReal (W omega) := by
      have := ENNReal.rpow_le_rpow (hE j) (by positivity : (0 : ℝ) ≤ p⁻¹)
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one,
        hGrpow] at this
      exact this
    have hmulw := mul_le_mul_right hstep
      (ENNReal.ofReal (Real.rpow (3 : ℝ) (-(theta / 2) * (j : ℝ))))
    have hone : ENNReal.ofReal (Real.rpow (3 : ℝ) (-(theta / 2) * (j : ℝ))) *
        wgt j = 1 := by
      rw [hwgt, ← ENNReal.ofReal_mul (rpow3_nonneg _), rpow3_add]
      have hzero : -(theta / 2) * (j : ℝ) + (theta / 2) * (j : ℝ) = 0 := by ring
      have h30 : Real.rpow (3 : ℝ) 0 = 1 := Real.rpow_zero 3
      rw [hzero, h30, ENNReal.ofReal_one]
    have hleft : ENNReal.ofReal (Real.rpow (3 : ℝ) (-(theta / 2) * (j : ℝ))) *
        (wgt j * E j omega) = E j omega := by
      rw [← mul_assoc, hone, one_mul]
    rw [hleft] at hmulw
    refine le_trans hmulw (le_of_eq ?_)
    rw [Section6Dirichlet.fixedCutoffDirichletResponseWeight,
      ENNReal.ofReal_mul (hW0 omega), mul_comm]
    congr 2
    ring_nf
  have hbound1 : ∀ k, (wgt k * D1 k omega) ^ p ≤ G omega := by
    intro k
    exact le_trans (ENNReal.le_tsum (f := fun j : ℕ => (wgt j * D1 j omega) ^ p) k) le_self_add
  have hbound2 : ∀ k, (wgt k * D2 k omega) ^ p ≤ G omega := by
    intro k
    exact le_trans (ENNReal.le_tsum (f := fun j : ℕ => (wgt j * D2 j omega) ^ p) k) le_add_self
  have hr1 := hkey D1 hbound1
  have hr2 := hkey D2 hbound2
  simp only [hD1] at hr1
  simp only [hD2] at hr2
  rw [hjN] at hr1 hr2
  exact ⟨hr1, hr2⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
