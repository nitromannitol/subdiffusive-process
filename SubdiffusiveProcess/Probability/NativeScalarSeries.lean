module

public import SubdiffusiveProcess.Probability.NativeLayerOrlicz
public import SubdiffusiveProcess.Probability.OrliczScalarSeries
public import SubdiffusiveProcess.Analysis.CompactPotentialC1Norm
public import SubdiffusiveProcess.Analysis.CompactGradientLipschitz

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
noncomputable section

namespace SubdiffusiveProcess

theorem exists_native_joint_scalar_series_exp_square_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (R : ℝ) (hR : 0 < R) :
  ∃ A : ℝ, 0 < A ∧
    ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ K : Compacts (SpatialCoordinates d),
        (∀ x ∈ (K : Set (SpatialCoordinates d)), ‖x‖ ≤ R) →
        let μ : Measure (NativeBilateralPotentialSample d) :=
          Measure.infinitePi (fun _ : ℤ =>
            (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
        let Z : ℕ → NativeBilateralPotentialSample d → ℝ := fun n ω =>
          max
            (compactPotentialC1Norm K
              (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
                (positiveScaledNativeLayer ω n)))
            (compactGradientLipschitzObservable K
              (positiveScaledNativeLayer ω n))
        (∀ n, Measurable (Z n)) →
        (∀ᵐ ω ∂μ, Summable (fun n => Z n ω)) →
        (∫⁻ ω, ENNReal.ofReal (Real.exp
          (((∑' n : ℕ, Z n ω) / (A * M.delta / 2)) ^ 2)) ∂μ) ≤ 2 ∧
        ∀ L : ℕ,
          (∫⁻ ω, ENNReal.ofReal (Real.exp
            (((∑ n ∈ Finset.range L, Z n ω) / (A * M.delta / 2)) ^ 2)) ∂μ) ≤ 2 := by
  obtain ⟨A, hA, hNative⟩ :=
    exists_native_layer_joint_exp_square_bound (d := d) R hR
  refine ⟨A, hA, ?_⟩
  intro M K hK
  let μ : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
  let Z : ℕ → NativeBilateralPotentialSample d → ℝ := fun n ω =>
    max
      (compactPotentialC1Norm K
        (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
          (positiveScaledNativeLayer ω n)))
      (compactGradientLipschitzObservable K
        (positiveScaledNativeLayer ω n))
  change (∀ n, Measurable (Z n)) →
    (∀ᵐ ω ∂μ, Summable (fun n => Z n ω)) →
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (((∑' n : ℕ, Z n ω) / (A * M.delta / 2)) ^ 2)) ∂μ) ≤ 2 ∧
    ∀ L : ℕ,
      (∫⁻ ω, ENNReal.ofReal (Real.exp
        (((∑ n ∈ Finset.range L, Z n ω) / (A * M.delta / 2)) ^ 2)) ∂μ) ≤ 2
  intro hZmeas hZsum
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  have hAδ : 0 < A * M.delta := mul_pos hA hδ
  let c : ℕ → ℝ := fun n => (3 : ℝ) ^ (-(n + 1 : ℤ))
  let a : ℕ → ℝ := fun n => A * M.delta * c n
  have hcpos : ∀ n, 0 < c n := by
    intro n
    exact zpow_pos (by norm_num) _
  have hc1 : ∀ n, c n ≤ 1 := by
    intro n
    dsimp [c]
    apply zpow_le_one_of_nonpos₀ (by norm_num)
    omega
  have hc_eq : c = fun n : ℕ => ((1 : ℝ) / 3) * ((1 : ℝ) / 3) ^ n := by
    funext n
    dsimp [c]
    rw [← inv_zpow']
    rw [show (n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) by norm_num, zpow_natCast]
    norm_num [pow_succ]
    ring
  have hcsum : (∑' n : ℕ, c n) = (1 / 2 : ℝ) := by
    calc
      (∑' n : ℕ, c n) =
          ∑' n : ℕ, ((1 : ℝ) / 3) * ((1 : ℝ) / 3) ^ n := by
        rw [hc_eq]
      _ = (1 / 3 : ℝ) * (∑' n : ℕ, ((1 : ℝ) / 3) ^ n) := by
        rw [tsum_mul_left]
      _ = (1 / 2 : ℝ) := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
  have hasummable : Summable a := by
    have hgeom : Summable (fun n : ℕ =>
        ((1 : ℝ) / 3) * ((1 : ℝ) / 3) ^ n) :=
      (summable_geometric_of_lt_one (r := (1 : ℝ) / 3)
        (by norm_num) (by norm_num)).mul_left (1 / 3)
    have hgeom' : Summable (fun n : ℕ =>
        (A * M.delta) * (((1 : ℝ) / 3) * ((1 : ℝ) / 3) ^ n)) :=
      hgeom.mul_left (A * M.delta)
    simpa [a, hc_eq] using hgeom'
  have hasum : (∑' n : ℕ, a n) = A * M.delta / 2 := by
    calc
      (∑' n : ℕ, a n) = A * M.delta * (∑' n : ℕ, c n) := by
        rw [show (fun n => a n) = fun n => (A * M.delta) * c n by
          funext n; rfl, tsum_mul_left]
      _ = A * M.delta / 2 := by rw [hcsum]; ring
  have ha : ∀ n, 0 < a n := by
    intro n
    exact mul_pos hAδ (hcpos n)
  have hC1nonneg {g : _root_.SubdiffusiveProcess.Model.PotentialField d} :
      0 ≤ compactPotentialC1Norm K g := by
    unfold compactPotentialC1Norm
    positivity
  have hLipnonneg {g : _root_.SubdiffusiveProcess.Model.PotentialField d} :
      0 ≤ compactGradientLipschitzObservable K g := by
    unfold compactGradientLipschitzObservable
    apply Real.sSup_nonneg
    rintro q ⟨x, y, hxy, rfl⟩
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hZ0 : ∀ n ω, 0 ≤ Z n ω := by
    intro n ω
    dsimp [Z]
    exact le_max_of_le_left hC1nonneg
  have hscale {x y q B : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
      (hB : 0 < B) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      max x y / (B * q) ≤ max (x / q) (y / q ^ 2) / B := by
    have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
    have hq2le : q ^ 2 ≤ q := by
      nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hq1)]
    have hyq : y / q ≤ y / q ^ 2 := by
      apply (div_le_div_iff₀ hq hq2).2
      nlinarith
    have hmax : max x y / q ≤ max (x / q) (y / q ^ 2) := by
      apply (div_le_iff₀ hq).2
      apply max_le
      · calc
          x = (x / q) * q := by field_simp
          _ ≤ max (x / q) (y / q ^ 2) * q :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hq.le
      · calc
          y = (y / q) * q := by field_simp
          _ ≤ (y / q ^ 2) * q :=
            mul_le_mul_of_nonneg_right hyq hq.le
          _ ≤ max (x / q) (y / q ^ 2) * q :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hq.le
    calc
      max x y / (B * q) = (max x y / q) / B := by field_simp
      _ ≤ max (x / q) (y / q ^ 2) / B :=
        div_le_div_of_nonneg_right hmax hB.le
  have hbound : ∀ n, (∫⁻ ω, ENNReal.ofReal (Real.exp
      ((Z n ω / a n) ^ 2)) ∂μ) ≤ 2 := by
    intro n
    have hn := hNative M K hK n
    dsimp [c, a, Z] at hn ⊢
    rcases hn with ⟨hn, hX, hY⟩
    apply (lintegral_mono (fun ω => ?_)).trans hn
    have hq := hcpos n
    have hq1 := hc1 n
    have hB := hAδ
    have hpoint := hscale hq hq1 hB (hX ω) (hY ω)
    have hleft : 0 ≤
        max
          (compactPotentialC1Norm K
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer ω n)))
          (compactGradientLipschitzObservable K
            (positiveScaledNativeLayer ω n)) /
          (A * M.delta * (3 : ℝ) ^ (-(n + 1 : ℤ))) := by
      apply div_nonneg
      · exact le_max_of_le_left hC1nonneg
      · exact (mul_pos hAδ (zpow_pos (by norm_num) _)).le
    have hright : 0 ≤
        max
          (compactPotentialC1Norm K
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer ω n)) /
            (3 : ℝ) ^ (-(n + 1 : ℤ)))
          (compactGradientLipschitzObservable K
            (positiveScaledNativeLayer ω n) /
          ((3 : ℝ) ^ (-(n + 1 : ℤ))) ^ 2) /
          (A * M.delta) := by
      apply div_nonneg
      · exact le_max_of_le_left (div_nonneg hC1nonneg (hcpos n).le)
      · exact hAδ.le
    exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr
      ((sq_le_sq₀ hleft hright).2 hpoint))
  have hfull := lintegral_exp_sq_tsum_le μ Z a
    (fun n => (hZmeas n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (hZ0 n))
    ha hasummable hZsum hbound
  refine ⟨?_, ?_⟩
  · rw [hasum] at hfull
    exact hfull
  · intro L
    rw [hasum] at hfull
    apply (lintegral_mono_ae ?_).trans hfull
    filter_upwards [hZsum] with ω hω
    have hpartial : (∑ n ∈ Finset.range L, Z n ω) ≤ ∑' n : ℕ, Z n ω :=
      hω.sum_le_tsum (Finset.range L) (fun n _ => hZ0 n ω)
    have hden : 0 ≤ A * M.delta / 2 := (div_nonneg hAδ.le (by norm_num))
    have hleft : 0 ≤ (∑ n ∈ Finset.range L, Z n ω) / (A * M.delta / 2) := by
      exact div_nonneg (Finset.sum_nonneg (fun n hn => hZ0 n ω)) hden
    have hright : 0 ≤ (∑' n : ℕ, Z n ω) / (A * M.delta / 2) := by
      exact div_nonneg (tsum_nonneg (fun n => hZ0 n ω)) hden
    exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr
      ((sq_le_sq₀ hleft hright).2
        (div_le_div_of_nonneg_right hpartial hden)))

end SubdiffusiveProcess
