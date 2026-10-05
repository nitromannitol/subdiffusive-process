module

public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity

@[expose] public section

open MeasureTheory ProbabilityTheory
open Homogenization hiding Vec Mat TriadicCube
open Homogenization.Book Homogenization.IndependentSums SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The normalized Lebesgue measure `⨍_U` of a set `U` of finite positive volume. -/
def aux_l_sensitivity_for_cutoffs_normalizedVolume {d : ℕ} (U : Set (Vec d)) : Measure (Vec d) :=
  (volume U)⁻¹ • volume.restrict U

theorem aux_l_sensitivity_for_cutoffs_ogamma_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {σ A A' : ℝ} {X : Ω → ℝ} (hσ : 0 < σ) (hA : 0 < A) (hAA' : A ≤ A')
    (hXm : AEMeasurable X μ) (hX : SubdiffusiveProcess.OGammaLE μ σ A X) : SubdiffusiveProcess.OGammaLE μ σ A' X := by
  have hA' : 0 < A' := lt_of_lt_of_le hA hAA'
  have hle : ∀ ω, Real.exp ((A'⁻¹ * max (X ω) 0) ^ σ) ≤ Real.exp ((A⁻¹ * max (X ω) 0) ^ σ) := by
    intro ω
    apply Real.exp_le_exp.mpr
    apply Real.rpow_le_rpow
    · exact mul_nonneg (inv_nonneg.mpr hA'.le) (le_max_right _ _)
    · exact mul_le_mul_of_nonneg_right (inv_anti₀ hA hAA') (le_max_right _ _)
    · exact hσ.le
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp ((A'⁻¹ * max (X ω) 0) ^ σ)) μ :=
    (Real.measurable_exp.comp_aemeasurable
      (((hXm.max aemeasurable_const).const_mul _).pow_const σ)).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · refine hX.1.mono' hmeas (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hle ω
  · refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hX.1
      (Filter.Eventually.of_forall hle)) hX.2

/-- A nonnegative a.e.-measurable `Γ₂`-tail-bounded variable has a measurable a.e.-equal copy with the
expectation-form bound `X ≤ O_{Γ₂}(2A)` (`4^{1/2} = 2`), still dominating any a.e.-dominated
extended-real quantity. -/
theorem aux_l_sensitivity_for_cutoffs_measurable_ogamma {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZae : AEMeasurable Z μ)
    (A : ℝ) (hA : 0 < A)
    (hbig : IsBigOWith μ (gammaSigma 2) Z A) (s : Ω → ℝ≥0∞)
    (hs : ∀ᵐ ω ∂μ, s ω ≤ ENNReal.ofReal (Z ω)) :
    ∃ Zm : Ω → ℝ, Measurable Zm ∧ SubdiffusiveProcess.OGammaLE μ 2 (2 * A) Zm ∧
      ∀ᵐ ω ∂μ, s ω ≤ ENNReal.ofReal (Zm ω) := by
  let Zm : Ω → ℝ := fun ω => max (hZae.mk Z ω) 0
  have hZm : Measurable Zm := hZae.measurable_mk.max measurable_const
  have hZeq : (fun ω => max (Z ω) 0) =ᵐ[μ] Zm := by
    filter_upwards [hZae.ae_eq_mk] with ω hω
    simp only [Zm, ← hω]
  have hZm0 : ∀ ω, 0 ≤ Zm ω := fun ω => le_max_right _ _
  have hbigm : IsBigO μ (gammaSigma 2) Zm A := by
    intro t ht
    have h := hbig ht
    have hAt : 0 < A * t := mul_pos hA (lt_of_lt_of_le zero_lt_one ht)
    have hset : upperTailEvent (fun ω => |Zm ω|) (A * t) =ᵐ[μ] upperTailEvent Z (A * t) := by
      filter_upwards [hZeq] with ω hω
      have habs : |Zm ω| = max (Z ω) 0 := by rw [abs_of_nonneg (hZm0 ω), ← hω]
      show (A * t < |Zm ω|) = (A * t < Z ω)
      rw [habs]
      apply propext
      constructor
      · intro hlt
        rcases le_or_gt (Z ω) 0 with hz | hz
        · rw [max_eq_right hz] at hlt
          linarith
        · rw [max_eq_left hz.le] at hlt
          exact hlt
      · intro hlt
        exact lt_of_lt_of_le hlt (le_max_left _ _)
    rw [measureReal_congr hset]
    exact h
  have hog := SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma (μ := μ) (σ := 2) (A := A)
    (X := Zm) (by norm_num) hA hZm hbigm
  have h4 : (4 : ℝ) ^ (2 : ℝ)⁻¹ = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    simp
  rw [h4] at hog
  refine ⟨Zm, hZm, hog, ?_⟩
  filter_upwards [hs, hZeq] with ω hω hω'
  rw [← hω']
  calc s ω ≤ ENNReal.ofReal (Z ω) := hω
    _ ≤ ENNReal.ofReal (max (Z ω) 0) := ENNReal.ofReal_le_ofReal (le_max_left _ _)


theorem aux_l_sensitivity_for_cutoffs_ogamma_of_bigOWith {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZm : Measurable Z)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (A : ℝ) (hA : 0 < A) (hbig : IsBigOWith μ (gammaSigma 2) Z A) :
    SubdiffusiveProcess.OGammaLE μ 2 (2 * A) Z := by
  have hbigO : IsBigO μ (gammaSigma 2) Z A := by
    intro t ht
    have h := hbig ht
    have hset : upperTailEvent (fun ω => |Z ω|) (A * t) = upperTailEvent Z (A * t) := by
      ext ω
      simp only [upperTailEvent, Set.mem_ofPred_eq, abs_of_nonneg (hZ0 ω)]
    rw [hset]
    exact h
  have hog := SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma (μ := μ) (σ := 2) (A := A)
    (X := Z) (by norm_num) hA hZm hbigO
  have h4 : (4 : ℝ) ^ (2 : ℝ)⁻¹ = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    simp
  rwa [h4] at hog

/-- `(∫⁻ s^ξ)^{1/ξ} ≤ ofReal ((∫ W^ξ)^{1/ξ})` when `s ≤ ofReal W` almost everywhere. -/
theorem aux_l_sensitivity_for_cutoffs_lp_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Ω → ℝ≥0∞) (W : Ω → ℝ) (xi : ℝ) (hxi : 1 ≤ xi) (hW0 : ∀ ω, 0 ≤ W ω)
    (hWint : Integrable (fun ω => W ω ^ xi) μ) (hs : ∀ᵐ ω ∂μ, s ω ≤ ENNReal.ofReal (W ω)) :
    paperENNRealLpNorm μ xi s ≤ ENNReal.ofReal ((∫ ω, W ω ^ xi ∂μ) ^ xi⁻¹) := by
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  unfold paperENNRealLpNorm
  calc (∫⁻ ω, s ω ^ xi ∂μ) ^ xi⁻¹
      ≤ (∫⁻ ω, ENNReal.ofReal (W ω) ^ xi ∂μ) ^ xi⁻¹ := by
        refine ENNReal.rpow_le_rpow ?_ (inv_nonneg.mpr hxi0.le)
        exact lintegral_mono_ae (hs.mono fun ω h => ENNReal.rpow_le_rpow h hxi0.le)
    _ = ENNReal.ofReal ((∫ ω, W ω ^ xi ∂μ) ^ xi⁻¹) := by
        have h1 : ∫⁻ ω, ENNReal.ofReal (W ω) ^ xi ∂μ = ENNReal.ofReal (∫ ω, W ω ^ xi ∂μ) := by
          rw [ofReal_integral_eq_lintegral_ofReal hWint
            (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hW0 ω) _)]
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.ofReal_rpow_of_nonneg (hW0 ω) hxi0.le]
        rw [h1, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun ω => Real.rpow_nonneg (hW0 ω) _)
          (inv_nonneg.mpr hxi0.le)]

/-- The normalized volume of a bounded open nonempty set is a probability measure. -/
theorem aux_l_sensitivity_for_cutoffs_nu_prob {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (hne : U.Nonempty) (hb : Bornology.IsBounded U) :
    IsProbabilityMeasure (aux_l_sensitivity_for_cutoffs_normalizedVolume U) := by
  refine ⟨?_⟩
  have h0 : volume U ≠ 0 := (hU.measure_pos volume hne).ne'
  have htop : volume U ≠ ⊤ := hb.measure_lt_top.ne
  simp only [aux_l_sensitivity_for_cutoffs_normalizedVolume, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 htop

/-- Tonelli packaging: uniform pointwise `p`-moments give the normalized spatial `L^p` observable, for an
arbitrary probability measure in space. -/
theorem aux_l_sensitivity_for_cutoffs_tonelli {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (nu : Measure (Vec d)) [IsProbabilityMeasure nu]
    (F : Omega → Vec d → ℝ) (p B : ℝ) (hp : 1 ≤ p) (hB : 0 ≤ B)
    (hF : Measurable (Function.uncurry F))
    (hpoint : ∀ x, Integrable (fun ω => |F ω x| ^ p) mu ∧
      (∫ ω, |F ω x| ^ p ∂mu) ^ p⁻¹ ≤ B) :
    paperENNRealLpNorm mu p (fun ω => eLpNorm (F ω) (ENNReal.ofReal p) nu) ≤
      ENNReal.ofReal B := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hmoment : ∀ x, ∫ ω, |F ω x| ^ p ∂mu ≤ B ^ p := by
    intro x
    have hI0 : 0 ≤ ∫ ω, |F ω x| ^ p ∂mu :=
      integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    have h := Real.rpow_le_rpow
      (Real.rpow_nonneg hI0 p⁻¹) (hpoint x).2 hp0.le
    calc
      ∫ ω, |F ω x| ^ p ∂mu =
          ((∫ ω, |F ω x| ^ p ∂mu) ^ p⁻¹) ^ p := by
        rw [← Real.rpow_mul hI0, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
      _ ≤ B ^ p := h
  have hinner : ∀ x,
      ∫⁻ ω, ‖F ω x‖ₑ ^ p ∂mu =
        ENNReal.ofReal (∫ ω, |F ω x| ^ p ∂mu) := by
    intro x
    calc
      ∫⁻ ω, ‖F ω x‖ₑ ^ p ∂mu =
          ∫⁻ ω, ENNReal.ofReal (|F ω x| ^ p) ∂mu := by
        apply lintegral_congr
        intro ω
        rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
        rw [← ofReal_norm]
        simp only [Real.norm_eq_abs]
      _ = ENNReal.ofReal (∫ ω, |F ω x| ^ p ∂mu) :=
        (ofReal_integral_eq_lintegral_ofReal (hpoint x).1
          (Filter.Eventually.of_forall fun ω =>
            Real.rpow_nonneg (abs_nonneg _) _)).symm
  have hinner_le : ∀ x, ∫⁻ ω, ‖F ω x‖ₑ ^ p ∂mu ≤ ENNReal.ofReal (B ^ p) := by
    intro x
    rw [hinner x]
    exact ENNReal.ofReal_le_ofReal (hmoment x)
  have hmeas : Measurable (fun z : Omega × Vec d => ‖F z.1 z.2‖ₑ ^ p) := by
    exact hF.enorm.pow_const p
  have hdouble : ∫⁻ ω, ∫⁻ x, ‖F ω x‖ₑ ^ p ∂nu ∂mu ≤
      ENNReal.ofReal (B ^ p) := by
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    calc
      ∫⁻ x, ∫⁻ ω, ‖F ω x‖ₑ ^ p ∂mu ∂nu ≤
          ∫⁻ _x, ENNReal.ofReal (B ^ p) ∂nu := lintegral_mono hinner_le
      _ = ENNReal.ofReal (B ^ p) := by rw [lintegral_const, measure_univ, mul_one]
  have houter : paperENNRealLpNorm mu p
      (fun ω => eLpNorm (F ω) (ENNReal.ofReal p) nu) =
      (∫⁻ ω, ∫⁻ x, ‖F ω x‖ₑ ^ p ∂nu ∂mu) ^ p⁻¹ := by
    unfold paperENNRealLpNorm
    congr 1
    apply lintegral_congr
    intro ω
    change eLpNorm (F ω) (ENNReal.ofReal p) nu ^ p =
      ∫⁻ x, ‖F ω x‖ₑ ^ p ∂nu
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := nu)
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
      (hF.of_uncurry_left (x := ω)).aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le, ← ENNReal.rpow_mul]
    rw [one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  rw [houter]
  calc
    (∫⁻ ω, ∫⁻ x, ‖F ω x‖ₑ ^ p ∂nu ∂mu) ^ p⁻¹ ≤
        (ENNReal.ofReal (B ^ p)) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow hdouble (inv_nonneg.mpr hp0.le)
    _ = ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hB hp0.le]
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]


/-- **Lemma `l.sensitivity.for.cutoffs`** : `∃ C(d)` (independent of the
model), for every model `M` (assumptions `a.g1`--`a.g4`), `n ∈ ℕ₀`, `k ∈ ℤ`:
(e.sensitivity.field) `sup_{m≥n} sup_{x,y∈cu_k} log((a_m a_n⁻¹)(x)/(a_m a_n⁻¹)(y)) ≤ O_{Γ₂}(Cδ3^{k-n})` (expectation form
`SubdiffusiveProcess.OGammaLE`, witnessed by a measurable majorant);
(e.infraredhom.approx.cutoffs.large.waves.field) the `L^ξ(ℙ)` norm of `sup_{m≥n} sup_{x,y} (ratio) - 1` is at most
`Cξ^{1/2}δ3^{k-n}exp(Cξδ²3^{2(k-n)})`; for `m > n`: (e.infrared.approx.cutoffs.field)
`‖log(a_m a_n⁻¹) + (m-n)τ²‖_{L^∞(cu_k)} ≤ O_{Γ₂}(Cδ((m-n)^{1/2} + (k-n)_+))` and (e.aman.Linfty.moments) the sum of the
`L^ξ(ℙ)` norms of `‖a_m a_n⁻¹ - 1‖_{L^∞(cu_k)}`, `‖a_m⁻¹ a_n - 1‖_{L^∞(cu_k)}` is at most
`(Cξ^{1/2}δ((m-n)^{1/2}+(k-n)_+)) exp(Cξδ²(m-n+(k-n)_+²))`; and for every bounded domain `U`, `p ≥ 1`,
`-1 ≤ n < m` (e.am.Lp.moments, e.am.Lp.moments.inv) the normalized spatial `L^p(U)` norms of `a_m a_n⁻¹ - 1` and
`a_m⁻¹ a_n - 1` have `L^p(ℙ)` norm at most `(Cp^{1/2}δ(m-n)^{1/2}) exp(Cpδ²(m-n))`.  The literal suprema are kept as
`ℝ≥0∞`-valued quantities (`cutoffLogRatioOscillationSup`, `cutoffRatioOscillationSup`, `cutoffShellBlockLinfty`,
`cutoffRatioLinfty`, `inverseCutoffRatioLinfty`) and the `L^ξ(ℙ)` norms are the `ℝ≥0∞` norms `paperENNRealLpNorm`. -/
theorem l_sensitivity_for_cutoffs {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ),
      -- (e.sensitivity.field)
      (∃ Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ, Measurable Z ∧
        SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (C * M.delta * (3 : ℝ) ^ (k - (n : ℤ))) Z ∧
        ∀ᵐ omega ∂M.P.toMeasure,
          cutoffLogRatioOscillationSup n k omega ≤ ENNReal.ofReal (Z omega)) ∧
      -- (e.infraredhom.approx.cutoffs.large.waves.field)
      (∀ xi : ℝ, 1 ≤ xi →
        paperENNRealLpNorm M.P.toMeasure xi (cutoffRatioOscillationSup n k) ≤
          ENNReal.ofReal (C * Real.sqrt xi * M.delta * (3 : ℝ) ^ (k - (n : ℤ)) *
            Real.exp (C * xi * M.delta ^ 2 * ((3 : ℝ) ^ (k - (n : ℤ))) ^ 2))) ∧
      (∀ m : ℕ, n < m →
        -- (e.infrared.approx.cutoffs.field)
        (∃ Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ, Measurable Z ∧
          SubdiffusiveProcess.OGammaLE M.P.toMeasure 2
            (C * M.delta * (Real.sqrt ((m : ℝ) - n) + max 0 ((k : ℝ) - n))) Z ∧
          ∀ omega, cutoffShellBlockLinfty m n k omega ≤ ENNReal.ofReal (Z omega)) ∧
        -- (e.aman.Linfty.moments)
        (∀ xi : ℝ, 1 ≤ xi →
          paperENNRealLpNorm M.P.toMeasure xi (cutoffRatioLinfty M m n k) +
            paperENNRealLpNorm M.P.toMeasure xi (inverseCutoffRatioLinfty M m n k) ≤
          ENNReal.ofReal
            (C * Real.sqrt xi * M.delta * (Real.sqrt ((m : ℝ) - n) + max 0 ((k : ℝ) - n)) *
              Real.exp (C * xi * M.delta ^ 2 *
                (((m : ℝ) - n) + (max 0 ((k : ℝ) - n)) ^ 2))))) ∧
      -- (e.am.Lp.moments) and (e.am.Lp.moments.inv), every bounded domain `U`
      (∀ (U : Set (Vec d)), IsOpen U → IsConnected U → Bornology.IsBounded U →
        ∀ (m : ℕ) (n' : ℤ) (p : ℝ), 1 ≤ p → -1 ≤ n' → n' < (m : ℤ) →
          paperENNRealLpNorm M.P.toMeasure p
              (fun omega => eLpNorm (cutoffRatioMinusOne M m n' omega)
                (ENNReal.ofReal p) (aux_l_sensitivity_for_cutoffs_normalizedVolume U)) ≤
            ENNReal.ofReal (C * Real.sqrt p * M.delta * Real.sqrt ((m : ℝ) - n') *
              Real.exp (C * p * M.delta ^ 2 * ((m : ℝ) - n'))) ∧
          paperENNRealLpNorm M.P.toMeasure p
              (fun omega => eLpNorm (inverseCutoffRatioMinusOne M m n' omega)
                (ENNReal.ofReal p) (aux_l_sensitivity_for_cutoffs_normalizedVolume U)) ≤
            ENNReal.ofReal (C * Real.sqrt p * M.delta * Real.sqrt ((m : ℝ) - n') *
              Real.exp (C * p * M.delta ^ 2 * ((m : ℝ) - n')))) := by
  classical
  let a1 : ℝ := 2 * shellSensitivityConst d
  let a2 : ℝ := 2 * gammaMomentConst 2 * Real.sqrt 2 * shellSensitivityConst d
  let a3 : ℝ := shellSensitivityConst d ^ 2
  let a4 : ℝ := 2 * finiteFieldConst d
  let a5 : ℝ := 2 * finiteFieldMomentConst d
  let a6 : ℝ := finiteFieldMomentExpConst d
  let a7 : ℝ := cutoffMomentConst
  let C : ℝ := 1 + |a1| + |a2| + |a3| + |a4| + |a5| + |a6| + |a7|
  have hC1 : 1 ≤ C := by
    have := abs_nonneg a1; have := abs_nonneg a2; have := abs_nonneg a3; have := abs_nonneg a4
    have := abs_nonneg a5; have := abs_nonneg a6; have := abs_nonneg a7
    simp only [C]; linarith
  have h1 : a1 ≤ C := by
    have := le_abs_self a1; have := abs_nonneg a2; have := abs_nonneg a3; have := abs_nonneg a4
    have := abs_nonneg a5; have := abs_nonneg a6; have := abs_nonneg a7
    simp only [C]; linarith
  have h2 : a2 ≤ C := by
    have := le_abs_self a2; have := abs_nonneg a1; have := abs_nonneg a3; have := abs_nonneg a4
    have := abs_nonneg a5; have := abs_nonneg a6; have := abs_nonneg a7
    simp only [C]; linarith
  have h3 : a3 ≤ C := by
    have := le_abs_self a3; have := abs_nonneg a1; have := abs_nonneg a2; have := abs_nonneg a4
    have := abs_nonneg a5; have := abs_nonneg a6; have := abs_nonneg a7
    simp only [C]; linarith
  have h4 : a4 ≤ C := by
    have := le_abs_self a4; have := abs_nonneg a1; have := abs_nonneg a2; have := abs_nonneg a3
    have := abs_nonneg a5; have := abs_nonneg a6; have := abs_nonneg a7
    simp only [C]; linarith
  have h5 : a5 ≤ C := by
    have := le_abs_self a5; have := abs_nonneg a1; have := abs_nonneg a2; have := abs_nonneg a3
    have := abs_nonneg a4; have := abs_nonneg a6; have := abs_nonneg a7
    simp only [C]; linarith
  have h6 : a6 ≤ C := by
    have := le_abs_self a6; have := abs_nonneg a1; have := abs_nonneg a2; have := abs_nonneg a3
    have := abs_nonneg a4; have := abs_nonneg a5; have := abs_nonneg a7
    simp only [C]; linarith
  have h7 : a7 ≤ C := by
    have := le_abs_self a7; have := abs_nonneg a1; have := abs_nonneg a2; have := abs_nonneg a3
    have := abs_nonneg a4; have := abs_nonneg a5; have := abs_nonneg a6
    simp only [C]; linarith
  refine ⟨C, by linarith, ?_⟩
  intro M n k
  have : IsProbabilityMeasure M.P.toMeasure := inferInstance
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  have hc1 : 0 < shellSensitivityConst d := shellSensitivityConst_pos d
  have hT : 0 < (3 : ℝ) ^ (k - (n : ℤ)) := zpow_pos (by norm_num) _
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (e.sensitivity.field)
    obtain ⟨Z, hZae, hZbig, hZdom⟩ := sensitivity_field M n k
    have hA : 0 < shellSensitivityConst d * M.delta * (3 : ℝ) ^ (k - (n : ℤ)) :=
      mul_pos (mul_pos hc1 hδ) hT
    obtain ⟨Zm, hZm, hog, hdom⟩ := aux_l_sensitivity_for_cutoffs_measurable_ogamma
      M.P.toMeasure Z hZae _ hA hZbig _ hZdom
    refine ⟨Zm, hZm, ?_, hdom⟩
    refine aux_l_sensitivity_for_cutoffs_ogamma_mono (by norm_num) (by positivity) ?_
      hZm.aemeasurable hog
    have hδT : 0 ≤ M.delta * (3 : ℝ) ^ (k - (n : ℤ)) := by positivity
    calc 2 * (shellSensitivityConst d * M.delta * (3 : ℝ) ^ (k - (n : ℤ)))
        = a1 * (M.delta * (3 : ℝ) ^ (k - (n : ℤ))) := by simp only [a1]; ring
      _ ≤ C * (M.delta * (3 : ℝ) ^ (k - (n : ℤ))) := mul_le_mul_of_nonneg_right h1 hδT
      _ = C * M.delta * (3 : ℝ) ^ (k - (n : ℤ)) := by ring
  · -- (e.infraredhom.approx.cutoffs.large.waves.field)
    intro xi hxi
    have hxi0 : 0 ≤ xi := by linarith
    obtain ⟨hint, hbound, hdom⟩ := infraredhom_approx_cutoffs_large_waves_field M n k xi hxi
    have hW0 : ∀ ω : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        0 ≤ Real.exp (sensitivityFieldRepresentative n k ω) - 1 := fun ω =>
      sub_nonneg.mpr (Real.one_le_exp (sensitivityFieldRepresentative_nonneg n k ω))
    refine (aux_l_sensitivity_for_cutoffs_lp_le M.P.toMeasure _ _ xi hxi hW0 hint hdom).trans
      (ENNReal.ofReal_le_ofReal (hbound.trans ?_))
    set T : ℝ := (3 : ℝ) ^ (k - (n : ℤ)) with hTdef
    have hsq : 0 ≤ Real.sqrt xi := Real.sqrt_nonneg _
    have hX : 0 ≤ Real.sqrt xi * M.delta * T := by positivity
    have hY : 0 ≤ xi * M.delta ^ 2 * T ^ 2 := by positivity
    have e1 : 2 * gammaMomentConst 2 * Real.sqrt (2 * xi) *
          (shellSensitivityConst d * M.delta * T) *
        Real.exp (xi * (shellSensitivityConst d * M.delta * T) ^ 2) =
        a2 * (Real.sqrt xi * M.delta * T) *
          Real.exp (a3 * (xi * M.delta ^ 2 * T ^ 2)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [a2, a3]
      congr 1
      · ring
      · congr 1; ring
    rw [e1]
    calc a2 * (Real.sqrt xi * M.delta * T) * Real.exp (a3 * (xi * M.delta ^ 2 * T ^ 2))
        ≤ C * (Real.sqrt xi * M.delta * T) * Real.exp (C * (xi * M.delta ^ 2 * T ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h2 hX)
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h3 hY)) (Real.exp_pos _).le
            (by have : 0 ≤ C := by linarith
                positivity)
      _ = C * Real.sqrt xi * M.delta * T * Real.exp (C * xi * M.delta ^ 2 * T ^ 2) := by ring_nf
  · intro m hnm
    have hcast : ((m - n : ℕ) : ℝ) = (m : ℝ) - n := Nat.cast_sub hnm.le
    have hscalepos : 0 < Real.sqrt ((m : ℝ) - n) + max 0 ((k : ℝ) - n) := by
      have : 0 < ((m : ℝ) - n) := by rw [← hcast]; exact_mod_cast Nat.sub_pos_of_lt hnm
      exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr this) (le_max_left _ _)
    refine ⟨?_, ?_⟩
    · -- (e.infrared.approx.cutoffs.field)
      obtain ⟨Z, hZm, hZ0, hZbig, hZdom⟩ := infrared_approx_cutoffs_field M m n k hnm
      have hA : 0 < finiteFieldConst d * M.delta * finiteFieldScale m n k := by
        refine mul_pos (mul_pos (finiteFieldConst_pos M) hδ) ?_
        exact finiteFieldScale_pos hnm k
      have hog := aux_l_sensitivity_for_cutoffs_ogamma_of_bigOWith M.P.toMeasure Z hZm hZ0 _ hA hZbig
      refine ⟨Z, hZm, ?_, hZdom⟩
      refine aux_l_sensitivity_for_cutoffs_ogamma_mono (by norm_num) (by positivity) ?_
        hZm.aemeasurable hog
      have hS : finiteFieldScale m n k = Real.sqrt ((m : ℝ) - n) + max 0 ((k : ℝ) - n) := by
        unfold finiteFieldScale; rw [hcast]
      rw [hS]
      have hδS : 0 ≤ M.delta * (Real.sqrt ((m : ℝ) - n) + max 0 ((k : ℝ) - n)) := by positivity
      calc 2 * (finiteFieldConst d * M.delta *
            (Real.sqrt ((m : ℝ) - n) + max 0 ((k : ℝ) - n)))
          = a4 * (M.delta * (Real.sqrt ((m : ℝ) - n) + max 0 ((k : ℝ) - n))) := by
            simp only [a4]; ring
        _ ≤ C * (M.delta * (Real.sqrt ((m : ℝ) - n) + max 0 ((k : ℝ) - n))) :=
            mul_le_mul_of_nonneg_right h4 hδS
        _ = _ := by ring
    · -- (e.aman.Linfty.moments)
      intro xi hxi
      have hxi0 : 0 ≤ xi := by linarith
      obtain ⟨W, hWm, hW0, hWint, hWbound, hWfwd, hWinv⟩ :=
        aman_Linfty_moments_source_bound M m n k hnm xi hxi
      have hfwd := aux_l_sensitivity_for_cutoffs_lp_le M.P.toMeasure
        (cutoffRatioLinfty M m n k) W xi hxi hW0 hWint (Filter.Eventually.of_forall hWfwd)
      have hinv := aux_l_sensitivity_for_cutoffs_lp_le M.P.toMeasure
        (inverseCutoffRatioLinfty M m n k) W xi hxi hW0 hWint (Filter.Eventually.of_forall hWinv)
      set S : ℝ := Real.sqrt ((m : ℝ) - n) + max 0 ((k : ℝ) - n) with hSdef
      set Q : ℝ := ((m : ℝ) - n) + (max 0 ((k : ℝ) - n)) ^ 2 with hQdef
      have hmn : 0 ≤ (m : ℝ) - n := by rw [← hcast]; exact Nat.cast_nonneg _
      have hS0 : 0 ≤ S := by positivity
      have hQ0 : 0 ≤ Q := by positivity
      have hB : (∫ ω, W ω ^ xi ∂M.P.toMeasure) ^ xi⁻¹ ≤
          finiteFieldMomentConst d * Real.sqrt xi * M.delta * S *
            Real.exp (finiteFieldMomentExpConst d * xi * M.delta ^ 2 * Q) := by
        have := hWbound
        simp only [hcast] at this
        exact this
      have hX : 0 ≤ Real.sqrt xi * M.delta * S := by positivity
      have hY : 0 ≤ xi * M.delta ^ 2 * Q := by positivity
      calc paperENNRealLpNorm M.P.toMeasure xi (cutoffRatioLinfty M m n k) +
            paperENNRealLpNorm M.P.toMeasure xi (inverseCutoffRatioLinfty M m n k)
          ≤ ENNReal.ofReal ((∫ ω, W ω ^ xi ∂M.P.toMeasure) ^ xi⁻¹) +
            ENNReal.ofReal ((∫ ω, W ω ^ xi ∂M.P.toMeasure) ^ xi⁻¹) := add_le_add hfwd hinv
        _ = ENNReal.ofReal (2 * (∫ ω, W ω ^ xi ∂M.P.toMeasure) ^ xi⁻¹) := by
            rw [two_mul, ENNReal.ofReal_add (Real.rpow_nonneg
              (integral_nonneg fun ω => Real.rpow_nonneg (hW0 ω) _) _)
              (Real.rpow_nonneg (integral_nonneg fun ω => Real.rpow_nonneg (hW0 ω) _) _)]
        _ ≤ ENNReal.ofReal (a5 * (Real.sqrt xi * M.delta * S) *
              Real.exp (a6 * (xi * M.delta ^ 2 * Q))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc 2 * (∫ ω, W ω ^ xi ∂M.P.toMeasure) ^ xi⁻¹
                ≤ 2 * (finiteFieldMomentConst d * Real.sqrt xi * M.delta * S *
                  Real.exp (finiteFieldMomentExpConst d * xi * M.delta ^ 2 * Q)) := by
                  linarith
              _ = a5 * (Real.sqrt xi * M.delta * S) *
                    Real.exp (a6 * (xi * M.delta ^ 2 * Q)) := by
                  simp only [a5, a6]
                  rw [show finiteFieldMomentExpConst d * xi * M.delta ^ 2 * Q =
                    finiteFieldMomentExpConst d * (xi * M.delta ^ 2 * Q) by ring]
                  ring
        _ ≤ ENNReal.ofReal (C * Real.sqrt xi * M.delta * S *
              Real.exp (C * xi * M.delta ^ 2 * Q)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc a5 * (Real.sqrt xi * M.delta * S) * Real.exp (a6 * (xi * M.delta ^ 2 * Q))
                ≤ C * (Real.sqrt xi * M.delta * S) * Real.exp (C * (xi * M.delta ^ 2 * Q)) :=
                  mul_le_mul (mul_le_mul_of_nonneg_right h5 hX)
                    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h6 hY)) (Real.exp_pos _).le
                    (by have : 0 ≤ C := by linarith
                        positivity)
              _ = C * Real.sqrt xi * M.delta * S * Real.exp (C * xi * M.delta ^ 2 * Q) := by
                  ring_nf
  · -- (e.am.Lp.moments), (e.am.Lp.moments.inv)
    intro U hU hconn hbdd m n' p hp hn hnm
    have hne : U.Nonempty := hconn.nonempty
    have := aux_l_sensitivity_for_cutoffs_nu_prob U hU hne hbdd
    have hp0 : 0 ≤ p := by linarith
    have hdiff : 0 ≤ (((m : ℤ) - n' : ℤ) : ℝ) := by
      exact_mod_cast (sub_pos.mpr hnm).le
    have hcastd : (((m : ℤ) - n' : ℤ) : ℝ) = (m : ℝ) - n' := by push_cast; ring
    have hBnn : 0 ≤ cutoffMomentConst * Real.sqrt p * M.delta *
        Real.sqrt (((m : ℤ) - n' : ℤ) : ℝ) *
        Real.exp (cutoffMomentConst * p * M.delta ^ 2 * (((m : ℤ) - n' : ℤ) : ℝ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg cutoffMomentConst_pos.le (Real.sqrt_nonneg p))
        hδ.le) (Real.sqrt_nonneg _)) (Real.exp_pos _).le
    have hmono : cutoffMomentConst * Real.sqrt p * M.delta *
        Real.sqrt (((m : ℤ) - n' : ℤ) : ℝ) *
        Real.exp (cutoffMomentConst * p * M.delta ^ 2 * (((m : ℤ) - n' : ℤ) : ℝ)) ≤
        C * Real.sqrt p * M.delta * Real.sqrt ((m : ℝ) - n') *
          Real.exp (C * p * M.delta ^ 2 * ((m : ℝ) - n')) := by
      rw [hcastd]
      have hX : 0 ≤ Real.sqrt p * M.delta * Real.sqrt ((m : ℝ) - n') := by positivity
      have hY : 0 ≤ p * M.delta ^ 2 * ((m : ℝ) - n') := by
        rw [← hcastd]; positivity
      have hC0 : 0 ≤ C := by linarith
      calc cutoffMomentConst * Real.sqrt p * M.delta * Real.sqrt ((m : ℝ) - n') *
            Real.exp (cutoffMomentConst * p * M.delta ^ 2 * ((m : ℝ) - n'))
          = a7 * (Real.sqrt p * M.delta * Real.sqrt ((m : ℝ) - n')) *
            Real.exp (a7 * (p * M.delta ^ 2 * ((m : ℝ) - n'))) := by
            simp only [a7]; ring_nf
        _ ≤ C * (Real.sqrt p * M.delta * Real.sqrt ((m : ℝ) - n')) *
            Real.exp (C * (p * M.delta ^ 2 * ((m : ℝ) - n'))) :=
            mul_le_mul (mul_le_mul_of_nonneg_right h7 hX)
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h7 hY)) (Real.exp_pos _).le
              (by positivity)
        _ = _ := by ring_nf
    constructor
    · refine (aux_l_sensitivity_for_cutoffs_tonelli M.P.toMeasure
        (aux_l_sensitivity_for_cutoffs_normalizedVolume U) (cutoffRatioMinusOne M m n') p _ hp hBnn
        (measurable_cutoffRatioMinusOne_uncurry M m n') ?_).trans
        (ENNReal.ofReal_le_ofReal hmono)
      intro x
      exact ⟨(integral_abs_cutoffRatioMinusOne_rpow_root_le_raw M m n' x p hp hn hnm).1,
        integral_abs_cutoffRatioMinusOne_rpow_root_le M m n' x p hp hn hnm⟩
    · refine (aux_l_sensitivity_for_cutoffs_tonelli M.P.toMeasure
        (aux_l_sensitivity_for_cutoffs_normalizedVolume U) (inverseCutoffRatioMinusOne M m n') p _ hp
        hBnn (measurable_inverseCutoffRatioMinusOne_uncurry M m n') ?_).trans
        (ENNReal.ofReal_le_ofReal hmono)
      intro x
      exact ⟨(integral_abs_inverseCutoffRatioMinusOne_rpow_root_le_raw M m n' x p hp hn hnm).1,
        integral_abs_inverseCutoffRatioMinusOne_rpow_root_le M m n' x p hp hn hnm⟩

end SubdiffusiveProcess.Paper
