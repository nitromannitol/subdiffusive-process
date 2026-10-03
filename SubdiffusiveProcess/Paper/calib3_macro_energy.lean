module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib3_HT
public import SubdiffusiveProcess.Paper.calib3_bank
public import SubdiffusiveProcess.Paper.calib3_prefix
public import SubdiffusiveProcess.Paper.calib3_fedata
public import SubdiffusiveProcess.Paper.calib3_macro_unit
public import SubdiffusiveProcess.Paper.prop_growth_macro_energy
public import SubdiffusiveProcess.Paper.prop_growth_trunc_macro_energy
public import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
public import SubdiffusiveProcess.Paper.aux_macro_moment_bank

@[expose] public section

/-! Stage 3 (calibration): macro-scale energy growth `ρ^{t1}` on the unit cube for the top-block-removed model
(`HT_j`, coefficient level `N + j`, FE level `N`) at all radii `3^{-(N+j)} ≤ ρ ≤ 1`, with a random constant of finite moments.
Analogue of `prop_growth_trunc_macro_energy` at unit cubes; the reference constants are deterministic
(`calib3_fedata`), so the constant is `2 Z 3^{t1 Lm}(e^{j|τ²|} + Kg)`. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise Distributions
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Moments of `2 Z · Y · (Kr + Kg)` at order `2P` from `Y, Kg ∈ L^{4P}` on a probability space. -/
theorem aux_calib3_macro_energy_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : ℝ) (hP : 1 ≤ P) (Y Kg : Ω → ℝ) (Z Kr : ℝ) (hZ : 0 ≤ Z) (hKr : 0 ≤ Kr) (BY BK : ℝ≥0∞)
    (hYm : AEStronglyMeasurable Y μ) (hBY : BY ≠ ⊤) (hBK : BK ≠ ⊤)
    (hYb : eLpNorm Y (ENNReal.ofReal (2 * (2 * P))) μ ≤ BY)
    (hK : MemLp Kg (ENNReal.ofReal (2 * (2 * P))) μ) (hKb : eLpNorm Kg (ENNReal.ofReal (2 * (2 * P))) μ ≤ BK) :
    MemLp (fun om => 2 * Z * (Y om * (Kr + Kg om))) (ENNReal.ofReal (2 * P)) μ ∧
      eLpNorm (fun om => 2 * Z * (Y om * (Kr + Kg om))) (ENNReal.ofReal (2 * P)) μ ≤
        ENNReal.ofReal (2 * Z) * (BY * (ENNReal.ofReal Kr + BK)) := by
  have hPpos : (0:ℝ) < 2 * (2 * P) := by nlinarith [hP]
  have hp4nz : ENNReal.ofReal (2 * (2 * P)) ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hPpos
  have hμnz : μ ≠ 0 := by
    intro h
    have h1 : μ Set.univ = 1 := measure_univ
    rw [h] at h1
    simp at h1
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * (2 * P)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hP])
  have hW_as : AEStronglyMeasurable (fun om => Kr + Kg om) μ :=
    (aestronglyMeasurable_const (b := Kr) (μ := μ)).add hK.aestronglyMeasurable
  have hconst : eLpNorm (fun _ : Ω => Kr) (ENNReal.ofReal (2 * (2 * P))) μ = ENNReal.ofReal Kr := by
    rw [eLpNorm_const (μ := μ) (p := ENNReal.ofReal (2 * (2 * P))) Kr hp4nz hμnz, measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_of_nonneg hKr]
  have hWb : eLpNorm (fun om => Kr + Kg om) (ENNReal.ofReal (2 * (2 * P))) μ ≤
      ENNReal.ofReal Kr + BK := by
    have hadd := eLpNorm_add_le (μ := μ) (p := ENNReal.ofReal (2 * (2 * P)))
      (f := fun _ : Ω => Kr) (g := Kg) hp1
    calc eLpNorm (fun om => Kr + Kg om) (ENNReal.ofReal (2 * (2 * P))) μ
        = eLpNorm ((fun _ : Ω => Kr) + Kg) (ENNReal.ofReal (2 * (2 * P))) μ := rfl
      _ ≤ eLpNorm (fun _ : Ω => Kr) (ENNReal.ofReal (2 * (2 * P))) μ +
            eLpNorm Kg (ENNReal.ofReal (2 * (2 * P))) μ := hadd
      _ = ENNReal.ofReal Kr + eLpNorm Kg (ENNReal.ofReal (2 * (2 * P))) μ := by rw [hconst]
      _ ≤ ENNReal.ofReal Kr + BK := add_le_add le_rfl hKb
  have hW : MemLp (fun om => Kr + Kg om) (ENNReal.ofReal (2 * (2 * P))) μ :=
    lt_top_iff_ne_top.2 (ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hBK⟩) hWb)
  have hHolder : eLpNorm (fun om => Y om * (Kr + Kg om)) (ENNReal.ofReal (2 * P)) μ ≤
      eLpNorm Y (ENNReal.ofReal (2 * (2 * P))) μ *
        eLpNorm (fun om => Kr + Kg om) (ENNReal.ofReal (2 * (2 * P))) μ :=
    aux_aux_macro_moment_bank_product_moment μ (2 * P) Y (fun om => Kr + Kg om) hYm hW_as
  have hprod_bd : eLpNorm (fun om => Y om * (Kr + Kg om)) (ENNReal.ofReal (2 * P)) μ ≤
      BY * (ENNReal.ofReal Kr + BK) := hHolder.trans (mul_le_mul' hYb hWb)
  have hprod_top : BY * (ENNReal.ofReal Kr + BK) ≠ ⊤ :=
    ENNReal.mul_ne_top hBY (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hBK⟩)
  have hprod : MemLp (fun om => Y om * (Kr + Kg om)) (ENNReal.ofReal (2 * P)) μ :=
    lt_top_iff_ne_top.2 (ne_top_of_le_ne_top hprod_top hprod_bd)
  have hc : 0 ≤ 2 * Z := by linarith
  have hscale : eLpNorm (fun om => 2 * Z * (Y om * (Kr + Kg om))) (ENNReal.ofReal (2 * P)) μ ≤
      ENNReal.ofReal (2 * Z) * eLpNorm (fun om => Y om * (Kr + Kg om)) (ENNReal.ofReal (2 * P)) μ := by
    have h := eLpNorm_const_smul_le (μ := μ) (p := ENNReal.ofReal (2 * P))
      (c := 2 * Z) (f := fun om => Y om * (Kr + Kg om))
    have h1 : ((2 * Z) • (fun om => Y om * (Kr + Kg om))) =
        (fun om => 2 * Z * (Y om * (Kr + Kg om))) := rfl
    rw [h1] at h
    rwa [Real.enorm_of_nonneg hc] at h
  refine ⟨MemLp.const_mul hprod (2 * Z), ?_⟩
  exact hscale.trans (mul_le_mul_right hprod_bd _)

/-- **Macro-scale energy growth on the unit cube for the top-block-removed model.** -/
theorem calib3_macro_energy :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (t1 : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t1 → t1 < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M), M.delta ≤ delta0 →
      ∀ (j : ℕ), 0 < j → ∀ (z : SpatialCoordinates d),
      ∃ (Kmac : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kmac N om) ∧
        (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z 1 one_pos : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z 1 one_pos : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z 1 one_pos)),
          ((b : SobolevData (centeredCube z 1 one_pos)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z one_pos) F b u →
          ∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ centeredCube z 1 one_pos → 0 < rad → rad ≤ 1 →
            (3 : ℝ) ^ (-((N + j : ℕ) : ℤ)) ≤ rad →
            localGradientEnergy (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z one_pos)
                (s := Metric.ball x rad ∩
                  (centeredCube z 1 one_pos : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z 1 one_pos).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z 1 one_pos))) ≤
              Kmac N om * (Kf + Cphi) ^ 2 * rad ^ t1 := by
  intro d hd _ _ E P X S t1 k ps ht1 ht2 hps
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  -- one exponent for all listed orders
  obtain ⟨Pexp, hPdef⟩ : ∃ Pexp : ℝ, Pexp = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => by linarith [hps i]
  have hP1 : 1 ≤ Pexp := by rw [hPdef]; linarith
  have hpsP : ∀ i, ps i ≤ Pexp := by
    intro i
    rw [hPdef]
    have := Finset.single_le_sum (f := ps) (fun j _ => by linarith [hps j]) (Finset.mem_univ i)
    linarith
  have ht10 : 0 < t1 := by linarith
  -- suppliers, all fixed before the model
  obtain ⟨dB, hdB, hbank⟩ := calib3_bank d hd E P X S (2 * (2 * Pexp)) (by linarith)
  obtain ⟨dA, hdA, hthr⟩ := aux_aux_macro_moment_bank_threshold (d := d) t1 (2 * Pexp) ht1 ht2
    ht10.le (by linarith)
  obtain ⟨Cp, -, hFE⟩ := aux_aux_macro_energy_recurrence_finite_estimate (d := d) hd
  refine ⟨min dB dA, lt_min hdB hdA, ?_⟩
  intro M Rm hδ j hj z
  have hδB : M.delta ≤ dB := hδ.trans (min_le_left _ _)
  have hδA : M.delta ≤ dA := hδ.trans (min_le_right _ _)
  -- the native regularity input and its thresholds
  obtain ⟨hδC, hα, hκ'⟩ := hthr M (aux_prop_growth_macro_energy_nativeSreg M) hδA
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 /
      ((aux_prop_growth_macro_energy_nativeSreg M).C * M.delta ^ 2 * |Real.log M.delta|) :=
    ⟨_, rfl⟩
  rw [← hκ] at hκ'
  have hlam : 0 ≤ 2 * (2 * Pexp) * t1 * Real.log 3 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    have : (0 : ℝ) ≤ Pexp := by linarith
    positivity
  have hκ0 : 0 < κ := lt_of_le_of_lt hlam hκ'
  obtain ⟨Lm, hLmeas, hLtail, hLpre⟩ := calib3_prefix M (aux_prop_growth_macro_energy_nativeSreg M)
    (1 - ((d : ℝ) - t1) / 4) κ hδC hα hκ hκ0 z j
  have hA1 : 1 ≤ (aux_prop_growth_macro_energy_nativeSreg M).C *
      Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M).C) := by
    have h1 : 1 ≤ (aux_prop_growth_macro_energy_nativeSreg M).C :=
      (aux_prop_growth_macro_energy_nativeSreg M).C_ge_one
    have h2 : 1 ≤ Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M).C) :=
      Real.one_le_exp (by positivity)
    nlinarith
  have hX : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M).C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M).C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * (2 * Pexp))) := by
    intro n
    have hraw := aux_aux_macro_moment_bank_eLpNorm_rpow_three_le _ (Lm n) t1 (2 * (2 * Pexp))
      (by linarith) _ (aux_aux_macro_moment_bank_lintegral_exp_le
        (chaosSampleLaw M).toMeasure (Lm n) (hLmeas n) _ κ _ hA1 hlam hκ' (hLtail n))
    have hXm : AEStronglyMeasurable (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
        (chaosSampleLaw M).toMeasure := by
      simpa only [Function.comp_def, Pi.mul_apply] using!
        (measurable_const.pow (measurable_const.mul
          (measurable_from_top.comp (hLmeas n)))).aestronglyMeasurable
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hXm] at hraw
    exact hraw
  -- the global-energy bank at the unit cube
  obtain ⟨Kg, Cg, hKg0, hKgmem, hKgnorm, hKgsrc⟩ := hbank M Rm hδB j hj z
  set Z := aux_aux_macro_energy_recurrence_Z (aux_prop_growth_macro_energy_nativeSreg M).C Cp t1 d with hZdef
  have hZ0 : 0 ≤ Z := aux_aux_macro_energy_recurrence_Z_nonneg _ _ _ _
  set Kr : ℝ := Real.exp ((j : ℝ) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) with hKrdef
  have hKr0 : 0 ≤ Kr := (Real.exp_pos _).le
  obtain ⟨BY, hBYdef⟩ : ∃ BY : ℝ≥0∞, BY =
      ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M).C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M).C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * (2 * Pexp))) :=
    ⟨_, rfl⟩
  have hBYfin : BY ≠ ⊤ := by
    rw [hBYdef]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hYm : ∀ N, AEStronglyMeasurable (fun om => (3 : ℝ) ^ (t1 * (Lm N om : ℝ)))
      (chaosSampleLaw M).toMeasure := fun N =>
    (measurable_const.pow (measurable_const.mul (measurable_from_top.comp (hLmeas N)))).aestronglyMeasurable
  have hmom := fun N => aux_calib3_macro_energy_moment (chaosSampleLaw M).toMeasure Pexp hP1
    (fun om => (3 : ℝ) ^ (t1 * (Lm N om : ℝ))) (Kg (N + j)) Z Kr hZ0 hKr0 BY (ENNReal.ofReal Cg)
    (hYm N) hBYfin ENNReal.ofReal_ne_top (by rw [hBYdef]; exact hX N) (hKgmem (N + j)) (hKgnorm (N + j))
  obtain ⟨Btot, hBtot⟩ : ∃ Btot : ℝ≥0∞, Btot =
      ENNReal.ofReal (2 * Z) * (BY * (ENNReal.ofReal Kr + ENNReal.ofReal Cg)) := ⟨_, rfl⟩
  have hfin : Btot ≠ ⊤ := by
    rw [hBtot]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hBYfin
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩))
  have hexp : ∀ i, ENNReal.ofReal (ps i) ≤ ENNReal.ofReal (2 * Pexp) := fun i =>
    ENNReal.ofReal_le_ofReal (by linarith [hpsP i, hP1])
  refine ⟨fun N om => 2 * Z * ((3 : ℝ) ^ (t1 * (Lm N om : ℝ)) * (Kr + Kg (N + j) om)),
    fun _ => Btot.toReal, ?_, ?_, ?_, ?_⟩
  · intro N om
    have := hKg0 (N + j) om
    positivity
  · intro i N
    obtain ⟨hm, hb⟩ := hmom N
    exact hm.mono_exponent (hexp i)
  · intro i N
    obtain ⟨hm, hb⟩ := hmom N
    rw [ENNReal.ofReal_toReal hfin]
    exact ((eLpNorm_le_eLpNorm_of_exponent_le (hexp i)).trans (hb.trans (le_of_eq hBtot.symm)))
  · filter_upwards [hKgsrc] with om hKg
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve x rad hx hrad0 hrad1 hradN
    have hR : (0 : ℝ) < 3 ^ (N + j) := by positivity
    obtain ⟨cF, hcF, hid, hk1, hk2⟩ := calib3_fedata M Rm (aux_prop_growth_macro_energy_nativeSreg M) om j N hj z
      one_pos hR
    have hform := hKg (N + j) F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have h3P : 0 ≤ (3 : ℝ) ^ (t1 * (Lm N om : ℝ)) := by positivity
    have hKg0' := hKg0 (N + j) om
    have hX0 : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
    have hKr' : (3 : ℝ) ^ (t1 * (Lm N om : ℝ)) * Kr ≤
        (3 : ℝ) ^ (t1 * (Lm N om : ℝ)) * (Kr + Kg (N + j) om) :=
      mul_le_mul_of_nonneg_left (by linarith) h3P
    have hKsrc : (3 : ℝ) ^ (t1 * (Lm N om : ℝ)) *
        sobolevCoefficientForm (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z one_pos)
          (u : SobolevData (centeredCube z 1 one_pos)) (u : SobolevData (centeredCube z 1 one_pos)) ≤
        ((3 : ℝ) ^ (t1 * (Lm N om : ℝ)) * (Kr + Kg (N + j) om)) * (Kf + Cphi) ^ 2 := by
      calc _ ≤ (3 : ℝ) ^ (t1 * (Lm N om : ℝ)) * (Kg (N + j) om * (Kf + Cphi) ^ 2) :=
            mul_le_mul_of_nonneg_left hform h3P
        _ ≤ _ := by
            have : (3 : ℝ) ^ (t1 * (Lm N om : ℝ)) * (Kg (N + j) om * (Kf + Cphi) ^ 2) ≤
                (3 : ℝ) ^ (t1 * (Lm N om : ℝ)) * ((Kr + Kg (N + j) om) * (Kf + Cphi) ^ 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hX0) h3P
            linarith [this, mul_assoc ((3 : ℝ) ^ (t1 * (Lm N om : ℝ))) (Kr + Kg (N + j) om) ((Kf + Cphi) ^ 2)]
    have hunit := calib3_macro_unit hd Cp hFE M (aux_prop_growth_macro_energy_nativeSreg M) t1 ht1 ht2 hδC hα
      (calib3_HT d j) om z (N + j) (Lm N om) hR Kr N ⟨cF, hcF, hid, hk1, hk2⟩ (hLpre om N) _ hKr' F Kf hKf hFm hFb
      phi Cphi hphi hCphi b u hb hsolve hKsrc x rad hx hrad0 hrad1 hradN
    refine hunit.trans (le_of_eq ?_)
    ring

end Paper
