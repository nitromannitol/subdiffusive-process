module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib3_HT
public import SubdiffusiveProcess.Paper.calib3_bank_cross
public import SubdiffusiveProcess.Paper.calib3_prefix
public import SubdiffusiveProcess.Paper.calib3_fedata
public import SubdiffusiveProcess.Paper.calib3_envelope
public import SubdiffusiveProcess.Paper.calib3_macro_energy
public import SubdiffusiveProcess.Paper.calib3_holder_assemble
public import SubdiffusiveProcess.Paper.calib3_holder_ae_bound
public import SubdiffusiveProcess.Paper.prop_growth_holder_macro_campanato
public import SubdiffusiveProcess.Paper.prop_growth_trunc_holder_macro
public import SubdiffusiveProcess.Paper.lane4_lambda_inv_moments
public import SubdiffusiveProcess.Paper.aux_macro_moment_bank
public import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence

@[expose] public section

/-! Stage 3 (calibration): macro Campanato decay (mean-oscillation growth `rad^{2α}`) above the wavelength on the unit cube for the
top-block-removed model `HT_j` (coefficient level `N + j`, FE level `N`).  Analogue of `prop_growth_trunc_holder_macro` at unit
cubes, instantiated at `r = 1`, `kk = 0`, `M' = M` of `calib3_holder_assemble`. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- A constant has `L^p` norm at most its absolute value on a probability space. -/
theorem aux_calib3_holder_macro_const_norm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 1 ≤ p) (c : ℝ) (hc : 0 ≤ c) :
    eLpNorm (fun _ : Ω => c) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal c := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    linarith
  have hμ : μ ≠ 0 := IsProbabilityMeasure.ne_zero μ
  rw [eLpNorm_const c hp0 hμ, measure_univ, ENNReal.one_rpow, mul_one,
      Real.enorm_of_nonneg hc]

/-- The residual shift at `r = 1`, `kk = 0` is the identity. -/
theorem aux_calib3_holder_macro_shift_id {d : ℕ} :
    MacroAllCube.residualShift (d := d) 1 0 = id := by
  funext om
  funext j
  ext x
  rw [MacroAllCube.residualShift_apply]
  simp

/-- At `kk = 0`, `M' = M` the normalization constant and envelope are `1`. -/
theorem aux_calib3_holder_macro_shift_bounds {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (om : BilateralField d) :
    aux_prop_growth_macro_energy_shiftC M M 0 n om ≤ aux_prop_growth_macro_energy_env M 0 om ∧
      (aux_prop_growth_macro_energy_shiftC M M 0 n om)⁻¹ ≤ aux_prop_growth_macro_energy_env M 0 om := by
  have hs : aux_prop_growth_macro_energy_shiftC M M 0 n om = 1 := by
    unfold aux_prop_growth_macro_energy_shiftC MacroAllCube.lowAnchor
    simp only [Nat.add_zero, Nat.cast_zero, Finset.range_zero, Finset.sum_empty,
      mul_zero, zero_mul, sub_zero, Real.exp_zero, mul_one]
    rw [div_self (ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M n))]
  have he : aux_prop_growth_macro_energy_env M 0 om = 1 := by
    unfold aux_prop_growth_macro_energy_env MacroAllCube.lowAnchor
    simp only [Nat.cast_zero, Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul,
      abs_zero, add_zero, Real.exp_zero]
  rw [hs, he]
  norm_num

/-- The coefficient identity at `r = 1`, `kk = 0`, `M' = M`. -/
theorem aux_calib3_holder_macro_coefid {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (n : ℕ) (om : BilateralField d) (x : SpatialCoordinates d) :
    cutoffCoefficient M H om (n + 0) ((1 : ℝ) • x) =
      aux_prop_growth_macro_energy_shiftC M M 0 n om *
        cutoffCoefficient M H (MacroAllCube.residualShift (d := d) 1 0 om) n x := by
  have hs : aux_prop_growth_macro_energy_shiftC M M 0 n om = 1 := by
    unfold aux_prop_growth_macro_energy_shiftC MacroAllCube.lowAnchor
    simp [div_self (ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M n))]
  have hr : MacroAllCube.residualShift (d := d) 1 0 om = om := by
    funext j
    ext y
    simp [MacroAllCube.residualShift_apply]
  rw [hs, hr]
  simp [cutoffCoefficient]

/-- The prefix lengths (indexed by the frame `n`, FE level `n - j`), their exponential moments, and the frame data of
`calib3_fedata` at every frame `n ≥ j` (deterministic reference `exp (j |τ²|)`). -/
theorem aux_calib3_holder_macro_frame {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (z : SpatialCoordinates d) (j : ℕ) (hj : 0 < j) (t1 Pexp : ℝ) (hP1 : 1 ≤ Pexp) (ht10 : 0 ≤ t1)
    (hδC : M.delta ≤ (aux_prop_growth_macro_energy_nativeSreg M).C⁻¹)
    (hα' : 1 - ((d : ℝ) - t1) / 4 ∈ (aux_prop_growth_macro_energy_nativeSreg M).alphaRange)
    (κ : ℝ) (hκ : κ = (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 /
      ((aux_prop_growth_macro_energy_nativeSreg M).C * M.delta ^ 2 * |Real.log M.delta|))
    (hκ' : 2 * (2 * Pexp) * t1 * Real.log 3 < κ) :
    ∃ (Lm : ℕ → BilateralField d → ℕ) (BX : ℝ≥0∞), (∀ n, Measurable (Lm n)) ∧ BX ≠ ⊤ ∧
      (∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
        (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤ BX) ∧
      aux_calib3_holder_ae_bound_FEData (aux_prop_growth_macro_energy_nativeSreg M)
        (calib3_HT d j) t1 z 1 Lm (fun _ => Real.exp ((j : ℝ) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|)) j := by
  have hlam : 0 ≤ 2 * (2 * Pexp) * t1 * Real.log 3 := by
    have : (0 : ℝ) ≤ Pexp := by linarith
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    positivity
  have hκ0 : 0 < κ := lt_of_le_of_lt hlam hκ'
  obtain ⟨Lm0, hLmeas0, hLtail, hLpre0⟩ := calib3_prefix M (aux_prop_growth_macro_energy_nativeSreg M)
    (1 - ((d : ℝ) - t1) / 4) κ hδC hα' hκ hκ0 ((1 : ℝ)⁻¹ • z) j
  obtain ⟨Lm, hLmdef⟩ : ∃ Lm : ℕ → BilateralField d → ℕ, Lm = fun n om => Lm0 (n - j) om := ⟨_, rfl⟩
  have hLmeas : ∀ n, Measurable (Lm n) := fun n => by rw [hLmdef]; exact hLmeas0 (n - j)
  have hA1 : 1 ≤ (aux_prop_growth_macro_energy_nativeSreg M).C *
      Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M).C) := by
    have h1 : 1 ≤ (aux_prop_growth_macro_energy_nativeSreg M).C :=
      (aux_prop_growth_macro_energy_nativeSreg M).C_ge_one
    have h2 : 1 ≤ Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M).C) :=
      Real.one_le_exp (mul_nonneg hκ0.le (by linarith))
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hX4 : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm0 n om : ℝ)))
      (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M).C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M).C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * (2 * Pexp))) := by
    intro n
    have hraw := aux_aux_macro_moment_bank_eLpNorm_rpow_three_le _ (Lm0 n) t1 (2 * (2 * Pexp))
      (by linarith) _ (aux_aux_macro_moment_bank_lintegral_exp_le (chaosSampleLaw M).toMeasure
        (Lm0 n) (hLmeas0 n) _ κ _ hA1 hlam hκ' (hLtail n))
    have hXm : AEStronglyMeasurable (fun om => (3 : ℝ) ^ (t1 * (Lm0 n om : ℝ)))
        (chaosSampleLaw M).toMeasure := by
      simpa only [Function.comp_def, Pi.mul_apply] using!
        (measurable_const.pow (measurable_const.mul
          (measurable_from_top.comp (hLmeas0 n)))).aestronglyMeasurable
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hXm] at hraw
    exact hraw
  have hle24 : ENNReal.ofReal (2 * Pexp) ≤ ENNReal.ofReal (2 * (2 * Pexp)) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨Lm, ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M).C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M).C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * (2 * Pexp))),
    hLmeas, ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top, ?_, ?_⟩
  · intro n
    have hXmeas : Measurable (fun om : BilateralField d => (3 : ℝ) ^ (t1 * (Lm0 (n - j) om : ℝ))) :=
      measurable_const.pow (measurable_const.mul
        ((measurable_from_nat (f := fun m : ℕ => (m : ℝ))).comp (hLmeas0 (n - j))))
    have h := (eLpNorm_le_eLpNorm_of_exponent_le hle24).trans (hX4 (n - j))
    rw [hLmdef]
    exact h
  · intro n hjn om'
    obtain ⟨N, rfl⟩ : ∃ N, n = N + j := ⟨n - j, by omega⟩
    obtain ⟨cF, hcF, hid, hk1, hk2⟩ := calib3_fedata M Rm (aux_prop_growth_macro_energy_nativeSreg M) om' j N hj
      ((1 : ℝ)⁻¹ • z) one_pos (pow_pos (by norm_num) (N + j))
    refine ⟨N, cF, hcF, hid, hk1, hk2, ?_⟩
    have h := hLpre0 om' N
    rw [hLmdef]
    simpa using h

/-- Reindexing of the macro energy from the pure level `N` (coefficient level `N + j`) to the frame. -/
theorem aux_calib3_holder_macro_mac {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : SpatialCoordinates d)
    (j : ℕ) (t1 : ℝ) (Kmac0 : ℕ → BilateralField d → ℝ)
    (hmacP : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
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
              Kmac0 N om * (Kf + Cphi) ^ 2 * rad ^ t1) :
    ∃ Kmac : ℕ → BilateralField d → ℝ, (∀ n om, Kmac n om = Kmac0 (n - j) om) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ), j ≤ N → ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
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
        SolvesDirichlet (cutoffPositiveCoefficient M (calib3_HT d j) om N z one_pos) F b u →
        ∀ (x : SpatialCoordinates d) (rad : ℝ),
          x ∈ centeredCube z 1 one_pos → 0 < rad → rad ≤ 1 →
          (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
          localGradientEnergy (cutoffPositiveCoefficient M (calib3_HT d j) om N z one_pos)
              (s := Metric.ball x rad ∩
                (centeredCube z 1 one_pos : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter
                (centeredCube z 1 one_pos).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (centeredCube z 1 one_pos))) ≤
            Kmac N om * (Kf + Cphi) ^ 2 * rad ^ t1 := by
  refine ⟨fun n om => Kmac0 (n - j) om, fun n om => rfl, ?_⟩
  filter_upwards [hmacP] with om h
  intro N' hjN'
  obtain ⟨N, rfl⟩ : ∃ N, N' = N + j := ⟨N' - j, by omega⟩
  have hK : Kmac0 (N + j - j) om = Kmac0 N om := by simp
  intro F Kf hKf hF hFb phi Cphi hphi hC b u hb hsol x hx rad h0 h1 h2
  have h' := h N F Kf hKf hF hFb phi Cphi hphi hC b u hb hsol x hx rad h0 h1 h2
  show _ ≤ Kmac0 (N + j - j) om * _ * _
  rw [hK]
  exact h'

/-- **Macro Campanato decay on the unit cube for the top-block-removed model.** -/
theorem calib3_holder_macro :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E) (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M), M.delta ≤ delta0 →
      ∀ (j : ℕ), 0 < j → ∀ (z : SpatialCoordinates d),
      ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kosc N om) ∧
        (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z 1 one_pos : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z 1 one_pos)),
          ((b : SobolevData (centeredCube z 1 one_pos)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z one_pos) F b u →
          ∀ x ∈ centeredCube z 1 one_pos, ∀ rad : ℝ, (3 : ℝ) ^ (-((N + j : ℕ) : ℤ)) ≤ rad → rad ≤ 1 →
            ∫ y in Metric.ball x rad ∩ (centeredCube z 1 one_pos : Set (SpatialCoordinates d)),
                ((u : SobolevData (centeredCube z 1 one_pos)).1 y - setAverage
                  (Metric.ball x rad ∩ (centeredCube z 1 one_pos : Set (SpatialCoordinates d)))
                  (u : SobolevData (centeredCube z 1 one_pos)).1) ^ 2
                ∂volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d)) ≤
              (Kosc N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) := by
  intro d hd _ _ E P X S alpha k ps ha0 ha1 hps
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
  -- the energy exponent and the excess
  obtain ⟨t1, ht1, ht2, ht10, hαM, he0, ht1Y⟩ :=
    aux_prop_growth_holder_macro_campanato_params d hd alpha ha0 ha1
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 2 + t1 - 2 * alpha - d := ⟨_, rfl⟩
  have he : 0 < e := by rw [hedef]; exact he0
  have hexp : 2 + t1 = 2 * alpha + d + e := by rw [hedef]; ring
  -- suppliers, all fixed before the model
  obtain ⟨dMac, hdMac, hmacro⟩ := calib3_macro_energy d hd E P X S t1 1 (fun _ => Pexp)
    ht1 ht2 (fun _ => hP1)
  obtain ⟨dB, hdB, hbank⟩ := calib3_bank_cross d hd E P X S (2 * Pexp) (by linarith)
  obtain ⟨dA, hdA, hthr⟩ := aux_aux_macro_moment_bank_threshold (d := d) t1 (2 * Pexp) ht1 ht2
    ht10 (by linarith)
  obtain ⟨dLf, hdLf, hlamM⟩ := lane4_lambda_inv_moments d hd E (1 / 8)
    ⟨by norm_num, by norm_num⟩
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hroot⟩ := calib3_envelope d hd Pexp hP1
  obtain ⟨CPw, hCPw0, hPoinc⟩ := aux_prop_growth_holder_micro_campanato_scaled_poincare d (by omega)
  obtain ⟨Cp, hCp, hFO⟩ := aux_prop_growth_holder_macro_campanato_FO_exists (d := d) hd
  obtain ⟨Kd, hKd1, hKd⟩ := aux_prop_growth_holder_macro_campanato_unit' (d := d) alpha ha0 ha1.le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdL := hdLf (2 * Pexp) (by linarith)
  obtain ⟨dabs, hdabs⟩ : ∃ s : ℝ, s = min 1 ((e / 2) * Real.log 3 / (Cd + Cpe)) := ⟨_, rfl⟩
  have hdabs0 : 0 < dabs := by
    rw [hdabs]
    exact lt_min one_pos (div_pos (mul_pos (half_pos he) hlog3) (add_pos hCd hCpe))
  refine ⟨min dMac (min dB (min dA (min (dLf (2 * Pexp)) (min (cd / (2 * Pexp)) dabs)))),
    lt_min hdMac (lt_min hdB (lt_min hdA (lt_min hdL (lt_min (div_pos hcd (by linarith)) hdabs0)))), ?_⟩
  intro M Rm hδ j hj z
  have hδMac : M.delta ≤ dMac := hδ.trans (min_le_left _ _)
  have hδB : M.delta ≤ dB := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδA : M.delta ≤ dA :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδL : M.delta ≤ dLf (2 * Pexp) :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))
  have hδc : M.delta ≤ cd / (2 * Pexp) :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))
  have hδabs : M.delta ≤ dabs :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))))
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ (e / 2) * Real.log 3 :=
    aux_prop_growth_holder_micro_campanato_rate Cd Cpe e M.delta hCd hCpe hdpos (hδabs.trans_eq hdabs)
  -- the native regularity input and its thresholds
  obtain ⟨hδC, hα', hκ'⟩ := hthr M (aux_prop_growth_macro_energy_nativeSreg M) hδA
  obtain ⟨H0, hH0⟩ := exists_infraredCharacterization hd M
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 /
      ((aux_prop_growth_macro_energy_nativeSreg M).C * M.delta ^ 2 * |Real.log M.delta|) :=
    ⟨_, rfl⟩
  rw [← hκ] at hκ'
  -- the prefix lengths and the frame data
  obtain ⟨Lm, BX, hLmeas, hBX, hX, hFEd⟩ := aux_calib3_holder_macro_frame M Rm z j hj t1 Pexp hP1 ht10
    hδC hα' κ hκ hκ'
  -- the macro energy of the actual problem, reindexed to the frame
  obtain ⟨Kmac0, CbK, hKmac00, hKmacmem0, hKmacnorm0, hmacP⟩ := hmacro M Rm hδMac j hj z
  obtain ⟨Kmac, hKmacdef, hmacE⟩ := aux_calib3_holder_macro_mac M z j t1 Kmac0 hmacP
  have hKmac0 : ∀ N om, 0 ≤ Kmac N om := fun N om => by rw [hKmacdef N om]; exact hKmac00 _ _
  -- the global energy
  obtain ⟨Kg, Cg, hKg0, hKgmem, hKgnorm, hKgsrc⟩ := hbank M Rm hδB H0 hH0 j hj z
  -- the coarse ellipticity of the root
  obtain ⟨CbL, hLmem, hLnorm⟩ := hlamM M Rm H0 hH0 z 1 one_pos le_rfl (2 * Pexp) (by linarith) hδL
  -- the coefficient floor
  obtain ⟨D, Mx, CD, CE, hCD, hCE, hDMx0, hext, hmem, -, hMxmom⟩ := hroot M hδc j hj z
  -- the deterministic reference
  obtain ⟨Kr, hKrdef⟩ : ∃ Kr : ℝ, Kr = Real.exp ((j : ℝ) * |SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P|) := ⟨_, rfl⟩
  have hKr0 : 0 ≤ Kr := by rw [hKrdef]; exact (Real.exp_pos _).le
  rw [← hKrdef] at hFEd
  have hRn := aux_calib3_holder_macro_const_norm (chaosSampleLaw M).toMeasure (2 * Pexp) (by linarith) Kr hKr0
  have hT : MeasurePreserving (MacroAllCube.residualShift (d := d) 1 0)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
    rw [aux_calib3_holder_macro_shift_id]
    exact MeasurePreserving.id _
  obtain ⟨Kosc, Cbound, hKosc0, hKoscmem, hKoscnorm, hKoscae⟩ :=
    calib3_holder_assemble hd P Cp hCp hFO CPw hCPw0 hPoinc alpha ha0 Kd hKd1 hKd ps Pexp hP1 hpsP M M
      (calib3_HT d j) (calib3_HT d j) H0 j t1 e ht10 hδC hα' hαM he hexp ht1Y z 1 one_pos le_rfl 0
      (by norm_num) (by norm_num) hT (aux_calib3_holder_macro_shift_bounds M) Lm hLmeas
      (fun n om x => aux_calib3_holder_macro_coefid M (calib3_HT d j) n om x) (fun _ => Kr) hFEd BX hBX hX measurable_const
      (ENNReal.ofReal Kr) ENNReal.ofReal_ne_top hRn
      Kmac (CbK 0) hKmac0
      (fun N => by
        have h : Kmac N = Kmac0 (N - j) := funext (hKmacdef N)
        rw [h]; exact (hKmacmem0 0 (N - j)).aestronglyMeasurable)
      (fun N => by
        have h : Kmac N = Kmac0 (N - j) := funext (hKmacdef N)
        rw [h]; exact hKmacnorm0 0 (N - j)) hmacE Kg Cg hKg0
      (fun N => (hKgmem N).aestronglyMeasurable) hKgnorm hKgsrc
      CbL (fun N => (hLmem N).aestronglyMeasurable) hLnorm Mx _ (fun N om => (hDMx0 N om).2) (fun N => (hmem N).2.aestronglyMeasurable)
      (fun N => aux_prop_growth_holder_macro_campanato_mx_moment _ _ (Mx N) e _ CE he hrate hCE N 0
        (hMxmom N))
      (by
        filter_upwards [hext] with om h
        intro N
        exact ⟨(h N).1, fun x hx => ((h N).2.1 x hx).1⟩)
  refine ⟨fun N om => Kosc (N + j) om, Cbound, fun N om => hKosc0 _ _, fun i N => hKoscmem i _,
    fun i N => hKoscnorm i _, ?_⟩
  filter_upwards [hKoscae] with om h
  intro N F Kf hKf hF hFb phi Cphi hphi hC b u hb hsol x hx rad hradN hrad1
  exact h (N + j) (by omega) F Kf hKf hF hFb phi Cphi hphi hC b u hb hsol x hx rad hradN hrad1

end Paper
