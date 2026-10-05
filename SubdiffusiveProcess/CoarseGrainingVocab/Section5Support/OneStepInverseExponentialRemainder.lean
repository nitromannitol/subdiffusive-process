module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepWeightedEnergyMoment

@[expose] public section




open MeasureTheory Homogenization Homogenization.IndependentSums
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Remainder after extracting the odd term `-zeta` from `exp (-H) - 1`. -/
def oneStepInverseExpRemainderAt {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (x : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  Real.exp (-oneStepCenteredShellAt M n h x omega) - 1 +
    cutoffShellSum (n + h) (n : ℤ) x omega

/-- Exact reciprocal multiplier split. -/
theorem oneStepInverseMultiplierAt_eq_negShell_add_remainder {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (x : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Real.exp (-oneStepCenteredShellAt M n h x omega) - 1 =
      -cutoffShellSum (n + h) (n : ℤ) x omega +
        oneStepInverseExpRemainderAt M n h x omega := by
  unfold oneStepInverseExpRemainderAt
  ring

/-- The reciprocal remainder obeys the same global quadratic envelope as
the forward remainder. -/
theorem abs_oneStepInverseExpRemainderAt_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (x : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    |oneStepInverseExpRemainderAt M n h x omega| ≤
      ((oneStepCenteredShellAt M n h x omega) ^ 2 / 2) *
          Real.exp |oneStepCenteredShellAt M n h x omega| +
        (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P := by
  let H := oneStepCenteredShellAt M n h x omega
  let b := (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
  have hb0 : 0 ≤ b := mul_nonneg (Nat.cast_nonneg h) M.G4.tauSq_pos.le
  have hrewrite : oneStepInverseExpRemainderAt M n h x omega =
      (Real.exp (-H) - 1 + H) + b := by
    dsimp only [oneStepInverseExpRemainderAt, oneStepCenteredShellAt, H, b]
    ring
  rw [hrewrite]
  calc
    |(Real.exp (-H) - 1 + H) + b| ≤
        |Real.exp (-H) - 1 + H| + |b| := abs_add_le _ _
    _ ≤ ((-H) ^ 2 / 2) * Real.exp |-H| + b := by
      rw [abs_of_nonneg hb0]
      have hTaylor := abs_exp_sub_one_sub_id_le_half_sq_mul_exp_abs (-H)
      simpa only [sub_neg_eq_add] using! add_le_add hTaylor le_rfl
    _ = (H ^ 2 / 2) * Real.exp |H| + b := by
      simp only [neg_sq, abs_neg]

/-- Fixed-point fourth-moment estimate for the reciprocal remainder. -/
theorem eLpNorm_oneStepInverseExpRemainderAt_four_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (x : Vec d) (hh : 0 < h) :
    eLpNorm (oneStepInverseExpRemainderAt M n h x) 4 M.P.toMeasure ≤
      oneStepExpRemainderFourBound M h := by
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := cutoffShellSum (n + h) (n : ℤ) x
  let A : ℝ := cutoffGammaConst * Real.sqrt (h : ℝ) * M.delta
  let b : ℝ := (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
  let H : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ X omega - b
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ |H omega| ^ (2 : ℝ)
  let g : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ Real.exp |H omega|
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (mul_pos cutoffGammaConst_pos
      (Real.sqrt_pos.mpr (by positivity))) M.shellPrefix.delta_pos
  have hXmeas : AEMeasurable X M.P.toMeasure :=
    (measurable_cutoffShellSum (n + h) (n : ℤ) x).aemeasurable
  have hXgamma : IsBigO M.P.toMeasure (gammaSigma 2) X A := by
    have hraw := isBigO_gammaTwo_cutoffShellSum_sourceScale
      M (n + h) (n : ℤ) x (by omega)
        (by exact_mod_cast Nat.lt_add_of_pos_right hh)
    have hdiff : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
      push_cast
      ring
    simpa only [X, A, hdiff] using! hraw
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    exact mul_nonneg (Nat.cast_nonneg h) M.G4.tauSq_pos.le
  have hHaem : AEMeasurable H M.P.toMeasure := hXmeas.sub_const b
  have hH16 : eLpNorm H 16 M.P.toMeasure ≤
      ENNReal.ofReal (gammaMomentConst 2 * Real.sqrt 16 * (A + |b|)) := by
    simpa only [H, ENNReal.ofReal_ofNat] using!
      SubdiffusiveProcess.CoarseGrainingVocab.eLpNorm_le_of_isBigO_gammaTwo
        (A := A + |b|) (p := 16)
        (add_pos_of_pos_of_nonneg hA (abs_nonneg b)) (by norm_num)
        (hXmeas.sub_const b)
        (by simpa only [H] using!
          SubdiffusiveProcess.CoarseGrainingVocab.isBigO_gammaTwo_sub_const hXgamma)
  have hfNorm : eLpNorm f 8 M.P.toMeasure =
      eLpNorm H 16 M.P.toMeasure ^ (2 : ℝ) := by
    have hr := eLpNorm_norm_rpow (μ := M.P.toMeasure) H
      (p := (8 : ℝ≥0∞)) (q := (2 : ℝ)) hHaem.aestronglyMeasurable (by norm_num)
    convert hr using 1
    all_goals
      norm_num only [f, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_ofNat,
        ENNReal.rpow_two]
  have hgNorm : eLpNorm g 8 M.P.toMeasure ≤
      (ENNReal.ofReal
        (4 * Real.exp (8 ^ 2 * A ^ 2 / 2 + 8 * |b|))) ^ (8 : ℝ)⁻¹ := by
    simpa only [g, H, ENNReal.ofReal_ofNat] using!
      eLpNorm_exp_abs_sub_const_le
        (mu := M.P.toMeasure) (X := X) (A := A) (q := 8) (b := b)
        hA (by norm_num) hXmeas hXgamma
  let : ENNReal.HolderTriple (8 : ℝ≥0∞) (8 : ℝ≥0∞) (4 : ℝ≥0∞) :=
    { inv_add_inv_eq_inv := by
        rw [← two_mul]
        have h8 : (8 : ℝ≥0∞) = 2 * 4 := by norm_num
        rw [h8, ENNReal.mul_inv (Or.inl (by norm_num))
          (Or.inl (by norm_num))]
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num)
          (by norm_num), one_mul] }
  have hfg : eLpNorm (fun omega ↦ f omega * g omega) 4 M.P.toMeasure ≤
      eLpNorm f 8 M.P.toMeasure * eLpNorm g 8 M.P.toMeasure := by
    simpa using! eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (fun a c : ℝ ↦ a * c) 1 continuous_mul
      ((hHaem.norm.pow_const 2).aestronglyMeasurable)
      ((Real.measurable_exp.comp_aemeasurable hHaem.norm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega ↦ by simp)
  have hmain : eLpNorm (fun omega ↦
      ((H omega) ^ 2 / 2) * Real.exp |H omega|) 4 M.P.toMeasure ≤
      (2 : ℝ≥0∞)⁻¹ *
        (ENNReal.ofReal (gammaMomentConst 2 * Real.sqrt 16 * (A + |b|))) ^
          (2 : ℕ) *
        ((ENNReal.ofReal
          (4 * Real.exp (8 ^ 2 * A ^ 2 / 2 + 8 * |b|))) ^ (8 : ℝ)⁻¹) := by
    have hscale : (fun omega ↦ ((H omega) ^ 2 / 2) * Real.exp |H omega|) =
        (2 : ℝ)⁻¹ • (fun omega ↦ f omega * g omega) := by
      funext omega
      dsimp only [f, g]
      rw [Pi.smul_apply, smul_eq_mul, Real.rpow_two, sq_abs]
      ring
    rw [hscale, eLpNorm_const_smul]
    have hc : ‖(2 : ℝ)⁻¹‖ₑ = (2 : ℝ≥0∞)⁻¹ := by
      rw [Real.enorm_eq_ofReal (by positivity : 0 ≤ (2 : ℝ)⁻¹),
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hc]
    calc
      (2 : ℝ≥0∞)⁻¹ * eLpNorm (fun omega ↦ f omega * g omega) 4
          M.P.toMeasure ≤
          (2 : ℝ≥0∞)⁻¹ *
            (eLpNorm f 8 M.P.toMeasure * eLpNorm g 8 M.P.toMeasure) := by
        gcongr
      _ ≤ (2 : ℝ≥0∞)⁻¹ *
          ((ENNReal.ofReal
            (gammaMomentConst 2 * Real.sqrt 16 * (A + |b|))) ^ (2 : ℝ) *
            ((ENNReal.ofReal
              (4 * Real.exp (8 ^ 2 * A ^ 2 / 2 + 8 * |b|))) ^
                (8 : ℝ)⁻¹)) := by
        gcongr
        rw [hfNorm]
        exact ENNReal.rpow_le_rpow hH16 (by norm_num)
      _ = _ := by
        norm_num [ENNReal.rpow_two, pow_two, mul_assoc]
  have htargetMeas : AEStronglyMeasurable
      (oneStepInverseExpRemainderAt M n h x) M.P.toMeasure := by
    exact ((Real.measurable_exp.comp
      ((measurable_cutoffShellSum (n + h) (n : ℤ) x).sub_const _).neg)
      |>.sub_const _ |>.add
        (measurable_cutoffShellSum (n + h) (n : ℤ) x)).aestronglyMeasurable
  have hmajorMeas : AEStronglyMeasurable (fun omega ↦
      ((H omega) ^ 2 / 2) * Real.exp |H omega|) M.P.toMeasure := by
    exact (((hHaem.pow_const 2).div_const 2).mul
      (Real.measurable_exp.comp_aemeasurable hHaem.norm)).aestronglyMeasurable
  have hconstMeas : AEStronglyMeasurable (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ b)
      M.P.toMeasure := aestronglyMeasurable_const
  have htri := eLpNorm_add_le (μ := M.P.toMeasure)
    (f := fun omega ↦ ((H omega) ^ 2 / 2) * Real.exp |H omega|)
    (g := fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ b)
    (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hmono : eLpNorm (oneStepInverseExpRemainderAt M n h x) 4
      M.P.toMeasure ≤
      eLpNorm (fun omega ↦
        ((H omega) ^ 2 / 2) * Real.exp |H omega| + b) 4
        M.P.toMeasure := by
    apply eLpNorm_mono_ae htargetMeas
    filter_upwards with omega
    have hpoint := abs_oneStepInverseExpRemainderAt_le M n h x omega
    change |oneStepInverseExpRemainderAt M n h x omega| ≤
      |((H omega) ^ 2 / 2) * Real.exp |H omega| + b|
    rw [abs_of_nonneg (add_nonneg
      (mul_nonneg (by positivity) (Real.exp_pos _).le) hb0)]
    simpa only [H, X, b, oneStepCenteredShellAt] using! hpoint
  calc
    eLpNorm (oneStepInverseExpRemainderAt M n h x) 4 M.P.toMeasure ≤
        eLpNorm (fun omega ↦
          ((H omega) ^ 2 / 2) * Real.exp |H omega| + b) 4
          M.P.toMeasure := hmono
    _ ≤ eLpNorm (fun omega ↦
          ((H omega) ^ 2 / 2) * Real.exp |H omega|) 4 M.P.toMeasure +
        eLpNorm (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ b) 4 M.P.toMeasure := htri
    _ ≤ (2 : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal (gammaMomentConst 2 * Real.sqrt 16 * (A + |b|))) ^
            (2 : ℕ) *
          ((ENNReal.ofReal
            (4 * Real.exp (8 ^ 2 * A ^ 2 / 2 + 8 * |b|))) ^
              (8 : ℝ)⁻¹) + ENNReal.ofReal b := by
      apply add_le_add hmain
      rw [eLpNorm_const b (by norm_num) (NeZero.ne M.P.toMeasure)]
      simp [Real.enorm_eq_ofReal hb0]
    _ = oneStepExpRemainderFourBound M h := by
      simp only [oneStepExpRemainderFourBound, A, b]

/-! ## Spatial forcing carrier -/

theorem measurable_oneStepInverseExpRemainderAt_uncurry {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) :
    Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d ↦
      oneStepInverseExpRemainderAt M n h q.2 q.1 := by
  have hs : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d ↦
      cutoffShellSum (n + h) (n : ℤ) q.2 q.1 :=
    measurable_cutoffShellSum_uncurry n h
  simpa only [oneStepInverseExpRemainderAt, oneStepCenteredShellAt] using!
    ((hs.sub_const _).neg.exp.sub_const _).add hs

theorem memLp_four_oneStepInverseExpRemainderAt_spatial {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    MemLp (fun x ↦ oneStepInverseExpRemainderAt M n h x omega) 4
      (normalizedCubeMeasure (originCube d m)) := by
  have hcont : Continuous fun x ↦
      oneStepInverseExpRemainderAt M n h x omega := by
    exact (((Real.continuous_exp.comp
      ((continuous_finsetSum _ fun k _ ↦
        (omega k).1.1.continuous).sub continuous_const).neg).sub
          continuous_const).add
      (continuous_finsetSum _ fun k _ ↦ (omega k).1.1.continuous))
  exact SubdiffusiveProcess.CoarseGrainingVocab.memLp_normalizedCubeMeasure_of_continuous
    (originCube d m) (4 : ℝ≥0∞) hcont

theorem lintegral_lintegral_oneStepInverseExpRemainder_four_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (m : ℤ)
    (hh : 0 < h) (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega, ∫⁻ x,
        ‖oneStepInverseExpRemainderAt M n h x omega‖ₑ ^ (4 : ℝ)
          ∂normalizedCubeMeasure (originCube d m) ∂M.P.toMeasure ≤
      (oneStepExpRemainderConst *
        ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) := by
  let Q := originCube d m
  let R : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d → ℝ := fun q ↦
    oneStepInverseExpRemainderAt M n h q.2 q.1
  have hR : Measurable R := by
    simpa only [R] using! measurable_oneStepInverseExpRemainderAt_uncurry M n h
  have hjoint : AEMeasurable
      (Function.uncurry fun omega x ↦ ‖R (omega, x)‖ₑ ^ (4 : ℝ))
      (M.P.toMeasure.prod (normalizedCubeMeasure Q)) := by
    simpa only [Function.uncurry_apply_pair] using!
      (hR.enorm.pow_const (4 : ℝ)).aemeasurable
  rw [lintegral_lintegral_swap hjoint]
  have hpoint : ∀ᵐ x ∂normalizedCubeMeasure Q,
      ∫⁻ omega, ‖R (omega, x)‖ₑ ^ (4 : ℝ) ∂M.P.toMeasure ≤
        (oneStepExpRemainderConst *
          ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) := by
    filter_upwards with x
    let F : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ R (omega, x)
    have hnorm : eLpNorm F 4 M.P.toMeasure ≤
        oneStepExpRemainderConst *
          ENNReal.ofReal (M.delta ^ 2 * (h : ℝ)) := by
      exact (eLpNorm_oneStepInverseExpRemainderAt_four_le M n h x hh).trans
        (oneStepExpRemainderFourBound_le M h hh hscale)
    have hpow := ENNReal.rpow_le_rpow hnorm (by norm_num : (0 : ℝ) ≤ 4)
    have hFmeas : AEStronglyMeasurable F M.P.toMeasure :=
      (hR.comp (measurable_id.prodMk (measurable_const (a := x)))).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := F) (by norm_num)
      (by norm_num) hFmeas] at hpow
    norm_num only [ENNReal.toReal_ofNat] at hpow
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)] at hpow
    simpa only [F, R, ENNReal.rpow_natCast] using! hpow
  calc
    (∫⁻ x, ∫⁻ omega, ‖R (omega, x)‖ₑ ^ (4 : ℝ)
        ∂M.P.toMeasure ∂normalizedCubeMeasure Q) ≤
      ∫⁻ _x, (oneStepExpRemainderConst *
        ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ)
          ∂normalizedCubeMeasure Q := lintegral_mono_ae hpoint
    _ = _ := by
      rw [lintegral_const]
      simp [normalizedCubeMeasure_apply_univ]

/-- Continuous reciprocal remainder field. -/
def oneStepInverseExpRemainderContinuousMap {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : C(Vec d, ℝ) where
  toFun := fun x ↦ oneStepInverseExpRemainderAt M n h x omega
  continuous_toFun := by
    exact (((Real.continuous_exp.comp
      ((continuous_finsetSum _ fun k _ ↦
        (omega k).1.1.continuous).sub continuous_const).neg).sub
          continuous_const).add
      (continuous_finsetSum _ fun k _ ↦ (omega k).1.1.continuous))

/-- Reciprocal remainder as a Hilbert `L²` vector forcing. -/
def oneStepInverseExpRemainderForcingL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    HilbertVectorL2 (openCubeSet Q) :=
  oneStepContinuousScalarForcingL2 Q p
    (oneStepInverseExpRemainderContinuousMap M n h omega)

theorem measurable_oneStepInverseExpRemainderForcingL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) :
    Measurable (oneStepInverseExpRemainderForcingL2 M n h p Q) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  apply measurable_of_forall_real_inner_right
  intro Y
  have hY : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d ↦
      (Y : Vec d → HilbertVec d) q.2 :=
    (MeasureTheory.Lp.stronglyMeasurable Y).measurable.comp measurable_snd
  have hint : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d ↦
      inner ℝ
        (oneStepInverseExpRemainderAt M n h q.2 q.1 • HilbertVec.ofVec p)
        ((Y : Vec d → HilbertVec d) q.2) :=
    ((measurable_oneStepInverseExpRemainderAt_uncurry M n h).smul_const
      (HilbertVec.ofVec p)).inner hY
  have hparam : Measurable fun omega ↦
      ∫ x, inner ℝ
        (oneStepInverseExpRemainderAt M n h x omega • HilbertVec.ofVec p)
        ((Y : Vec d → HilbertVec d) x)
        ∂(volumeMeasureOn (openCubeSet Q)) :=
    hint.stronglyMeasurable.integral_prod_right'.measurable
  have heq : (fun omega ↦ inner ℝ
      (oneStepInverseExpRemainderForcingL2 M n h p Q omega) Y) =
      fun omega ↦
        ∫ x, inner ℝ
          (oneStepInverseExpRemainderAt M n h x omega • HilbertVec.ofVec p)
          ((Y : Vec d → HilbertVec d) x)
          ∂(volumeMeasureOn (openCubeSet Q)) := by
    funext omega
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards
      [coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepInverseExpRemainderContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p)))]
      with x hx
    change inner ℝ
      ((toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepInverseExpRemainderContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p))) :
          Vec d → HilbertVec d) x) ((Y : Vec d → HilbertVec d) x) = _
    rw [hx]
    rfl
  rw [heq]
  exact hparam

theorem memLp_four_oneStepInverseExpRemainderForcingFourthNorm
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    let A := oneStepExpRemainderConst *
      ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))
    MemLp (fun omega ↦ oneStepNormalizedFourthNormBorel
        (originCube d m)
        (oneStepInverseExpRemainderForcingL2 M n h p
          (originCube d m) omega)) 4 M.P.toMeasure ∧
      eLpNorm (fun omega ↦ oneStepNormalizedFourthNormBorel
          (originCube d m)
          (oneStepInverseExpRemainderForcingL2 M n h p
            (originCube d m) omega)) 4 M.P.toMeasure ≤ A := by
  let Q := originCube d m
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) :=
    oneStepInverseExpRemainderForcingL2 M n h p Q
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → HilbertVec d := fun omega x ↦
    oneStepInverseExpRemainderAt M n h x omega • HilbertVec.ofVec p
  let A : ℝ≥0∞ := oneStepExpRemainderConst *
    ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))
  have hpNorm : ‖HilbertVec.ofVec p‖ = 1 := by
    have hsquare : ‖HilbertVec.ofVec p‖ ^ 2 = 1 := by
      rw [HilbertVec.norm_sq_ofVec]
      exact hp
    nlinarith [norm_nonneg (HilbertVec.ofVec p)]
  have hf : ∀ omega, MemLp (f omega) 4 (normalizedCubeMeasure Q) := by
    intro omega
    have hs := memLp_four_oneStepInverseExpRemainderAt_spatial M n h m omega
    let L : ℝ →L[ℝ] HilbertVec d :=
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (HilbertVec.ofVec p)
    simpa only [f, L, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self] using! hs.continuousLinearMap_comp L
  have hcoe : ∀ omega, (G omega : Vec d → HilbertVec d) =ᵐ[
      normalizedCubeMeasure Q] f omega := by
    intro omega
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    simpa only [G, f, oneStepInverseExpRemainderForcingL2,
      oneStepContinuousScalarForcingL2,
      oneStepInverseExpRemainderContinuousMap] using!
      coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepInverseExpRemainderContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p)))
  have hAtop : A < ∞ := by
    apply lt_top_iff_ne_top.mpr
    apply ENNReal.mul_ne_top
    · unfold oneStepExpRemainderConst
      finiteness
    · exact ENNReal.ofReal_ne_top
  have hm : ∫⁻ omega,
      (eLpNorm (f omega) 4 (normalizedCubeMeasure Q)) ^ (4 : ℝ)
        ∂M.P.toMeasure ≤ A ^ (4 : ℝ) := by
    calc
      _ = ∫⁻ omega, ∫⁻ x,
          ‖oneStepInverseExpRemainderAt M n h x omega‖ₑ ^ (4 : ℝ)
            ∂normalizedCubeMeasure Q ∂M.P.toMeasure := by
        apply lintegral_congr
        intro omega
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hf omega).aestronglyMeasurable]
        norm_num only [ENNReal.toReal_ofNat]
        rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
          ENNReal.rpow_inv_rpow (by norm_num)]
        apply lintegral_congr
        intro x
        have hpEnorm : ‖HilbertVec.ofVec p‖ₑ = 1 := by
          rw [← ofReal_norm, hpNorm]
          simp
        dsimp only [f]
        rw [enorm_smul, hpEnorm, mul_one]
      _ ≤ A ^ (4 : ℝ) := by
        simpa only [Q, A] using!
          lintegral_lintegral_oneStepInverseExpRemainder_four_le
            M n h m hh hscale
  simpa only [A, G, Q] using!
    memLp_oneStepNormalizedFourthNormBorel_comp_of_raw_moment
      Q G f A (measurable_oneStepInverseExpRemainderForcingL2 M n h p Q)
      hf hcoe hAtop hm

/-! ## Literal reciprocal weighted cubic -/

/-- Hilbert forcing for `exp (-H) - 1`, written as its odd part plus the
quadratic reciprocal remainder. -/
def oneStepInverseShellForcingL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    HilbertVectorL2 (openCubeSet Q) :=
  -oneStepLinearShellForcingL2 Q p n h omega +
    oneStepInverseExpRemainderForcingL2 M n h p Q omega

theorem measurable_oneStepInverseShellForcingL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) :
    Measurable (oneStepInverseShellForcingL2 M n h p Q) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  apply measurable_of_forall_real_inner_right
  intro Y
  have hz : Measurable fun omega ↦ inner ℝ
      (oneStepLinearShellForcingL2 Q p n h omega) Y :=
    (continuous_id.inner continuous_const).measurable.comp
      (measurable_oneStepLinearShellForcingL2 Q p n h)
  have he : Measurable fun omega ↦ inner ℝ
      (oneStepInverseExpRemainderForcingL2 M n h p Q omega) Y :=
    (continuous_id.inner continuous_const).measurable.comp
      (measurable_oneStepInverseExpRemainderForcingL2 M n h p Q)
  simpa only [oneStepInverseShellForcingL2, inner_add_left,
    inner_neg_left] using! hz.neg.add he

theorem oneStepNormalizedFourthNormBorel_neg {d : ℕ}
    (Q : TriadicCube d) (F : HilbertVectorL2 (openCubeSet Q)) :
    oneStepNormalizedFourthNormBorel Q (-F) =
      oneStepNormalizedFourthNormBorel Q F := by
  unfold oneStepNormalizedFourthNormBorel
  rw [oneStepNormalizedFourthNormENNRealBorel_eq_eLpNorm_coe,
    oneStepNormalizedFourthNormENNRealBorel_eq_eLpNorm_coe]
  have hcoe : ((-F : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      -(F : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_neg F
  rw [eLpNorm_congr_ae hcoe, eLpNorm_neg]

theorem oneStepNormalizedWeightedCubicBorel_right_neg_of_memLp
    {d : ℕ} (Q : TriadicCube d) (p : HilbertVec d)
    (F G : HilbertVectorL2 (openCubeSet Q))
    (hF : MemLp (F : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q))
    (hG : MemLp (G : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q)) :
    oneStepNormalizedWeightedCubicBorel Q p F (-G) =
      -oneStepNormalizedWeightedCubicBorel Q p F G := by
  have hneg : MemLp ((-G : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q) := by
    have hcoe : ((-G : HilbertVectorL2 (openCubeSet Q)) :
        Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        -(G : Vec d → HilbertVec d) := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact Lp.coeFn_neg G
    exact hG.neg.ae_eq hcoe.symm
  rw [oneStepNormalizedWeightedCubicBorel_eq_cubeAverage Q p F (-G) hF hneg,
    oneStepNormalizedWeightedCubicBorel_eq_cubeAverage Q p F G hF hG,
    cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure, ← integral_neg]
  apply integral_congr_ae
  have hcoe : ((-G : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      -(G : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_neg G
  filter_upwards [hcoe] with x hx
  unfold oneStepWeightedCubicIntegrand
  rw [hx]
  simp only [Pi.neg_apply, inner_neg_right]
  ring



def oneStepOriginNeumannInverseWeightedCubicBorel {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  oneStepNormalizedWeightedCubicBorel (originCube d m) (HilbertVec.ofVec p)
    (oneStepOriginNeumannGradientL2 M n h p m omega)
    (oneStepInverseShellForcingL2 M n h p (originCube d m) omega)

theorem measurable_oneStepOriginNeumannInverseWeightedCubicBorel
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (oneStepOriginNeumannInverseWeightedCubicBorel M n h p m) := by
  let pair : _root_.SubdiffusiveProcess.Model.PotentialSample d →
      HilbertVectorL2 (openCubeSet (originCube d m)) ×
        HilbertVectorL2 (openCubeSet (originCube d m)) := fun omega ↦
    (oneStepOriginNeumannGradientL2 M n h p m omega,
      oneStepInverseShellForcingL2 M n h p (originCube d m) omega)
  have hpair : Measurable pair :=
    (measurable_oneStepOriginNeumannGradientL2 M n h p m hh).prodMk
      (measurable_oneStepInverseShellForcingL2
        M n h p (originCube d m))
  simpa only [oneStepOriginNeumannInverseWeightedCubicBorel, pair] using!
    (measurable_oneStepNormalizedWeightedCubicBorel
      (originCube d m) (HilbertVec.ofVec p)).comp hpair

/-- Borel fourth-norm envelope for the reciprocal nonlinear replacement. -/
def oneStepOriginNeumannInverseWeightedCubicMajorantBorel
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  let Q := originCube d m
  let u := oneStepOriginNeumannGradientL2 M n h p m omega
  let r := (oneStepExpRemainderNeumannSolution M n h p m omega)
    |>.gradToHilbertVectorL2
  let z := oneStepLinearShellForcingL2 Q p n h omega
  let e := oneStepInverseExpRemainderForcingL2 M n h p Q omega
  oneStepNormalizedFourthNormBorel Q r *
      (2 * oneStepNormalizedFourthNormBorel Q u +
        oneStepNormalizedFourthNormBorel Q r) *
      oneStepNormalizedFourthNormBorel Q z +
    oneStepNormalizedFourthNormBorel Q u *
      oneStepNormalizedFourthNormBorel Q u *
      oneStepNormalizedFourthNormBorel Q e

theorem measurable_oneStepOriginNeumannInverseWeightedCubicMajorantBorel
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable
      (oneStepOriginNeumannInverseWeightedCubicMajorantBorel M n h p m) := by
  have hu := (measurable_oneStepNormalizedFourthNormBorel (originCube d m)).comp
    (measurable_oneStepOriginNeumannGradientL2 M n h p m hh)
  have hr := (measurable_oneStepNormalizedFourthNormBorel (originCube d m)).comp
    (measurable_oneStepExpRemainderNeumannGradientL2 M n h p m hh)
  have hz := (measurable_oneStepNormalizedFourthNormBorel (originCube d m)).comp
    (measurable_oneStepLinearShellForcingL2 (originCube d m) p n h)
  have he := (measurable_oneStepNormalizedFourthNormBorel (originCube d m)).comp
    (measurable_oneStepInverseExpRemainderForcingL2
      M n h p (originCube d m))
  exact ((hr.mul ((hu.const_mul 2).add hr)).mul hz).add
    ((hu.mul hu).mul he)

/-- The reciprocal weighted cubic differs from its odd linear part by the
same fourth-norm envelope as the forward comparison. -/
theorem abs_oneStepOriginNeumannInverseWeightedCubicBorel_sub_linear_le
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    |oneStepOriginNeumannInverseWeightedCubicBorel M n h p m omega +
      oneStepNormalizedSignedLinearNeumannCubicBorel
        (originCube d m) p n h omega| ≤
      oneStepOriginNeumannInverseWeightedCubicMajorantBorel
        M n h p m omega := by
  let Q := originCube d m
  let u := oneStepOriginNeumannGradientL2 M n h p m omega
  let v := -oneStepLinearNeumannGradient Q p n h omega
  let r := (oneStepExpRemainderNeumannSolution M n h p m omega)
    |>.gradToHilbertVectorL2
  let z := -oneStepLinearShellForcingL2 Q p n h omega
  let e := oneStepInverseExpRemainderForcingL2 M n h p Q omega
  obtain ⟨_Cactual, _hCactual, hCZactual⟩ :=
    exists_oneStepOriginNeumann_gradient_four_cz d
  have hu4raw := (hCZactual M n h omega p m hh hp).1
  have hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hmem := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure Q
      (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function hu4raw
    have hmem' : MemLp
        ((oneStepOriginNeumannSolution M n h p m omega hh)
          |>.gradToHilbertVectorL2 : Vec d → HilbertVec d) 4
          (normalizedCubeMeasure Q) := by
      simpa only [H1MeanZeroFunction.gradToHilbertVectorL2] using! hmem
    rw [oneStepOriginNeumannSolution_gradient_eq M n h p m omega hh] at hmem'
    exact hmem'
  obtain ⟨_Crem, _hCrem, hCZrem⟩ :=
    exists_oneStepExpRemainderNeumann_gradient_four_cz d
  have hr4raw := (hCZrem M n h omega p m hp).1
  have hr4 : MemLp (r : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) :=
    memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure Q
      (oneStepExpRemainderNeumannSolution M n h p m omega).toH1Function
      hr4raw
  have hz4pos : MemLp
      (oneStepLinearShellForcingL2 Q p n h omega : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) :=
    memLp_four_oneStepContinuousScalarForcingL2 Q p
      (oneStepShellSumContinuousMap n h omega)
  have hz4 : MemLp (z : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hcoe : (z : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        -(oneStepLinearShellForcingL2 Q p n h omega :
          Vec d → HilbertVec d) := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact Lp.coeFn_neg (oneStepLinearShellForcingL2 Q p n h omega)
    exact hz4pos.neg.ae_eq hcoe.symm
  have he4 : MemLp (e : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) :=
    memLp_four_oneStepContinuousScalarForcingL2 Q p
      (oneStepInverseExpRemainderContinuousMap M n h omega)
  have hsplit : u = v + r :=
    oneStepOriginNeumannGradientL2_eq_linear_add_remainder
      M n h p m omega hh
  have hvEq : v = u - r := by rw [hsplit]; abel
  have hsub : ((u - r : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (u : Vec d → HilbertVec d) - (r : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_sub u r
  have hv4 : MemLp (v : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    rw [hvEq]
    exact (hu4.sub hr4).ae_eq hsub.symm
  have hadd : ((v + r : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (v : Vec d → HilbertVec d) + (r : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_add v r
  have hu : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (v : Vec d → HilbertVec d) + (r : Vec d → HilbertVec d) := by
    rw [hsplit]
    exact hadd
  have hpHilbert : ‖HilbertVec.ofVec p‖ ≤ 1 := by
    have hsquare : ‖HilbertVec.ofVec p‖ ^ 2 = 1 := by
      rw [HilbertVec.norm_sq_ofVec]
      exact hp
    nlinarith [norm_nonneg (HilbertVec.ofVec p)]
  have hdet := abs_oneStepNormalizedWeightedCubicBorel_sub_le_four Q
    (HilbertVec.ofVec p) u v r z e hpHilbert hu hu4 hv4 hr4 hz4 he4
  have hlinear : oneStepNormalizedWeightedCubicBorel Q
      (HilbertVec.ofVec p) v z =
      -oneStepNormalizedSignedLinearNeumannCubicBorel Q p n h omega := by
    rw [oneStepNormalizedSignedLinearNeumannCubicBorel]
    dsimp only [v, z]
    rw [oneStepNormalizedWeightedCubicBorel,
      oneStepNormalizedWeightedCubicBorel]
    exact oneStepNormalizedWeightedCubicBorel_right_neg_of_memLp Q
      (HilbertVec.ofVec p) v
      (oneStepLinearShellForcingL2 Q p n h omega) hv4 hz4pos
  have hraw : oneStepNormalizedWeightedCubicBorel Q (HilbertVec.ofVec p)
      u (z + e) =
      oneStepOriginNeumannInverseWeightedCubicBorel M n h p m omega := rfl
  rw [hraw, hlinear] at hdet
  have hmajor := oneStepFourthNormMajorant_le_borel Q u v r
    (-oneStepLinearShellForcingL2 Q p n h omega) e hu hu4 hv4 hr4
  simpa only [sub_neg_eq_add] using! hdet.trans (by
    simpa only [oneStepOriginNeumannInverseWeightedCubicMajorantBorel,
      Q, u, r, e, oneStepNormalizedFourthNormBorel_neg] using! hmajor)

theorem exists_integrable_oneStepOriginNeumannInverseWeightedCubicMajorant
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (_ : 0 < h) (_ : vecNormSq p = 1)
        (_ : (h : ℝ) ≤ M.delta⁻¹),
        Integrable
          (oneStepOriginNeumannInverseWeightedCubicMajorantBorel M n h p m)
          M.P.toMeasure ∧
        ∫ omega, oneStepOriginNeumannInverseWeightedCubicMajorantBorel
            M n h p m omega ∂M.P.toMeasure ≤
          C * M.delta ^ 4 * (h : ℝ) ^ 2 := by
  obtain ⟨CN, hCNtop, hN⟩ :=
    exists_memLp_four_oneStepOriginNeumannFourthNorm d
  obtain ⟨CR, hCRtop, hR⟩ :=
    exists_memLp_four_oneStepExpRemainderNeumannFourthNorm d
  let KU : ℝ≥0∞ := CN ^ (1 / 4 : ℝ) *
    ENNReal.ofReal oneStepRatioEightUniformConst
  let KR : ℝ≥0∞ := CR ^ (1 / 4 : ℝ) * oneStepExpRemainderConst
  let KZ : ℝ≥0∞ := oneStepLinearShellFourConst
  let KE : ℝ≥0∞ := oneStepExpRemainderConst
  let K : ℝ≥0∞ := KR * (2 * KU + KR) * KZ + KU * KU * KE
  refine ⟨K.toReal + 1, by positivity, ?_⟩
  intro M n h p m hh hp hscale
  let Q := originCube d m
  let U : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepOriginNeumannGradientL2 M n h p m omega)
  let R : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    ((oneStepExpRemainderNeumannSolution M n h p m omega)
      |>.gradToHilbertVectorL2)
  let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepLinearShellForcingL2 Q p n h omega)
  let E : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepInverseExpRemainderForcingL2 M n h p Q omega)
  obtain ⟨hUmem, hUnorm⟩ := hN M n h p m hh hp
  obtain ⟨hRmem, hRnorm⟩ := hR M n h p m hh hp hscale
  obtain ⟨hZmem, hZnorm⟩ :=
    memLp_four_oneStepLinearShellFourthNorm M n h p m hh hp
  obtain ⟨hEmem, hEnorm⟩ :=
    memLp_four_oneStepInverseExpRemainderForcingFourthNorm
      M n h p m hh hp hscale
  let x : ℝ := M.delta * Real.sqrt (h : ℝ)
  let y : ℝ := M.delta ^ 2 * (h : ℝ)
  have hx0 : 0 ≤ x := mul_nonneg M.shellPrefix.delta_pos.le
    (Real.sqrt_nonneg _)
  have hy0 : 0 ≤ y := mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hyx : y = x ^ 2 := by
    dsimp [x, y]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg h)]
  have hy_le_x : y ≤ x := by
    have hdh : M.delta * (h : ℝ) ≤ 1 := by
      calc
        M.delta * (h : ℝ) ≤ M.delta * M.delta⁻¹ :=
          mul_le_mul_of_nonneg_left hscale M.shellPrefix.delta_pos.le
        _ = 1 := mul_inv_cancel₀ M.shellPrefix.delta_pos.ne'
    have hdeltaSqH : M.delta ^ 2 * (h : ℝ) ≤ M.delta := by
      nlinarith [M.shellPrefix.delta_pos]
    have hxSq : x ^ 2 ≤ 1 := by
      rw [← hyx]
      exact hdeltaSqH.trans M.shellPrefix.delta_le_half |>.trans (by norm_num)
    rw [hyx]
    nlinarith
  have hratio := oneStepRatioMinusOneEightBound_le_sqrtScale M h hscale
  have hUenn : eLpNorm U 4 M.P.toMeasure ≤ KU * ENNReal.ofReal x := by
    calc
      _ ≤ (CN * (ENNReal.ofReal
          (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ)) ^
            (1 / 4 : ℝ) := by simpa only [U, Q] using! hUnorm
      _ = CN ^ (1 / 4 : ℝ) *
          ENNReal.ofReal (oneStepRatioMinusOneEightBound M h) :=
        fourthRoot_mul_four_eq _ _
      _ ≤ KU * ENNReal.ofReal x := by
        dsimp only [KU, x]
        rw [mul_assoc]
        gcongr
        rw [← ENNReal.ofReal_mul oneStepRatioEightUniformConst_pos.le]
        exact ENNReal.ofReal_le_ofReal (by
          convert hratio using 1
          ring)
  have hRenn : eLpNorm R 4 M.P.toMeasure ≤ KR * ENNReal.ofReal y := by
    calc
      _ ≤ (CR * (oneStepExpRemainderConst * ENNReal.ofReal y) ^
          (4 : ℝ)) ^ (1 / 4 : ℝ) := by
        simpa only [R, Q, y] using! hRnorm
      _ = CR ^ (1 / 4 : ℝ) *
          (oneStepExpRemainderConst * ENNReal.ofReal y) :=
        fourthRoot_mul_four_eq _ _
      _ = KR * ENNReal.ofReal y := by dsimp [KR]; ring
  have hZenn : eLpNorm Z 4 M.P.toMeasure ≤ KZ * ENNReal.ofReal x := by
    simpa only [Z, Q, KZ, x] using! hZnorm
  have hEenn : eLpNorm E 4 M.P.toMeasure ≤ KE * ENNReal.ofReal y := by
    simpa only [E, Q, KE, y] using! hEnorm
  have hKUtop : KU ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCNtop.ne)
    ENNReal.ofReal_ne_top
  have hKRtop : KR ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCRtop.ne) (by
      unfold oneStepExpRemainderConst
      finiteness)
  have hKZtop : KZ ≠ ∞ := by
    dsimp [KZ, oneStepLinearShellFourConst]
    finiteness
  have hKEtop : KE ≠ ∞ := by
    dsimp [KE, oneStepExpRemainderConst]
    finiteness
  have hagg := integral_fourNormMajorant_quantitative M.P.toMeasure U R Z E
    (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)
    (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)
    hUmem hRmem hZmem hEmem KU KR KZ KE hKUtop hKRtop hKZtop hKEtop
    x y hx0 hy0 hyx hy_le_x hUenn hRenn hZenn hEenn
  refine ⟨by
    simpa only [oneStepOriginNeumannInverseWeightedCubicMajorantBorel,
      U, R, Z, E, Q] using! hagg.1, ?_⟩
  calc
    _ ≤ K.toReal * y ^ 2 := by
      simpa only [oneStepOriginNeumannInverseWeightedCubicMajorantBorel,
        U, R, Z, E, Q, K] using! hagg.2
    _ ≤ (K.toReal + 1) * M.delta ^ 4 * (h : ℝ) ^ 2 := by
      have hySq : y ^ 2 = M.delta ^ 4 * (h : ℝ) ^ 2 := by
        dsimp [y]
        ring
      rw [hySq]
      have hbase0 : 0 ≤ M.delta ^ 4 * (h : ℝ) ^ 2 := by positivity
      nlinarith [ENNReal.toReal_nonneg (a := K)]

theorem abs_oneStepNormalizedWeightedCubicBorel_add_le_borel
    {d : ℕ} (Q : TriadicCube d) (p : HilbertVec d)
    (u z e : HilbertVectorL2 (openCubeSet Q))
    (hp : ‖p‖ ≤ 1)
    (hu4 : MemLp (u : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q))
    (hz4 : MemLp (z : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q))
    (he4 : MemLp (e : Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q)) :
    |oneStepNormalizedWeightedCubicBorel Q p u (z + e)| ≤
      oneStepNormalizedFourthNormBorel Q u *
        oneStepNormalizedFourthNormBorel Q u *
        (oneStepNormalizedFourthNormBorel Q z +
          oneStepNormalizedFourthNormBorel Q e) := by
  have hadd : ((z + e : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      (z : Vec d → HilbertVec d) + (e : Vec d → HilbertVec d) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    exact Lp.coeFn_add z e
  have hze4 : MemLp ((z + e : HilbertVectorL2 (openCubeSet Q)) :
      Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q) :=
    (hz4.add he4).ae_eq hadd.symm
  have hraw := abs_oneStepNormalizedWeightedCubicBorel_le_four
    Q p u (z + e) hp hu4 hze4
  have hsum : cubeLpNorm Q 4 (fun x ↦
      ‖((z + e : HilbertVectorL2 (openCubeSet Q)) :
        Vec d → HilbertVec d) x‖) ≤
      cubeLpNorm Q 4 (fun x ↦ ‖(z : Vec d → HilbertVec d) x‖) +
        cubeLpNorm Q 4 (fun x ↦ ‖(e : Vec d → HilbertVec d) x‖) := by
    unfold cubeLpNorm
    rw [eLpNorm_norm _ hze4.aestronglyMeasurable, eLpNorm_congr_ae hadd,
      eLpNorm_norm _ hz4.aestronglyMeasurable, eLpNorm_norm _ he4.aestronglyMeasurable]
    exact cubeLpNorm_add_le Q 4 (z : Vec d → HilbertVec d)
      (e : Vec d → HilbertVec d) hz4 he4 (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hsum
    (mul_nonneg
      (cubeLpNorm_nonneg Q 4
        (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖))
      (cubeLpNorm_nonneg Q 4
        (fun x ↦ ‖(u : Vec d → HilbertVec d) x‖)))
  exact hraw.trans (by
    simpa only [oneStepNormalizedFourthNormBorel_eq_cubeLpNorm] using! hmul)

/-- The literal lower quadratic error at paper label `l.one.step.lower`. -/
theorem exists_integral_oneStepOriginNeumannInverseWeightedCubicBorel_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (_ : 0 < h) (_ : vecNormSq p = 1)
        (_ : (h : ℝ) ≤ M.delta⁻¹),
        Integrable
          (oneStepOriginNeumannInverseWeightedCubicBorel M n h p m)
          M.P.toMeasure ∧
        |∫ omega, oneStepOriginNeumannInverseWeightedCubicBorel
            M n h p m omega ∂M.P.toMeasure| ≤
          C * M.delta ^ 4 * (h : ℝ) ^ 2 := by
  obtain ⟨C, hC, hmajor⟩ :=
    exists_integrable_oneStepOriginNeumannInverseWeightedCubicMajorant d
  obtain ⟨_CN, _hCN, hN⟩ :=
    exists_memLp_four_oneStepOriginNeumannFourthNorm d
  refine ⟨C, hC, ?_⟩
  intro M n h p m hh hp hscale
  let Q := originCube d m
  let U : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepOriginNeumannGradientL2 M n h p m omega)
  let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepLinearShellForcingL2 Q p n h omega)
  let E : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ oneStepNormalizedFourthNormBorel Q
    (oneStepInverseExpRemainderForcingL2 M n h p Q omega)
  obtain ⟨hUmem, _hUnorm⟩ := hN M n h p m hh hp
  obtain ⟨hZmem, _hZnorm⟩ :=
    memLp_four_oneStepLinearShellFourthNorm M n h p m hh hp
  obtain ⟨hEmem, _hEnorm⟩ :=
    memLp_four_oneStepInverseExpRemainderForcingFourthNorm
      M n h p m hh hp hscale
  obtain ⟨hmajInt, hmajBound⟩ := hmajor M n h p m hh hp hscale
  have hpHilbert : ‖HilbertVec.ofVec p‖ ≤ 1 := by
    have hsquare : ‖HilbertVec.ofVec p‖ ^ 2 = 1 := by
      rw [HilbertVec.norm_sq_ofVec]
      exact hp
    nlinarith [norm_nonneg (HilbertVec.ofVec p)]
  have hfInt : Integrable
      (oneStepOriginNeumannInverseWeightedCubicBorel M n h p m)
      M.P.toMeasure :=
    integrable_of_abs_le_fourProduct
      (oneStepOriginNeumannInverseWeightedCubicBorel M n h p m) U Z E
      (measurable_oneStepOriginNeumannInverseWeightedCubicBorel
        M n h p m hh |>.aestronglyMeasurable)
      hUmem hZmem hEmem
      (fun omega ↦ by
        let u := oneStepOriginNeumannGradientL2 M n h p m omega
        let z := -oneStepLinearShellForcingL2 Q p n h omega
        let e := oneStepInverseExpRemainderForcingL2 M n h p Q omega
        obtain ⟨_Cactual, _hCactual, hCZactual⟩ :=
          exists_oneStepOriginNeumann_gradient_four_cz d
        have hu4raw := (hCZactual M n h omega p m hh hp).1
        have hu4 : MemLp (u : Vec d → HilbertVec d) 4
            (normalizedCubeMeasure Q) := by
          have hmem := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure Q
            (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function
            hu4raw
          have hmem' : MemLp
              ((oneStepOriginNeumannSolution M n h p m omega hh)
                |>.gradToHilbertVectorL2 : Vec d → HilbertVec d) 4
                (normalizedCubeMeasure Q) := by
            simpa only [H1MeanZeroFunction.gradToHilbertVectorL2] using! hmem
          rw [oneStepOriginNeumannSolution_gradient_eq
            M n h p m omega hh] at hmem'
          exact hmem'
        have hz4pos : MemLp
            (oneStepLinearShellForcingL2 Q p n h omega :
              Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q) :=
          memLp_four_oneStepContinuousScalarForcingL2 Q p
            (oneStepShellSumContinuousMap n h omega)
        have hz4 : MemLp (z : Vec d → HilbertVec d) 4
            (normalizedCubeMeasure Q) := by
          have hcoe : (z : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
              -(oneStepLinearShellForcingL2 Q p n h omega :
                Vec d → HilbertVec d) := by
            apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
            exact Lp.coeFn_neg (oneStepLinearShellForcingL2 Q p n h omega)
          exact hz4pos.neg.ae_eq hcoe.symm
        have he4 : MemLp (e : Vec d → HilbertVec d) 4
            (normalizedCubeMeasure Q) :=
          memLp_four_oneStepContinuousScalarForcingL2 Q p
            (oneStepInverseExpRemainderContinuousMap M n h omega)
        have hraw := abs_oneStepNormalizedWeightedCubicBorel_add_le_borel
          Q (HilbertVec.ofVec p) u z e hpHilbert hu4 hz4 he4
        simpa only [oneStepOriginNeumannInverseWeightedCubicBorel,
          oneStepInverseShellForcingL2, U, Z, E, Q, u, z, e,
          oneStepNormalizedFourthNormBorel_neg] using! hraw)
      (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)
      (fun _ ↦ ENNReal.toReal_nonneg)
  refine ⟨hfInt, ?_⟩
  exact abs_integral_of_cancelled_majorant
    (oneStepOriginNeumannInverseWeightedCubicBorel M n h p m)
    (fun omega ↦ -oneStepNormalizedSignedLinearNeumannCubicBorel
      Q p n h omega)
    (oneStepOriginNeumannInverseWeightedCubicMajorantBorel M n h p m)
    hfInt
    (measurable_oneStepNormalizedSignedLinearNeumannCubicBorel Q p n h
      |>.neg.aestronglyMeasurable)
    (by
      rw [integral_neg,
        integral_oneStepNormalizedSignedLinearNeumannCubicBorel_eq_zero]
      simp)
    hmajInt
    (fun omega ↦ by
      simp only [oneStepOriginNeumannInverseWeightedCubicMajorantBorel]
      unfold oneStepNormalizedFourthNormBorel
      positivity)
    (fun omega ↦ by
      simpa only [sub_neg_eq_add] using!
        abs_oneStepOriginNeumannInverseWeightedCubicBorel_sub_linear_le
          M n h p m omega hh hp)
    hmajBound

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
