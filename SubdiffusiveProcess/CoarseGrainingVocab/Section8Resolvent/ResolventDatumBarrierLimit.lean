import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierProfile
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumGMCDenseRange




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- **The nonnegative compact-data exhaustion, under a barrier.**  Every cube
solution is trapped under the fixed supersolution `b`, hence so is the limit. -/
theorem exists_barrier_bounded_localMassiveWeakSolution_of_compactSupport [NeZero d]
    {c rho b : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    (hcC1 : ContDiff ℝ 1 c) (hrhoNe : ∀ x, rho x ≠ 0)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbnn : ∀ x, 0 ≤ b x)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (hsuper : ∀ x, f x ≤ smoothMassiveForcing c rho mu b x) :
    ∃ u : Vec d → ℝ,
      (∀ x, 0 ≤ u x ∧ u x ≤ ‖compactSupportToC0 f‖ / mu) ∧
      (∀ᵐ x ∂(volume : Measure (Vec d)), u x ≤ b x) ∧
        ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
          uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
            IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) uLocal f := by
  classical
  obtain ⟨uCube, v, u, hu, hvEq, _hvMono, hvBounds, hvLim⟩ :=
    exists_pointwiseMonotoneMassiveCubeLimit_of_compactSupport B hmu f hf
  have huBounds : ∀ x, 0 ≤ u x ∧ u x ≤ ‖compactSupportToC0 f‖ / mu := by
    intro x
    exact isClosed_Icc.mem_of_tendsto (hvLim x) <|
      Filter.Eventually.of_forall fun n ↦ hvBounds n x
  -- the barrier bound on every cube, transported to the zero extension
  have hbar : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure (Vec d)), v n x ≤ b x := by
    intro n
    have hcube := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
    have hfL2 : MemL2On (cube d (n : ℤ)) f :=
      (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).restrict _
    have hloc := ae_le_barrier_of_isMassiveWeakSolutionOn hcube hmu (B.rhoMin_pos n)
      (B.lam_pos n) (B.ell n) (B.coeff_lower n) hcC1 (B.rho_measurable n)
      (B.rho_lower n) (B.rho_bounded n) hrhoNe hb hbnn hfL2
      (fun x _ ↦ hsuper x) (hu n).1
    have hmeas : MeasurableSet (cube d (n : ℤ)) := hcube.isOpen.measurableSet
    rw [ae_restrict_iff' hmeas] at hloc
    filter_upwards [hloc, hvEq n] with x hx hxv
    rw [hxv]
    by_cases hxc : x ∈ cube d (n : ℤ)
    · rw [(uCube n).zeroExtension_apply_of_mem hxc]
      exact hx hxc
    · rw [(uCube n).zeroExtension_apply_of_not_mem hxc]
      exact hbnn x
  have hub : ∀ᵐ x ∂(volume : Measure (Vec d)), u x ≤ b x := by
    filter_upwards [ae_all_iff.2 hbar] with x hx
    exact le_of_tendsto' (hvLim x) hx
  refine ⟨u, huBounds, hub, fun k ↦ ?_⟩
  let hcube := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
  letI : IsFiniteMeasure (volumeMeasureOn (cube d (k : ℤ))) :=
    hcube.isBoundedDomain.isFiniteMeasure_restrict_volume
  let hsubset (n : ℕ) : cube d (k : ℤ) ⊆ cube d ((k + n : ℕ) : ℤ) :=
    Section6ExcessDecay.cube_subset_cube_of_le (by omega)
  let w (n : ℕ) : H1Function (cube d (k : ℤ)) :=
    (uCube (k + n)).toH1Function.restrict hcube.isOpen (hsubset n)
  obtain ⟨Cgrad, _hCgrad, hgradient⟩ :=
    exists_uniform_local_gradient_norm_bound B hmu f uCube hu k
  have hbound : ∀ n, ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      |(w n).toFun x| ≤ ‖compactSupportToC0 f‖ / mu := by
    intro n
    exact (hu (k + n)).2.2.2.filter_mono <|
      ae_mono (Measure.restrict_mono (hsubset n) le_rfl)
  have hwEq : ∀ n, (w n).toFun =ᵐ[
      volumeMeasureOn (cube d (k : ℤ))] v (k + n) := by
    intro n
    have hvLocal : v (k + n) =ᵐ[
        volumeMeasureOn (cube d (k : ℤ))] (uCube (k + n)).zeroExtension :=
      (hvEq (k + n)).filter_mono <|
        ae_mono (show volume.restrict (cube d (k : ℤ)) ≤ volume from
          Measure.restrict_le_self)
    filter_upwards [hvLocal,
      ae_restrict_mem hcube.isOpen.measurableSet] with x hx hxCube
    simp only [w, H1Function.restrict, hx]
    exact ((uCube (k + n)).zeroExtension_apply_of_mem ((hsubset n) hxCube)).symm
  have hpoint : ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      Tendsto (fun n ↦ (w n).toFun x) atTop (nhds (u x)) := by
    filter_upwards [ae_all_iff.2 hwEq] with x hx
    have hvSub : Tendsto (fun n ↦ v (k + n) x) atTop (nhds (u x)) := by
      simpa only [Function.comp_apply] using
        (hvLim x).comp (strictMono_id.const_add k).tendsto_atTop
    apply Filter.Tendsto.congr' _ hvSub
    exact Filter.Eventually.of_forall fun n ↦ (hx n).symm
  have hw : ∀ n, IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) (w n) f := by
    intro n
    exact IsMassiveWeakSolutionOn.restrict hcube.isOpen
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        ((k + n : ℕ) : ℤ)).isOpen
      (hsubset n) (hu (k + n)).1
  have hfLocal : MemL2On (cube d (k : ℤ)) f :=
    (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).restrict _
  obtain ⟨uLocal, huLocal, hsolution⟩ :=
    exists_isMassiveWeakSolutionOn_of_bounded_pointwise_limit
      (B.ell k) (B.rho_measurable k) (B.rho_bounded k) hfLocal w
      hbound hpoint (by simpa only [w] using hgradient) hw
  exact ⟨uLocal, huLocal, hsolution⟩

/-- **The signed compact-data exhaustion, under a barrier.**  The positive and
negative parts are each trapped under `b`, so their difference is trapped under
`2 b`. -/
theorem exists_barrier_bounded_signed_localMassiveWeakSolution_of_compactSupport
    [NeZero d] {c rho b : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    (hcC1 : ContDiff ℝ 1 c) (hrhoNe : ∀ x, rho x ≠ 0)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbnn : ∀ x, 0 ≤ b x)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ))
    (hsuper : ∀ x, |f x| ≤ smoothMassiveForcing c rho mu b x) :
    ∃ u : Vec d → ℝ,
      (∀ x, |u x| ≤
        ‖compactSupportToC0 f.nnrealPart.toReal‖ / mu +
          ‖compactSupportToC0 (-f).nnrealPart.toReal‖ / mu) ∧
      (∀ᵐ x ∂(volume : Measure (Vec d)), |u x| ≤ 2 * b x) ∧
        ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
          uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
            IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) uLocal f := by
  classical
  let fPlus : C_c(Vec d, ℝ) := f.nnrealPart.toReal
  let fMinus : C_c(Vec d, ℝ) := (-f).nnrealPart.toReal
  have hfPlus : ∀ x, 0 ≤ fPlus x := fun x ↦
    CompactlySupportedContinuousMap.toReal_nonneg x
  have hfMinus : ∀ x, 0 ≤ fMinus x := fun x ↦
    CompactlySupportedContinuousMap.toReal_nonneg x
  have hfPlusLe : ∀ x, fPlus x ≤ |f x| := by
    intro x
    have hval : fPlus x = max (f x) 0 := by
      simp [fPlus, CompactlySupportedContinuousMap.nnrealPart_apply,
        Real.coe_toNNReal']
    rw [hval]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hfMinusLe : ∀ x, fMinus x ≤ |f x| := by
    intro x
    have hval : fMinus x = max (-(f x)) 0 := by
      simp [fMinus, CompactlySupportedContinuousMap.nnrealPart_apply,
        Real.coe_toNNReal']
    rw [hval]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  obtain ⟨uPlus, huPlusBound, huPlusBar, huPlus⟩ :=
    exists_barrier_bounded_localMassiveWeakSolution_of_compactSupport B hcC1 hrhoNe
      hb hbnn hmu fPlus hfPlus (fun x ↦ (hfPlusLe x).trans (hsuper x))
  obtain ⟨uMinus, huMinusBound, huMinusBar, huMinus⟩ :=
    exists_barrier_bounded_localMassiveWeakSolution_of_compactSupport B hcC1 hrhoNe
      hb hbnn hmu fMinus hfMinus (fun x ↦ (hfMinusLe x).trans (hsuper x))
  refine ⟨uPlus - uMinus, ?_, ?_, fun k ↦ ?_⟩
  · intro x
    calc |uPlus x - uMinus x| ≤ |uPlus x| + |uMinus x| := abs_sub _ _
      _ = uPlus x + uMinus x := by
          rw [abs_of_nonneg (huPlusBound x).1, abs_of_nonneg (huMinusBound x).1]
      _ ≤ ‖compactSupportToC0 f.nnrealPart.toReal‖ / mu +
          ‖compactSupportToC0 (-f).nnrealPart.toReal‖ / mu := by
          simpa only [fPlus, fMinus] using
            add_le_add (huPlusBound x).2 (huMinusBound x).2
  · filter_upwards [huPlusBar, huMinusBar] with x hxP hxM
    simp only [Pi.sub_apply]
    have hnn : 0 ≤ uPlus x := (huPlusBound x).1
    have hnn' : 0 ≤ uMinus x := (huMinusBound x).1
    have habs : |uPlus x - uMinus x| ≤ uPlus x + uMinus x := by
      rcases abs_cases (uPlus x - uMinus x) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    linarith
  · obtain ⟨uPlusLocal, huPlusAE, huPlusSolution⟩ := huPlus k
    obtain ⟨uMinusLocal, huMinusAE, huMinusSolution⟩ := huMinus k
    refine ⟨uPlusLocal - uMinusLocal, ?_, ?_⟩
    · filter_upwards [huPlusAE, huMinusAE] with x hxPlus hxMinus
      simp only [H1Function.sub_toFun, Pi.sub_apply, hxPlus, hxMinus]
    · have hfPlusL2 : MemL2On (cube d (k : ℤ)) fPlus :=
        (fPlus.continuous.memLp_of_hasCompactSupport fPlus.hasCompactSupport).restrict _
      have hfMinusL2 : MemL2On (cube d (k : ℤ)) fMinus :=
        (fMinus.continuous.memLp_of_hasCompactSupport fMinus.hasCompactSupport).restrict _
      have hsolution := huPlusSolution.sub (B.ell k) (B.rho_measurable k)
        (B.rho_bounded k) hfPlusL2 hfMinusL2 huMinusSolution
      have hfDecomp : fPlus - fMinus = f := by
        simpa only [fPlus, fMinus] using
          (CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg f)
      have hfDecompFun : (fPlus : Vec d → ℝ) - fMinus = f := by
        funext x
        exact congrArg (fun q : C_c(Vec d, ℝ) ↦ q x) hfDecomp
      simpa only [hfDecompFun] using hsolution

/-! ### The `C₀` solution for compactly supported data -/

/-- The exponent of the barrier, chosen against the growth constant. -/
def barrierExponent (dd : ℕ) (K mu : ℝ) : ℝ :=
  min 1 (mu / (2 * (K + 1) * (2 * Real.sqrt dd + 6)))

theorem barrierExponent_le_one (dd : ℕ) (K mu : ℝ) :
    barrierExponent dd K mu ≤ 1 := min_le_left _ _

theorem barrierExponent_pos (dd : ℕ) {K mu : ℝ} (hK : 0 ≤ K) (hmu : 0 < mu) :
    0 < barrierExponent dd K mu := by
  have hs : (0 : ℝ) ≤ Real.sqrt dd := Real.sqrt_nonneg _
  have h6 : (0 : ℝ) < 2 * Real.sqrt dd + 6 := by linarith
  have hden : (0 : ℝ) < 2 * (K + 1) * (2 * Real.sqrt dd + 6) := by
    have : (0 : ℝ) < 2 * (K + 1) := by linarith
    exact mul_pos this h6
  exact lt_min one_pos (div_pos hmu hden)

theorem barrierExponent_mul_le (dd : ℕ) {K mu : ℝ} (hK : 0 ≤ K) (hmu : 0 < mu) :
    barrierExponent dd K mu * K * (2 * Real.sqrt dd + 6) ≤ mu / 2 := by
  have hs : (0 : ℝ) ≤ Real.sqrt dd := Real.sqrt_nonneg _
  have h6 : (0 : ℝ) < 2 * Real.sqrt dd + 6 := by linarith
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  have hden : (0 : ℝ) < 2 * (K + 1) * (2 * Real.sqrt dd + 6) := by
    have : (0 : ℝ) < 2 * (K + 1) := by linarith
    exact mul_pos this h6
  have hle : barrierExponent dd K mu ≤ mu / (2 * (K + 1) * (2 * Real.sqrt dd + 6)) :=
    min_le_right _ _
  have hfac : 0 ≤ K * (2 * Real.sqrt dd + 6) := mul_nonneg hK h6.le
  have hmul := mul_le_mul_of_nonneg_right hle hfac
  have heq : mu / (2 * (K + 1) * (2 * Real.sqrt dd + 6)) *
      (K * (2 * Real.sqrt dd + 6)) = mu * K / (2 * (K + 1)) := by
    field_simp
    try ring
  have hbound : mu * K / (2 * (K + 1)) ≤ mu / 2 := by
    have hpos : (0 : ℝ) < 2 * (K + 1) := by linarith
    rw [div_le_iff₀ hpos]
    have hrw : mu / 2 * (2 * (K + 1)) = mu * (K + 1) := by field_simp; try ring
    rw [hrw]
    nlinarith [hmu.le]
  calc barrierExponent dd K mu * K * (2 * Real.sqrt dd + 6)
      = barrierExponent dd K mu * (K * (2 * Real.sqrt dd + 6)) := by ring
    _ ≤ mu / (2 * (K + 1) * (2 * Real.sqrt dd + 6)) * (K * (2 * Real.sqrt dd + 6)) := hmul
    _ = mu * K / (2 * (K + 1)) := heq
    _ ≤ mu / 2 := hbound

/-- **The whole-space solvability obligation R5-v3, from linear coefficient
growth.**  If `‖∇c‖ + c ≤ K ρ (1 + ‖x‖)` with `ρ > 0`, then for every positive
shift and every compactly supported datum the massive equation has a solution in
`C₀(ℝᵈ)`: the minimal cube-exhaustion solution is trapped under the radial
barrier `A (1 + |x|²)^{-β/2}`, which vanishes at infinity. -/
theorem hasC0MassiveSolutionsOnCompactData_of_linearGrowth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {rho : Vec d → ℝ} (B : MassiveCubeBounds (coefficientAt M L omega) rho)
    (hrhopos : ∀ x, 0 < rho x) {K : ℝ} (hK : 0 ≤ K)
    (hgrowth : ∀ x, euclideanNorm (euclideanGradient (coefficientAt M L omega) x) +
        coefficientAt M L omega x ≤ K * rho x * (1 + ‖x‖)) :
    HasC0MassiveSolutionsOnCompactData (coefficientAt M L omega) rho := by
  classical
  intro mu hmu f
  have hcC1 : ContDiff ℝ 1 (coefficientAt M L omega) := contDiff_one_coefficientAt M L omega
  have hcdiff : Differentiable ℝ (coefficientAt M L omega) := hcC1.differentiable le_rfl
  have hcpos : ∀ x, 0 < coefficientAt M L omega x := coefficientAt_pos M L omega
  have hrhoNe : ∀ x, rho x ≠ 0 := fun x ↦ (hrhopos x).ne'
  set beta : ℝ := barrierExponent d K mu with hbetadef
  have hbetapos : 0 < beta := barrierExponent_pos d hK hmu
  have hbeta1 : beta ≤ 1 := barrierExponent_le_one d K mu
  have hbetaK : beta * K * (2 * Real.sqrt d + 6) ≤ mu / 2 := barrierExponent_mul_le d hK hmu
  -- a radius containing the support of the datum
  obtain ⟨R0, hR0sub⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).1
      f.hasCompactSupport.isCompact.isBounded
  set R : ℝ := max R0 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hRsupp : ∀ x, x ∈ tsupport (f : Vec d → ℝ) → ‖x‖ ≤ R := by
    intro x hx
    have := hR0sub hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set T : ℝ := (d : ℝ) * R ^ 2 with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hTpos : (0 : ℝ) < 1 + T := by linarith
  set nf : ℝ := ‖compactSupportToC0 f‖ with hnfdef
  have hnf0 : 0 ≤ nf := norm_nonneg _
  set A : ℝ := 2 * nf / mu * (1 + T) ^ (beta / 2) + 1 with hAdef
  have hApos : 0 < A := by
    have h1 : 0 ≤ 2 * nf / mu * (1 + T) ^ (beta / 2) := by
      have := Real.rpow_pos_of_pos hTpos (beta / 2)
      positivity
    linarith
  set bb : Vec d → ℝ := radialBarrier A beta with hbbdef
  have hbbpos : ∀ x, 0 < bb x := fun x ↦ radialBarrier_pos hApos beta x
  have hbbsmooth : ContDiff ℝ (⊤ : ℕ∞) bb := contDiff_radialBarrier A beta
  -- the supersolution inequality
  have hdivle : ∀ x, coeffFluxDiv (coefficientAt M L omega) bb x ≤
      mu * rho x / 2 * bb x :=
    fun x ↦ coeffFluxDiv_radialBarrier_le hcdiff (fun y ↦ (hcpos y).le) hK hApos
      hrhopos hgrowth hbetapos hbeta1 hbetaK x
  have hhalf : ∀ x, mu * bb x / 2 ≤
      smoothMassiveForcing (coefficientAt M L omega) rho mu bb x := by
    intro x
    have hquot : coeffFluxDiv (coefficientAt M L omega) bb x / rho x ≤ mu * bb x / 2 := by
      rw [div_le_iff₀ (hrhopos x)]
      have := hdivle x
      nlinarith [this]
    have : smoothMassiveForcing (coefficientAt M L omega) rho mu bb x =
        mu * bb x - coeffFluxDiv (coefficientAt M L omega) bb x / rho x := rfl
    rw [this]
    linarith
  have hsuper : ∀ x, |f x| ≤ smoothMassiveForcing (coefficientAt M L omega) rho mu bb x := by
    intro x
    refine le_trans ?_ (hhalf x)
    by_cases hx : x ∈ tsupport (f : Vec d → ℝ)
    · have hnorm : |f x| ≤ nf := by
        have hpoint : |f x| ≤ ‖compactSupportToC0 f‖ := by
          simpa only [Real.norm_eq_abs, compactSupportToC0_apply] using
            BoundedContinuousFunction.norm_coe_le_norm
              (ZeroAtInftyContinuousMap.toBCF (compactSupportToC0 f)) x
        exact hpoint
      have hxT : vecNormSq x ≤ T := by
        have h1 : vecNormSq x ≤ (d : ℝ) * ‖x‖ ^ 2 := vecNormSq_le_dim_mul_sq_norm x
        have h2 : ‖x‖ ≤ R := hRsupp x hx
        have h3 : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg x]
        have h4 : (d : ℝ) * ‖x‖ ^ 2 ≤ (d : ℝ) * R ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg d)
        linarith
      have hlow := radialBarrier_ge_of_vecNormSq_le hApos hbetapos.le hxT
      have hcancel : (1 + T) ^ (beta / 2) * (1 + T) ^ (-(beta / 2)) = 1 := by
        rw [← Real.rpow_add hTpos]
        simp
      have hAval : A * (1 + T) ^ (-(beta / 2)) = 2 * nf / mu + (1 + T) ^ (-(beta / 2)) := by
        rw [hAdef, add_mul, one_mul, mul_assoc, hcancel, mul_one]
      have hbig : 2 * nf / mu ≤ bb x := by
        have hposrp : (0 : ℝ) < (1 + T) ^ (-(beta / 2)) := Real.rpow_pos_of_pos hTpos _
        have hbbx : A * (1 + T) ^ (-(beta / 2)) ≤ bb x := by
          rw [hbbdef]; exact hlow
        rw [hAval] at hbbx
        linarith
      have : nf ≤ mu * bb x / 2 := by
        have hmul := mul_le_mul_of_nonneg_left hbig hmu.le
        have hexp : mu * (2 * nf / mu) = 2 * nf := by field_simp
        rw [hexp] at hmul
        linarith
      linarith
    · have hzero : f x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hbb : 0 < mu * bb x / 2 := by
        have := hbbpos x
        positivity
      rw [hzero]
      simpa using hbb.le
  -- the exhaustion under the barrier
  obtain ⟨u, hubd, hbar, hloc⟩ :=
    exists_barrier_bounded_signed_localMassiveWeakSolution_of_compactSupport B hcC1
      hrhoNe hbbsmooth (fun x ↦ (hbbpos x).le) hmu f hsuper
  have hreg := continuous_and_ae_eq_localMassiveLimitRepresentative M L omega B f hubd hloc
  set U : Vec d → ℝ := Section6BoundedMultiplier.euclideanBallAverageRepresentative u
    with hUdef
  have hUcont : Continuous U := hreg.1
  have hUb : ∀ x, |U x| ≤ 2 * bb x := by
    have hae : ∀ᵐ x ∂(volume : Measure (Vec d)), |U x| ≤ 2 * bb x := by
      filter_upwards [hreg.2, hbar] with x hx hxb
      rw [hx]
      exact hxb
    intro x
    by_contra hcon
    push_neg at hcon
    have hopen : IsOpen {y : Vec d | 2 * bb y < |U y|} :=
      isOpen_lt (continuous_const.mul hbbsmooth.continuous) hUcont.abs
    have hne : ({y : Vec d | 2 * bb y < |U y|}).Nonempty := ⟨x, hcon⟩
    have hpos : 0 < volume {y : Vec d | 2 * bb y < |U y|} := hopen.measure_pos volume hne
    have hzero : volume {y : Vec d | 2 * bb y < |U y|} = 0 := by
      have hnot : ∀ᵐ y ∂(volume : Measure (Vec d)), ¬ (2 * bb y < |U y|) := by
        filter_upwards [hae] with y hy
        exact not_lt.mpr hy
      simpa using MeasureTheory.ae_iff.mp hnot
    exact absurd hzero hpos.ne'
  have hdecay : Filter.Tendsto U (Filter.cocompact (Vec d)) (nhds 0) := by
    refine squeeze_zero_norm (a := fun x ↦ 2 * bb x) (fun x ↦ ?_) ?_
    · simpa only [Real.norm_eq_abs] using hUb x
    · have := (tendsto_radialBarrier_cocompact (d := d) A hbetapos).const_mul (2 : ℝ)
      simpa [hbbdef] using this
  refine ⟨{ toContinuousMap := ⟨U, hUcont⟩, zero_at_infty' := hdecay }, fun k ↦ ?_⟩
  obtain ⟨v, hv, hvsol⟩ := hloc k
  have huAE : U =ᵐ[volume.restrict (cube d (k : ℤ))] u :=
    hreg.2.filter_mono (ae_mono Measure.restrict_le_self)
  have hvU : v.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] U := hv.trans huAE.symm
  refine ⟨H1Function.ofAEEq v U hvU.symm, fun x ↦ rfl, ?_⟩
  exact IsMassiveWeakSolutionOn.congr (u := v) hvU
    (Filter.Eventually.of_forall fun _ ↦ rfl) hvsol

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
