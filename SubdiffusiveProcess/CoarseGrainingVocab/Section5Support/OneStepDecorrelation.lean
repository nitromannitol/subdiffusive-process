import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRange
import SubdiffusiveProcess.CoarseGrainingVocab.RestrictionContinuousBridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCumulant
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepOrbitContinuity
import Mathlib.Probability.Independence.Integration




open MeasureTheory ProbabilityTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-! ## Local measurability -/

private theorem aCutoffPotentialLocalSigma_mono_level {d L K : ℕ}
    (hLK : L ≤ K) (U : Set (Vec d)) :
    aCutoffPotentialLocalSigma L U ≤ aCutoffPotentialLocalSigma K U := by
  unfold aCutoffPotentialLocalSigma
  refine iSup_le fun i => ?_
  let j : Fin (K + 1) := ⟨i, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hLK)⟩
  simpa only [j] using le_iSup
    (fun q : Fin (K + 1) =>
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U).comap
        (fun omega : Sample d => omega q)) j

private theorem measurable_aCutoff_eval_thickening {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (x : Vec d) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    @Measurable (Sample d) ℝ
      (aCutoffPotentialLocalSigma L
        (Metric.thickening epsilon ({x} : Set (Vec d)))) _
      (fun omega => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) := by
  haveI : NeZero d := ⟨by have := M.shellPrefix.dimension; omega⟩
  let i : Fin d := ⟨0, by have := M.shellPrefix.dimension; omega⟩
  let A : Sample d → RegCoeffField d := aCutoffRegCoeffField M L
  let U : Set (Vec d) := {x}
  have hU : MeasurableSet U := measurableSet_singleton x
  have hxU : x ∈ U := Set.mem_singleton x
  have hentry : @Measurable (RegCoeffField d) ℝ
      (RestrictionSigmaR U hU) _ (fun a => a x i i) :=
    measurable_apply_entry_restrictionSigmaR_of_mem hU hxU i i
  have hentryPull : @Measurable (Sample d) ℝ
      (MeasurableSpace.comap A (RestrictionSigmaR U hU)) _
      (fun omega => A omega x i i) :=
    hentry.comp (Measurable.of_comap_le le_rfl)
  have hcontinuous : ∀ omega a b,
      Continuous (fun y : Vec d => A omega y a b) := by
    intro omega a b
    have hmat : Continuous (fun y : Vec d =>
        scalarMatrix (d := d)
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y)) :=
      (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).smul
        continuous_const
    exact (continuous_apply b).comp ((continuous_apply a).comp hmat)
  have hbridge : MeasurableSpace.comap A (RestrictionSigmaR U hU) ≤
      MeasurableSpace.comap A
        (LocalSigmaR (Metric.thickening epsilon U)) :=
    comap_restrictionSigmaR_le_comap_localSigmaR_thickening
      A hcontinuous U hU epsilon hepsilon
  have hlocal : @Measurable (Sample d) (RegCoeffField d)
      (aCutoffPotentialLocalSigma L (Metric.thickening epsilon U))
      (LocalSigmaR (Metric.thickening epsilon U)) A := by
    exact measurable_aCutoffRegCoeffField_local M L Metric.isOpen_thickening
  have hle : MeasurableSpace.comap A (RestrictionSigmaR U hU) ≤
      aCutoffPotentialLocalSigma L (Metric.thickening epsilon U) :=
    hbridge.trans hlocal.comap_le
  have hmeas := hentryPull.mono hle le_rfl
  simpa [A, U, aCutoffRegCoeffField_apply, scalarMatrix, i] using hmeas

/-- The suffix multiplier at `x` is measurable from the natural local source
sigma field of its upper cutoff. -/
theorem measurable_oneStepMultiplierAt_thickening {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (x : Vec d) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    @Measurable (Sample d) ℝ
      (aCutoffPotentialLocalSigma (n + h)
        (Metric.thickening epsilon ({x} : Set (Vec d)))) _
      (oneStepMultiplierAt M n h x) := by
  let U : Set (Vec d) := Metric.thickening epsilon ({x} : Set (Vec d))
  have htop := measurable_aCutoff_eval_thickening M (n + h) x hepsilon
  have hbottom0 := measurable_aCutoff_eval_thickening M n x hepsilon
  have hbottom : @Measurable (Sample d) ℝ
      (aCutoffPotentialLocalSigma (n + h) U) _
      (fun omega => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x) :=
    hbottom0.mono (aCutoffPotentialLocalSigma_mono_level
      (Nat.le_add_right n h) U) le_rfl
  exact htop.div hbottom |>.sub_const 1

/-! ## Geometry and independence -/

private theorem ambientNorm_le_vecNorm {d : ℕ} (v : Vec d) :
    ‖v‖ ≤ Homogenization.Book.Ch02.vecNorm v := by
  rw [pi_norm_le_iff_of_nonneg
    (Homogenization.Book.Ch02.vecNorm_nonneg v)]
  intro i
  simpa [Homogenization.Book.Ch02.vecNorm] using
    (PiLp.norm_apply_le
      (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) i)

private theorem cutoffRangeSeparated_thickenings {d : ℕ}
    {L : ℕ} {x y : Vec d} {epsilon : ℝ}
    (hsep : Real.sqrt (d : ℝ) * (3 : ℝ) ^ L + 2 * epsilon ≤ ‖x - y‖) :
    ∀ {u v : Vec d},
      u ∈ Metric.thickening epsilon ({x} : Set (Vec d)) →
      v ∈ Metric.thickening epsilon ({y} : Set (Vec d)) →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤
        Homogenization.Book.Ch02.vecNorm (u - v) := by
  intro u v hu hv
  obtain ⟨xu, hxu, hux⟩ := Metric.mem_thickening_iff.1 hu
  obtain ⟨yv, hyv, hvy⟩ := Metric.mem_thickening_iff.1 hv
  rw [Set.mem_singleton_iff] at hxu hyv
  subst xu
  subst yv
  have htri : ‖x - y‖ ≤ ‖x - u‖ + ‖u - v‖ + ‖v - y‖ := by
    have houter := norm_add_le ((x - u) + (u - v)) (v - y)
    have hinner := norm_add_le (x - u) (u - v)
    rw [show x - y = (x - u) + (u - v) + (v - y) by abel]
    linarith
  have hxuNorm : ‖x - u‖ < epsilon := by
    simpa only [dist_eq_norm, norm_sub_rev] using hux
  have hyvNorm : ‖v - y‖ < epsilon := by
    simpa only [dist_eq_norm] using hvy
  have hnorm : Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤ ‖u - v‖ := by
    linarith
  exact hnorm.trans (ambientNorm_le_vecNorm (u - v))

/-- Two evaluations of the one-step multiplier are independent beyond the
natural upper-cutoff range. -/
theorem indepFun_oneStepMultiplierAt_of_cutoffRange_lt_norm {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    {x y : Vec d}
    (hxy : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) < ‖x - y‖) :
    IndepFun (oneStepMultiplierAt M n h x)
      (oneStepMultiplierAt M n h y) M.P.toMeasure := by
  let rho : ℝ := Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h)
  let epsilon : ℝ := (‖x - y‖ - rho) / 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon, rho]
    linarith
  let U : Set (Vec d) := Metric.thickening epsilon ({x} : Set (Vec d))
  let V : Set (Vec d) := Metric.thickening epsilon ({y} : Set (Vec d))
  have hsep : ∀ (u v : Vec d), u ∈ U → v ∈ V →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) ≤
        Homogenization.Book.Ch02.vecNorm (u - v) := by
    intro u v hu hv
    have hbudget : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) +
        2 * epsilon ≤ ‖x - y‖ := by
      dsimp only [epsilon, rho]
      linarith
    exact cutoffRangeSeparated_thickenings (u := u) (v := v)
      (L := n + h) (x := x) (y := y) (epsilon := epsilon)
      hbudget (by simpa only [U] using hu) (by simpa only [V] using hv)
  have hindep := indep_aCutoffPotentialLocalSigma_of_separation
    M (n + h) U V Metric.isOpen_thickening.measurableSet
      Metric.isOpen_thickening.measurableSet
      (fun {_u _v} hu hv => hsep _u _v hu hv)
  have hxmeas : @Measurable (Sample d) ℝ
      (aCutoffPotentialLocalSigma (n + h) U) _
      (oneStepMultiplierAt M n h x) := by
    simpa only [U] using
      measurable_oneStepMultiplierAt_thickening M n h x hepsilon
  have hymeas : @Measurable (Sample d) ℝ
      (aCutoffPotentialLocalSigma (n + h) V) _
      (oneStepMultiplierAt M n h y) := by
    simpa only [V] using
      measurable_oneStepMultiplierAt_thickening M n h y hepsilon
  exact (IndepFun_iff_Indep _ _ _).2
    (indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hindep hxmeas.comap_le) hymeas.comap_le)

/-! ## Centering and covariance support -/

/-- Stationarity transports the already-proved origin centering identity to
every spatial evaluation. -/
theorem integral_oneStepMultiplierAt_eq_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (x : Vec d) (hh : 0 < h) :
    ∫ omega : Sample d, oneStepMultiplierAt M n h x omega
      ∂M.P.toMeasure = 0 := by
  letI := potentialSequenceVAddInvariant M
  have hrepr : (fun omega : Sample d => oneStepMultiplierAt M n h x omega) =
      fun omega => oneStepOriginMultiplier M n h (x +ᵥ omega) := by
    funext omega
    dsimp only [oneStepMultiplierAt, oneStepOriginMultiplier,
      cutoffRatioMinusOne, aCutoffAtInt]
    simp only [if_neg (not_lt_of_ge (Int.natCast_nonneg n)),
      Int.toNat_natCast]
    change SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega x /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x - 1 =
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h)
          (translatePotentialSequence x omega) 0 /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n
          (translatePotentialSequence x omega) 0 - 1
    rw [aCutoff_translatePotentialSequence M (n + h) x omega 0,
      aCutoff_translatePotentialSequence M n x omega 0, zero_add]
  rw [hrepr]
  rw [(Stationary.measurePreserving_const_vadd
    (mu := M.P.toMeasure) x).integral_comp
      (measurableEmbedding_const_vadd x)]
  exact integral_oneStepOriginMultiplier_eq_zero M n h hh

/-- The scalar one-step covariance is compactly supported in the natural
cutoff ball.  This is the stochastic zero-mode input for the stationary
Helmholtz trace theorem. -/
theorem integral_oneStepMultiplierAt_mul_eq_zero_of_cutoffRange_lt_norm
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (hh : 0 < h) {x y : Vec d}
    (hxy : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) < ‖x - y‖) :
    ∫ omega : Sample d,
        oneStepMultiplierAt M n h x omega *
          oneStepMultiplierAt M n h y omega ∂M.P.toMeasure = 0 := by
  have hindep := indepFun_oneStepMultiplierAt_of_cutoffRange_lt_norm M n h hxy
  have hfactor := hindep.integral_fun_mul_eq_mul_integral
    (measurable_oneStepMultiplierAt M n h x).aestronglyMeasurable
    (measurable_oneStepMultiplierAt M n h y).aestronglyMeasurable
  rw [integral_oneStepMultiplierAt_eq_zero M n h x hh,
    integral_oneStepMultiplierAt_eq_zero M n h y hh, mul_zero] at hfactor
  exact hfactor

/-- Origin/translate form of compact covariance support. -/
theorem integral_oneStepMultiplierAt_mul_origin_eq_zero_of_cutoffRange_lt_norm
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (hh : 0 < h) {x : Vec d}
    (hx : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) < ‖x‖) :
    ∫ omega : Sample d,
        oneStepMultiplierAt M n h x omega *
          oneStepOriginMultiplier M n h omega ∂M.P.toMeasure = 0 := by
  have hx' : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) < ‖x - 0‖ := by
    simpa only [sub_zero] using hx
  simpa only [oneStepOriginMultiplier, oneStepMultiplierAt] using
    integral_oneStepMultiplierAt_mul_eq_zero_of_cutoffRange_lt_norm
      M n h hh (x := x) (y := 0) hx'

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
