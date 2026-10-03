module

public import SubdiffusiveProcess.Lane1.VagueMeasurable
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Lane1.VagueFunctional
public import SubdiffusiveProcess.Lane1.TestFunctionMartingale
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

@[expose] public section

/-!
# The measurable vague limit family

Assembling: on a measurable full-measure event the test integrals converge, so
the limsup functional is a genuine limit there and is linear and positive; off
the event it is taken to be zero, which is also linear and positive.  The
functional is measurable in the parameter, so the Riesz measures form a
measurable family, and on the event they are the vague limits.
-/

open Filter MeasureTheory

open scoped CompactlySupported ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- A Riesz measure is finite on compacts, hence locally finite. -/
instance isLocallyFiniteMeasure_rieszMeasure {d : ℕ}
    (Lam : C_c(SpatialCoordinates d, ℝ) →ₚ[ℝ] ℝ) :
    IsLocallyFiniteMeasure (RealRMK.rieszMeasure Lam) := by
  refine ⟨fun x => ⟨Metric.ball x (1 / 2), Metric.ball_mem_nhds x (by norm_num), ?_⟩⟩
  have hK : IsCompact (Metric.closedBall x (1 / 2 : ℝ)) := isCompact_closedBall _ _
  have hdisj : Disjoint (Metric.closedBall x (1 / 2 : ℝ))
      (Metric.ball x (1 : ℝ))ᶜ := by
    rw [Set.disjoint_left]
    intro y hy hy2
    exact hy2 (Metric.closedBall_subset_ball (by norm_num) hy)
  obtain ⟨g, hg1, hg0, hgcs, hg01⟩ :=
    exists_continuous_one_zero_of_isCompact hK Metric.isOpen_ball.isClosed_compl hdisj
  calc RealRMK.rieszMeasure Lam (Metric.ball x (1 / 2))
      ≤ RealRMK.rieszMeasure Lam (Metric.closedBall x (1 / 2)) :=
        measure_mono Metric.ball_subset_closedBall
    _ ≤ ENNReal.ofReal (Lam ⟨g, hgcs⟩) :=
        RealRMK.rieszMeasure_le_of_eq_one Lam (fun y => (hg01 y).1) hK
          (fun y hy => hg1 hy)
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- **The measurable vague limit.**  On a measurable event where every test
integral converges, the limits are the integrals against a measurable family of
measures. -/
theorem exists_measurable_vague_limit
    {d : ℕ} {Om : Type*} [MeasurableSpace Om]
    (nuN : Om → ℕ → Measure (SpatialCoordinates d))
    (G : Set Om) (hG : MeasurableSet G)
    (hint : ∀ (w : Om) (N : ℕ) (f : C_c(SpatialCoordinates d, ℝ)),
      Integrable (f : SpatialCoordinates d → ℝ) (nuN w N))
    (hmbleint : ∀ (N : ℕ) (f : C_c(SpatialCoordinates d, ℝ)),
      Measurable (fun w => ∫ x, f x ∂(nuN w N)))
    (hGconv : ∀ w ∈ G, ∀ f : C_c(SpatialCoordinates d, ℝ),
      ∃ L : ℝ, Tendsto (fun N => ∫ x, f x ∂(nuN w N)) atTop (nhds L)) :
    ∃ mu : Om → Measure (SpatialCoordinates d), Measurable mu ∧
      (∀ w, IsLocallyFiniteMeasure (mu w)) ∧
      (∀ (w : Om) (U : Set (SpatialCoordinates d)), IsOpen U →
        ∀ c : ℝ≥0∞, c < mu w U →
          ∃ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
            tsupport (f : SpatialCoordinates d → ℝ) ⊆ U ∧
            c < ENNReal.ofReal (∫ x, f x ∂(mu w))) ∧
      ∀ w ∈ G, MeasuresConvergeLocally (nuN w) (mu w) := by
  classical
  set Lam : Om → C_c(SpatialCoordinates d, ℝ) → ℝ :=
    fun w f => if w ∈ G then limsup (fun N => ∫ x, f x ∂(nuN w N)) atTop else 0
    with hLamdef
  have hLamtend : ∀ w ∈ G, ∀ f : C_c(SpatialCoordinates d, ℝ),
      Tendsto (fun N => ∫ x, f x ∂(nuN w N)) atTop (nhds (Lam w f)) := by
    intro w hw f
    obtain ⟨L, hL⟩ := hGconv w hw f
    have hEq : Lam w f = L := by
      rw [hLamdef]
      simp only [if_pos hw]
      exact hL.limsup_eq
    rw [hEq]
    exact hL
  have hadd : ∀ (w : Om) (f g : C_c(SpatialCoordinates d, ℝ)),
      Lam w (f + g) = Lam w f + Lam w g := by
    intro w f g
    by_cases hw : w ∈ G
    · refine tendsto_nhds_unique (hLamtend w hw (f + g)) ?_
      have hpt : ∀ N : ℕ, ∫ x, (f + g) x ∂(nuN w N)
          = (∫ x, f x ∂(nuN w N)) + ∫ x, g x ∂(nuN w N) := by
        intro N
        simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
        exact integral_add (hint w N f) (hint w N g)
      simp only [hpt]
      exact (hLamtend w hw f).add (hLamtend w hw g)
    · simp [hLamdef, if_neg hw]
  have hsmul : ∀ (w : Om) (c : ℝ) (f : C_c(SpatialCoordinates d, ℝ)),
      Lam w (c • f) = c * Lam w f := by
    intro w c f
    by_cases hw : w ∈ G
    · refine tendsto_nhds_unique (hLamtend w hw (c • f)) ?_
      have hpt : ∀ N : ℕ, ∫ x, (c • f) x ∂(nuN w N)
          = c * ∫ x, f x ∂(nuN w N) := by
        intro N
        simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
          smul_eq_mul]
        exact integral_const_mul c _
      simp only [hpt]
      exact (hLamtend w hw f).const_mul c
    · simp [hLamdef, if_neg hw]
  have hmono : ∀ w : Om, Monotone (Lam w) := by
    intro w f g hfg
    by_cases hw : w ∈ G
    · refine le_of_tendsto_of_tendsto (hLamtend w hw f) (hLamtend w hw g) ?_
      filter_upwards with N
      exact integral_mono (hint w N f) (hint w N g) (fun x => hfg x)
    · simp [hLamdef, if_neg hw]
  set Lp : Om → C_c(SpatialCoordinates d, ℝ) →ₚ[ℝ] ℝ := fun w =>
    { toFun := Lam w
      map_add' := hadd w
      map_smul' := by intro c f; simpa using hsmul w c f
      monotone' := hmono w } with hLpdef
  have hLpmble : ∀ f : C_c(SpatialCoordinates d, ℝ),
      Measurable (fun w => Lp w f) := by
    intro f
    have heq : (fun w => Lp w f) = fun w =>
        if w ∈ G then limsup (fun N => ∫ x, f x ∂(nuN w N)) atTop else 0 := rfl
    rw [heq]
    exact Measurable.ite hG (Measurable.limsup (fun N => hmbleint N f))
      measurable_const
  refine ⟨fun w => RealRMK.rieszMeasure (Lp w), ?_,
    fun w => isLocallyFiniteMeasure_rieszMeasure (Lp w),
    fun w U hU c hc => rieszMeasure_innerApprox (Lp w) hU hc, ?_⟩
  · exact measurable_rieszMeasure_family Lp hLpmble
      (fun w => isLocallyFiniteMeasure_rieszMeasure (Lp w))
  · intro w hw f
    have hval : ∫ x, f x ∂(RealRMK.rieszMeasure (Lp w)) = Lam w f :=
      RealRMK.integral_rieszMeasure (Lp w) f
    rw [hval]
    exact hLamtend w hw f

/-- **The vague limit of the cutoff measures**, as a measurable family. -/
theorem chaos_vague_limit_of_cube_limits
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (hcubeae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (∀ (j : ℕ) (k : Fin d → ℤ), ∃ L : ℝ, Tendsto (fun N =>
        ((weightedChaosCutoff M H N omega) ((centeredCube (tileCenter j k)
          ((3 : ℝ) ^ (-(j : ℤ))) (zpow_neg_pos j)) :
            Set (SpatialCoordinates d))).toReal) atTop (nhds L)) ∧
      (∀ n : ℕ, ∃ L : ℝ, Tendsto (fun N =>
        ((weightedChaosCutoff M H N omega) ((centeredCube
          (0 : SpatialCoordinates d) (2 * ((n : ℝ) + 4)) (by positivity)) :
            Set (SpatialCoordinates d))).toReal) atTop (nhds L))) :
    ∃ mu : BilateralField d → Measure (SpatialCoordinates d), Measurable mu ∧
      (∀ omega, IsLocallyFiniteMeasure (mu omega)) ∧
      (∀ (omega : BilateralField d) (U : Set (SpatialCoordinates d)), IsOpen U →
        ∀ c : ℝ≥0∞, c < mu omega U →
          ∃ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
            tsupport (f : SpatialCoordinates d → ℝ) ⊆ U ∧
            c < ENNReal.ofReal (∫ x, f x ∂(mu omega))) ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        MeasuresConvergeLocally
          (fun N => weightedChaosCutoff M H N omega) (mu omega) := by
  classical
  set G : Set (BilateralField d) :=
    {omega |
      (∀ (j : ℕ) (k : Fin d → ℤ), ∃ L : ℝ, Tendsto (fun N =>
        ((weightedChaosCutoff M H N omega) ((centeredCube (tileCenter j k)
          ((3 : ℝ) ^ (-(j : ℤ))) (zpow_neg_pos j)) :
            Set (SpatialCoordinates d))).toReal) atTop (nhds L)) ∧
      (∀ n : ℕ, ∃ L : ℝ, Tendsto (fun N =>
        ((weightedChaosCutoff M H N omega) ((centeredCube
          (0 : SpatialCoordinates d) (2 * ((n : ℝ) + 4)) (by positivity)) :
            Set (SpatialCoordinates d))).toReal) atTop (nhds L))} with hGdef
  have hcubemble : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ),
      StronglyMeasurable (fun omega : BilateralField d =>
        ((weightedChaosCutoff M H N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) := by
    intro z r hr N
    exact ((weightedChaosCutoff_centeredCube_adapted M H hH.1 z r hr N).mono
      ((conditionalFineFiltration H hH.1).le N) le_rfl).stronglyMeasurable
  have hGmble : MeasurableSet G := by
    rw [hGdef]
    have h1 : MeasurableSet {omega : BilateralField d |
        ∀ (j : ℕ) (k : Fin d → ℤ), ∃ L : ℝ, Tendsto (fun N =>
          ((weightedChaosCutoff M H N omega) ((centeredCube (tileCenter j k)
            ((3 : ℝ) ^ (-(j : ℤ))) (zpow_neg_pos j)) :
              Set (SpatialCoordinates d))).toReal) atTop (nhds L)} := by
      have heq : {omega : BilateralField d |
          ∀ (j : ℕ) (k : Fin d → ℤ), ∃ L : ℝ, Tendsto (fun N =>
            ((weightedChaosCutoff M H N omega) ((centeredCube (tileCenter j k)
              ((3 : ℝ) ^ (-(j : ℤ))) (zpow_neg_pos j)) :
                Set (SpatialCoordinates d))).toReal) atTop (nhds L)}
          = ⋂ j : ℕ, ⋂ k : Fin d → ℤ, {omega : BilateralField d | ∃ L : ℝ,
              Tendsto (fun N => ((weightedChaosCutoff M H N omega)
                ((centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ)))
                  (zpow_neg_pos j)) : Set (SpatialCoordinates d))).toReal)
                atTop (nhds L)} := by
        ext omega
        simp [Set.mem_iInter]
      rw [heq]
      refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => ?_
      exact measurableSet_exists_tendsto
        (fun N => (hcubemble (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ)))
          (zpow_neg_pos j) N).measurable)
    have h2 : MeasurableSet {omega : BilateralField d |
        ∀ n : ℕ, ∃ L : ℝ, Tendsto (fun N =>
          ((weightedChaosCutoff M H N omega) ((centeredCube
            (0 : SpatialCoordinates d) (2 * ((n : ℝ) + 4)) (by positivity)) :
              Set (SpatialCoordinates d))).toReal) atTop (nhds L)} := by
      have heq : {omega : BilateralField d |
          ∀ n : ℕ, ∃ L : ℝ, Tendsto (fun N =>
            ((weightedChaosCutoff M H N omega) ((centeredCube
              (0 : SpatialCoordinates d) (2 * ((n : ℝ) + 4)) (by positivity)) :
                Set (SpatialCoordinates d))).toReal) atTop (nhds L)}
          = ⋂ n : ℕ, {omega : BilateralField d | ∃ L : ℝ,
              Tendsto (fun N => ((weightedChaosCutoff M H N omega)
                ((centeredCube (0 : SpatialCoordinates d) (2 * ((n : ℝ) + 4))
                  (by positivity)) : Set (SpatialCoordinates d))).toReal)
                atTop (nhds L)} := by
        ext omega
        simp [Set.mem_iInter]
      rw [heq]
      refine MeasurableSet.iInter fun n => ?_
      have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 4) := by positivity
      exact measurableSet_exists_tendsto
        (fun N => (hcubemble (0 : SpatialCoordinates d) (2 * ((n : ℝ) + 4))
          hpos N).measurable)
    exact h1.inter h2
  have hGfull : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, omega ∈ G := hcubeae
  have hint : ∀ (w : BilateralField d) (N : ℕ) (f : C_c(SpatialCoordinates d, ℝ)),
      Integrable (f : SpatialCoordinates d → ℝ)
        (weightedChaosCutoff M H N w) := by
    intro w N f
    haveI := weightedChaosCutoff_isLocallyFinite M H N w
    exact (map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport
  have hmbleint : ∀ (N : ℕ) (f : C_c(SpatialCoordinates d, ℝ)),
      Measurable (fun w : BilateralField d =>
        ∫ x, f x ∂(weightedChaosCutoff M H N w)) := by
    intro N f
    exact ((weightedChaosCutoff_test_adapted M H hH.1
      (f : SpatialCoordinates d → ℝ) (map_continuous f) N).mono
        ((conditionalFineFiltration H hH.1).le N) le_rfl)
  obtain ⟨mu, hmumble, hmuloc, hmuinner, hmuconv⟩ :=
    exists_measurable_vague_limit
      (fun w N => weightedChaosCutoff M H N w) G hGmble hint hmbleint
      (fun w hw f => chaos_vague_functional M H w hw.1 hw.2 f)
  refine ⟨mu, hmumble, hmuloc, hmuinner, ?_⟩
  filter_upwards [hGfull] with omega homega
  exact hmuconv omega homega

/-- Each cube mass converges almost surely: it is a nonnegative martingale
whose mean is constant in the cutoff, hence bounded in `L^1`. -/
theorem chaos_cube_ae_tendsto
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ L : ℝ,
      Tendsto (fun N => ((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
        atTop (nhds L) := by
  classical
  obtain ⟨hmart, hnn0⟩ :=
    weightedChaosCutoff_centeredCube_martingale_nonnegative hd M H hH z r hr
  set f : ℕ → BilateralField d → ℝ := fun N omega =>
    ((weightedChaosCutoff M H N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal with hfdef
  have hsub : Submartingale f (conditionalFineFiltration H hH.1)
      (chaosSampleLaw M).toMeasure := hmart.submartingale
  have hnn : ∀ (N : ℕ) (omega : BilateralField d), 0 ≤ f N omega :=
    fun N omega => ENNReal.toReal_nonneg
  set R : ℝ≥0 := ⟨∫ omega, f 0 omega ∂(chaosSampleLaw M).toMeasure,
    integral_nonneg (fun omega => hnn 0 omega)⟩ with hRdef
  have hmean : ∀ N : ℕ,
      ∫ omega, f N omega ∂(chaosSampleLaw M).toMeasure
        = ∫ omega, f 0 omega ∂(chaosSampleLaw M).toMeasure := by
    intro N
    have h := Martingale.setIntegral_eq hmart (Nat.zero_le N) MeasurableSet.univ
    rw [setIntegral_univ, setIntegral_univ] at h
    exact h.symm
  have hbdd : ∀ N : ℕ,
      eLpNorm (f N) 1 (chaosSampleLaw M).toMeasure ≤ (R : ℝ≥0∞) := by
    intro N
    have hintN : Integrable (f N) (chaosSampleLaw M).toMeasure := hsub.integrable N
    rw [eLpNorm_one_eq_lintegral_enorm hintN.aestronglyMeasurable]
    have hcongr : ∫⁻ omega, ‖f N omega‖ₑ ∂(chaosSampleLaw M).toMeasure
        = ENNReal.ofReal (∫ omega, f N omega ∂(chaosSampleLaw M).toMeasure) := by
      rw [ofReal_integral_eq_lintegral_ofReal hintN
        (Filter.Eventually.of_forall (fun omega => hnn N omega))]
      refine lintegral_congr fun omega => ?_
      rw [Real.enorm_eq_ofReal (hnn N omega)]
    rw [hcongr, hmean N, hRdef,
      ENNReal.ofReal_eq_coe_nnreal (integral_nonneg (fun omega => hnn 0 omega))]
    rfl
  exact hsub.exists_ae_tendsto_of_bdd hbdd

end SubdiffusiveProcess
