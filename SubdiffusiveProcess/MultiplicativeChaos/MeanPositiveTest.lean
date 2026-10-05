module

public import SubdiffusiveProcess.MultiplicativeChaos.MeanPositive
public import SubdiffusiveProcess.MultiplicativeChaos.TailNull

@[expose] public section

/-!
# Positivity of the mean of the limiting mass

The cube masses of the cutoff chaos are a martingale, so their mean does not
move; the limit therefore cannot vanish identically unless the whole family
does.  The argument runs on a test function under the cube rather than on the
cube itself, because that is what vague convergence delivers directly: no
portmanteau step and no identification of the cube-mass limit is needed.
-/

open Filter MeasureTheory
open scoped CompactlySupported ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- A test integral is at most the mass of any open set containing the
support. -/
theorem integral_le_measure_of_tsupport_subset [_instPreserved0 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_instPreserved1 : BorelSpace C(SpatialCoordinates d, ℝ)]
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasureOnCompacts nu]
    (f : C_c(SpatialCoordinates d, ℝ)) (hf1 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {U : Set (SpatialCoordinates d)} (hU : MeasurableSet U)
    (hsub : tsupport (f : SpatialCoordinates d → ℝ) ⊆ U) (hfin : nu U ≠ ⊤) :
    ∫ x, f x ∂nu ≤ (nu U).toReal := by
  have hind : Integrable (U.indicator (fun _ => (1 : ℝ))) nu := by
    refine (integrable_indicator_iff hU).mpr ?_
    exact integrableOn_const (C := (1 : ℝ)) hfin
  have hle : ∫ x, f x ∂nu ≤ ∫ x, U.indicator (fun _ => (1 : ℝ)) x ∂nu := by
    refine integral_mono (integrable_cc f nu) hind fun x => ?_
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]
      exact (hf1 x).2
    · have hnx : x ∉ tsupport (f : SpatialCoordinates d → ℝ) := fun hc => hx (hsub hc)
      have : f x = 0 := by
        by_contra hne
        exact hnx (subset_tsupport _ hne)
      rw [Set.indicator_of_notMem hx, this]
  rwa [integral_indicator_const (1 : ℝ) hU, smul_eq_mul, mul_one] at hle

/-- Positivity of the mean of the limiting mass of a cube.  The hypotheses are
exactly what `\noderef{chaos_vague_limit}`, `\noderef{chaos_test_martingale}`
and `\noderef{lem_chaos_moments}` produce. -/
theorem chaos_mean_positive_of_vague (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (mu : BilateralField d → Measure (SpatialCoordinates d))
    (hmumble : Measurable mu)
    (_hlocfin : ∀ omega, IsLocallyFiniteMeasure (mu omega))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (p : ℕ) (hp : 2 ≤ p) (Cmom : ℝ)
    (hintp : ∀ N : ℕ, Integrable (fun omega =>
      (((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) ^ p)
      (chaosSampleLaw M).toMeasure)
    (hmom : ∀ N : ℕ, ∫ omega,
      (((weightedChaosCutoff M H N omega)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) ^ p
      ∂(chaosSampleLaw M).toMeasure ≤ Cmom)
    (hconv : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally
        (fun N => weightedChaosCutoff M H N omega) (mu omega)) :
    0 < ∫⁻ omega, mu omega (centeredCube z r hr : Set (SpatialCoordinates d))
      ∂(chaosSampleLaw M).toMeasure := by
  classical
  have : IsProbabilityMeasure ((chaosSampleLaw M).toMeasure) := inferInstance
  set U : Set (SpatialCoordinates d) :=
    (centeredCube z r hr : Set (SpatialCoordinates d)) with hUdef
  have hUopen : IsOpen U := by
    rw [hUdef, centeredCube_coe_eq_ball]
    exact Metric.isOpen_ball
  have hzU : z ∈ U := by
    rw [hUdef, centeredCube_coe_eq_ball]
    exact Metric.mem_ball_self (by linarith)
  obtain ⟨n, hzn⟩ : ∃ n : ℕ, z ∈ openPiece U n := by
    have hz : z ∈ ⋃ k, openPiece U k := by rw [iUnion_openPiece hUopen]; exact hzU
    exact Set.mem_iUnion.mp hz
  set f : C_c(SpatialCoordinates d, ℝ) := urysohnSeq hUopen n with hfdef
  have hf1 : ∀ x, 0 ≤ f x ∧ f x ≤ 1 := (urysohnSeq_spec hUopen n).1
  have hfnn : ∀ x, 0 ≤ f x := fun x => (hf1 x).1
  have hfsupp : tsupport (f : SpatialCoordinates d → ℝ) ⊆ U :=
    (urysohnSeq_spec hUopen n).2.2
  have hfz : f z = 1 := (urysohnSeq_spec hUopen n).2.1 z hzn
  obtain ⟨hmart, hXnn⟩ := chaos_test_martingale hd M H hH f hfnn
  set X : ℕ → BilateralField d → ℝ := fun N omega =>
    ∫ x, f x ∂(weightedChaosCutoff M H N omega) with hXdef
  set Xinf : BilateralField d → ℝ := fun omega => ∫ x, f x ∂(mu omega) with hXinfdef
  have hint : ∀ N, Integrable (X N) (chaosSampleLaw M).toMeasure :=
    fun N => hmart.integrable N
  have hmean : ∀ N, ∫ w, X N w ∂(chaosSampleLaw M).toMeasure
      = ∫ w, X 0 w ∂(chaosSampleLaw M).toMeasure := by
    intro N
    have h := Martingale.setIntegral_eq hmart (Nat.zero_le N) MeasurableSet.univ
    rw [setIntegral_univ, setIntegral_univ] at h
    exact h.symm
  -- the cutoff at stage zero already charges the test function
  have hm0 : 0 < ∫ w, X 0 w ∂(chaosSampleLaw M).toMeasure := by
    have hpos : ∀ omega, 0 < X 0 omega := by
      intro omega
      rw [hXdef]
      simp only
      rw [integral_weightedChaosCutoff_eq]
      have hnn : ∀ x, 0 ≤ (Real.exp (H omega x) * fineDensity M 0 omega x) * f x :=
        fun x => mul_nonneg
          (mul_pos (Real.exp_pos _) (fineDensity_pos M 0 omega x)).le (hfnn x)
      have hcont : Continuous (fun x =>
          (Real.exp (H omega x) * fineDensity M 0 omega x) * f x) :=
        ((Real.continuous_exp.comp (H omega).continuous).mul
          (continuous_fineDensity M 0 omega)).mul (map_continuous f)
      have hintg : Integrable (fun x =>
          (Real.exp (H omega x) * fineDensity M 0 omega x) * f x) volume :=
        hcont.integrable_of_hasCompactSupport (f.hasCompactSupport.mul_left)
      rw [integral_pos_iff_support_of_nonneg hnn hintg]
      have hsub : {x : SpatialCoordinates d | 0 < f x} ⊆
          Function.support (fun x =>
            (Real.exp (H omega x) * fineDensity M 0 omega x) * f x) := by
        intro x hx
        exact ne_of_gt (mul_pos
          (mul_pos (Real.exp_pos _) (fineDensity_pos M 0 omega x)) hx)
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      have hopen : IsOpen {x : SpatialCoordinates d | 0 < f x} :=
        isOpen_lt continuous_const (map_continuous f)
      exact hopen.measure_pos volume ⟨z, by simp [hfz]⟩
    have hintX0 : Integrable (X 0) (chaosSampleLaw M).toMeasure := hint 0
    have := (integral_pos_iff_support_of_nonneg (fun w => (hpos w).le) hintX0).mpr
    refine this ?_
    have : Function.support (X 0) = Set.univ := by
      ext w
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (hpos w)
    rw [this]
    simp
  -- the L^p bound transfers from the cube masses
  have hdom : ∀ (N : ℕ) (omega : BilateralField d),
      X N omega ≤ ((weightedChaosCutoff M H N omega) U).toReal := by
    intro N omega
    have := weightedChaosCutoff_isLocallyFinite M H N omega
    have hcpt : IsCompact (closure U) := by
      rw [hUdef, centeredCube_coe_eq_ball]
      exact (Metric.isBounded_ball).isCompact_closure
    have hfin : (weightedChaosCutoff M H N omega) U ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt (measure_mono subset_closure) ?_)
      exact hcpt.measure_lt_top
    exact integral_le_measure_of_tsupport_subset _ f hf1
      hUopen.measurableSet hfsupp hfin
  have hintXp : ∀ N, Integrable (fun w => (X N w) ^ p)
      (chaosSampleLaw M).toMeasure := by
    intro N
    refine Integrable.mono' (hintp N)
      (((hint N).aemeasurable.pow_const p).aestronglyMeasurable) ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hXnn N omega) p)]
    exact pow_le_pow_left₀ (hXnn N omega) (hdom N omega) p
  have hmomX : ∀ N, ∫ w, (X N w) ^ p ∂(chaosSampleLaw M).toMeasure ≤ Cmom := by
    intro N
    refine le_trans (integral_mono (hintXp N) (hintp N) fun omega => ?_) (hmom N)
    exact pow_le_pow_left₀ (hXnn N omega) (hdom N omega) p
  have hXconv : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      Tendsto (fun N => X N w) atTop (nhds (Xinf w)) := by
    filter_upwards [hconv] with omega homega
    exact homega f
  have hnotzero := not_ae_eq_zero_of_mean_pos X Xinf hXnn hint
    (fun N => (hint N).aestronglyMeasurable) hmean hm0 p hp Cmom hintXp hmomX hXconv
  -- if the mean of the limiting mass vanished, the test integrals would too
  by_contra hcon
  push Not at hcon
  have hzero : ∫⁻ omega, mu omega U ∂(chaosSampleLaw M).toMeasure = 0 :=
    le_antisymm hcon zero_le
  refine hnotzero ?_
  have hmeasU : Measurable fun omega => mu omega U :=
    (Measure.measurable_coe hUopen.measurableSet).comp hmumble
  have hae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, mu omega U = 0 := by
    have := (lintegral_eq_zero_iff hmeasU).mp hzero
    filter_upwards [this] with omega homega
    exact homega
  filter_upwards [hae] with omega homega
  have hsupp : {x | f x ≠ 0} ⊆ U := fun x hx => hfsupp (subset_tsupport _ hx)
  have hnull : mu omega {x | f x ≠ 0} = 0 := measure_mono_null hsupp homega
  refine integral_eq_zero_of_ae ?_
  have := measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [this] with x hx
  simpa using not_not.mp hx

end SubdiffusiveProcess
