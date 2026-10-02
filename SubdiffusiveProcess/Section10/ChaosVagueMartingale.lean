import Mathlib
import SubdiffusiveProcess.Section10.ChaosFiniteBank
import SubdiffusiveProcess.Section10.VagueWeights
import SubdiffusiveProcess.Lane1.VagueLimit
open Filter MeasureTheory ProbabilityTheory Topology Set
open SubdiffusiveProcess
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace Paper

/-- Fix 9, limiting-process.tex L:258–301; independently harvested flash leaf. -/

theorem aux_lim_measure_cutoff_measurable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) :
    Measurable (chaosCutoff M n) := by
  rw [Measure.measurable_measure]
  intro s hs
  have hjoint : Measurable (Function.uncurry
      (fun (omega : BilateralField d) (a : SpatialCoordinates d) =>
        ENNReal.ofReal (fineDensity M n omega a))) := by
    unfold fineDensity finePotential
    fun_prop
  have hmeas : Measurable (fun omega : BilateralField d =>
      ∫⁻ a, ENNReal.ofReal (fineDensity M n omega a) ∂(volume.restrict s)) :=
    Measurable.lintegral_prod_right (ν := volume.restrict s) hjoint
  have hfun : (fun omega : BilateralField d => (chaosCutoff M n omega) s)
      = (fun omega : BilateralField d =>
          ∫⁻ a, ENNReal.ofReal (fineDensity M n omega a) ∂(volume.restrict s)) := by
    funext omega
    rw [chaosCutoff, withDensity_apply _ hs]
    rfl
  rw [hfun]
  exact hmeas


/-- Fix 9, limiting-process.tex L:258–301; independently harvested flash leaf. -/

theorem aux_lim_measure_compact_unit_cover
    {d : ℕ} (K : Set (SpatialCoordinates d)) (hK : IsCompact K) :
    ∃ s : Finset (SpatialCoordinates d),
      K ⊆ ⋃ z ∈ s, (centeredCube z 1 zero_lt_one : Set (SpatialCoordinates d)) := by
  have hUo : ∀ z : SpatialCoordinates d,
      IsOpen ((centeredCube z 1 zero_lt_one).carrier) := by
    intro z
    change IsOpen (Metric.ball z ((1 : ℝ) / 2))
    exact Metric.isOpen_ball
  have hcover : K ⊆ ⋃ z, ((centeredCube z 1 zero_lt_one).carrier) := by
    intro x _hx
    refine mem_iUnion.mpr ⟨x, ?_⟩
    change x ∈ Metric.ball x ((1 : ℝ) / 2)
    exact Metric.mem_ball_self (by norm_num)
  exact IsCompact.elim_finite_subcover hK
    (fun z => (centeredCube z 1 zero_lt_one).carrier) hUo hcover


/-- Fix 9, limiting-process.tex L:258–301; independently harvested flash leaf. -/

theorem aux_lim_measure_test_finite_cover_bound
    {X I : Type*} [MeasurableSpace X] (mu : Measure X)
    (f : X → ℝ≥0∞) (B : ℝ≥0∞) (s : Finset I) (U : I → Set X)
    (hU : ∀ i, MeasurableSet (U i)) (hB : ∀ x, f x ≤ B)
    (hsupp : Function.support f ⊆ ⋃ i ∈ s, U i) :
    (∫⁻ x, f x ∂mu) ≤ B * ∑ i ∈ s, mu (U i) := by
  let UU : Set X := ⋃ i ∈ s, U i
  have hUU : MeasurableSet UU := Finset.measurableSet_biUnion s (fun i _ => hU i)
  have hle : f ≤ UU.indicator (fun _ => B) := by
    intro x
    by_cases hx : x ∈ UU
    · rw [Set.indicator_of_mem hx]
      exact hB x
    · rw [Set.indicator_of_notMem hx]
      have h0 : f x = 0 := by
        by_contra h
        exact hx (hsupp (Function.mem_support.mpr h))
      rw [h0]
  calc ∫⁻ x, f x ∂mu
      ≤ ∫⁻ x, UU.indicator (fun _ => B) x ∂mu := lintegral_mono hle
    _ = B * mu UU := lintegral_indicator_const hUU B
    _ ≤ B * ∑ i ∈ s, mu (U i) :=
        mul_le_mul_right (measure_biUnion_finset_le s U) B


/-- Fix 9, limiting-process.tex L:258–301; independently harvested flash leaf. -/

theorem aux_lim_measure_retained_dominated_passage
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (X : ℕ → Ω → ℝ) (Y D : Ω → ℝ) (b : ℝ)
    (hX : ∀ n, AEStronglyMeasurable (X n) P)
    (hD : Integrable D P) (hb : ∀ n, ∀ᵐ w ∂P, ‖X n w‖ ≤ D w)
    (hconv : ∀ᵐ w ∂P, Tendsto (fun n => X n w) atTop (𝓝 (Y w)))
    (heq : ∀ᶠ n in atTop, (∫ w in A, X n w ∂P) = b) :
    (∫ w in A, Y w ∂P) = b := by
  have htend :
      Tendsto (fun n => ∫ w in A, X n w ∂P) atTop (𝓝 (∫ w in A, Y w ∂P)) :=
    tendsto_integral_of_dominated_convergence (μ := P.restrict A) D
      (fun n => (hX n).restrict)
      hD.restrict
      (fun n => ae_restrict_of_ae (hb n))
      (ae_restrict_of_ae hconv)
  have hb_tend : Tendsto (fun n => ∫ w in A, X n w ∂P) atTop (𝓝 b) :=
    Tendsto.congr' (heq.mono fun n hn => hn.symm) tendsto_const_nhds
  exact tendsto_nhds_unique htend hb_tend


/-- Fix 9, limiting-process.tex L:258–301; independently harvested flash leaf. -/

theorem aux_lim_measure_finite_bind
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n m : ℕ) (hnm : n ≤ m) (A : Set (BilateralField d))
    (hA : MeasurableSet[(conditionalFineFiltration
      (fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) measurable_const) n] A) :
    ((chaosSampleLaw M).toMeasure.restrict A).bind (chaosCutoff M m) =
      ((chaosSampleLaw M).toMeasure.restrict A).bind (chaosCutoff M n) := by
  apply Measure.ext
  intro D hD
  rw [Measure.bind_apply hD ((aux_lim_measure_cutoff_measurable M m).aemeasurable),
    Measure.bind_apply hD ((aux_lim_measure_cutoff_measurable M n).aemeasurable)]
  exact aux_lim_measure_finite_rectangle M n m hnm A hA D hD


/-- Fix 9, limiting-process.tex L:258–301; independently harvested flash leaf. -/

theorem aux_lim_measure_vague_positive_lintegral
    {d : ℕ} (muN : ℕ → Measure (SpatialCoordinates d))
    (mu : Measure (SpatialCoordinates d))
    (hN : ∀ n, IsLocallyFiniteMeasure (muN n)) [IsLocallyFiniteMeasure mu]
    (hconv : MeasuresConvergeLocally muN mu) (f : C_c(SpatialCoordinates d, ℝ))
    (hf : ∀ x, 0 ≤ f x) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f x) ∂muN n) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂mu)) := by
  have hfi : ∀ n, Integrable (fun x => f x) (muN n) := fun n =>
    CompactlySupportedContinuousMap.integrable f
  have hfi' : Integrable (fun x => f x) mu := CompactlySupportedContinuousMap.integrable f
  have hgoal_eq : (fun n => ∫⁻ x, ENNReal.ofReal (f x) ∂muN n)
      = fun n => ENNReal.ofReal (∫ x, f x ∂muN n) := by
    funext n
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfi n)
      (MeasureTheory.ae_of_all _ hf)).symm
  have hlim_eq : (∫⁻ x, ENNReal.ofReal (f x) ∂mu) = ENNReal.ofReal (∫ x, f x ∂mu) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi'
      (MeasureTheory.ae_of_all _ hf)).symm
  rw [hgoal_eq, hlim_eq]
  exact (ENNReal.continuous_ofReal.tendsto _).comp (hconv f)


/-- Fix 9, limiting-process.tex L:258–301; independently harvested flash leaf. -/

theorem aux_lim_measure_unweighted_test_measurable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (f : C_c(SpatialCoordinates d, ℝ)) :
    Measurable (fun w => ∫ x, f x ∂chaosCutoff M n w) := by
  have hH : Measurable (fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) := measurable_const
  have hadapt := weightedChaosCutoff_test_adapted M (fun _ => 0) hH
    (⇑f) f.continuous
  have hmeas : Measurable
      (fun w => ∫ x, (⇑f : SpatialCoordinates d → ℝ) x
        ∂weightedChaosCutoff M (fun _ => 0) n w) :=
    (Adapted.stronglyMeasurable (i := n) hadapt).measurable
  rw [show (fun w => ∫ x, f x ∂chaosCutoff M n w)
      = fun w => ∫ x, (⇑f : SpatialCoordinates d → ℝ) x
          ∂weightedChaosCutoff M (fun _ => 0) n w from by
        funext w; rw [chaosCutoff_eq_weightedChaosCutoff_zero]]
  exact hmeas


/-- Fix 9, limiting-process.tex L:258–301; independently harvested flash leaf. -/

theorem aux_lim_measure_countable_cube_limits
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Z : ℕ → SpatialCoordinates d)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) :
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ j : ℕ,
      ∃ L : ℝ, Tendsto (fun n => ((chaosCutoff M n w)
        (centeredCube (Z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal) atTop (𝓝 L) := by
  rw [MeasureTheory.ae_all_iff]
  intro j
  obtain ⟨X, _, hX, _⟩ := chaosCutoff_centeredCube_ae_tendsto M (Z j) (r j) (hr j)
  filter_upwards [hX] with w hw
  exact ⟨X w, hw⟩


theorem aux_lim_measure_positive_test_envelope
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (f : C_c(SpatialCoordinates d, ℝ)) :
    ∃ b : BilateralField d → ℝ≥0∞, Measurable b ∧
      (∫⁻ w, b w ∂(chaosSampleLaw M).toMeasure) ≠ ⊤ ∧
      ∀ n, ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
        (∫⁻ x, ENNReal.ofReal (f x) ∂chaosCutoff M n w) ≤ b w := by
  classical
  obtain ⟨D, hDmeas, hDpos, hD⟩ := aux_lim_measure_unit_integrable_envelope hd M hdelta
  obtain ⟨s, hs⟩ := aux_lim_measure_compact_unit_cover _ f.hasCompactSupport
  obtain ⟨B, hB⟩ := (f.hasCompactSupport.isCompact_range f.continuous).isBounded.exists_norm_le
  let b : BilateralField d → ℝ≥0∞ := fun w => ENNReal.ofReal B * ∑ z ∈ s, ENNReal.ofReal (D z w)
  have hbmeas : Measurable b := measurable_const.mul
    (Finset.measurable_fun_sum s (fun z hz => (hDmeas z).ennreal_ofReal))
  refine ⟨b, hbmeas, ?_, ?_⟩
  · dsimp [b]
    rw [lintegral_const_mul _ (Finset.measurable_fun_sum s (fun z hz => (hDmeas z).ennreal_ofReal)),
      lintegral_finset_sum s (fun z hz => (hDmeas z).ennreal_ofReal)]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ne_of_lt
    exact ENNReal.sum_lt_top.mpr (fun z hz => lt_top_iff_ne_top.mpr
      ((lintegral_ofReal_ne_top_iff_integrable (hDmeas z).aestronglyMeasurable
        (ae_of_all _ (hDpos z))).mpr (hD z).1))
  · intro n
    have hall : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ z ∈ s, ∀ n,
        ((chaosCutoff M n w) (centeredCube z 1 zero_lt_one : Set (SpatialCoordinates d))).toReal ≤ D z w :=
      (s.eventually_all).mpr (fun z hz => (hD z).2)
    filter_upwards [hall] with w hw
    haveI := chaosCutoff_isLocallyFinite M n w
    have htest := aux_lim_measure_test_finite_cover_bound (chaosCutoff M n w)
      (fun x => ENNReal.ofReal (f x)) (ENNReal.ofReal B) s
      (fun z => (centeredCube z 1 zero_lt_one : Set (SpatialCoordinates d)))
      (fun z => (centeredCube z 1 zero_lt_one).isOpen.measurableSet)
      (fun x => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB _ (mem_range_self x))))
      (fun x hx => hs (subset_tsupport _ (fun hx0 => hx (by simp [hx0]))))
    apply htest.trans
    apply mul_le_mul_right
    apply Finset.sum_le_sum
    intro z hz
    have hmass : (chaosCutoff M n w) (centeredCube z 1 zero_lt_one : Set (SpatialCoordinates d)) ≠ ⊤ := by
      rw [centeredCube_coe_eq_ball]
      exact measure_ball_ne_top
    rw [← ENNReal.ofReal_toReal hmass]
    exact ENNReal.ofReal_le_ofReal (hw z hz n)


theorem aux_lim_measure_local_finite_of_positive_tests
    {d : ℕ} (mu : Measure (SpatialCoordinates d))
    (h : ∀ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x) →
      (∫⁻ x, ENNReal.ofReal (f x) ∂mu) ≠ ⊤) : IsLocallyFiniteMeasure mu := by
  haveI : IsFiniteMeasureOnCompacts mu := ⟨by
    intro K hK
    obtain ⟨f, hfone, hfc, _, hf⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
      hK isOpen_univ (subset_univ _)
    let g : C_c(SpatialCoordinates d, ℝ) := ⟨f, hfc⟩
    have hb : mu K ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂mu := by
      calc mu K = ∫⁻ x, K.indicator (fun _ => (1 : ℝ≥0∞)) x ∂mu := by
            rw [lintegral_indicator hK.measurableSet]; simp
           _ ≤ _ := lintegral_mono (fun x => by
            by_cases hx : x ∈ K
            · simp [Set.indicator_of_mem hx, g, hfone hx]
            · simp [Set.indicator_of_notMem hx])
    exact lt_of_le_of_lt hb (lt_top_iff_ne_top.mpr (h g (fun x => (hf x).1)))⟩
  infer_instance

theorem aux_lim_measure_eq_of_positive_test_lintegrals
    {d : ℕ} (mu nu : Measure (SpatialCoordinates d)) [IsLocallyFiniteMeasure nu]
    (h : ∀ f : C_c(SpatialCoordinates d, ℝ), (∀ x, 0 ≤ f x) →
      (∫⁻ x, ENNReal.ofReal (f x) ∂mu) = ∫⁻ x, ENNReal.ofReal (f x) ∂nu) : mu = nu := by
  haveI : IsLocallyFiniteMeasure mu := aux_lim_measure_local_finite_of_positive_tests mu (by
    intro f hf
    rw [h f hf]
    exact (lintegral_ofReal_ne_top_iff_integrable f.continuous.measurable.aestronglyMeasurable
      (ae_of_all _ hf)).mpr f.integrable)
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro f
  have hnn : ∀ x, 0 ≤ f.toReal x := fun x => by simp
  have hh := h f.toReal hnn
  have heq := (ofReal_integral_eq_lintegral_ofReal (μ := mu) f.toReal.integrable
    (ae_of_all _ hnn)).trans (hh.trans
      (ofReal_integral_eq_lintegral_ofReal (μ := nu) f.toReal.integrable (ae_of_all _ hnn)).symm)
  have hh2 := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_ofReal (integral_nonneg (μ := mu) hnn),
    ENNReal.toReal_ofReal (integral_nonneg (μ := nu) hnn)] at hh2
  simpa only [CompactlySupportedContinuousMap.toReal_apply] using hh2


theorem aux_lim_measure_retained_bind_le_volume
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n : ℕ) (A : Set (BilateralField d)) :
    ((chaosSampleLaw M).toMeasure.restrict A).bind (chaosCutoff M n) ≤ volume := by
  apply Measure.le_iff.mpr
  intro D hD
  rw [Measure.bind_apply hD (aux_lim_measure_cutoff_measurable M n).aemeasurable]
  calc (∫⁻ w in A, chaosCutoff M n w D ∂(chaosSampleLaw M).toMeasure)
      ≤ ∫⁻ w, chaosCutoff M n w D ∂(chaosSampleLaw M).toMeasure :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = volume D := aux_lim_measure_cutoff_mean_measure M n D hD

theorem aux_lim_measure_vague_retained_bind
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (Mlim : BilateralField d → Measure (SpatialCoordinates d)) (hMlim : Measurable Mlim)
    (hloc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, IsLocallyFiniteMeasure (Mlim w))
    (hconv : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun m => chaosCutoff M m w) (Mlim w))
    (n : ℕ) (A : Set (BilateralField d))
    (hA : MeasurableSet[(conditionalFineFiltration
      (fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) measurable_const) n] A) :
    ((chaosSampleLaw M).toMeasure.restrict A).bind Mlim =
      ((chaosSampleLaw M).toMeasure.restrict A).bind (chaosCutoff M n) := by
  haveI : IsLocallyFiniteMeasure
      (((chaosSampleLaw M).toMeasure.restrict A).bind (chaosCutoff M n)) :=
    Measure.isLocallyFiniteMeasure_of_le (aux_lim_measure_retained_bind_le_volume M n A)
  apply aux_lim_measure_eq_of_positive_test_lintegrals
  intro f hf
  have hfmeas : Measurable (fun x => ENNReal.ofReal (f x)) := f.continuous.measurable.ennreal_ofReal
  rw [Measure.lintegral_bind hMlim.aemeasurable hfmeas.aemeasurable,
    Measure.lintegral_bind (aux_lim_measure_cutoff_measurable M n).aemeasurable hfmeas.aemeasurable]
  obtain ⟨b, hbmeas, hbfin, hb⟩ := aux_lim_measure_positive_test_envelope hd M hdelta f
  have hlim : Tendsto (fun m => ∫⁻ w in A, ∫⁻ x, ENNReal.ofReal (f x) ∂chaosCutoff M m w
      ∂(chaosSampleLaw M).toMeasure) atTop
      (𝓝 (∫⁻ w in A, ∫⁻ x, ENNReal.ofReal (f x) ∂Mlim w ∂(chaosSampleLaw M).toMeasure)) := by
    apply tendsto_lintegral_of_dominated_convergence b
    · intro m
      exact (Measure.measurable_lintegral hfmeas).comp (aux_lim_measure_cutoff_measurable M m)
    · intro m
      exact ae_restrict_of_ae (hb m)
    · exact ne_top_of_le_ne_top hbfin (lintegral_mono' Measure.restrict_le_self le_rfl)
    · apply ae_restrict_of_ae
      filter_upwards [hconv, hloc] with w hw hwl
      haveI := hwl
      exact aux_lim_measure_vague_positive_lintegral _ _
        (fun m => chaosCutoff_isLocallyFinite M m w) hw f hf
  apply tendsto_nhds_unique hlim
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [← Measure.lintegral_bind (aux_lim_measure_cutoff_measurable M n).aemeasurable hfmeas.aemeasurable,
    ← Measure.lintegral_bind (aux_lim_measure_cutoff_measurable M m).aemeasurable hfmeas.aemeasurable,
    aux_lim_measure_finite_bind M n m hm A hA]

theorem aux_lim_measure_same_limit_rectangle
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (Mlim : BilateralField d → Measure (SpatialCoordinates d)) (hMlim : Measurable Mlim)
    (hloc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, IsLocallyFiniteMeasure (Mlim w))
    (hconv : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun m => chaosCutoff M m w) (Mlim w))
    (n : ℕ) (A : Set (BilateralField d))
    (hA : MeasurableSet[(conditionalFineFiltration
      (fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) measurable_const) n] A)
    (D : Set (SpatialCoordinates d)) (hD : MeasurableSet D) :
    (∫⁻ w in A, Mlim w D ∂(chaosSampleLaw M).toMeasure) =
      ∫⁻ w in A, ∫⁻ x in D, ENNReal.ofReal (fineDensity M n w x) ∂volume
        ∂(chaosSampleLaw M).toMeasure := by
  have h := congrArg (fun nu : Measure (SpatialCoordinates d) => nu D)
    (aux_lim_measure_vague_retained_bind hd M hdelta Mlim hMlim hloc hconv n A hA)
  dsimp only at h
  rw [Measure.bind_apply hD hMlim.aemeasurable,
    Measure.bind_apply hD (aux_lim_measure_cutoff_measurable M n).aemeasurable] at h
  simpa only [aux_lim_measure_cutoff_apply M n _ D hD] using h


theorem aux_lim_measure_exists_unweighted_vague_limit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∃ mu : BilateralField d → Measure (SpatialCoordinates d), Measurable mu ∧
      (∀ w, IsLocallyFiniteMeasure (mu w)) ∧
      ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
        MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu w) := by
  classical
  let G0 : Set (BilateralField d) := {w |
    (∀ (j : ℕ) (k : Fin d → ℤ), ∃ L : ℝ, Tendsto (fun n =>
      ((chaosCutoff M n w) (centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ)))
        (zpow_neg_pos j) : Set (SpatialCoordinates d))).toReal) atTop (𝓝 L)) ∧
    (∀ j : ℕ, ∃ L : ℝ, Tendsto (fun n => ((chaosCutoff M n w)
      (centeredCube (0 : SpatialCoordinates d) (2 * ((j : ℝ) + 4)) (by positivity) :
        Set (SpatialCoordinates d))).toReal) atTop (𝓝 L))}
  have hsmall : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      ∀ (j : ℕ) (k : Fin d → ℤ), ∃ L : ℝ, Tendsto (fun n =>
        ((chaosCutoff M n w) (centeredCube (tileCenter j k) ((3 : ℝ) ^ (-(j : ℤ)))
          (zpow_neg_pos j) : Set (SpatialCoordinates d))).toReal) atTop (𝓝 L) := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    obtain ⟨Y, _, hY, _⟩ := chaosCutoff_centeredCube_ae_tendsto M (tileCenter j k)
      ((3 : ℝ) ^ (-(j : ℤ))) (zpow_neg_pos j)
    filter_upwards [hY] with w hw
    exact ⟨Y w, hw⟩
  have hbig := aux_lim_measure_countable_cube_limits M (fun _ => (0 : SpatialCoordinates d))
    (fun j => 2 * ((j : ℝ) + 4)) (fun _ => by positivity)
  have hG0 : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, w ∈ G0 := by
    filter_upwards [hsmall, hbig] with w hw hw'
    exact ⟨hw, hw'⟩
  let G : Set (BilateralField d) := (toMeasurable (chaosSampleLaw M).toMeasure G0ᶜ)ᶜ
  have hGmeas : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGsub : G ⊆ G0 := compl_subset_comm.mpr (subset_toMeasurable _ _)
  have hGfull : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, w ∈ G := by
    apply compl_mem_ae_iff.mpr
    rw [measure_toMeasurable]
    exact mem_ae_iff.mp hG0
  obtain ⟨mu, hm, hl, _, hc⟩ := exists_measurable_vague_limit
    (fun w n => chaosCutoff M n w) G hGmeas
    (fun w n f => by
      haveI := chaosCutoff_isLocallyFinite M n w
      exact f.integrable)
    (aux_lim_measure_unweighted_test_measurable M)
    (fun w hw f => by
      have hw0 := hGsub hw
      have hh := chaos_vague_functional M (fun _ => 0) w
        (by simpa only [chaosCutoff_eq_weightedChaosCutoff_zero] using hw0.1)
        (by simpa only [chaosCutoff_eq_weightedChaosCutoff_zero] using hw0.2) f
      simpa only [chaosCutoff_eq_weightedChaosCutoff_zero] using hh)
  exact ⟨mu, hm, hl, hGfull.mono (fun w hw => hc w hw)⟩


theorem aux_lim_measure_mean_of_unweighted_vague
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (mu : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu)
    (hl : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, IsLocallyFiniteMeasure (mu w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu w))
    (D : Set (SpatialCoordinates d)) (hD : MeasurableSet D) :
    (∫⁻ w, mu w D ∂(chaosSampleLaw M).toMeasure) = volume D := by
  have hh := aux_lim_measure_vague_retained_bind hd M hdelta mu hm hl hc 0 Set.univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at hh
  have h := congrArg (fun nu : Measure (SpatialCoordinates d) => nu D) hh
  dsimp only at h
  rw [Measure.bind_apply hD hm.aemeasurable,
    Measure.bind_apply hD (aux_lim_measure_cutoff_measurable M 0).aemeasurable] at h
  exact h.trans (aux_lim_measure_cutoff_mean_measure M 0 D hD)

theorem aux_lim_measure_unweighted_vague_martingale
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4) :
    ∃ mu : BilateralField d → Measure (SpatialCoordinates d), Measurable mu ∧
      (∀ w, IsLocallyFiniteMeasure (mu w)) ∧
      (∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
        MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu w)) ∧
      (∀ D : Set (SpatialCoordinates d), MeasurableSet D →
        (∫⁻ w, mu w D ∂(chaosSampleLaw M).toMeasure) = volume D) ∧
      ∀ (n : ℕ) (A : Set (BilateralField d)),
        MeasurableSet[(conditionalFineFiltration
          (fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) measurable_const) n] A →
        ∀ D : Set (SpatialCoordinates d), MeasurableSet D →
          (∫⁻ w in A, mu w D ∂(chaosSampleLaw M).toMeasure) =
            ∫⁻ w in A, ∫⁻ x in D, ENNReal.ofReal (fineDensity M n w x) ∂volume
              ∂(chaosSampleLaw M).toMeasure := by
  obtain ⟨mu, hm, hl, hc⟩ := aux_lim_measure_exists_unweighted_vague_limit M
  exact ⟨mu, hm, hl, hc,
    aux_lim_measure_mean_of_unweighted_vague hd M hdelta mu hm (ae_of_all _ hl) hc,
    aux_lim_measure_same_limit_rectangle hd M hdelta mu hm (ae_of_all _ hl) hc⟩


end Paper
