import SubdiffusiveProcess.Section10.ChaosVagueMartingale
import SubdiffusiveProcess.Section10.FiniteWindowKernel
import SubdiffusiveProcess.Section10.ChaosStrongLaw
open MeasureTheory ProbabilityTheory Filter Topology Set SubdiffusiveProcess
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace Paper

theorem aux_lim_measure_same_limit_random_window
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (mu : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu)
    (hl : ∀ w, IsLocallyFiniteMeasure (mu w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu w))
    (U : Set (SpatialCoordinates d)) (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    (n : ℕ) (B : Set (BilateralField d × SpatialCoordinates d))
    (hB : MeasurableSet[(((conditionalFineFiltration (fun _ : BilateralField d =>
      (0 : C(SpatialCoordinates d, ℝ))) measurable_const) n).prod inferInstance)] B) :
    (∫⁻ w, mu w {x | x ∈ U ∧ (w,x) ∈ B} ∂(chaosSampleLaw M).toMeasure) =
      ∫⁻ w, ∫⁻ x in {x | x ∈ U ∧ (w,x) ∈ B}, ENNReal.ofReal (fineDensity M n w x)
        ∂volume ∂(chaosSampleLaw M).toMeasure := by
  let k := aux_lim_measure_window_kernel mu hm U hU
  let l := aux_lim_measure_window_kernel (chaosCutoff M n) (aux_lim_measure_cutoff_measurable M n) U hU
  haveI : IsSFiniteKernel k := aux_lim_measure_window_kernel_sfinite mu hm U hU (fun w => by
    haveI := hl w
    exact hUb.measure_lt_top.ne)
  haveI : IsSFiniteKernel l := aux_lim_measure_window_kernel_sfinite _ _ U hU (fun w => by
    haveI := chaosCutoff_isLocallyFinite M n w
    exact hUb.measure_lt_top.ne)
  haveI : IsFiniteMeasure ((chaosSampleLaw M).toMeasure ⊗ₘ k) := ⟨by
    rw [← Set.univ_prod_univ, Measure.compProd_apply_prod MeasurableSet.univ MeasurableSet.univ,
      setLIntegral_univ]
    change (∫⁻ w, (mu w).restrict U Set.univ ∂(chaosSampleLaw M).toMeasure) < ⊤
    simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [aux_lim_measure_mean_of_unweighted_vague hd M hdelta mu hm (ae_of_all _ hl) hc U hU]
    exact hUb.measure_lt_top⟩
  let F := conditionalFineFiltration (fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) measurable_const
  have hprod : (F n).prod (inferInstance : MeasurableSpace (SpatialCoordinates d)) ≤
      (inferInstance : MeasurableSpace (BilateralField d × SpatialCoordinates d)) :=
    sup_le_sup (MeasurableSpace.comap_mono (F.le n)) le_rfl
  have hrect : ∀ (A : Set (BilateralField d)) (D : Set (SpatialCoordinates d)),
      MeasurableSet[F n] A → MeasurableSet D →
      (∫⁻ w in A, k w D ∂(chaosSampleLaw M).toMeasure) =
        ∫⁻ w in A, l w D ∂(chaosSampleLaw M).toMeasure := by
    intro A D hA hD
    change (∫⁻ w in A, (mu w).restrict U D ∂(chaosSampleLaw M).toMeasure) =
      ∫⁻ w in A, (chaosCutoff M n w).restrict U D ∂(chaosSampleLaw M).toMeasure
    simp only [Measure.restrict_apply hD]
    have hh := aux_lim_measure_same_limit_rectangle hd M hdelta mu hm (ae_of_all _ hl) hc n A hA
      (D ∩ U) (hD.inter hU)
    simpa only [aux_lim_measure_cutoff_apply M n _ _ (hD.inter hU)] using hh
  have hh := aux_lim_measure_random_test_of_rectangles hprod (F.le n)
    (chaosSampleLaw M).toMeasure k l hrect B hB
  have hB0 : MeasurableSet B := hprod B hB
  have hsec (w : BilateralField d) : MeasurableSet {x : SpatialCoordinates d | (w,x) ∈ B} :=
    measurable_prodMk_left hB0
  change (∫⁻ w, (mu w).restrict U {x | (w,x) ∈ B} ∂(chaosSampleLaw M).toMeasure) =
    (∫⁻ w, (chaosCutoff M n w).restrict U {x | (w,x) ∈ B} ∂(chaosSampleLaw M).toMeasure) at hh
  simp only [Measure.restrict_apply (hsec _), aux_lim_measure_cutoff_apply M n _ _ ((hsec _).inter hU)] at hh
  simpa only [Set.inter_comm, Set.inter_setOf_eq_sep, Set.sep_setOf, and_comm] using hh



theorem aux_lim_measure_retained_density_joint
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) :
    @Measurable (BilateralField d × SpatialCoordinates d) ℝ
      (((conditionalFineFiltration (fun _ : BilateralField d =>
        (0 : C(SpatialCoordinates d, ℝ))) measurable_const) n).prod inferInstance)
      inferInstance (fun q => fineDensity M n q.1 q.2) := by
  let F : Filtration ℕ (inferInstance : MeasurableSpace (BilateralField d)) :=
    conditionalFineFiltration (fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) measurable_const
  have hcont : ∀ x : BilateralField d,
      Continuous (fun i : SpatialCoordinates d => fineDensity M n x i) :=
    fun x => continuous_fineDensity M n x
  have hmeas : ∀ i : SpatialCoordinates d, Measurable[(F n)] (fun omega => fineDensity M n omega i) := by
    intro i
    exact ((conditionalFineFiltration_zero_eq_restrict_and_fineDensity_martingale M i).2.adapted n).measurable
  have hU := measurable_uncurry_of_continuous_of_measurable (m := F n)
      (u := fun (i : SpatialCoordinates d) (omega : BilateralField d) => fineDensity M n omega i) hcont hmeas
  have hswap : @Measurable (BilateralField d × SpatialCoordinates d) (SpatialCoordinates d × BilateralField d)
      ((F n).prod (inferInstance : MeasurableSpace (SpatialCoordinates d)))
      ((inferInstance : MeasurableSpace (SpatialCoordinates d)).prod (F n)) Prod.swap :=
    measurable_swap (α := BilateralField d) (β := SpatialCoordinates d) (m := F n) (mβ := inferInstance)
  exact hU.comp hswap


theorem aux_lim_measure_same_limit_sublevel_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (mu : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu)
    (hl : ∀ w, IsLocallyFiniteMeasure (mu w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu w))
    (U : Set (SpatialCoordinates d)) (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    (n : ℕ) (e : ℝ) :
    (∫⁻ w, mu w {x | x ∈ U ∧ fineDensity M n w x ≤ e} ∂(chaosSampleLaw M).toMeasure) ≤
      ENNReal.ofReal e * volume U := by
  have hB := measurableSet_le (g := fun _ => e) (aux_lim_measure_retained_density_joint M n) measurable_const
  have heq := aux_lim_measure_same_limit_random_window hd M hdelta mu hm hl hc U hU hUb n
    {q | fineDensity M n q.1 q.2 ≤ e} hB
  dsimp only [Set.mem_setOf_eq] at heq
  rw [heq]
  calc (∫⁻ w, ∫⁻ x in {x | x ∈ U ∧ fineDensity M n w x ≤ e},
      ENNReal.ofReal (fineDensity M n w x) ∂volume ∂(chaosSampleLaw M).toMeasure)
      ≤ ∫⁻ _w, ENNReal.ofReal e * volume U ∂(chaosSampleLaw M).toMeasure := by
        apply lintegral_mono
        intro w
        have hs : MeasurableSet {x | x ∈ U ∧ fineDensity M n w x ≤ e} :=
          hU.inter (measurableSet_le (continuous_fineDensity M n w).measurable measurable_const)
        calc (∫⁻ x in {x | x ∈ U ∧ fineDensity M n w x ≤ e},
              ENNReal.ofReal (fineDensity M n w x) ∂volume)
            ≤ ∫⁻ _x in {x | x ∈ U ∧ fineDensity M n w x ≤ e}, ENNReal.ofReal e ∂volume := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hs] with x hx
              exact ENNReal.ofReal_le_ofReal hx.2
          _ = ENNReal.ofReal e * volume {x | x ∈ U ∧ fineDensity M n w x ≤ e} := by simp
          _ ≤ _ := mul_le_mul_right (measure_mono (fun x hx => hx.1)) _
    _ = _ := by simp


theorem aux_lim_measure_same_limit_zero_carrier_window
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (mu : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu)
    (hl : ∀ w, IsLocallyFiniteMeasure (mu w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu w))
    (U : Set (SpatialCoordinates d)) (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) :
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      mu w {x | x ∈ U ∧ Tendsto (fun n => fineDensity M n w x) atTop (𝓝 0)} = 0 := by
  let S : BilateralField d → Set (SpatialCoordinates d) := fun w =>
    {x | x ∈ U ∧ Tendsto (fun n => fineDensity M n w x) atTop (𝓝 0)}
  let B : ℕ → ℕ → BilateralField d → Set (SpatialCoordinates d) := fun j n w =>
    {x | x ∈ U ∧ fineDensity M n w x ≤ 1 / ((j : ℝ) + 1)}
  have hfin (w : BilateralField d) : mu w U ≠ ⊤ := by
    haveI := hl w
    exact hUb.measure_lt_top.ne
  have hS : ∀ w, MeasurableSet (S w) := fun w =>
    hU.inter (measurable_prodMk_left (aux_lim_measure_measurable_zero_carrier M))
  have hSM : Measurable (fun w => mu w (S w)) :=
    aux_lim_measure_measurable_finite_window mu hm U hU hfin _ (aux_lim_measure_measurable_zero_carrier M)
  have hBj (j n : ℕ) : MeasurableSet {q : BilateralField d × SpatialCoordinates d |
      fineDensity M n q.1 q.2 ≤ 1 / ((j : ℝ) + 1)} :=
    measurableSet_le (stronglyMeasurable_fineDensity_uncurry M n).measurable measurable_const
  have hB : ∀ j n w, MeasurableSet (B j n w) :=
    fun j n w => hU.inter (measurable_prodMk_left (hBj j n))
  have hBM : ∀ j n, Measurable (fun w => mu w (B j n w)) := fun j n =>
    aux_lim_measure_measurable_finite_window mu hm U hU hfin _ (hBj j n)
  apply aux_lim_measure_random_carrier_fatou (chaosSampleLaw M).toMeasure mu S hS hSM B hB hBM
    (fun j w x hx => aux_lim_measure_zero_carrier_eventually M w U
      (1 / ((j : ℝ) + 1)) (by positivity) x hx.1 hx.2)
    (fun j => ENNReal.ofReal (1 / ((j : ℝ) + 1)) * volume U)
  · have ht : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const ht (Or.inr (show volume U ≠ ⊤ from hUb.measure_lt_top.ne))
  · intro j n
    exact aux_lim_measure_same_limit_sublevel_bound hd M hdelta mu hm hl hc U hU hUb n _


theorem aux_lim_measure_same_limit_singular
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (mu : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu)
    (hl : ∀ w, IsLocallyFiniteMeasure (mu w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu w)) :
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, mu w ⟂ₘ volume := by
  have hwin : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ j : ℕ,
      mu w {x | x ∈ Metric.ball (0 : SpatialCoordinates d) ((j : ℝ) + 1) ∧
        Tendsto (fun n => fineDensity M n w x) atTop (𝓝 0)} = 0 := by
    apply ae_all_iff.mpr
    intro j
    exact aux_lim_measure_same_limit_zero_carrier_window hd M hdelta mu hm hl hc
      _ Metric.isOpen_ball.measurableSet Metric.isBounded_ball
  filter_upwards [hwin, aux_lim_measure_fineDensity_zero_ae M] with w hw hv
  let S : Set (SpatialCoordinates d) := {x | Tendsto (fun n => fineDensity M n w x) atTop (𝓝 0)}
  refine ⟨S, measurable_prodMk_left (aux_lim_measure_measurable_zero_carrier M), ?_, ?_⟩
  · apply measure_mono_null (t := ⋃ j : ℕ, {x | x ∈ Metric.ball (0 : SpatialCoordinates d) ((j : ℝ) + 1) ∧ x ∈ S})
    · intro x hx
      obtain ⟨j, hj⟩ := exists_nat_gt (dist x (0 : SpatialCoordinates d))
      exact Set.mem_iUnion.mpr ⟨j, (lt_trans hj (by linarith) : dist x 0 < (j : ℝ) + 1), hx⟩
    · exact measure_iUnion_null (fun j => hw j)
  · exact ae_iff.mp hv

theorem aux_lim_measure_same_limit_nondeterministic
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4)
    (mu : BilateralField d → Measure (SpatialCoordinates d)) (hm : Measurable mu)
    (hl : ∀ w, IsLocallyFiniteMeasure (mu w))
    (hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu w)) :
    ¬ ∃ m : Measure (SpatialCoordinates d), ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, mu w = m := by
  exact aux_lim_measure_nondeterministic (chaosSampleLaw M).toMeasure mu volume
    (by exact NeZero.ne _)
    (aux_lim_measure_mean_of_unweighted_vague hd M hdelta mu hm (ae_of_all _ hl) hc)
    (aux_lim_measure_same_limit_singular hd M hdelta mu hm hl hc)


theorem aux_lim_measure_weighted_cutoff_eq
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (n : ℕ) (w : BilateralField d) :
    weightedChaosCutoff M H n w =
      (chaosCutoff M n w).withDensity (fun x => ENNReal.ofReal (Real.exp (H w x))) := by
  have hρ : Measurable (ENNReal.ofReal ∘ fineDensity M n w) :=
    ENNReal.continuous_ofReal.measurable.comp (continuous_fineDensity M n w).measurable
  have hH : Measurable (fun x => ENNReal.ofReal (Real.exp (H w x))) :=
    (Real.continuous_exp.comp (H w).continuous).measurable.ennreal_ofReal
  rw [chaosCutoff, ← withDensity_mul volume hρ hH, weightedChaosCutoff]
  congr 1
  funext x
  simp only [Pi.mul_apply, Function.comp_apply, ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact mul_comm _ _

theorem aux_lim_measure_weighted_vague_and_singular
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (w : BilateralField d)
    (mu : Measure (SpatialCoordinates d)) [IsLocallyFiniteMeasure mu]
    (hc : MeasuresConvergeLocally (fun n => chaosCutoff M n w) mu) (hs : mu ⟂ₘ volume) :
    MeasuresConvergeLocally (fun n => weightedChaosCutoff M H n w)
        (mu.withDensity (fun x => ENNReal.ofReal (Real.exp (H w x)))) ∧
      IsLocallyFiniteMeasure (mu.withDensity (fun x => ENNReal.ofReal (Real.exp (H w x)))) ∧
      mu.withDensity (fun x => ENNReal.ofReal (Real.exp (H w x))) ⟂ₘ volume := by
  let g : C(SpatialCoordinates d, ℝ) := ⟨fun x => Real.exp (H w x), (Real.continuous_exp.comp (H w).continuous)⟩
  refine ⟨?_, IsLocallyFiniteMeasure.withDensity_ofReal (Real.continuous_exp.comp (H w).continuous), hs.withDensity⟩
  simpa only [aux_lim_measure_weighted_cutoff_eq] using
    aux_lim_measure_vague_weight _ mu hc g (fun x => (Real.exp_pos _).le)

theorem aux_lim_measure_exists_singular_vague_limit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 0 < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hdelta : M.delta ≤ 1 / 4) :
    ∃ mu : BilateralField d → Measure (SpatialCoordinates d), Measurable mu ∧
      (∀ w, IsLocallyFiniteMeasure (mu w)) ∧
      (∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
        MeasuresConvergeLocally (fun n => chaosCutoff M n w) (mu w) ∧ mu w ⟂ₘ volume) ∧
      (∀ D : Set (SpatialCoordinates d), MeasurableSet D →
        (∫⁻ w, mu w D ∂(chaosSampleLaw M).toMeasure) = volume D) ∧
      (¬ ∃ m : Measure (SpatialCoordinates d), ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, mu w = m) := by
  obtain ⟨mu, hm, hl, hc⟩ := aux_lim_measure_exists_unweighted_vague_limit M
  exact ⟨mu, hm, hl, hc.and (aux_lim_measure_same_limit_singular hd M hdelta mu hm hl hc),
    aux_lim_measure_mean_of_unweighted_vague hd M hdelta mu hm (ae_of_all _ hl) hc,
    aux_lim_measure_same_limit_nondeterministic hd M hdelta mu hm hl hc⟩


end Paper
