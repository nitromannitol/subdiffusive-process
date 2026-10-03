module

public import SubdiffusiveProcess.Section10.GaussianLeaves
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace Paper
/-- L:395–398. Pool order `astra10r2_0927_diameter_ball`, independently accepted. -/
theorem aux_lim_nongaussian_diameter_ball
    {X : Type*} [MetricSpace X] (s : Set X) (x : X) (hx : x ∈ s)
    (h0 : Metric.ediam s ≠ 0) (ht : Metric.ediam s ≠ ⊤) :
    s ⊆ Metric.ball x (2 * (Metric.ediam s).toReal) := by
  intro y hy
  rw [Metric.mem_ball]
  have hle : edist y x ≤ Metric.ediam s := Metric.edist_le_ediam_of_mem hy hx
  have hpos : 0 < (Metric.ediam s).toReal := ENNReal.toReal_pos h0 ht
  have hto : (edist y x).toReal ≤ (Metric.ediam s).toReal := ENNReal.toReal_mono ht hle
  rw [dist_edist]
  linarith


/-- L:395–398. Pool order `astra10r2_0927_diameter_zero_null`, independently accepted. -/
theorem aux_lim_nongaussian_diameter_zero_null
    {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (mu : Measure X) [NullSingletonClass mu] (s : Set X) (h : Metric.ediam s = 0) :
    mu s = 0 := by
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx⟩ := hs
    have hsub : s ⊆ {x} := by
      intro y hy
      have hle : edist y x ≤ Metric.ediam s := Metric.edist_le_ediam_of_mem hy hx
      rw [h] at hle
      rw [mem_singleton_iff]
      exact edist_eq_zero.mp (le_antisymm hle (zero_le))
    exact measure_mono_null hsub (NullSingletonClass.measure_singleton x)
  · rw [not_nonempty_iff_eq_empty] at hs
    rw [hs]
    simp


/-- L:395–398. Pool order `astra10r2_0927_hausdorff_ac_diameter_retry`, independently accepted. -/
theorem aux_lim_nongaussian_hausdorff_ac_diameter
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCt : C ≠ ⊤)
    (s : ℝ) (e : ℝ≥0∞) (he : 0 < e)
    (hbound : ∀ A : Set X, Metric.ediam A ≤ e → mu A ≤ C * Metric.ediam A ^ s) :
    mu ≪ Measure.hausdorffMeasure s := by
  have h1 : mu ≤ Measure.mkMetric (fun r => C * r ^ s) :=
    Measure.le_mkMetric (fun r => C * r ^ s) mu e he hbound
  have h2 : (Measure.mkMetric (fun r => C * r ^ s) : Measure X) ≤ C • Measure.hausdorffMeasure s := by
    rw [Measure.hausdorffMeasure]
    refine Measure.mkMetric_mono_smul (X := X) (m₁ := fun r => C * r ^ s)
      (m₂ := fun r => r ^ s) hCt hC0 ?_
    filter_upwards with r
    rfl
  exact Measure.absolutelyContinuous_of_le_smul (h1.trans h2)


/-- L:395–398. Pool order `astra10r2_0927_kernel_dimension`, independently accepted. -/
theorem aux_lim_nongaussian_kernel_dimension
    {d : ℕ} (L : StrongDual ℝ (SpatialCoordinates d)) (hL : L ≠ 0) :
    (Module.finrank ℝ (LinearMap.ker L.toLinearMap) : ℝ) < (d : ℝ) - 1 / 2 := by
  have hker : LinearMap.ker L.toLinearMap ≠ ⊤ := by
    intro h
    apply hL
    have h0 : L.toLinearMap = 0 := (LinearMap.ker_eq_top).mp h
    ext x
    have hx := congr_fun (congrArg DFunLike.coe h0) x
    simpa using hx
  have hrank : Module.finrank ℝ (SpatialCoordinates d) = d := by
    simpa [SpatialCoordinates] using Module.finrank_fin_fun ℝ (n := d)
  have hlt : Module.finrank ℝ ↥(LinearMap.ker L.toLinearMap) < d := by
    have h := Submodule.finrank_lt (K := ℝ) (V := SpatialCoordinates d) hker
    rwa [hrank] at h
  have hle : (Module.finrank ℝ ↥(LinearMap.ker L.toLinearMap) : ℝ) + 1 ≤ (d : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hlt : Module.finrank ℝ ↥(LinearMap.ker L.toLinearMap) + 1 ≤ d)
  linarith


/-- L:395–398. Pool order `astra10r2_0927_hyperplane_range`, independently accepted. -/
theorem aux_lim_nongaussian_hyperplane_range
    {d : ℕ} (L : StrongDual ℝ (SpatialCoordinates d)) (a : ℝ)
    (x : SpatialCoordinates d) (hx : L x = a) :
    Set.range (fun y : LinearMap.ker L.toLinearMap => (y : SpatialCoordinates d) + x) =
      {y | L y = a} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    show L ((z : SpatialCoordinates d) + x) = a
    rw [map_add,
      show L (z : SpatialCoordinates d) = 0 from LinearMap.mem_ker.mp z.property,
      zero_add, hx]
  · intro h
    rw [Set.mem_setOf_eq] at h
    refine ⟨⟨y - x, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, map_sub,
        show (L.toLinearMap) y = a from h,
        show (L.toLinearMap) x = a from hx, sub_self]
    · show (y - x) + x = y
      rw [sub_add_cancel]


/-- L:395–398. Pool order `astra10r2_0927_growth_power`, independently accepted. -/
theorem aux_lim_nongaussian_growth_power
    (K s : ℝ) (hK : 0 ≤ K) (hs : 0 ≤ s) (D : ℝ≥0∞) (hD : D ≠ ⊤) :
    ENNReal.ofReal (K * (2 * D.toReal) ^ s) ≤
      ENNReal.ofReal (1 + K * (2 : ℝ) ^ s) * D ^ s := by
    have hDnn : 0 ≤ D.toReal := ENNReal.toReal_nonneg
    have hs2 : (0 : ℝ) ≤ 2 := by norm_num
    have hKs : 0 ≤ K * 2 ^ s := mul_nonneg hK (Real.rpow_nonneg hs2 s)
    have hsplit : (2 * D.toReal) ^ s = 2 ^ s * D.toReal ^ s := Real.mul_rpow hs2 hDnn
    have hgoal : ENNReal.ofReal (K * (2 * D.toReal) ^ s)
        = ENNReal.ofReal (K * 2 ^ s) * D ^ s := by
      rw [hsplit, show K * (2 ^ s * D.toReal ^ s) = (K * 2 ^ s) * D.toReal ^ s by ring]
      rw [ENNReal.ofReal_mul hKs, ← ENNReal.ofReal_rpow_of_nonneg hDnn hs,
          ENNReal.ofReal_toReal hD]
    rw [hgoal]
    gcongr
    linarith [hKs]


/-- L:395–398. Pool order `astra10r2_0927_growth_nonzero_diameter`, independently accepted. -/
theorem aux_lim_nongaussian_growth_nonzero_diameter
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) (S A : Set X) (x : X) (hxA : x ∈ A) (hxS : x ∈ S)
    (K s : ℝ)
    (hg : ∀ y ∈ S, ∀ r : ℝ, 0 < r → r ≤ 1 →
      mu (Metric.ball y r) ≤ ENNReal.ofReal (K * r ^ s))
    (hD0 : Metric.ediam A ≠ 0) (hD : Metric.ediam A ≤ 1 / 2) :
    (mu.restrict S) A ≤ ENNReal.ofReal (K * (2 * (Metric.ediam A).toReal) ^ s) := by
  have hb : (1 / 2 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  have htopt : Metric.ediam A ≠ ⊤ := ne_top_of_le_ne_top hb hD
  have h12 : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat 2]
  have hd_pos : 0 < (Metric.ediam A).toReal := ENNReal.toReal_pos hD0 htopt
  have hd_le : (Metric.ediam A).toReal ≤ 1 / 2 := by
    have h := ENNReal.toReal_mono hb hD
    rwa [h12] at h
  have hr_pos : 0 < 2 * (Metric.ediam A).toReal := by linarith
  have hr_le : 2 * (Metric.ediam A).toReal ≤ 1 := by linarith
  calc (mu.restrict S) A ≤ mu A := Measure.restrict_apply_le S A
    _ ≤ mu (Metric.ball x (2 * (Metric.ediam A).toReal)) :=
        measure_mono (aux_lim_nongaussian_diameter_ball A x hxA hD0 htopt)
    _ ≤ ENNReal.ofReal (K * (2 * (Metric.ediam A).toReal) ^ s) :=
        hg x hxS (2 * (Metric.ediam A).toReal) hr_pos hr_le


/-- L:395–398. Pool order `astra10r2_0927_hyperplane_hausdorff`, independently accepted. -/
theorem aux_lim_nongaussian_hyperplane_hausdorff
    {d : ℕ} (hd : 2 ≤ d) (L : StrongDual ℝ (SpatialCoordinates d)) (hL : L ≠ 0)
    (a : ℝ) : Measure.hausdorffMeasure ((d : ℝ) - 1 / 2) {x | L x = a} = 0 := by
  by_cases hempty : {x | L x = a} = ∅
  · rw [hempty]; simp
  · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    rw [← aux_lim_nongaussian_hyperplane_range L a x hx]
    have hs : 0 ≤ (d : ℝ) - 1 / 2 := by
      have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hf : LipschitzWith 1
        (fun y : ↥(LinearMap.ker L.toLinearMap) => (y : SpatialCoordinates d) + x) := by
      simpa only [Function.comp_apply, one_mul] using! (isometry_add_right x).lipschitz.comp (LipschitzWith.subtype_val _)
    exact aux_lim_nongaussian_hausdorff_image_null ((d : ℝ) - 1 / 2) hs
      (aux_lim_nongaussian_kernel_dimension L hL) _ 1 hf


/-- L:395–398. Pool order `astra10r2_0927_restricted_growth_diameter`, independently accepted. -/
theorem aux_lim_nongaussian_restricted_growth_diameter
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [NullSingletonClass mu] (S : Set X) (hS : MeasurableSet S)
    (K s : ℝ) (hK : 0 ≤ K) (hs : 0 ≤ s)
    (hg : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ 1 →
      mu (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ s)) :
    ∀ A : Set X, Metric.ediam A ≤ 1 / 2 →
      (mu.restrict S) A ≤ ENNReal.ofReal (1 + K * (2 : ℝ) ^ s) * Metric.ediam A ^ s := by
  intro A hD
  by_cases hd0 : Metric.ediam A = 0
  · rw [aux_lim_nongaussian_diameter_zero_null (mu.restrict S) A hd0]
    exact zero_le
  · by_cases hAS : A ∩ S = ∅
    · rw [Measure.restrict_apply' hS, hAS]
      simp
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hAS
      rw [Set.mem_inter_iff] at hx
      obtain ⟨hxA, hxS⟩ := hx
      have hDt : Metric.ediam A ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hD
      calc (mu.restrict S) A
          ≤ ENNReal.ofReal (K * (2 * (Metric.ediam A).toReal) ^ s) :=
            aux_lim_nongaussian_growth_nonzero_diameter mu S A x hxA hxS K s hg hd0 hD
        _ ≤ ENNReal.ofReal (1 + K * (2 : ℝ) ^ s) * Metric.ediam A ^ s :=
            aux_lim_nongaussian_growth_power K s hK hs (Metric.ediam A) hDt


/-- L:395–398: the local growth bank dominates Hausdorff measure on each carrier. -/
theorem aux_lim_nongaussian_local_growth_hyperplane_null
    {d : ℕ} (hd : 2 ≤ d) (mu : Measure (SpatialCoordinates d)) [NullSingletonClass mu]
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S)
    (K : ℝ) (hK : 0 ≤ K)
    (hg : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ 1 →
      mu (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2)))
    (L : StrongDual ℝ (SpatialCoordinates d)) (hL : L ≠ 0) (a : ℝ) :
    (mu.restrict S) {x | L x = a} = 0 := by
  have hs : 0 ≤ (d : ℝ) - 1 / 2 := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hc : 0 < 1 + K * (2 : ℝ) ^ ((d : ℝ) - 1 / 2) := by positivity
  have hac : mu.restrict S ≪ Measure.hausdorffMeasure ((d : ℝ) - 1 / 2) :=
    aux_lim_nongaussian_hausdorff_ac_diameter (mu.restrict S)
      (ENNReal.ofReal (1 + K * (2 : ℝ) ^ ((d : ℝ) - 1 / 2)))
      (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top
      ((d : ℝ) - 1 / 2) (1 / 2) (by norm_num)
      (aux_lim_nongaussian_restricted_growth_diameter mu S hS K _ hK hs hg)
  exact hac (aux_lim_nongaussian_hyperplane_hausdorff hd L hL a)

/-- L:395–398: countably many local growth bounds give one event for ALL hyperplanes. -/
theorem aux_lim_nongaussian_hyperplanes_of_local_growth
    {d : ℕ} (hd : 2 ≤ d) (mu : Measure (SpatialCoordinates d)) [NullSingletonClass mu]
    (hg : ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1),
        ∀ r : ℝ, 0 < r → r ≤ 1 →
          mu (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2))) :
    ∀ L : StrongDual ℝ (SpatialCoordinates d), L ≠ 0 →
      ∀ a : ℝ, mu {x | L x = a} = 0 := by
  intro L hL a
  have hn (n : ℕ) : mu ({x | L x = a} ∩
      Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1)) = 0 := by
    obtain ⟨K, hK, hbound⟩ := hg n
    have h := aux_lim_nongaussian_local_growth_hyperplane_null hd mu
      (Metric.ball 0 ((n : ℝ) + 1)) Metric.isOpen_ball.measurableSet
      K hK hbound L hL a
    rwa [Measure.restrict_apply (isClosed_eq L.continuous continuous_const).measurableSet] at h
  apply measure_mono_null (t := ⋃ n : ℕ,
    {x | L x = a} ∩ Metric.ball (0 : SpatialCoordinates d) ((n : ℝ) + 1))
  · intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (dist x (0 : SpatialCoordinates d))
    exact Set.mem_iUnion.mpr ⟨n, hx, (show dist x 0 < (n : ℝ) + 1 by linarith)⟩
  · exact measure_iUnion_null hn

end Paper
