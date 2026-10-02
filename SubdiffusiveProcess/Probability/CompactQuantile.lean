import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.Real.Cardinality

/-! Quantile realization for probability laws supported on the unit interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace SubdiffusiveProcess.Probability

/-- The common source measure for quantile realizations. -/
def quantileSource : Measure ℝ := volume.restrict (Ioc 0 1)

instance : IsProbabilityMeasure quantileSource := by
  constructor
  simp only [quantileSource, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
    ENNReal.ofReal_one]

instance : NoAtoms quantileSource :=
  inferInstanceAs (NoAtoms (volume.restrict (Ioc (0 : ℝ) 1)))

/-- Generalized inverse of the cdf on the compact interval. -/
def compactQuantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  sInf {x | x ∈ Icc (0 : ℝ) 1 ∧ min 1 (max 0 u) ≤ cdf μ x}

theorem cdf_one_of_unit_support {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Icc (0 : ℝ) 1) = 1) : cdf μ 1 = 1 := by
  apply ENNReal.ofReal_eq_one.mp
  rw [ofReal_cdf]
  exact le_antisymm prob_le_one
    (by rw [← hμ]; exact measure_mono (fun _ hx => hx.2))

theorem compactQuantile_mem {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Icc (0 : ℝ) 1) = 1) (u : ℝ) : compactQuantile μ u ∈ Icc (0 : ℝ) 1 := by
  have hn : {x : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ min 1 (max 0 u) ≤ cdf μ x}.Nonempty :=
    ⟨1, ⟨⟨zero_le_one, le_rfl⟩, by rw [cdf_one_of_unit_support hμ]; exact min_le_left _ _⟩⟩
  have hb : BddBelow {x : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ min 1 (max 0 u) ≤ cdf μ x} :=
    ⟨0, fun _ hx => hx.1.1⟩
  exact ⟨le_csInf hn (fun _ hx => hx.1.1), csInf_le hb ⟨⟨zero_le_one, le_rfl⟩, by rw [cdf_one_of_unit_support hμ]; exact min_le_left _ _⟩⟩

theorem cdf_compactQuantile {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Icc (0 : ℝ) 1) = 1) (u : ℝ) :
    min 1 (max 0 u) ≤ cdf μ (compactQuantile μ u) := by
  let A : Set ℝ := {x | x ∈ Icc (0 : ℝ) 1 ∧ min 1 (max 0 u) ≤ cdf μ x}
  have hn : A.Nonempty := ⟨1, ⟨⟨zero_le_one, le_rfl⟩,
    by rw [cdf_one_of_unit_support hμ]; exact min_le_left _ _⟩⟩
  have hr : Tendsto (cdf μ) (𝓝[>] (compactQuantile μ u))
      (𝓝 (cdf μ (compactQuantile μ u))) :=
    (continuousWithinAt_Ioi_iff_Ici.mpr ((cdf μ).right_continuous _))
  apply ge_of_tendsto hr
  filter_upwards [self_mem_nhdsWithin] with b hb
  obtain ⟨a, ha, hab⟩ := exists_lt_of_csInf_lt hn hb
  exact ha.2.trans ((cdf μ).mono hab.le)

theorem compactQuantile_le_iff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Icc (0 : ℝ) 1) = 1) {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    compactQuantile μ u ≤ x ↔ u ≤ cdf μ x := by
  have hc : min 1 (max 0 u) = u := by rw [max_eq_right hu.1.le, min_eq_right hu.2]
  constructor
  · intro hq
    rw [← hc]
    exact (cdf_compactQuantile hμ u).trans ((cdf μ).mono hq)
  · intro hux
    by_cases hx : 0 ≤ x
    · by_cases hx1 : x ≤ 1
      · exact csInf_le ⟨0, fun _ hy => hy.1.1⟩ ⟨⟨hx, hx1⟩, by rwa [hc]⟩
      · exact (compactQuantile_mem hμ u).2.trans (le_of_not_ge hx1)
    · have hm : μ (Iic x) = 0 := by
        apply measure_mono_null (t := (Icc (0 : ℝ) 1)ᶜ) _
          ((prob_compl_eq_zero_iff measurableSet_Icc).mpr hμ)
        intro y hy hyI
        exact hx (hyI.1.trans hy)
      have hF : cdf μ x = 0 := by
        have := ofReal_cdf μ x
        rw [hm, ENNReal.ofReal_eq_zero] at this
        exact le_antisymm this (cdf_nonneg μ x)
      exact False.elim ((not_le_of_gt hu.1) (hF ▸ hux))

theorem monotone_compactQuantile {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Icc (0 : ℝ) 1) = 1) : Monotone (compactQuantile μ) := by
  intro u v huv
  change sInf {x : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ min 1 (max 0 u) ≤ cdf μ x} ≤
    sInf {x : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ min 1 (max 0 v) ≤ cdf μ x}
  apply csInf_le_csInf
  · exact ⟨0, fun _ hx => hx.1.1⟩
  · exact ⟨1, ⟨⟨zero_le_one, le_rfl⟩,
      by rw [cdf_one_of_unit_support hμ]; exact min_le_left _ _⟩⟩
  · intro x hx
    exact ⟨hx.1, (min_le_min_left 1 (max_le_max_left 0 huv)).trans hx.2⟩

theorem measurable_compactQuantile {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Icc (0 : ℝ) 1) = 1) : Measurable (compactQuantile μ) := by
  exact (monotone_compactQuantile hμ).measurable

theorem map_compactQuantile {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Icc (0 : ℝ) 1) = 1) : quantileSource.map (compactQuantile μ) = μ := by
  have hq := measurable_compactQuantile hμ
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hq measurableSet_Iic, quantileSource,
    Measure.restrict_apply (hq measurableSet_Iic)]
  have he : compactQuantile μ ⁻¹' Iic x ∩ Ioc (0 : ℝ) 1 = Ioc 0 (cdf μ x) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨hqx, hu0, hu1⟩
      exact ⟨hu0, (compactQuantile_le_iff hμ ⟨hu0, hu1⟩ x).mp hqx⟩
    · rintro ⟨hu0, huF⟩
      have hu1 := huF.trans (cdf_le_one μ x)
      exact ⟨(compactQuantile_le_iff hμ ⟨hu0, hu1⟩ x).mpr huF, hu0, hu1⟩
  rw [he, Real.volume_Ioc, sub_zero, ofReal_cdf]

theorem exists_nonatom_between (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {a b : ℝ} (hab : a < b) : ∃ c ∈ Ioo a b, ν {c} = 0 := by
  have hatoms : {c : ℝ | 0 < ν {c}}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun c => measurableSet_singleton c)
      (fun _ _ h => disjoint_singleton.mpr h)
  by_contra hn
  push_neg at hn
  have hi : (Ioo a b).Countable := hatoms.mono (fun c hc => pos_iff_ne_zero.mpr (hn c hc))
  exact (not_le_of_gt hab) (Cardinal.Real.Ioo_countable_iff.mp hi)

theorem tendsto_cdf_of_weak_convergence {μ : ℕ → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} (h : Tendsto μ atTop (𝓝 ν))
    {c : ℝ} (hc : (ν : Measure ℝ) {c} = 0) :
    Tendsto (fun n => cdf (μ n : Measure ℝ) c) atTop (𝓝 (cdf (ν : Measure ℝ) c)) := by
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (E := Iic c) h
    (by simpa only [frontier_Iic] using hc)
  simpa only [cdf_eq_real, measureReal_def] using
    (ENNReal.continuousAt_toReal (measure_ne_top (ν : Measure ℝ) (Iic c))).tendsto.comp hm

theorem tendsto_compactQuantile {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hμ : ∀ n, (μ n : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hν : (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (h : Tendsto μ atTop (𝓝 ν)) :
    ∀ᵐ u ∂quantileSource,
      Tendsto (fun n => compactQuantile (μ n : Measure ℝ) u) atTop
        (𝓝 (compactQuantile (ν : Measure ℝ) u)) := by
  have hcont := (monotone_compactQuantile hν).countable_not_continuousAt.ae_notMem quantileSource
  have hi : ∀ᵐ u ∂quantileSource, u ∈ Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  filter_upwards [hi, quantileSource.ae_ne 1, hcont] with u hu hne hc
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, lt_of_le_of_ne hu.2 hne⟩
  have hqc : ContinuousAt (compactQuantile (ν : Measure ℝ)) u := not_not.mp hc
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨c, hac, hcν⟩ := exists_nonatom_between (ν : Measure ℝ) ha
    have hcu : cdf (ν : Measure ℝ) c < u := by
      apply lt_of_not_ge
      intro huc
      exact (not_le_of_gt hac.2) ((compactQuantile_le_iff hν hu c).mpr huc)
    filter_upwards [(tendsto_cdf_of_weak_convergence h hcν).eventually_lt_const hcu] with n hn
    have hcq : c < compactQuantile (μ n : Measure ℝ) u := by
      apply lt_of_not_ge
      intro hqn
      exact (not_le_of_gt hn) ((compactQuantile_le_iff (hμ n) hu c).mp hqn)
    exact hac.1.trans hcq
  · intro b hb
    obtain ⟨c, hcb, hcν⟩ := exists_nonatom_between (ν : Measure ℝ) hb
    have hv : {v | compactQuantile (ν : Measure ℝ) v < c} ∩ Ioo (0 : ℝ) 1 ∈ 𝓝 u :=
      inter_mem (hqc.preimage_mem_nhds (Iio_mem_nhds hcb.1)) (isOpen_Ioo.mem_nhds hu')
    have hv' : ∀ᶠ v in 𝓝[>] u,
        v ∈ ({v | compactQuantile (ν : Measure ℝ) v < c} ∩ Ioo (0 : ℝ) 1) ∧ u < v :=
      ((show ∀ᶠ v in 𝓝 u, v ∈ ({v | compactQuantile (ν : Measure ℝ) v < c} ∩
        Ioo (0 : ℝ) 1) from hv).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨v, ⟨hvq, hv0, hv1⟩, huv⟩ := hv'.exists
    have huc : u < cdf (ν : Measure ℝ) c :=
      huv.trans_le ((compactQuantile_le_iff hν ⟨hv0, hv1.le⟩ c).mp hvq.le)
    filter_upwards [(tendsto_cdf_of_weak_convergence h hcν).eventually (Ioi_mem_nhds huc)] with n hn
    exact ((compactQuantile_le_iff (hμ n) hu c).mpr hn.le).trans_lt hcb.2

end SubdiffusiveProcess.Probability
