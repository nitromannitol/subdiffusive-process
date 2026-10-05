module

public import SubdiffusiveProcess.Main.DiffusionPath
public import MarkovProcess.Path.ExitTimeShift
public import MarkovProcess.Kernel.OnePointExtension
public import MarkovProcess.Path.Polish
public import MarkovProcess.Continuity.DenseTimeContinuousExtension
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Metrizable.Urysohn

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.KilledFeller
/-- The path `w` killed on leaving `U`, read in the one-point compactification `U ∪ {∞}`:
`w t` while `t` is strictly before the exit time from `U`, the point `∞` from the exit time on. -/
def killFun {d : ℕ} (U : Set (SpatialCoordinates d)) (w : DiffusionPath d)
    (t : ℝ≥0) : OnePoint ↥U :=
  if ht : (t : ℝ≥0∞) < ContinuousPath.exitTime U w then
    ((⟨w t, ContinuousPath.mem_of_lt_exitTime U w t ht⟩ : ↥U) : OnePoint ↥U)
  else OnePoint.infty

theorem killFun_continuous {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) (w : DiffusionPath d) :
    Continuous (killFun U w) := by
  classical
  set τ := ContinuousPath.exitTime U w with hτ
  rw [continuous_iff_continuousAt]
  intro t0
  have hopen1 : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < τ} :=
    isOpen_Iio.preimage ENNReal.continuous_coe
  have hopen2 : IsOpen {t : ℝ≥0 | τ < (t : ℝ≥0∞)} :=
    isOpen_Ioi.preimage ENNReal.continuous_coe
  rcases lt_trichotomy (t0 : ℝ≥0∞) τ with h | h | h
  · -- alive at `t0`
    have hcont : ContinuousOn (killFun U w)
        {t : ℝ≥0 | (t : ℝ≥0∞) < τ} := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hs : Continuous (fun t : {t : ℝ≥0 | (t : ℝ≥0∞) < τ} =>
          (⟨w t.1, ContinuousPath.mem_of_lt_exitTime U w t.1 t.2⟩ : ↥U)) :=
        Continuous.subtype_mk (w.continuous.comp continuous_subtype_val) _
      have : ({t : ℝ≥0 | (t : ℝ≥0∞) < τ}.domRestrict (killFun U w)) =
          fun t => ((⟨w t.1, ContinuousPath.mem_of_lt_exitTime U w t.1 t.2⟩ : ↥U) :
            OnePoint ↥U) := by
        funext t
        change (if ht : (t.1 : ℝ≥0∞) < ContinuousPath.exitTime U w then
          ((⟨w t.1, ContinuousPath.mem_of_lt_exitTime U w t.1 ht⟩ : ↥U) : OnePoint ↥U)
          else OnePoint.infty) = _
        exact dite_eq_left (t.2 : (t.1 : ℝ≥0∞) < ContinuousPath.exitTime U w)
      rw [this]
      exact OnePoint.continuous_coe.comp hs
    exact hcont.continuousAt (hopen1.mem_nhds h)
  · -- at the exit time
    have hfin : τ ≠ ⊤ := by rw [← h]; exact ENNReal.coe_ne_top
    have hτeq : (τ.toNNReal : ℝ≥0∞) = τ := ENNReal.coe_toNNReal hfin
    have ht0 : t0 = τ.toNNReal := by
      apply ENNReal.coe_injective; rw [hτeq]; exact h
    have hbefore : ∀ s : ℝ≥0, s < τ.toNNReal → w s ∈ U := by
      intro s hs
      apply ContinuousPath.mem_of_lt_exitTime
      show (s : ℝ≥0∞) < τ
      rw [← hτeq, ENNReal.coe_lt_coe]
      exact hs
    have hnot : w t0 ∉ U := by
      have hle : τ ≤ (t0 : ℝ≥0∞) := le_of_eq h.symm
      obtain ⟨s, hs⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy U hU t0 w).mp hle
      have hge : t0 ≤ (s : ℝ≥0) := by
        by_contra hlt
        exact hs (hbefore s (by rw [← ht0]; exact lt_of_not_ge hlt))
      have hseq : (s : ℝ≥0) = t0 := le_antisymm s.property hge
      rw [← hseq]
      exact hs
    have hval : killFun U w t0 = OnePoint.infty := by
      simp only [killFun]
      rw [dite_eq_right (by rw [h]; exact lt_irrefl _)]
    show Tendsto (killFun U w) (𝓝 t0)
      (𝓝 (killFun U w t0))
    rw [hval, (OnePoint.hasBasis_nhds_infty).tendsto_right_iff]
    intro K hK
    obtain ⟨hKc, hKcomp⟩ := hK
    have hKw : IsCompact (Subtype.val '' K : Set (SpatialCoordinates d)) :=
      hKcomp.image continuous_subtype_val
    have hwK : w t0 ∉ (Subtype.val '' K : Set (SpatialCoordinates d)) := by
      rintro ⟨x, -, hx⟩
      exact hnot (hx ▸ x.2)
    have hev : ∀ᶠ t in 𝓝 t0, w t ∉ (Subtype.val '' K : Set (SpatialCoordinates d)) :=
      w.continuous.continuousAt.eventually (hKw.isClosed.isOpen_compl.mem_nhds hwK)
    filter_upwards [hev] with t ht
    by_cases hlt : (t : ℝ≥0∞) < τ
    · left
      refine ⟨⟨w t, ContinuousPath.mem_of_lt_exitTime U w t hlt⟩, ?_, ?_⟩
      · intro hx
        exact ht ⟨_, hx, rfl⟩
      · simp only [killFun]
        rw [dite_eq_left hlt]
    · right
      simp only [killFun]
      rw [dite_eq_right hlt]
      rfl
  · -- dead at `t0`
    have hcont : ContinuousOn (killFun U w)
        {t : ℝ≥0 | τ < (t : ℝ≥0∞)} := by
      have : Set.EqOn (killFun U w)
          (fun _ => (OnePoint.infty : OnePoint ↥U)) {t : ℝ≥0 | τ < (t : ℝ≥0∞)} := by
        intro t ht
        simp only [killFun]
        rw [dite_eq_right (not_lt.mpr (le_of_lt ht))]
      exact continuousOn_const.congr this
    exact hcont.continuousAt (hopen2.mem_nhds h)


/-- Killing a continuous path at the first exit, with the boundary collapsed. -/
def killPath {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (w : DiffusionPath d) : ContinuousPath (OnePoint ↥U) :=
  ⟨killFun U w, killFun_continuous U hU w⟩

/-- Every fixed-time killed coordinate is Borel measurable. -/
theorem measurable_killFun {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (t : ℝ≥0) :
    Measurable[borel (DiffusionPath d), borel (OnePoint ↥U)]
      (fun w => killFun U w t) := by
  classical
  let : MeasurableSpace (OnePoint ↥U) := borel _
  have : BorelSpace (OnePoint ↥U) := ⟨rfl⟩
  let A : Set (DiffusionPath d) := {w | (t : ℝ≥0∞) < ContinuousPath.exitTime U w}
  have hA : MeasurableSet A := ContinuousPath.measurableSet_lt_exitTime U hU t
  have hlive : Continuous (fun w : A =>
      (⟨w.val t, ContinuousPath.mem_of_lt_exitTime U w.val t w.property⟩ : ↥U)) :=
    Continuous.subtype_mk ((continuous_eval_const t).comp continuous_subtype_val) _
  have hm : Measurable (fun w : A =>
      ((⟨w.val t, ContinuousPath.mem_of_lt_exitTime U w.val t w.property⟩ : ↥U) :
        OnePoint ↥U)) := (OnePoint.continuous_coe.comp hlive).measurable
  exact hm.dite measurable_const hA

/-- The killed-path map is Borel measurable for the compact-open path topology. -/
theorem measurable_killPath {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U) :
    Measurable[borel (DiffusionPath d), borel (ContinuousPath (OnePoint ↥U))]
      (killPath U hU) := by
  classical
  let : MeasurableSpace (OnePoint ↥U) := borel _
  have : BorelSpace (OnePoint ↥U) := ⟨rfl⟩
  have : LocallyCompactSpace ↥U := hU.locallyCompactSpace
  let : MetricSpace (OnePoint ↥U) := TopologicalSpace.metrizableSpaceMetric (OnePoint ↥U)
  have : CompleteSpace (OnePoint ↥U) := inferInstance
  have hrestriction : Measurable (fun w => ContinuousPath.denseRestriction (killPath U hU w)) := by
    rw [measurable_pi_iff]
    intro q
    exact measurable_killFun U hU (DenseTime.castOrderEmbedding q)
  exact ContinuousPath.measurableEmbedding_denseRestriction.measurable_comp_iff.mp hrestriction

end SubdiffusiveProcess.KilledFeller
