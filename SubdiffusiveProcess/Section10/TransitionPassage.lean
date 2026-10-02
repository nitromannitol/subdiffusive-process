import SubdiffusiveProcess.Section10.TransitionTopology
import Mathlib
import MarkovProcess.Path.ExitTime
import SubdiffusiveProcess.Main.DiffusionPath
open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace Paper

/-- Source L:358–360 and Fix 10. Pool order `astra10_0927_fatou_finite`; independently harvested. -/
theorem aux_lim_transition_domination_fatou_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : ℕ → Ω → ℝ≥0∞) (hK : ∀ n, Measurable (K n))
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hbound : ∀ n, ∫⁻ w, K n w ∂P ≤ C) :
    ∀ᵐ w ∂P, Filter.liminf (fun n => K n w) atTop < ⊤ := by
  have hmeas : Measurable (fun w => Filter.liminf (fun n => K n w) atTop) :=
    Measurable.liminf hK
  have hfatou :
      ∫⁻ w, Filter.liminf (fun n => K n w) atTop ∂P ≤
        Filter.liminf (fun n => ∫⁻ w, K n w ∂P) atTop :=
    MeasureTheory.lintegral_liminf_le hK
  have hliminf_le : Filter.liminf (fun n => ∫⁻ w, K n w ∂P) atTop ≤ C :=
    Filter.liminf_le_of_frequently_le'
      (Filter.frequently_atTop.2 (fun a => ⟨a, le_refl a, hbound a⟩))
  have hle : ∫⁻ w, Filter.liminf (fun n => K n w) atTop ∂P ≤ C :=
    le_trans hfatou hliminf_le
  have hne : ∫⁻ w, Filter.liminf (fun n => K n w) atTop ∂P ≠ ⊤ := by
    intro htop
    exact hC (top_le_iff.mp (htop ▸ hle))
  exact MeasureTheory.ae_lt_top hmeas hne

/-- Source Fix 10, L:358–360. Pool order `astra10_0927_bounded_subsequence`; independently harvested. -/
theorem aux_lim_transition_domination_bounded_subsequence
    (K : ℕ → ℝ≥0∞) (hK : Filter.liminf K atTop < ⊤) :
    ∃ C : ℕ, ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∀ n, K (phi n) ≤ C := by
    have hne : Filter.liminf K atTop ≠ ⊤ := ne_of_lt hK
    obtain ⟨C, hC⟩ := ENNReal.exists_nat_gt hne
    have hfreq : ∃ᶠ n in atTop, K n < (C : ℝ≥0∞) :=
      Filter.frequently_lt_of_liminf_lt (u := K) (f := atTop) (h := hC)
    obtain ⟨phi, hphi_mono, hphi⟩ := Filter.extraction_of_frequently_atTop hfreq
    exact ⟨C, phi, hphi_mono, fun n => le_of_lt (hphi n)⟩

/-- Source Fix 10, L:358–377. Pool order `astra10_0927_portmanteau_lsc`; independently harvested. -/
theorem aux_lim_transition_domination_portmanteau_lsc
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (P : Measure X) (PN : ℕ → Measure X) (f : X → ℝ)
    (hf : LowerSemicontinuous f) (hpos : ∀ x, 0 ≤ f x)
    (hopen : ∀ G : Set X, IsOpen G → P G ≤ Filter.liminf (fun n => PN n G) atTop) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂P ≤
      Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (f x) ∂PN n) atTop := by
  have hf_meas : Measurable f := hf.measurable
  have hP_layer : ∫⁻ x, ENNReal.ofReal (f x) ∂P = ∫⁻ t in Ioi (0:ℝ), P {a | t < f a} :=
    MeasureTheory.lintegral_eq_lintegral_meas_lt P (Filter.Eventually.of_forall hpos) hf_meas.aemeasurable
  have hN_layer : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (f x) ∂PN n = ∫⁻ t in Ioi (0:ℝ), PN n {a | t < f a} :=
    fun n => MeasureTheory.lintegral_eq_lintegral_meas_lt (PN n) (Filter.Eventually.of_forall hpos) hf_meas.aemeasurable
  rw [hP_layer]
  rw [show Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (f x) ∂PN n) atTop =
      Filter.liminf (fun n => ∫⁻ t in Ioi (0:ℝ), PN n {a | t < f a}) atTop from
    Filter.liminf_congr (Filter.Eventually.of_forall hN_layer)]
  calc ∫⁻ t in Ioi (0:ℝ), P {a | t < f a}
      ≤ ∫⁻ t in Ioi (0:ℝ), Filter.liminf (fun n => PN n {a | t < f a}) atTop := by
        apply MeasureTheory.lintegral_mono
        intro t
        exact hopen {a | t < f a} (hf.isOpen_preimage t)
    _ ≤ Filter.liminf (fun n => ∫⁻ t in Ioi (0:ℝ), PN n {a | t < f a}) atTop := by
        apply MeasureTheory.lintegral_liminf_le
        intro n
        apply Antitone.measurable
        intro t1 t2 h
        apply measure_mono
        intro x hx
        exact lt_of_le_of_lt h hx

/-- Source Fix 10, L:358–377. Pool order `astra10_0927_killed_portmanteau_bound`; independently harvested. -/
theorem aux_lim_transition_domination_killed_portmanteau_bound
    {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : C(SpatialCoordinates d, ℝ)) (hpos : ∀ x, 0 ≤ f x)
    (P : ProbabilityMeasure (DiffusionPath d)) (PN : ℕ → ProbabilityMeasure (DiffusionPath d))
    (hconv : Tendsto PN atTop (𝓝 P)) (b : ℕ → ℝ≥0∞) (a : ℝ≥0∞)
    (hb : Tendsto b atTop (𝓝 a))
    (hbound : ∀ n, ∫⁻ w, ENNReal.ofReal
      (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
      ∂(PN n : Measure (DiffusionPath d)) ≤ b n) :
    (∫⁻ w, ENNReal.ofReal
      (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
      ∂(P : Measure (DiffusionPath d))) ≤ a := by
  have hnonneg : ∀ w : DiffusionPath d,
      0 ≤ (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0) := by
    intro w
    by_cases h : (t : ℝ≥0∞) < ContinuousPath.exitTime U w
    · simp only [h, if_true]; exact hpos (w t)
    · simp only [h, if_false]; exact le_refl 0
  have hL := aux_lim_transition_domination_portmanteau_lsc
      (P : Measure (DiffusionPath d)) (fun n => (PN n : Measure (DiffusionPath d)))
      (fun w : DiffusionPath d =>
        if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
      (aux_lim_transition_domination_killed_test_lsc U hU t f hpos) hnonneg
      (fun G hG => MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hG)
  calc ∫⁻ w, ENNReal.ofReal
        (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
        ∂(P : Measure (DiffusionPath d))
      ≤ Filter.liminf (fun n => ∫⁻ w, ENNReal.ofReal
          (if (t : ℝ≥0∞) < ContinuousPath.exitTime U w then f (w t) else 0)
          ∂(PN n : Measure (DiffusionPath d))) atTop := hL
    _ ≤ Filter.liminf b atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound)
    _ = a := Filter.Tendsto.liminf_eq hb

/-- Source L:379–382, Fix 10. Pool order `astra10_0927_exhaustion_ac`; independently harvested. -/
theorem aux_lim_transition_domination_exhaustion_ac
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (mu : Measure X) (f : Ω → X) (hf : Measurable f)
    (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet (E n))
    (hcover : (⋃ n, E n) = Set.univ)
    (hac : ∀ n, (P.restrict (E n)).map f ≪ mu) :
    P.map f ≪ mu := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hsA hsmu
  have hfA : MeasurableSet (f ⁻¹' s) := hsA.preimage hf
  have hzero : ∀ n, P (f ⁻¹' s ∩ E n) = 0 := by
    intro n
    have h1 : ((P.restrict (E n)).map f) s = (P.restrict (E n)) (f ⁻¹' s) :=
      Measure.map_apply hf hsA
    have h2 : (P.restrict (E n)) (f ⁻¹' s) = P (f ⁻¹' s ∩ E n) :=
      Measure.restrict_apply hfA
    rw [← h2, ← h1]
    exact hac n hsmu
  have hunion : P (⋃ n, f ⁻¹' s ∩ E n) = 0 :=
    measure_iUnion_null hzero
  have hsub1 : (⋃ n, f ⁻¹' s ∩ E n) ⊆ f ⁻¹' s := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨n, hn⟩
    exact hn.1
  have hsub2 : f ⁻¹' s ⊆ (⋃ n, f ⁻¹' s ∩ E n) := by
    intro x hx
    have hxU : x ∈ ⋃ n, E n := by rw [hcover]; exact Set.mem_univ x
    rw [Set.mem_iUnion] at hxU
    rcases hxU with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hx, hn⟩
  have hset : (⋃ n, f ⁻¹' s ∩ E n) = f ⁻¹' s :=
    Set.Subset.antisymm hsub1 hsub2
  calc
    (P.map f) s = P (f ⁻¹' s) := Measure.map_apply hf hsA
    _ = P (⋃ n, f ⁻¹' s ∩ E n) := by rw [hset]
    _ = 0 := hunion

end Paper
