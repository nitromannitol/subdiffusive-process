module

public import Mathlib
public import SubdiffusiveProcess.Section10.TransitionTopology
public import SubdiffusiveProcess.Section10.TransitionPassage
public import SubdiffusiveProcess.Section10.ChaosCarrier
public import SubdiffusiveProcess.Section10.GaussianSupport
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.MultiplicativeChaos.ChaosBasic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section10Nash.TwoDimGeneralExponent
@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section10Nash Homogenization
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace SubdiffusiveProcess.Paper


theorem aux_lim_nonbrownian_exit_truncated_passage
    {d : ℕ} (r : ℝ) (P : ProbabilityMeasure (DiffusionPath d))
    (PN : ℕ → ProbabilityMeasure (DiffusionPath d)) (hconv : Tendsto PN atTop (𝓝 P))
    (b : ℝ≥0∞) (hbound : ∀ᶠ n in atTop, ∫⁻ w,
      ContinuousPath.exitTime (Metric.ball (w 0) r) w ∂(PN n : Measure (DiffusionPath d)) ≤ b)
    (T : ℝ≥0∞) (hT : T ≠ ⊤) :
    (∫⁻ w, ENNReal.ofReal (ENNReal.truncateToReal T
      (ContinuousPath.exitTime (Metric.ball (w 0) r) w)) ∂(P : Measure (DiffusionPath d))) ≤ b := by
  have hle : ∀ x : ℝ≥0∞, ENNReal.ofReal (T.truncateToReal x) ≤ x := by
    intro x
    change ENNReal.ofReal ((min T x).toReal) ≤ x
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top hT (min_le_left T x))]
    exact min_le_right T x
  have hf : LowerSemicontinuous (fun w : DiffusionPath d =>
      T.truncateToReal (ContinuousPath.exitTime (Metric.ball (w 0) r) w)) := by
    have h1 := Continuous.comp_lowerSemicontinuous (ENNReal.continuous_truncateToReal hT)
      (_root_.SubdiffusiveProcess.Paper.aux_lim_nonbrownian_centered_exit_lsc (d := d) r)
      (ENNReal.monotone_truncateToReal hT)
    simpa only [Function.comp_apply] using! h1
  have hPort := _root_.SubdiffusiveProcess.Paper.aux_lim_transition_domination_portmanteau_lsc
    (P := (P : Measure (DiffusionPath d)))
    (PN := fun n => (PN n : Measure (DiffusionPath d)))
    (f := fun w => T.truncateToReal (ContinuousPath.exitTime (Metric.ball (w 0) r) w))
    hf (fun w => ENNReal.truncateToReal_nonneg)
    (fun G hG => MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hG)
  refine le_trans hPort ?_
  apply Filter.liminf_le_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [hbound] with n hn
  calc ∫⁻ w, ENNReal.ofReal
        (T.truncateToReal (ContinuousPath.exitTime (Metric.ball (w 0) r) w))
        ∂(PN n : Measure (DiffusionPath d))
      ≤ ∫⁻ w, ContinuousPath.exitTime (Metric.ball (w 0) r) w
        ∂(PN n : Measure (DiffusionPath d)) := by
        apply MeasureTheory.lintegral_mono
        intro w
        exact hle _
    _ ≤ b := hn



theorem aux_lim_nonbrownian_exit_positive
    {d : ℕ} (r : ℝ) (hr : 0 < r) (w : DiffusionPath d) :
    0 < ContinuousPath.exitTime (Metric.ball (w 0) r) w := by
  by_contra h
  have hle : ContinuousPath.exitTime (Metric.ball (w 0) r) w ≤ ((0 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_zero]
    exact not_lt.mp h
  have hh := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy (Metric.ball (w 0) r)
    Metric.isOpen_ball (0 : ℝ≥0) w).mp hle
  rw [ContinuousPath.hitsSetBy] at hh
  simp only [mem_ofPred_eq, Set.mem_compl_iff] at hh
  obtain ⟨s, hs⟩ := hh
  have hs0 : (s : ℝ≥0) = 0 := le_antisymm s.2 zero_le
  rw [hs0] at hs
  exact hs (Metric.mem_ball_self hr)



theorem aux_lim_nonbrownian_brownian_event_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ≥0∞) (Y : Ω → ℝ≥0∞)
    (hX : ∀ n, Measurable (X n)) (E : Set Ω) (hE : MeasurableSet E)
    (hlim : ∀ w ∈ E, Tendsto (fun n => X n w) atTop (𝓝 0))
    (hident : ∀ n a, P {w | X n w < a} = P {w | Y w < a})
    (a : ℝ≥0∞) (ha : 0 < a) :
    P E ≤ P {w | Y w < a} := by
  have hB : ∀ n, MeasurableSet {w | X n w < a} := fun n =>
    measurableSet_lt (hX n) measurable_const
  have hSB : ∀ w ∈ E, ∀ᶠ n in atTop, w ∈ {w | X n w < a} := by
    intro w hw
    exact (hlim w hw).eventually (eventually_lt_nhds ha)
  have hmain := aux_lim_measure_set_fatou P E hE (fun n => {w | X n w < a}) hB hSB
  have hconst : liminf (fun n => P {w | X n w < a}) atTop = P {w | Y w < a} := by
    have hfun : (fun n => P {w | X n w < a}) = fun _ => P {w | Y w < a} := by
      funext n
      exact hident n a
    rw [hfun, Filter.liminf_const]
  exact le_of_le_of_eq hmain hconst



theorem aux_lim_nonbrownian_brownian_sublevels_null
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Y : Ω → ℝ≥0∞) (hY : Measurable Y) (hpos : ∀ᵐ w ∂P, 0 < Y w)
    (E : Set Ω) (hb : ∀ a : ℝ≥0∞, 0 < a → P E ≤ P {w | Y w < a}) :
    P E = 0 := by
  have hInv_pos : ∀ n : ℕ, 0 < ((↑(n+1) : ℝ≥0∞))⁻¹ := by
    intro n
    rw [ENNReal.inv_pos]
    exact ENNReal.coe_ne_top
  have hbound : P E ≤ ⨅ n : ℕ, P {w : Ω | Y w < ((↑(n+1) : ℝ≥0∞))⁻¹} := by
    apply le_iInf
    intro n
    exact hb _ (hInv_pos n)
  have hmeas : ∀ n : ℕ, MeasurableSet {w : Ω | Y w < ((↑(n+1) : ℝ≥0∞))⁻¹} :=
    fun n => hY measurableSet_Iio
  have hanti : Antitone (fun n : ℕ => {w : Ω | Y w < ((↑(n+1) : ℝ≥0∞))⁻¹}) := by
    apply antitone_nat_of_succ_le
    intro n w hw
    simp only [mem_ofPred_eq] at hw ⊢
    exact lt_of_lt_of_le hw (ENNReal.inv_le_inv.2 (by exact_mod_cast Nat.le_succ (n+1)))
  have hinter : P (⋂ n : ℕ, {w : Ω | Y w < ((↑(n+1) : ℝ≥0∞))⁻¹})
      = ⨅ n : ℕ, P {w : Ω | Y w < ((↑(n+1) : ℝ≥0∞))⁻¹} :=
    Antitone.measure_iInter hanti (fun n => (hmeas n).nullMeasurableSet) ⟨0, measure_ne_top P _⟩
  have hlim : Tendsto (fun n : ℕ => ((↑(n+1) : ℝ≥0∞))⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hmem : ∀ w, w ∈ ⋂ n : ℕ, {w : Ω | Y w < ((↑(n+1) : ℝ≥0∞))⁻¹} → Y w = 0 := by
    intro w hw
    have hle : ∀ n : ℕ, Y w ≤ ((↑(n+1) : ℝ≥0∞))⁻¹ :=
      fun n => le_of_lt (Set.mem_iInter.mp hw n)
    exact nonpos_iff_eq_zero.mp (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hle)
  have hzero : P {w : Ω | Y w = 0} = 0 := by
    have hset : {w : Ω | Y w = 0} = {w : Ω | ¬ 0 < Y w} := by
      ext w; simp only [mem_ofPred_eq, not_lt, nonpos_iff_eq_zero]
    rw [hset]
    exact (MeasureTheory.ae_iff).mp hpos
  apply le_antisymm
  · calc P E ≤ ⨅ n : ℕ, P {w : Ω | Y w < ((↑(n+1) : ℝ≥0∞))⁻¹} := hbound
      _ = P (⋂ n : ℕ, {w : Ω | Y w < ((↑(n+1) : ℝ≥0∞))⁻¹}) := hinter.symm
      _ ≤ P {w : Ω | Y w = 0} := measure_mono (fun w hw => hmem w hw)
      _ = 0 := hzero
  · exact zero_le


theorem aux_lim_nonbrownian_exit_passage
    {d : ℕ} (r : ℝ) (P : ProbabilityMeasure (DiffusionPath d))
    (PN : ℕ → ProbabilityMeasure (DiffusionPath d)) (hconv : Tendsto PN atTop (𝓝 P))
    (b : ℝ≥0∞) (hbound : ∀ᶠ n in atTop, ∫⁻ w,
      ContinuousPath.exitTime (Metric.ball (w 0) r) w ∂(PN n : Measure (DiffusionPath d)) ≤ b) :
    (∫⁻ w, ContinuousPath.exitTime (Metric.ball (w 0) r) w ∂(P : Measure (DiffusionPath d))) ≤ b := by
  let s : DiffusionPath d → ℝ≥0∞ := fun w => ContinuousPath.exitTime (Metric.ball (w 0) r) w
  have hs : Measurable s := (aux_lim_nonbrownian_centered_exit_lsc r).measurable
  have hconv' := lintegral_tendsto_of_tendsto_of_monotone
    (μ := (P : Measure (DiffusionPath d)))
    (f := fun n w => min (n : ℝ≥0∞) (s w))
    (fun n => (measurable_const.min hs).aemeasurable)
    (ae_of_all _ (fun w i j hij => min_le_min_right _ (by exact_mod_cast hij)))
    (ae_of_all _ (fun w => by simpa only [min_top_left] using
      ENNReal.tendsto_nat_nhds_top.min (tendsto_const_nhds (x := s w))))
  apply le_of_tendsto hconv'
  apply Eventually.of_forall
  intro n
  have h := aux_lim_nonbrownian_exit_truncated_passage r P PN hconv b hbound n
    (by exact_mod_cast ENNReal.natCast_ne_top n)
  simpa [ENNReal.truncateToReal, s] using h

theorem aux_lim_nonbrownian_common_carrier_of_exit_scaling
    {d : ℕ} (Q : Measure (DiffusionPath d)) [IsFiniteMeasure Q]
    (hscale : ∀ (k : ℕ) (a : ℝ≥0∞),
      Q {w | (3 : ℝ≥0∞) ^ (2 * k) * ContinuousPath.exitTime
          (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w < a} =
        Q {w | ContinuousPath.exitTime (Metric.ball (w 0) (1 / 2)) w < a}) :
    Q {w | Tendsto (fun k : ℕ => (3 : ℝ≥0∞) ^ (2 * k) *
      ContinuousPath.exitTime (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w)
      atTop (𝓝 0)} = 0 := by
  let X : ℕ → DiffusionPath d → ℝ≥0∞ := fun k w => (3 : ℝ≥0∞) ^ (2 * k) *
      ContinuousPath.exitTime (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w
  have hX : ∀ k, Measurable (X k) := fun k =>
    measurable_const.mul (aux_lim_nonbrownian_centered_exit_lsc _).measurable
  have hE : MeasurableSet {w | Tendsto (fun k => X k w) atTop (𝓝 0)} := measurableSet_tendsto (𝓝 0) hX
  apply aux_lim_nonbrownian_brownian_sublevels_null Q
    (fun w => ContinuousPath.exitTime (Metric.ball (w 0) (1 / 2)) w)
    (aux_lim_nonbrownian_centered_exit_lsc _).measurable
    (ae_of_all _ (fun w => aux_lim_nonbrownian_exit_positive _ (by norm_num) w))
  intro a ha
  exact aux_lim_nonbrownian_brownian_event_bound Q X _ hX _ hE
    (fun w hw => hw) hscale a ha


end SubdiffusiveProcess.Paper
