module

public import SubdiffusiveProcess.Section10.PhysicalTightnessKilledCompact

@[expose] public section

/-! Measurable environment descent of compact uniform small-time survival.
A measurable integral of failing starts replaces an uncountable supremum.
The proved excessive-function upgrade restores EVERY start on the open set. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

/-- A compact interior start set admits a deterministic time and a measurable
exceptional environment set of arbitrarily small mass. The input is the actual
joint kernel with its local characterization, not a caller tightness promise. -/
theorem measurable_small_time_exit_on_open {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (law : Kernel (Omega × Vec d) (Path d))
    (c rho : Omega → Vec d → ℝ)
    (hdata : ∀ᵐ omega ∂mu, LocalDiffusionData (c omega) (rho omega)
      (Kernel.comap law (fun x => (omega, x)) measurable_prodMk_left))
    {U W K : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hW : IsOpen W) (hWK : W ⊆ K) (hK : IsCompact K) (hKU : K ⊆ U)
    (b e : ℝ) (hb : 0 < b) (he : 0 < e) :
    ∃ n : ℕ, ∃ S : Set Omega, MeasurableSet S ∧ mu S ≤ ENNReal.ofReal e ∧
      ∀ᵐ omega ∂mu, omega ∉ S → ∀ x ∈ W,
        law (omega, x) {w | LifetimePath.exitTime U w ≤ (headTime n : ENNReal)} ≤ ENNReal.ofReal b := by
  classical
  let E : ℕ → Set (Path d) := fun n => {w | LifetimePath.exitTime U w ≤ (headTime n : ENNReal)}
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_le (localTorsion_exitTime_measurable U hU) measurable_const
  let A : ℕ → Set (Omega × Vec d) := fun n =>
    {p | p.2 ∈ W ∧ ENNReal.ofReal b < law p (E n)}
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    (measurable_snd hW.measurableSet).inter (measurableSet_lt measurable_const (law.measurable_coe (hEm n)))
  let I : ℕ → Omega × Vec d → ENNReal := fun n => (A n).indicator (fun _ => 1)
  have hIm : ∀ n, Measurable (I n) := fun n => measurable_const.indicator (hAm n)
  let J : ℕ → Omega → ENNReal := fun n omega => ∫⁻ y in U, I n (omega, y)
  have hJm : ∀ n, Measurable (J n) := fun n => (hIm n).lintegral_prod_right'
  let S : ℕ → Set Omega := fun n => {omega | J n omega ≠ 0}
  have hSm : ∀ n, MeasurableSet (S n) := fun n => ((hJm n) (measurableSet_singleton (0 : ENNReal))).compl
  have hSanti : Antitone S := by
    intro n m hnm omega homega
    have hle : J m omega ≤ J n omega := by
      apply lintegral_mono
      intro y
      apply indicator_le_indicator_of_subset (s := A m) (t := A n)
      · intro p hp
        refine ⟨hp.1, hp.2.trans_le ?_⟩
        exact measure_mono fun w hw => hw.trans (ENNReal.coe_le_coe.mpr (headTime_antitone hnm))
      · intro p; exact zero_le_one
    exact fun hzero => homega (le_antisymm (hzero ▸ hle) bot_le)
  have hzero : mu (⋂ n, S n) = 0 := by
    have hae : ∀ᵐ omega ∂mu, omega ∉ ⋂ n, S n := by
      filter_upwards [hdata] with omega hD
      obtain ⟨n, hn⟩ := compact_uniform_exit_headTime hD hU hUb hK hKU b hb
      intro homega
      have hJn : J n omega = 0 := by
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [] with y
        by_cases hy : y ∈ W
        · exact indicator_of_notMem (fun hp => hp.2.not_ge (hn y (hWK hy))) _
        · exact indicator_of_notMem (fun hp => hy hp.1) _
      exact (mem_iInter.mp homega n) hJn
    simpa only [not_not, Set.setOf_mem_eq] using! ae_iff.mp hae
  have hlim : Tendsto (fun n => mu (S n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hzero] using
      tendsto_measure_iInter_atTop (μ := mu) (fun n => (hSm n).nullMeasurableSet) hSanti ⟨0, measure_ne_top _ _⟩
  obtain ⟨n, hn⟩ := ((hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr he))).exists)
  refine ⟨n, S n, hSm n, hn.le, ?_⟩
  filter_upwards [hdata] with omega hD homega
  have hJn : J n omega = 0 := not_not.mp homega
  have hvol : ∀ᵐ y ∂volume.restrict U, y ∈ W → law (omega, y) (E n) ≤ ENNReal.ofReal b := by
    have hzeroI := (lintegral_eq_zero_iff
      ((hIm n).comp (measurable_const.prodMk measurable_id))).mp hJn
    filter_upwards [hzeroI] with y hy hyW
    by_contra hbad
    have hmem : (omega, y) ∈ A n := ⟨hyW, lt_of_not_ge hbad⟩
    have hone : I n (omega, y) = 1 := indicator_of_mem hmem _
    exact one_ne_zero (hone.symm.trans hy)
  have hweight := (weightedMeasure_restrict_absolutelyContinuous_volume_restrict
    (rho := rho omega) hU.measurableSet).ae_le hvol
  exact exit_probability_le_of_ae hD hU hUb hW (hWK.trans hKU) (headTime n) b hb.le hweight

end SubdiffusiveProcess.Section10.PhysicalTightness
