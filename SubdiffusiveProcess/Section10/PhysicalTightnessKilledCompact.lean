module

public import SubdiffusiveProcess.Section10.PhysicalTightnessKilledSemicontinuity

@[expose] public section

/-! Compact uniform small-time survival, on the actual all-start lifetime law.
The continuous killed density provides semicontinuity; path continuity at its
specified initial point provides the small-time limit. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

/-- Positive decreasing deterministic time mesh, used only for the finite head. -/
def headTime (n : ℕ) : NNReal := ((n + 1 : ℕ) : NNReal)⁻¹

theorem headTime_pos (n : ℕ) : 0 < headTime n := by dsimp [headTime]; positivity

theorem headTime_antitone : Antitone headTime := by
  intro n m hnm
  dsimp only [headTime]
  exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)

theorem tendsto_headTime_zero : Tendsto (fun n => (headTime n : ENNReal)) atTop (𝓝 0) := by
  have hcast : ∀ n : ℕ, (headTime n : ENNReal) = ((n + 1 : ℕ) : ENNReal)⁻¹ := by
    intro n
    rw [headTime, ENNReal.coe_inv (by positivity), ENNReal.coe_natCast]
  simpa only [hcast, Function.comp_def] using
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)

/-- At each actual starting point, small-time exit probability tends to zero. -/
theorem tendsto_exit_headTime_zero {d : ℕ}
    (law : Kernel (Vec d) (Path d)) (hSM : StrongMarkov law)
    (U : Set (Vec d)) (hU : IsOpen U) {x : Vec d} (hx : x ∈ U) :
    Tendsto (fun n => law x {w | LifetimePath.exitTime U w ≤ (headTime n : ENNReal)})
      atTop (𝓝 0) := by
  have : IsProbabilityMeasure (law x) := ⟨hSM.1 x⟩
  let E : ℕ → Set (Path d) := fun n => {w | LifetimePath.exitTime U w ≤ (headTime n : ENNReal)}
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_le (localTorsion_exitTime_measurable U hU) measurable_const
  have hanti : Antitone E := fun n m hnm w hw =>
    hw.trans (ENNReal.coe_le_coe.mpr (headTime_antitone hnm))
  have hzero : law x (⋂ n, E n) = 0 := by
    apply measure_mono_null (t := {w | LifetimePath.coordinate 0 w ≠ Cemetery.alive x})
    · intro w hw hstart
      have hpos := goodCube_exitTime_pos_of_start U hU w hx hstart
      have hle : LifetimePath.exitTime U w ≤ 0 :=
        ge_of_tendsto tendsto_headTime_zero (Eventually.of_forall fun n => mem_iInter.mp hw n)
      exact hpos.not_ge hle
    · exact ae_iff.mp (hSM.2.1 x)
  have hlim := tendsto_measure_iInter_atTop (μ := law x) (fun n => (hEm n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  simpa only [Function.comp_def, hzero, E] using hlim

/-- A compact interior set has uniformly small early-exit probability at one
positive deterministic time. There is no Feller or nonexplosion premise. -/
theorem compact_uniform_exit_headTime {d : ℕ}
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData c rho law) {U K : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hKU : K ⊆ U) (b : ℝ) (hb : 0 < b) :
    ∃ n : ℕ, ∀ x ∈ K,
      law x {w | LifetimePath.exitTime U w ≤ (headTime n : ENNReal)} ≤ ENNReal.ofReal b := by
  classical
  let : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD.1
  by_cases hb1 : 1 ≤ b
  · exact ⟨0, fun _ _ => prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal hb1)⟩
  let F : ℕ → Vec d → ENNReal := fun n x => killedKernel law U hU (headTime n) x univ
  let c0 : ENNReal := 1 - ENNReal.ofReal b
  have hc0 : c0 < 1 := ENNReal.sub_lt_self (by simp) (by simp) (by simpa using hb)
  have hmono : ∀ x, Monotone (fun n => F n x) := by
    intro x n m hnm
    simp only [F, killed_apply law U hU _ x univ MeasurableSet.univ]
    exact measure_mono fun w hw => ⟨mem_univ _,
      lt_of_le_of_lt (ENNReal.coe_le_coe.mpr (headTime_antitone hnm)) hw.2⟩
  have hsemi : ∀ n ∈ (univ : Set ℕ), LowerSemicontinuousOn (F n) K := by
    intro n _
    have ht : 0 < (headTime n : ℝ) := headTime_pos n
    have h := lowerSemicontinuousOn_killed_survival hD hU hUb ht
    simpa only [Real.toNNReal_coe] using h.mono hKU
  have hlim : ∀ x ∈ K, Tendsto (fun n => F n x) atTop (𝓝 1) := by
    intro x hx
    have he := tendsto_exit_headTime_zero law hD.1.1 U hU (hKU hx)
    have h := ENNReal.Tendsto.sub tendsto_const_nhds he (Or.inl (by simp : (1 : ENNReal) ≠ ⊤))
    simpa only [F, killed_survival_eq_one_sub_exit, tsub_zero] using h
  have hempty : K ∩ ⋂ n ∈ (univ : Set ℕ), (F n) ⁻¹' Iic c0 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hle : ∀ n, F n x ≤ c0 := fun n => mem_iInter.mp (mem_iInter.mp hx.2 n) (mem_univ n)
    exact hc0.not_ge (le_of_tendsto (hlim x hx.1) (Eventually.of_forall hle))
  obtain ⟨s, hs⟩ :=
    (LowerSemicontinuousOn.disjoint_biInter_preimage_Iic_iff_exists_finset hK hsemi).mp (Set.disjoint_iff_inter_eq_empty.mpr hempty)
  let n : ℕ := s.sup fun i => i.val
  refine ⟨n, ?_⟩
  intro x hx
  obtain ⟨i, hi, hix⟩ := hs x hx
  have hlarge : c0 ≤ F n x := hix.le.trans (hmono x (Finset.le_sup (f := fun i => i.val) hi))
  rw [show F n x = 1 - law x {w | LifetimePath.exitTime U w ≤ (headTime n : ENNReal)} from
    killed_survival_eq_one_sub_exit law U hU _ x] at hlarge
  exact (ENNReal.sub_le_sub_iff_left (show law x _ ≤ 1 from prob_le_one) (by simp)).mp hlarge

end SubdiffusiveProcess.Section10.PhysicalTightness
