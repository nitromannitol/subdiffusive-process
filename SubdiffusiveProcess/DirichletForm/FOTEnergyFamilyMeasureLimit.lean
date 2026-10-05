module

public import SubdiffusiveProcess.DirichletForm.FOTCoreMeasure
public import Mathlib.MeasureTheory.Measure.AddContent

@[expose] public section

open MeasureTheory Filter Set Topology Function

noncomputable section
namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X]

/-- A uniform setwise limit of finite measures is again a finite measure. -/
theorem family_uniform_measure_limit (μ : ℕ → Measure X)
    (hfinite : ∀ n, IsFiniteMeasure (μ n)) (f : Set X → ℝ)
    (hlim : ∀ B, MeasurableSet B →
      Tendsto (fun n => (μ n B).toReal) atTop (𝓝 (f B)))
    (huni : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ B, MeasurableSet B →
      |(μ n B).toReal - f B| ≤ ε) :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧
      ∀ B, MeasurableSet B → (ν B).toReal = f B := by
  let (n : ℕ) : IsFiniteMeasure (μ n) := hfinite n
  have hf0 : f ∅ = 0 := tendsto_nhds_unique (hlim ∅ MeasurableSet.empty)
    (by simpa only [measure_empty, ENNReal.toReal_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  have hfpos : ∀ B, MeasurableSet B → 0 ≤ f B := fun B hB =>
    ge_of_tendsto (hlim B hB) (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  have hfadd : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
      f (B ∪ C) = f B + f C := by
    intro B C hB hC hd
    apply tendsto_nhds_unique (hlim (B ∪ C) (hB.union hC))
    apply ((hlim B hB).add (hlim C hC)).congr
    intro n
    exact (measureReal_union hd hC (measure_ne_top _ _) (measure_ne_top _ _)).symm
  let C : Set (Set X) := {B | MeasurableSet B}
  have hC : IsSetRing C := {
    empty_mem := MeasurableSet.empty
    union_mem := by intro B C hB hC; exact hB.union hC
    sdiff_mem := by intro B C hB hC; exact hB.diff hC }
  let a : AddContent ENNReal C := hC.addContent_of_union (fun B => ENNReal.ofReal (f B))
    (by change ENNReal.ofReal (f ∅) = 0; rw [hf0, ENNReal.ofReal_zero])
    (fun hB hC hd => by
      rw [hfadd _ _ hB hC hd, ENNReal.ofReal_add (hfpos _ hB) (hfpos _ hC)])
  have hzero : ∀ (s : ℕ → Set X), (∀ n, MeasurableSet (s n)) → Antitone s →
      (⋂ n, s n) = ∅ → Tendsto (fun n => f (s n)) atTop (𝓝 0) := by
    intro s hs ha hempty
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := huni (ε / 2) (by positivity)
    have hm : Tendsto (fun n => (μ N (s n)).toReal) atTop (𝓝 (0 : ℝ)) := by
      have ht := tendsto_measure_iInter_atTop (μ := μ N)
        (fun n => (hs n).nullMeasurableSet) ha ⟨0, measure_ne_top _ _⟩
      rw [hempty, measure_empty] at ht
      exact (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp ht
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      (hm.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2)))
    refine ⟨M, fun n hn => ?_⟩
    have hb := (abs_le.mp (hN N le_rfl (s n) (hs n))).1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hfpos _ (hs n))]
    linarith [hM n hn]
  have hadd : ∀ (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n)),
      Pairwise (Disjoint on s) → ENNReal.ofReal (f (⋃ n, s n)) =
        ∑' n, ENNReal.ofReal (f (s n)) := by
    intro s hs hd
    exact addContent_iUnion_eq_sum_of_tendsto_zero hC a
      (fun _ _ => ENNReal.ofReal_ne_top)
      (fun {s'} hs' ha hempty => by
        change Tendsto (fun n => ENNReal.ofReal (f (s' n))) atTop (𝓝 0)
        simpa only [ENNReal.ofReal_zero, Function.comp_def] using
          (ENNReal.continuous_ofReal.tendsto 0).comp (hzero s' hs' ha hempty))
      hs (MeasurableSet.iUnion hs) hd
  let ν := Measure.ofMeasurable (fun B _ => ENNReal.ofReal (f B))
    (by rw [hf0, ENNReal.ofReal_zero])
    (fun {s} hs hd => hadd s hs hd)
  have hν : ∀ B, MeasurableSet B → ν B = ENNReal.ofReal (f B) :=
    fun B hB => Measure.ofMeasurable_apply B hB
  refine ⟨ν, ⟨by rw [hν univ MeasurableSet.univ]; exact ENNReal.ofReal_lt_top⟩, ?_⟩
  intro B hB
  rw [hν B hB, ENNReal.toReal_ofReal (hfpos B hB)]

/-- Uniform Cauchy bounds supply the real setwise limit used above. -/
theorem family_cauchy_measure_limit (μ : ℕ → Measure X)
    (hfinite : ∀ n, IsFiniteMeasure (μ n))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      ∀ B, MeasurableSet B → |(μ n B).toReal - (μ k B).toReal| < ε) :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ B, MeasurableSet B →
        |(μ n B).toReal - (ν B).toReal| ≤ ε := by
  classical
  have hex : ∀ B : {B : Set X // MeasurableSet B}, ∃ r : ℝ,
      Tendsto (fun n => (μ n B).toReal) atTop (𝓝 r) := by
    intro B
    apply cauchySeq_tendsto_of_complete
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    exact ⟨N, fun n hn k hk => by
      rw [Real.dist_eq]
      exact hN n hn k hk B B.2⟩
  choose r hr using hex
  let f : Set X → ℝ := fun B => if hB : MeasurableSet B then r ⟨B, hB⟩ else 0
  have hlim : ∀ B, MeasurableSet B →
      Tendsto (fun n => (μ n B).toReal) atTop (𝓝 (f B)) := by
    intro B hB
    simpa only [f, dite_eq_left hB] using hr ⟨B, hB⟩
  have huni : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ B, MeasurableSet B →
      |(μ n B).toReal - f B| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, ?_⟩
    intro n hn B hB
    apply le_of_tendsto ((tendsto_const_nhds.sub (hlim B hB)).abs)
    filter_upwards [eventually_ge_atTop N] with k hk
    exact (hN n hn k hk B hB).le
  obtain ⟨ν, hν, hval⟩ := family_uniform_measure_limit μ hfinite f hlim huni
  refine ⟨ν, hν, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := huni ε hε
  exact ⟨N, fun n hn B hB => by rw [hval B hB]; exact hN n hn B hB⟩

end SubdiffusiveProcess.DirichletForm.FOTConstruction
