module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452AeLimit

@[expose] public section




set_option autoImplicit false

open Filter Homogenization MeasureTheory MarkovProcess Set

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-! ## The good event -/

/-- The event on which the composed sequence `a k ∘ ω` has summable sup-increments over every
integer horizon -- hence converges in `C(ℝ≥0, ℝ)`. -/
def goodSet (a : ℕ → C(Vec d, ℝ)) : Set (ContinuousPath (Vec d)) :=
  {ω | ∀ N : ℕ, (∑' k : ℕ, supIncr (fun k t => a k (ω t)) (N : ℝ≥0) k) ≠ ⊤}

theorem measurable_supIncr_comp (a : ℕ → C(Vec d, ℝ)) (T : ℝ≥0) (k : ℕ) :
    Measurable fun ω : ContinuousPath (Vec d) => supIncr (fun k t => a k (ω t)) T k := by
  refine measurable_iSup_le_of_continuous
    (F := fun (ω : ContinuousPath (Vec d)) (t : ℝ≥0) =>
      ENNReal.ofReal |a (k + 1) (ω t) - a k (ω t)|) ?_ ?_ T
  · intro ω
    exact ENNReal.continuous_ofReal.comp
      ((((a (k + 1)).continuous.comp ω.continuous).sub
        ((a k).continuous.comp ω.continuous)).abs)
  · intro t
    have hev : Measurable fun ω : ContinuousPath (Vec d) => ω t :=
      ContinuousPath.measurable_coordinateProcess t
    exact ENNReal.measurable_ofReal.comp
      ((((a (k + 1)).continuous.measurable.comp hev).sub
        ((a k).continuous.measurable.comp hev)).abs)

theorem measurableSet_goodSet (a : ℕ → C(Vec d, ℝ)) : MeasurableSet (goodSet a) := by
  have h : goodSet a
      = ⋂ N : ℕ, {ω : ContinuousPath (Vec d) |
        (∑' k : ℕ, supIncr (fun k t => a k (ω t)) (N : ℝ≥0) k) ∈ ({⊤}ᶜ : Set ℝ≥0∞)} := by
    ext ω; simp only [goodSet, mem_setOf_eq, mem_iInter, mem_compl_iff, mem_singleton_iff]
  rw [h]
  refine MeasurableSet.iInter fun N => ?_
  exact (Measurable.ennreal_tsum fun k => measurable_supIncr_comp a (N : ℝ≥0) k)
    (measurableSet_singleton (⊤ : ℝ≥0∞)).compl

/-! ## The lift -/

open scoped Classical in
/-- The path lift: the `C(ℝ≥0, ℝ)`-valued limit of `a k ∘ ω` on `goodSet a`, and `0` off it. -/
def pathLift (a : ℕ → C(Vec d, ℝ)) : ContinuousPath (Vec d) → C(ℝ≥0, ℝ) :=
  (goodSet a).piecewise (fun ω => limUnder atTop fun k => (a k).comp ω) 0

theorem pathLift_of_not_mem {a : ℕ → C(Vec d, ℝ)} {ω : ContinuousPath (Vec d)}
    (hω : ω ∉ goodSet a) : pathLift a ω = 0 := by
  classical
  exact Set.piecewise_eq_of_notMem _ _ _ hω

/-- **Steps 3–4.**  On the good event the composed sequence converges to `pathLift a ω`, in
`C(ℝ≥0, ℝ)` and uniformly on every `Icc 0 T`. -/
theorem pathLift_spec {a : ℕ → C(Vec d, ℝ)} {ω : ContinuousPath (Vec d)} (hω : ω ∈ goodSet a) :
    Tendsto (fun k => (a k).comp ω) atTop (𝓝 (pathLift a ω)) ∧
      ∀ T : ℝ≥0, TendstoUniformlyOn (fun k t => a k (ω t)) (fun t => pathLift a ω t)
        atTop (Icc 0 T) := by
  classical
  obtain ⟨g, hg, hgu⟩ := exists_tendsto_of_summable_supIncr (fun k => (a k).comp ω) hω
  have hlim : pathLift a ω = g := by
    rw [pathLift, Set.piecewise_eq_of_mem _ _ _ hω]
    exact hg.limUnder_eq
  rw [hlim]
  exact ⟨hg, hgu⟩

theorem tendsto_pathLift_apply {a : ℕ → C(Vec d, ℝ)} {ω : ContinuousPath (Vec d)}
    (hω : ω ∈ goodSet a) (t : ℝ≥0) :
    Tendsto (fun k => a k (ω t)) atTop (𝓝 (pathLift a ω t)) :=
  ((pathLift_spec hω).2 t).tendsto_at (by exact ⟨bot_le, le_rfl⟩)

/-! ## Measurability -/

theorem measurable_pathLift (a : ℕ → C(Vec d, ℝ)) : Measurable (pathLift a) := by
  classical
  set G : ℕ → ContinuousPath (Vec d) → C(ℝ≥0, ℝ) := fun k =>
    (goodSet a).piecewise (fun ω => (a k).comp ω) 0 with hG
  have hGmeas : ∀ k, Measurable (G k) := fun k =>
    Measurable.piecewise (measurableSet_goodSet a)
      (ContinuousMap.continuous_postcomp (a k)).measurable measurable_const
  refine measurable_of_tendsto_metrizable' atTop hGmeas (tendsto_pi_nhds.mpr fun ω => ?_)
  by_cases hω : ω ∈ goodSet a
  · have hGω : ∀ k, G k ω = (a k).comp ω := fun k => Set.piecewise_eq_of_mem _ _ _ hω
    simpa only [hGω] using (pathLift_spec hω).1
  · have hGω : ∀ k, G k ω = 0 := fun k => Set.piecewise_eq_of_notMem _ _ _ hω
    rw [pathLift_of_not_mem hω]
    simpa only [hGω] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : C(ℝ≥0, ℝ))) atTop (𝓝 0))

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
