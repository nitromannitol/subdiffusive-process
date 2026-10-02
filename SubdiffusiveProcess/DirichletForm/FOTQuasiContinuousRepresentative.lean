import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousUniform

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
noncomputable section
namespace DirichletForm.FOTConstruction
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- A representative with approximation outside a capacity-null set. -/
structure CoreRepresentative (F : _root_.DirichletForm m) (U : Set X) (u : Lp ℝ 2 m) where
  toFun : X → ℝ
  measurable : Measurable toFun
  ae_rep : ⇑u =ᵐ[m] toFun
  quasiContinuous : ∀ ε : ℝ, 0 < ε → ∃ O : Set X, IsOpen O ∧ O ⊆ U ∧
    coreCapacity F U O < ENNReal.ofReal ε ∧ ContinuousOn toFun (U \ O)
  approx_capacity : ∀ (vn : ℕ → Lp ℝ 2 m), (∀ n, F.toClosedForm.MemCoreOn U (vn n)) →
    ∀ (gn : ℕ → X → ℝ),
      (∀ n, Continuous (gn n) ∧ HasCompactSupport (gn n) ∧ tsupport (gn n) ⊆ U ∧
        ⇑(vn n) =ᵐ[m] gn n) →
      Tendsto (fun n => F.energyNormSq (vn n - u)) atTop (𝓝 0) →
      ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ A : Set X, coreCapacity F U A = 0 ∧
        ∀ x ∉ A, Tendsto (fun n => gn (s n) x) atTop (𝓝 (toFun x))

lemma exists_coreRepresentative [BorelSpace X] (F : _root_.DirichletForm m) {U : Set X}
    (h : Data F U) {u : Lp ℝ 2 m} (hu : u ∈ F.domain) :
    Nonempty (CoreRepresentative F U u) := by
  classical
  obtain ⟨un, fn, hun, hfn, hfast, henergy, hlp⟩ := qc_fast_core_approx F h hu
  let A : ℕ → Set X := fun n => {x | qcRate n < |fn (n + 1) x - fn n x|}
  have hA : ∀ n, coreCapacity F U (A n) ≤ ENNReal.ofReal (2 * qcRate n) := by
    intro n
    apply qc_level_difference hu (hun (n + 1)) (hun n) (hfn (n + 1)) (hfn n) n
      ((hfast (n + 1)).trans (pow_le_pow_left₀ (qcRate_nonneg _) (qcRate_next n) 2)) (hfast n)
  let O : ℕ → Set X := fun N => ⋃ k, A (k + N)
  let Z : Set X := ⋂ N, O N
  obtain ⟨hZ, hcap⟩ := qc_capacity_tail A hA
  have hOpen : ∀ N, IsOpen (O N) := fun N => isOpen_iUnion fun k =>
    isOpen_lt continuous_const (((hfn _).1.sub (hfn _).1).abs)
  have hOU : ∀ N, O N ⊆ U := by
    intro N x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    by_contra hxu
    have hfzero : ∀ n, fn n x = 0 := fun n =>
      image_eq_zero_of_notMem_tsupport (fun hh => hxu ((hfn n).2.2.1 hh))
    have hh : qcRate (k + N) < |fn (k + N + 1) x - fn (k + N) x| := hk
    simp only [hfzero, sub_self, abs_zero] at hh
    exact (qcRate_nonneg _).not_gt hh
  let f : X → ℝ := fun x => limUnder atTop (fun n => fn n x)
  have hlimit : ∀ N, ContinuousOn f (O N)ᶜ ∧ ∀ x ∉ O N,
      Tendsto (fun n => fn n x) atTop (𝓝 (f x)) := by
    intro N
    apply qc_uniform_limit fn (fun n => (hfn n).1)
      (fun n => (hfn n).1.bounded_above_of_compact_support (hfn n).2.1) N (O N)ᶜ
    intro n x hx
    apply le_of_not_gt
    intro hh
    exact hx (mem_iUnion.mpr ⟨n, hh⟩)
  have hfpoint : ∀ x ∉ Z, Tendsto (fun n => fn n x) atTop (𝓝 (f x)) := by
    intro x hx
    obtain ⟨N, hN⟩ := not_forall.mp (fun hh => hx (mem_iInter.mpr hh))
    exact (hlimit N).2 x hN
  have hfae : ⇑u =ᵐ[m] f := by
    have hZm : m Z = 0 := measure_zero_of_coreCapacity_zero F h hZ
    have hZae : ∀ᵐ x ∂m, x ∉ Z := by simpa only [ae_iff, not_not] using hZm
    obtain ⟨s, hs, hsae⟩ := (tendstoInMeasure_of_tendsto_Lp hlp).exists_seq_tendsto_ae
    have heq : ∀ᵐ x ∂m, ∀ n, un (s n) x = fn (s n) x :=
      ae_all_iff.mpr (fun n => (hfn (s n)).2.2.2)
    filter_upwards [hZae, hsae, heq] with x hx hsx heqx
    have hp := (hfpoint x hx).comp hs.tendsto_atTop
    have ht : Tendsto (fun n => fn (s n) x) atTop (𝓝 (u x)) := by
      simpa only [← heqx] using hsx
    exact tendsto_nhds_unique ht hp
  refine ⟨⟨f, ?_, hfae, ?_, ?_⟩⟩
  · exact (StronglyMeasurable.limUnder (fun n => (hfn n).1.stronglyMeasurable)).measurable
  · intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hcap.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε)))
    refine ⟨O N, hOpen N, hOU N, hN N le_rfl, (hlimit N).1.mono ?_⟩
    exact fun x hx => hx.2
  · intro vn hvn gn hgn hve
    obtain ⟨s, hs, hvs⟩ := qc_fast_subsequence F vn hve
    let B : ℕ → Set X := fun n => {x | qcRate n < |gn (s n) x - fn n x|}
    have hB : ∀ n, coreCapacity F U (B n) ≤ ENNReal.ofReal (2 * qcRate n) := fun n =>
      qc_level_difference hu (hvn (s n)) (hun n) (hgn (s n)) (hfn n) n (hvs n) (hfast n)
    let W : Set X := ⋂ N, ⋃ k, B (k + N)
    have hW := (qc_capacity_tail B hB).1
    refine ⟨s, hs, W ∪ Z, ?_, ?_⟩
    · apply le_antisymm _ (zero_le _)
      exact (measure_union_le W Z).trans (by rw [hW, hZ, zero_add])
    · intro x hx
      have hd := qc_small_difference (f := fun n => gn (s n)) (g := fn)
        (fun n => rfl) (x := x) (fun hh => hx (Or.inl hh))
      have hp := hfpoint x (fun hh => hx (Or.inr hh))
      simpa only [sub_add_cancel, zero_add] using hd.add hp

lemma CoreRepresentative.approx_ae [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    {F : _root_.DirichletForm m} {U : Set X} (h : Data F U) (Γ : EnergyFamily F U)
    {u : Lp ℝ 2 m} (q : CoreRepresentative F U u)
    (vn : ℕ → Lp ℝ 2 m) (hvn : ∀ n, F.toClosedForm.MemCoreOn U (vn n))
    (gn : ℕ → X → ℝ)
    (hgn : ∀ n, Continuous (gn n) ∧ HasCompactSupport (gn n) ∧ tsupport (gn n) ⊆ U ∧
      ⇑(vn n) =ᵐ[m] gn n)
    (he : Tendsto (fun n => F.energyNormSq (vn n - u)) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ w ∈ F.domain, ∀ᵐ x ∂Γ.measure w,
      Tendsto (fun n => gn (s n) x) atTop (𝓝 (q.toFun x)) := by
  obtain ⟨s, hs, A, hA, hp⟩ := q.approx_capacity vn hvn gn hgn he
  refine ⟨s, hs, fun w hw => ?_⟩
  have hz := Γ.zero_of_coreCapacity_zero h hA hw
  have hh : ∀ᵐ x ∂Γ.measure w, x ∉ A := by simpa only [ae_iff, not_not] using hz
  exact hh.mono hp

end DirichletForm.FOTConstruction
