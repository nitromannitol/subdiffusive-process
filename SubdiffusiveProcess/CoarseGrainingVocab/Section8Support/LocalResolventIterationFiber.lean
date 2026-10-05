module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationScaling
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

@[expose] public section

/-!
# From row bounds on a countable basis to an almost-everywhere kernel bound

The finite-iteration estimates control `∫⁻ y in B, h x y ∂μ` for each fixed
measurable `B`, but only for almost every `x`, with an exceptional set that
depends on `B`.  On a second-countable Borel space the exceptional sets can be
chosen once and for all along a countable basis, and outer regularity upgrades
the resulting bound from open sets to every measurable set.  This yields the
almost-everywhere bound on the product measure.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationFiber

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

/-- A bound on the finite unions of a basis extends to every open set. -/
theorem setLIntegral_open_le {μ : Measure X} {h : X → ℝ≥0∞} (hh : Measurable h)
    {M : ℝ≥0∞} (e : ℕ → Set X) (he : ∀ i, IsOpen (e i))
    (hfin : ∀ F : Finset ℕ, (∫⁻ y in ⋃ i ∈ F, e i, h y ∂μ) ≤ M * μ (⋃ i ∈ F, e i))
    (V : Set X) (hV : IsOpen V) (hbasis : ∀ x ∈ V, ∃ i, x ∈ e i ∧ e i ⊆ V) :
    (∫⁻ y in V, h y ∂μ) ≤ M * μ V := by
  classical
  set F : ℕ → Finset ℕ := fun n => (Finset.range n).filter (fun i => e i ⊆ V) with hF
  set A : ℕ → Set X := fun n => ⋃ i ∈ F n, e i with hA
  have hAmeas : ∀ n, MeasurableSet (A n) := by
    intro n
    exact (Finset.measurableSet_biUnion _ (fun i _ => (he i).measurableSet))
  have hmemF : ∀ k j : ℕ, j ∈ F k ↔ j < k ∧ e j ⊆ V := by
    intro k j
    rw [hF]
    simp only [Finset.mem_filter, Finset.mem_range]
  have hAmono : Monotone A := by
    intro m n hmn
    refine Set.iUnion₂_subset fun i hi => ?_
    have hi' := (hmemF m i).mp hi
    exact Set.subset_biUnion_of_mem (u := fun i => e i)
      ((hmemF n i).mpr ⟨lt_of_lt_of_le hi'.1 hmn, hi'.2⟩)
  have hAsub : ∀ n, A n ⊆ V := by
    intro n
    refine Set.iUnion₂_subset fun i hi => ?_
    exact ((hmemF n i).mp hi).2
  have hunion : ⋃ n, A n = V := by
    apply Set.Subset.antisymm (Set.iUnion_subset hAsub)
    intro x hx
    obtain ⟨i, hxi, hiV⟩ := hbasis x hx
    refine Set.mem_iUnion.mpr ⟨i + 1, ?_⟩
    exact Set.mem_biUnion (s := F (i+1)) ((hmemF (i+1) i).mpr ⟨Nat.lt_succ_self i, hiV⟩) hxi
  have hsupind : (fun y => V.indicator h y) = fun y => ⨆ n, (A n).indicator h y := by
    funext y
    by_cases hy : y ∈ V
    · rw [Set.indicator_of_mem hy]
      rw [← hunion] at hy
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      apply le_antisymm
      · exact le_iSup_of_le n (by rw [Set.indicator_of_mem hn])
      · refine iSup_le fun m => ?_
        by_cases hm : y ∈ A m
        · rw [Set.indicator_of_mem hm]
        · rw [Set.indicator_of_notMem hm]
          exact zero_le
    · rw [Set.indicator_of_notMem hy]
      refine (le_antisymm (iSup_le fun m => ?_) (zero_le)).symm
      rw [Set.indicator_of_notMem (fun hc => hy (hAsub m hc))]
  calc
    (∫⁻ y in V, h y ∂μ) = ∫⁻ y, V.indicator h y ∂μ :=
      (lintegral_indicator hV.measurableSet h).symm
    _ = ∫⁻ y, ⨆ n, (A n).indicator h y ∂μ := by rw [hsupind]
    _ = ⨆ n, ∫⁻ y, (A n).indicator h y ∂μ := by
        refine lintegral_iSup (fun n => hh.indicator (hAmeas n)) ?_
        intro m n hmn y
        show (A m).indicator h y ≤ (A n).indicator h y
        by_cases hy : y ∈ A m
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hAmono hmn hy)]
        · rw [Set.indicator_of_notMem hy]
          exact zero_le
    _ = ⨆ n, ∫⁻ y in A n, h y ∂μ := by
        exact iSup_congr fun n => lintegral_indicator (hAmeas n) h
    _ ≤ ⨆ n, M * μ (A n) := iSup_mono fun n => hfin (F n)
    _ = M * ⨆ n, μ (A n) := (ENNReal.mul_iSup _ _).symm
    _ = M * μ V := by rw [← hAmono.measure_iUnion, hunion]

omit [OpensMeasurableSpace X] in
/-- Outer regularity upgrades an open-set bound to every set. -/
theorem setLIntegral_le_of_open {μ : Measure X} [μ.OuterRegular] [IsFiniteMeasure μ]
    {h : X → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hopen : ∀ V : Set X, IsOpen V → (∫⁻ y in V, h y ∂μ) ≤ M * μ V)
    (B : Set X) : (∫⁻ y in B, h y ∂μ) ≤ M * μ B := by
  rcases eq_or_ne M 0 with rfl | hM0
  · calc
      (∫⁻ y in B, h y ∂μ) ≤ ∫⁻ y in univ, h y ∂μ :=
        lintegral_mono' (Measure.restrict_mono (subset_univ B) le_rfl) le_rfl
      _ ≤ 0 * μ univ := hopen univ isOpen_univ
      _ = 0 * μ B := by simp
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  have hlt : μ B < c / M := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hM0) (Or.inl hM)]
    rwa [mul_comm] at hc
  obtain ⟨V, hBV, hVo, hV⟩ := B.exists_isOpen_lt_of_lt (c / M) hlt
  calc
    (∫⁻ y in B, h y ∂μ) ≤ ∫⁻ y in V, h y ∂μ :=
      lintegral_mono' (Measure.restrict_mono hBV le_rfl) le_rfl
    _ ≤ M * μ V := hopen V hVo
    _ ≤ M * (c / M) := mul_le_mul_right hV.le M
    _ = c := ENNReal.mul_div_cancel hM0 hM

/-- Row bounds valid for each measurable set, up to a set-dependent null set of rows, give an
almost-everywhere bound of the kernel on the product measure. -/
theorem ae_prod_le_of_forall_setLIntegral_le [SecondCountableTopology X]
    {nu mu : Measure X} [SFinite nu] [IsFiniteMeasure mu] [mu.OuterRegular]
    {h : X → X → ℝ≥0∞} (hh : Measurable (Function.uncurry h)) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hyp : ∀ B : Set X, MeasurableSet B → ∀ᵐ x ∂nu, (∫⁻ y in B, h x y ∂mu) ≤ M * mu B) :
    ∀ᵐ z ∂(nu.prod mu), h z.1 z.2 ≤ M := by
  classical
  obtain ⟨e, he⟩ := (Set.Countable.insert ∅ (TopologicalSpace.countable_countableBasis X)).exists_eq_range
    ⟨∅, Set.mem_insert _ _⟩
  have hmemE : ∀ i, e i ∈ insert (∅ : Set X) (TopologicalSpace.countableBasis X) := by
    intro i
    rw [he]
    exact Set.mem_range_self i
  have heopen : ∀ i, IsOpen (e i) := by
    intro i
    rcases hmemE i with h0 | hb
    · rw [h0]; exact isOpen_empty
    · exact TopologicalSpace.isBasis_countableBasis X |>.isOpen hb
  have heball : ∀ V : Set X, IsOpen V → ∀ x ∈ V, ∃ i, x ∈ e i ∧ e i ⊆ V := by
    intro V hV x hx
    obtain ⟨b, hb, hxb, hbV⟩ :=
      (TopologicalSpace.isBasis_countableBasis X).exists_subset_of_mem_open hx hV
    have : b ∈ Set.range e := by
      rw [← he]
      exact Set.mem_insert_of_mem _ hb
    obtain ⟨i, hi⟩ := this
    exact ⟨i, hi ▸ hxb, hi ▸ hbV⟩
  have hmeasA : ∀ F : Finset ℕ, MeasurableSet (⋃ i ∈ F, e i) :=
    fun F => Finset.measurableSet_biUnion _ (fun i _ => (heopen i).measurableSet)
  have hall : ∀ᵐ x ∂nu, ∀ F : Finset ℕ,
      (∫⁻ y in ⋃ i ∈ F, e i, h x y ∂mu) ≤ M * mu (⋃ i ∈ F, e i) :=
    (ae_all_iff).mpr (fun F => hyp _ (hmeasA F))
  have hrow : ∀ᵐ x ∂nu, ∀ᵐ y ∂mu, h x y ≤ M := by
    filter_upwards [hall] with x hx
    have hhx : Measurable (h x) := hh.comp (measurable_const.prodMk measurable_id)
    have hopen : ∀ V : Set X, IsOpen V → (∫⁻ y in V, h x y ∂mu) ≤ M * mu V :=
      fun V hV => setLIntegral_open_le hhx e heopen hx V hV (heball V hV)
    have hgen : ∀ B : Set X, (∫⁻ y in B, h x y ∂mu) ≤ M * mu B :=
      fun B => setLIntegral_le_of_open hM hopen B
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hhx (g := fun _ => M) ?_
    intro s hs _
    rw [setLIntegral_const]
    exact hgen s
  have hset : MeasurableSet {z : X × X | h z.1 z.2 ≤ M} :=
    measurableSet_le hh measurable_const
  exact (Measure.ae_prod_iff_ae_ae hset).mpr hrow

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationFiber
