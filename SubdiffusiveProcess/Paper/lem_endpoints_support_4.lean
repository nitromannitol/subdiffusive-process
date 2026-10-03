module

public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_endpoints_support_2
public import SubdiffusiveProcess.Paper.lem_endpoints_support_3
public import SubdiffusiveProcess.Paper.lem_endpoints_zero_one

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ContDiff
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Paper
section Resample
variable {d : ℕ} (S : Finset ℤ) (om1 om2 : BilateralField d)

theorem aux_lem_endpoints_support_4_endpoint_invariance_H_shift
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hom1 : Tendsto (infraredPartialSum om1) atTop (𝓝 (H om1)))
    (hom' : Tendsto (infraredPartialSum (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2))
      atTop (𝓝 (H (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2)))) :
    H (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2) =
      H om1 + aux_lem_endpoints_support_3_endpoint_invariance_Dpos S om1 om2 := by
  have hcongr : (fun L => infraredPartialSum (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2) L)
      =ᶠ[atTop] fun L => infraredPartialSum om1 L + aux_lem_endpoints_support_3_endpoint_invariance_Dpos S om1 om2 := by
    filter_upwards [Filter.eventually_ge_atTop (aux_lem_endpoints_support_3_endpoint_invariance_L0 S)] with L hL
    rw [← lem_endpoints_support_3 S om1 om2 hL]
    abel
  have htarget : Tendsto (fun L => infraredPartialSum om1 L +
      aux_lem_endpoints_support_3_endpoint_invariance_Dpos S om1 om2) atTop
      (𝓝 (H om1 + aux_lem_endpoints_support_3_endpoint_invariance_Dpos S om1 om2)) :=
    hom1.add tendsto_const_nhds
  exact tendsto_nhds_unique hom' (htarget.congr' hcongr.symm)

noncomputable def aux_lem_endpoints_support_4_endpoint_invariance_weight : C(SpatialCoordinates d, ℝ) :=
  aux_lem_endpoints_support_3_endpoint_invariance_Dpos S om1 om2 + aux_lem_endpoints_support_3_endpoint_invariance_Dneg S om1 om2

theorem aux_lem_endpoints_support_4_endpoint_invariance_cutoffPotential_eq
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHshift : H (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2) =
      H om1 + aux_lem_endpoints_support_3_endpoint_invariance_Dpos S om1 om2)
    {N : ℕ} (hN : aux_lem_endpoints_support_3_endpoint_invariance_N0 S ≤ N) (x : SpatialCoordinates d) :
    cutoffPotential H (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2) N x =
      cutoffPotential H om1 N x + aux_lem_endpoints_support_4_endpoint_invariance_weight S om1 om2 x := by
  have hstable_x := DFunLike.congr_fun
    (aux_lem_endpoints_support_3_endpoint_invariance_cutoffSum_stable S om1 om2 hN) x
  rw [aux_lem_endpoints_support_3_endpoint_invariance_coe_sum] at hstable_x
  simp only [ContinuousMap.sub_apply] at hstable_x
  have hHx := DFunLike.congr_fun hHshift x
  rw [ContinuousMap.add_apply] at hHx
  show H (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2) x +
        ∑ j ∈ Finset.range (N + 1),
          (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2 (-((j : ℕ) : ℤ))) x =
      H om1 x + (∑ j ∈ Finset.range (N + 1), (om1 (-((j : ℕ) : ℤ))) x) +
        (aux_lem_endpoints_support_4_endpoint_invariance_weight S om1 om2) x
  unfold aux_lem_endpoints_support_4_endpoint_invariance_weight
  rw [ContinuousMap.add_apply, hHx]
  have hsum : ∑ j ∈ Finset.range (N + 1), (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2
        (-((j : ℕ) : ℤ))) x =
      (∑ j ∈ Finset.range (N + 1), (om1 (-((j : ℕ) : ℤ))) x) +
        (aux_lem_endpoints_support_3_endpoint_invariance_Dneg S om1 om2) x := by
    rw [← hstable_x, Finset.sum_sub_distrib]
    ring
  rw [hsum]
  ring

theorem aux_lem_endpoints_support_4_endpoint_invariance_cutoffCoefficient_eq
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHshift : H (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2) =
      H om1 + aux_lem_endpoints_support_3_endpoint_invariance_Dpos S om1 om2)
    {N : ℕ} (hN : aux_lem_endpoints_support_3_endpoint_invariance_N0 S ≤ N) (x : SpatialCoordinates d) :
    cutoffCoefficient M H (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2) N x =
      Real.exp (aux_lem_endpoints_support_4_endpoint_invariance_weight S om1 om2 x) *
        cutoffCoefficient M H om1 N x := by
  have hpot := aux_lem_endpoints_support_4_endpoint_invariance_cutoffPotential_eq S om1 om2 H hHshift hN x
  unfold cutoffCoefficient
  rw [hpot]
  have hexp : Real.exp
      ((cutoffPotential H om1 N x + aux_lem_endpoints_support_4_endpoint_invariance_weight S om1 om2 x) -
        ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      Real.exp (aux_lem_endpoints_support_4_endpoint_invariance_weight S om1 om2 x) *
        Real.exp (cutoffPotential H om1 N x - ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

theorem aux_lem_endpoints_support_4_endpoint_invariance_cutoffPositiveCoefficient_eq
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHshift : H (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2) =
      H om1 + aux_lem_endpoints_support_3_endpoint_invariance_Dpos S om1 om2)
    {N : ℕ} (hN : aux_lem_endpoints_support_3_endpoint_invariance_N0 S ≤ N)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ hx : x ∈ centeredCube z r hr,
        (Lane4.cutoffPositiveCoefficient M H
            (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2) N z hr).val x =
          Real.exp (aux_lem_endpoints_support_4_endpoint_invariance_weight S om1 om2 x) *
            (Lane4.cutoffPositiveCoefficient M H om1 N z hr).val x := by
  have h1 := normalizedContinuousPositiveCoefficient_coeFn (Ω := centeredCube z r hr)
    (hΩ := ⟨centeredCube_subset_closedCube z hr⟩)
    (closedCube z r hr) (Lane4.cutoffCoefficientCM M H om1 N z hr)
    (Lane4.cutoffCoefficientCM_pos M H om1 N z hr) 1 one_pos
  have h2 := normalizedContinuousPositiveCoefficient_coeFn (Ω := centeredCube z r hr)
    (hΩ := ⟨centeredCube_subset_closedCube z hr⟩)
    (closedCube z r hr) (Lane4.cutoffCoefficientCM M H
      (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2) N z hr)
    (Lane4.cutoffCoefficientCM_pos M H
      (aux_lem_endpoints_support_3_endpoint_invariance_resample S om1 om2) N z hr) 1 one_pos
  unfold Lane4.cutoffPositiveCoefficient
  filter_upwards [h1, h2] with x hx1 hx2 hx
  rw [hx2 hx, hx1 hx, div_one, div_one]
  exact aux_lem_endpoints_support_4_endpoint_invariance_cutoffCoefficient_eq S om1 om2 M H hHshift hN x

end Resample

section Measure
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)] (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)

theorem aux_lem_endpoints_support_4_endpoint_invariance_resample_measurePreserving (S : Finset ℤ) :
    MeasurePreserving (fun z : BilateralField d × BilateralField d =>
        aux_lem_endpoints_support_3_endpoint_invariance_resample S z.1 z.2)
      (((chaosSampleLaw model).toMeasure).prod ((chaosSampleLaw model).toMeasure))
      (chaosSampleLaw model).toMeasure := by
  have h := aux_lem_endpoints_resample_preserving
    (Y := fun _ : ℤ => C(SpatialCoordinates d, ℝ))
    (fun j => (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure) S
  simpa only [aux_lem_endpoints_support_3_endpoint_invariance_resample, chaosSampleLaw, commonScaleLaw] using! h

theorem aux_lem_endpoints_support_4_endpoint_invariance_ae_resample (S : Finset ℤ)
    {p : BilateralField d → Prop}
    (hp : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, p omega) :
    ∀ᵐ z ∂(((chaosSampleLaw model).toMeasure).prod ((chaosSampleLaw model).toMeasure)),
      p (aux_lem_endpoints_support_3_endpoint_invariance_resample S z.1 z.2) := by
  have hmp := aux_lem_endpoints_support_4_endpoint_invariance_resample_measurePreserving model S
  have h : ∀ᵐ y ∂(((chaosSampleLaw model).toMeasure).prod
      ((chaosSampleLaw model).toMeasure)).map
        (fun z => aux_lem_endpoints_support_3_endpoint_invariance_resample S z.1 z.2), p y := by
    rw [hmp.map_eq]; exact hp
  exact ae_of_ae_map hmp.measurable.aemeasurable h

end Measure


theorem aux_lem_endpoints_support_4_forall_le_of_dense {E : Type*} [TopologicalSpace E]
    (φ : E → ℝ) (hφ : Continuous φ) (D : Set E) (hD : Dense D) (c : ℝ)
    (h : ∀ g ∈ D, φ g ≤ c) : ∀ g, φ g ≤ c := by
  have hcl : IsClosed {g : E | φ g ≤ c} := isClosed_le hφ continuous_const
  have hsub : closure D ⊆ {g : E | φ g ≤ c} := hcl.closure_subset_iff.mpr h
  intro g
  exact hsub (hD.closure_eq ▸ Set.mem_univ g)

theorem aux_lem_endpoints_support_4_opNorm_measurable {X : Type*} [MeasurableSpace X]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SeparableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : X → E →L[ℝ] F) (hT : ∀ f : E, StronglyMeasurable (fun x => T x f)) :
    Measurable (fun x => ‖T x‖) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense E
  haveI : Countable D := hDc.to_subtype
  refine measurable_of_Iic (fun c => ?_)
  by_cases hc : c < 0
  · have h0 : (fun x : X => ‖T x‖) ⁻¹' Iic c = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Set.mem_preimage, Set.mem_Iic] at hx
      exact absurd (le_trans (norm_nonneg (T x)) hx) hc.not_ge
    rw [h0]
    exact MeasurableSet.empty
  · push_neg at hc
    have h1 : (fun x : X => ‖T x‖) ⁻¹' Iic c
        = ⋂ f : D, (fun x : X => ‖T x (f : E)‖) ⁻¹' Iic (c * ‖(f : E)‖) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter]
      constructor
      · intro hx f
        calc ‖T x (f : E)‖ ≤ ‖T x‖ * ‖(f : E)‖ := ContinuousLinearMap.le_opNorm (T x) (f : E)
          _ ≤ c * ‖(f : E)‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg (f : E))
      · intro hx
        refine ContinuousLinearMap.opNorm_le_bound (T x) hc (fun y => ?_)
        have hclosed : IsClosed {y : E | ‖T x y‖ ≤ c * ‖y‖} :=
          isClosed_le (T x).continuous.norm (continuous_const.mul continuous_norm)
        have hsub : D ⊆ {y : E | ‖T x y‖ ≤ c * ‖y‖} := fun f hf => hx ⟨f, hf⟩
        have hclo : closure D ⊆ {y : E | ‖T x y‖ ≤ c * ‖y‖} :=
          (IsClosed.closure_subset_iff hclosed).mpr hsub
        have hyc : y ∈ closure D := by
          rw [hDd.closure_eq]
          exact Set.mem_univ y
        exact hclo hyc
    rw [h1]
    apply MeasurableSet.iInter
    intro f
    exact measurableSet_le ((hT (f : E)).norm.measurable) measurable_const

theorem aux_lem_endpoints_support_4_cauchySeq_measurableSet {X : Type*} [MeasurableSpace X]
    {M : Type*} [PseudoMetricSpace M]
    (g : ℕ → X → M) (hg : ∀ m n, Measurable (fun x => dist (g m x) (g n x))) :
    MeasurableSet {x | CauchySeq (fun n => g n x)} := by
  have h_eq : {x : X | CauchySeq fun n => g n x} =
      ⋂ k : ℕ, ⋃ N : ℕ, ⋂ m : ℕ, ⋂ n : ℕ,
        {x : X | N ≤ m → N ≤ n → dist (g m x) (g n x) < 1 / ((k:ℝ)+1)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    rw [Metric.cauchySeq_iff]
    constructor
    · intro h k
      obtain ⟨N, hN⟩ := h (1 / ((k:ℝ)+1)) Nat.one_div_pos_of_nat
      exact ⟨N, fun m n hm hn => hN m hm n hn⟩
    · intro h ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨N, hN⟩ := h k
      exact ⟨N, fun m hm n hn => lt_trans (hN m n hm hn) hk⟩
  rw [h_eq]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iInter
  intro n
  by_cases h : N ≤ m ∧ N ≤ n
  · have heq : {x : X | N ≤ m → N ≤ n → dist (g m x) (g n x) < 1 / ((k:ℝ)+1)}
        = {x : X | dist (g m x) (g n x) < 1 / ((k:ℝ)+1)} := by
      ext x
      simp only [Set.mem_setOf_eq]
      have : (N ≤ m → N ≤ n → dist (g m x) (g n x) < 1 / ((k:ℝ)+1))
          ↔ (dist (g m x) (g n x) < 1 / ((k:ℝ)+1)) := by
        constructor
        · intro hh; exact hh h.1 h.2
        · intro hh _ _; exact hh
      exact this
    rw [heq]
    exact measurableSet_lt (hg m n) measurable_const
  · have heq : {x : X | N ≤ m → N ≤ n → dist (g m x) (g n x) < 1 / ((k:ℝ)+1)} = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro hm hn
      exact absurd ⟨hm, hn⟩ h
    rw [heq]
    exact MeasurableSet.univ

theorem aux_lem_endpoints_support_4_limUnder_apply_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℕ → X → E →L[ℝ] F) (hg : ∀ n f, StronglyMeasurable (fun x => g n x f))
    (A : Set X) (hA : MeasurableSet A)
    (hconv : ∀ x ∈ A, ∃ L, Tendsto (fun n => g n x) atTop (𝓝 L)) (f : E) :
    StronglyMeasurable
      (fun x => (A.indicator (fun x => limUnder atTop (fun n => g n x)) x) f) := by
  apply stronglyMeasurable_of_tendsto (u := atTop)
    (f := fun n => A.indicator (fun x => g n x f))
    (g := fun x => (A.indicator (fun x => limUnder atTop (fun n => g n x)) x) f)
  · intro n
    exact (hg n f).indicator hA
  · rw [tendsto_pi_nhds]
    intro x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      have h := tendsto_nhds_limUnder (hconv x hx)
      have h2 := ((ContinuousLinearMap.apply ℝ F f).continuous.tendsto _).comp h
      simpa [ContinuousLinearMap.apply_apply] using! h2
    · simp only [Set.indicator_of_notMem hx, ContinuousLinearMap.zero_apply]
      exact tendsto_const_nhds

theorem aux_lem_endpoints_support_4_sSup_aemeasurable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : X → Set ℝ) (T : Set X) (hT : MeasurableSet T) (hTae : ∀ᵐ x ∂μ, x ∈ T)
    (hdown : ∀ x ∈ T, ∀ a ∈ L x, ∀ b : ℝ, b ≤ a → b ∈ L x)
    (hne : ∀ x ∈ T, (L x).Nonempty) (hbdd : ∀ x ∈ T, BddAbove (L x))
    (hq : ∀ q : ℚ, MeasurableSet {x | x ∈ T ∧ (q : ℝ) ∈ L x}) :
    AEMeasurable (fun x => sSup (L x)) μ := by
  classical
  have key : ∀ x ∈ T, ∀ c : ℝ, c < sSup (L x) ↔ ∃ q : ℚ, c < (q:ℝ) ∧ (q:ℝ) ∈ L x := by
    intro x hx c
    constructor
    · intro hc
      obtain ⟨b, hbL, hcb⟩ := (lt_csSup_iff (hbdd x hx) (hne x hx)).mp hc
      obtain ⟨q, hcq, hqb⟩ := exists_rat_btwn hcb
      exact ⟨q, hcq, hdown x hx b hbL (q:ℝ) (le_of_lt hqb)⟩
    · rintro ⟨q, hcq, hqL⟩
      exact lt_of_lt_of_le hcq (le_csSup (hbdd x hx) hqL)
  have hmem : ∀ x ∈ T, (T.indicator (fun y => sSup (L y))) x = sSup (L x) :=
    fun x hx => Set.indicator_of_mem hx _
  have hnotmem : ∀ x, x ∉ T → (T.indicator (fun y => sSup (L y))) x = 0 :=
    fun x hx => Set.indicator_of_notMem hx _
  have hmeas : Measurable (T.indicator fun y => sSup (L y)) := by
    apply measurable_of_Ioi
    intro c
    have hset : (T.indicator fun y => sSup (L y)) ⁻¹' Ioi c =
        (⋃ q : ℚ, {x : X | x ∈ T ∧ c < (q:ℝ) ∧ (q:ℝ) ∈ L x}) ∪ (Tᶜ ∩ {x : X | c < 0}) := by
      ext x
      by_cases hx : x ∈ T
      · rw [Set.mem_preimage, Set.mem_Ioi, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
          Set.mem_compl_iff, Set.mem_setOf_eq, hmem x hx]
        rw [key x hx c]
        exact ⟨fun ⟨q, hcq, hqL⟩ => Or.inl ⟨q, hx, hcq, hqL⟩,
          fun h' => h'.elim (fun ⟨q, _, hcq, hqL⟩ => ⟨q, hcq, hqL⟩) (fun ⟨hx', _⟩ => absurd hx hx')⟩
      · rw [Set.mem_preimage, Set.mem_Ioi, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
          Set.mem_compl_iff, Set.mem_setOf_eq, hnotmem x hx]
        exact ⟨fun hc0 => Or.inr ⟨hx, hc0⟩,
          fun h' => h'.elim (fun ⟨_, hxT, _, _⟩ => absurd hxT hx) (fun ⟨_, hc0⟩ => hc0)⟩
    rw [hset]
    refine MeasurableSet.union ?_ ?_
    · refine MeasurableSet.iUnion ?_
      intro q
      by_cases hcq : c < (q:ℝ)
      · have hq' : {x : X | x ∈ T ∧ c < (q:ℝ) ∧ (q:ℝ) ∈ L x} = {x : X | x ∈ T ∧ (q:ℝ) ∈ L x} := by
          ext x
          exact ⟨fun ⟨hxT, _, hqL⟩ => ⟨hxT, hqL⟩, fun ⟨hxT, hqL⟩ => ⟨hxT, hcq, hqL⟩⟩
        rw [hq']
        exact hq q
      · have hq' : {x : X | x ∈ T ∧ c < (q:ℝ) ∧ (q:ℝ) ∈ L x} = ∅ := by
          ext x
          exact ⟨fun ⟨_, hc', _⟩ => absurd hc' hcq, fun h' => absurd h' (Set.notMem_empty x)⟩
        rw [hq']
        exact MeasurableSet.empty
    · refine MeasurableSet.inter hT.compl ?_
      by_cases hc : c < (0:ℝ)
      · have hz : {x : X | c < (0:ℝ)} = Set.univ := by
          ext x
          exact ⟨fun _ => Set.mem_univ x, fun _ => hc⟩
        rw [hz]
        exact MeasurableSet.univ
      · have hz : {x : X | c < (0:ℝ)} = ∅ := by
          ext x
          exact ⟨fun h' => absurd h' hc, fun h' => absurd h' (Set.notMem_empty x)⟩
        rw [hz]
        exact MeasurableSet.empty
  have hcongr : (T.indicator fun y => sSup (L y)) =ᶠ[ae μ] fun x => sSup (L x) := by
    filter_upwards [hTae] with x hx
    exact hmem x hx
  exact AEMeasurable.congr hmeas.aemeasurable hcongr

theorem aux_lem_endpoints_support_4_sInf_aemeasurable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (U : X → Set ℝ) (T : Set X) (hT : MeasurableSet T) (hTae : ∀ᵐ x ∂μ, x ∈ T)
    (hup : ∀ x ∈ T, ∀ a ∈ U x, ∀ b : ℝ, a ≤ b → b ∈ U x)
    (hne : ∀ x ∈ T, (U x).Nonempty) (hbdd : ∀ x ∈ T, BddBelow (U x))
    (hq : ∀ q : ℚ, MeasurableSet {x | x ∈ T ∧ (q : ℝ) ∈ U x}) :
    AEMeasurable (fun x => sInf (U x)) μ := by
  have hclaim : ∀ x ∈ T, ∀ c : ℝ, sInf (U x) < c ↔ ∃ q : ℚ, (q : ℝ) < c ∧ (q : ℝ) ∈ U x := by
    intro x hx c
    constructor
    · intro hlt
      obtain ⟨b, hbU, hbc⟩ := (csInf_lt_iff (hbdd x hx) (hne x hx)).mp hlt
      obtain ⟨q, hbq, hqc⟩ := exists_rat_btwn hbc
      exact ⟨q, hqc, hup x hx b hbU q (le_of_lt hbq)⟩
    · rintro ⟨q, hqc, hqU⟩
      exact lt_of_le_of_lt (csInf_le (hbdd x hx) hqU) hqc
  have hmeas : Measurable (T.indicator fun x => sInf (U x)) := by
    apply measurable_of_Iio
    intro c
    have hM : ∀ x : X,
        (x ∈ (⋃ q : {q : ℚ // (q : ℝ) < c}, {y | y ∈ T ∧ (q : ℝ) ∈ U y}) ∪
            (Tᶜ ∩ {y : X | (0 : ℝ) < c})) ↔
        (∃ q : {q : ℚ // (q : ℝ) < c}, x ∈ T ∧ (q : ℝ) ∈ U x) ∨ (x ∉ T ∧ (0 : ℝ) < c) := by
      intro x
      refine (Set.mem_union x _ _).trans (or_congr ?_ ?_)
      · exact (Set.mem_iUnion (s := fun q : {q : ℚ // (q : ℝ) < c} =>
          {y | y ∈ T ∧ (q : ℝ) ∈ U y})).trans (exists_congr fun q => Set.mem_setOf)
      · exact (Set.mem_inter_iff x Tᶜ {y : X | (0 : ℝ) < c}).trans
          (and_congr (Set.mem_compl_iff T x) Set.mem_setOf)
    have hset : (T.indicator fun x => sInf (U x)) ⁻¹' Iio c =
        (⋃ q : {q : ℚ // (q : ℝ) < c}, {x | x ∈ T ∧ (q : ℝ) ∈ U x}) ∪
          (Tᶜ ∩ {x : X | (0 : ℝ) < c}) := by
      ext x
      by_cases hx : x ∈ T
      · rw [Set.mem_preimage, Set.mem_Iio, Set.indicator_of_mem hx (fun x => sInf (U x))]
        constructor
        · intro hlt
          obtain ⟨q, hqc, hqU⟩ := (hclaim x hx c).mp hlt
          exact (hM x).mpr (Or.inl ⟨⟨q, hqc⟩, hx, hqU⟩)
        · intro hxm
          rcases (hM x).mp hxm with ⟨q, -, hqU⟩ | ⟨hnx, -⟩
          · exact (hclaim x hx c).mpr ⟨q.1, q.2, hqU⟩
          · exact absurd hx hnx
      · rw [Set.mem_preimage, Set.mem_Iio, Set.indicator_of_notMem hx (fun x => sInf (U x))]
        constructor
        · intro h
          exact (hM x).mpr (Or.inr ⟨hx, h⟩)
        · intro hxm
          rcases (hM x).mp hxm with ⟨q, hqT, -⟩ | ⟨-, h⟩
          · exact absurd hqT hx
          · exact h
    rw [hset]
    refine MeasurableSet.union ?_ ?_
    · refine MeasurableSet.iUnion ?_
      intro q
      exact hq (q : ℚ)
    · refine MeasurableSet.inter hT.compl ?_
      by_cases h0 : (0 : ℝ) < c
      · rw [show {x : X | (0 : ℝ) < c} = univ from by ext x; simp [h0]]
        exact MeasurableSet.univ
      · rw [show {x : X | (0 : ℝ) < c} = ∅ from by ext x; simp [h0]]
        exact MeasurableSet.empty
  have hfin : (T.indicator fun x => sInf (U x)) =ᵐ[μ] (fun x => sInf (U x)) := by
    filter_upwards [hTae] with x hx
    exact Set.indicator_of_mem hx (fun x => sInf (U x))
  exact hmeas.aemeasurable.congr hfin

theorem aux_lem_endpoints_support_4_ae_mem_of_map {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Measure X) (field : Ω → X) (hf : Measurable field)
    (hmap : Measure.map field P = μ) (A : Set X) (hA : MeasurableSet A)
    (h : ∀ᵐ omega ∂P, field omega ∈ A) : ∀ᵐ x ∂μ, x ∈ A := by
  subst hmap
  exact (ae_map_iff hf.aemeasurable (by simpa using hA)).2 h

theorem aux_lem_endpoints_support_4_indicator_limit_tendsto {X : Type*}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : ℕ → X → E →L[ℝ] F) (A : Set X) (x : X) (hx : x ∈ A)
    (hc : CauchySeq (fun n => g n x)) :
    Tendsto (fun n => g n x) atTop
      (𝓝 (A.indicator (fun y => limUnder atTop (fun n => g n y)) x)) := by
  rw [Set.indicator_of_mem hx]
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hc)

noncomputable def aux_lem_endpoints_support_4_seq {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (i : ℕ) : ℕ → DomainL2 (centeredCube (z i) (r i) (hr i)) :=
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  denseSeq (DomainL2 (centeredCube (z i) (r i) (hr i)))

theorem aux_lem_endpoints_support_4_seq_dense {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (i : ℕ) : DenseRange (aux_lem_endpoints_support_4_seq z r hr i) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  exact denseRange_denseSeq _

def aux_lem_endpoints_support_4_upperTest {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (a : ℝ) (omega : Ω) : Prop :=
  ∀ i k l : ℕ,
    2 * inner ℝ (aux_lem_endpoints_support_4_seq z r hr i l) (GE i omega (aux_lem_endpoints_support_4_seq z r hr i k)) -
        inner ℝ (aux_lem_endpoints_support_4_seq z r hr i l) (GF i omega (aux_lem_endpoints_support_4_seq z r hr i l)) ≤
      a * inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GE i omega (aux_lem_endpoints_support_4_seq z r hr i k))

def aux_lem_endpoints_support_4_goodSeq {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (C0 : ℝ) (omega : Ω) : Prop :=
  (∀ i k l : ℕ,
    inner ℝ (GE i omega (aux_lem_endpoints_support_4_seq z r hr i k)) (aux_lem_endpoints_support_4_seq z r hr i l) =
        inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GE i omega (aux_lem_endpoints_support_4_seq z r hr i l)) ∧
      inner ℝ (GF i omega (aux_lem_endpoints_support_4_seq z r hr i k)) (aux_lem_endpoints_support_4_seq z r hr i l) =
        inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GF i omega (aux_lem_endpoints_support_4_seq z r hr i l))) ∧
  (∀ i k : ℕ,
    0 ≤ inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GE i omega (aux_lem_endpoints_support_4_seq z r hr i k)) ∧
      0 ≤ inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GF i omega (aux_lem_endpoints_support_4_seq z r hr i k))) ∧
  aux_lem_endpoints_support_4_upperTest z r hr GE GF C0 omega ∧
  aux_lem_endpoints_support_4_upperTest z r hr GF GE C0 omega ∧
  (∃ i k : ℕ,
    0 < inner ℝ (aux_lem_endpoints_support_4_seq z r hr i k) (GE i omega (aux_lem_endpoints_support_4_seq z r hr i k)))

theorem aux_lem_endpoints_support_4_formLe_iff_dense {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hsym : ∀ x y : DomainL2 Q, inner ℝ (GE x) y = inner ℝ x (GE y))
    (hpos : ∀ x : DomainL2 Q, 0 ≤ inner ℝ x (GE x))
    (D : Set (DomainL2 Q)) (hD : Dense D) (a : ℝ) (ha : 0 ≤ a) :
    (∀ u ∈ limitFormDomain GE,
        limitFormEnergy GF u ≤ ((a * (limitFormEnergy GE u).toReal : ℝ) : EReal)) ↔
      ∀ f ∈ D, ∀ g ∈ D,
        2 * inner ℝ g (GE f) - inner ℝ g (GF g) ≤ a * inner ℝ f (GE f) := by
  constructor
  · intro h f hf g hg
    have hEf : limitFormEnergy GE (GE f) = ((inner ℝ f (GE f) : ℝ) : EReal) :=
      aux_lem_endpoints_support_3_energy_range GE hsym hpos f
    have hmem : GE f ∈ limitFormDomain GE := by
      change limitFormEnergy GE (GE f) < ⊤
      rw [hEf]
      exact EReal.coe_lt_top _
    have h1 := h (GE f) hmem
    have hval : (limitFormEnergy GE (GE f)).toReal = inner ℝ f (GE f) := by
      rw [hEf, EReal.toReal_coe]
    rw [hval] at h1
    have h2 : ((2 * inner ℝ g (GE f) - inner ℝ g (GF g) : ℝ) : EReal) ≤
        limitFormEnergy GF (GE f) :=
      le_iSup (fun w : DomainL2 Q =>
        ((2 * inner ℝ w (GE f) - inner ℝ w (GF w) : ℝ) : EReal)) g
    exact EReal.coe_le_coe_iff.mp (h2.trans h1)
  · intro h
    refine aux_lem_endpoints_support_3_core_closure GE GF hsym D hD a ha ?_
    intro f hf
    have hcont : Continuous fun g : DomainL2 Q =>
        (2 : ℝ) * inner ℝ g (GE f) - inner ℝ g (GF g) :=
      (continuous_const.mul (continuous_id.inner continuous_const)).sub
        (continuous_id.inner GF.continuous)
    have hpoint : ∀ g : DomainL2 Q,
        (2 : ℝ) * inner ℝ g (GE f) - inner ℝ g (GF g) ≤ a * inner ℝ f (GE f) :=
      aux_lem_endpoints_support_4_forall_le_of_dense (fun g : DomainL2 Q =>
          (2 : ℝ) * inner ℝ g (GE f) - inner ℝ g (GF g)) hcont D hD
        (a * inner ℝ f (GE f)) (fun g hg => h f hf g hg)
    refine iSup_le fun g => EReal.coe_le_coe_iff.mpr (hpoint g)

theorem aux_lem_endpoints_support_4_upperTest_iff {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω)
    (hsym : ∀ i (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y))
    (hpos : ∀ i (x : DomainL2 (centeredCube (z i) (r i) (hr i))), 0 ≤ inner ℝ x (GE i omega x))
    (a : ℝ) (ha : 0 ≤ a) :
    aux_lem_endpoints_support_4_upperTest z r hr GE GF a omega ↔
      ∀ i, ∀ u ∈ limitFormDomain (GE i omega),
        limitFormEnergy (GF i omega) u ≤
          ((a * (limitFormEnergy (GE i omega) u).toReal : ℝ) : EReal) := by
  constructor
  · intro h i
    refine (aux_lem_endpoints_support_4_formLe_iff_dense (GE i omega) (GF i omega) (hsym i) (hpos i)
      (Set.range (aux_lem_endpoints_support_4_seq z r hr i)) (aux_lem_endpoints_support_4_seq_dense z r hr i) a ha).2 ?_
    rw [Set.forall_mem_range]
    intro k
    rw [Set.forall_mem_range]
    intro l
    exact h i k l
  · intro h i k l
    exact (aux_lem_endpoints_support_4_formLe_iff_dense (GE i omega) (GF i omega) (hsym i) (hpos i)
      (Set.range (aux_lem_endpoints_support_4_seq z r hr i)) (aux_lem_endpoints_support_4_seq_dense z r hr i) a ha).1
      (h i) (aux_lem_endpoints_support_4_seq z r hr i k) ⟨k, rfl⟩ (aux_lem_endpoints_support_4_seq z r hr i l) ⟨l, rfl⟩

theorem aux_lem_endpoints_support_4_goodSeq_symm_pos {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (C0 : ℝ) (omega : Ω) (hgood : aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 omega) (i : ℕ) :
    ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)), inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y)) ∧
      (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)), 0 ≤ inner ℝ x (GE i omega x))) ∧
    ((∀ x y : DomainL2 (centeredCube (z i) (r i) (hr i)), inner ℝ (GF i omega x) y = inner ℝ x (GF i omega y)) ∧
      (∀ x : DomainL2 (centeredCube (z i) (r i) (hr i)), 0 ≤ inner ℝ x (GF i omega x))) := by
    unfold aux_lem_endpoints_support_4_goodSeq at hgood
    obtain ⟨hsym, hpos, -, -, -⟩ := hgood
    have hs := aux_lem_endpoints_support_4_seq_dense z r hr i
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro x y
      refine (hs.prodMap hs).induction_on (x, y)
        (p := fun q : DomainL2 (centeredCube (z i) (r i) (hr i)) ×
            DomainL2 (centeredCube (z i) (r i) (hr i)) =>
          inner ℝ (GE i omega q.1) q.2 = inner ℝ q.1 (GE i omega q.2)) ?_ ?_
      · refine isClosed_eq ?_ ?_
        · exact ((GE i omega).continuous.comp continuous_fst).inner continuous_snd
        · exact continuous_fst.inner ((GE i omega).continuous.comp continuous_snd)
      · rintro ⟨k, l⟩
        exact (hsym i k l).1
    · intro x
      refine hs.induction_on x (p := fun y : DomainL2 (centeredCube (z i) (r i) (hr i)) =>
        0 ≤ inner ℝ y (GE i omega y)) ?_ ?_
      · exact isClosed_le continuous_const (continuous_id.inner (GE i omega).continuous)
      · intro k
        exact (hpos i k).1
    · intro x y
      refine (hs.prodMap hs).induction_on (x, y)
        (p := fun q : DomainL2 (centeredCube (z i) (r i) (hr i)) ×
            DomainL2 (centeredCube (z i) (r i) (hr i)) =>
          inner ℝ (GF i omega q.1) q.2 = inner ℝ q.1 (GF i omega q.2)) ?_ ?_
      · refine isClosed_eq ?_ ?_
        · exact ((GF i omega).continuous.comp continuous_fst).inner continuous_snd
        · exact continuous_fst.inner ((GF i omega).continuous.comp continuous_snd)
      · rintro ⟨k, l⟩
        exact (hsym i k l).2
    · intro x
      refine hs.induction_on x (p := fun y : DomainL2 (centeredCube (z i) (r i) (hr i)) =>
        0 ≤ inner ℝ y (GF i omega y)) ?_ ?_
      · exact isClosed_le continuous_const (continuous_id.inner (GF i omega).continuous)
      · intro k
        exact (hpos i k).2

theorem lem_endpoints_support_4 {d : ℕ} (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) {Ω : Type}
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (omega : Ω)
    (hsymE : ∀ i (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      inner ℝ (GE i omega x) y = inner ℝ x (GE i omega y))
    (hposE : ∀ i (x : DomainL2 (centeredCube (z i) (r i) (hr i))), 0 ≤ inner ℝ x (GE i omega x))
    (hsymF : ∀ i (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      inner ℝ (GF i omega x) y = inner ℝ x (GF i omega y))
    (hposF : ∀ i (x : DomainL2 (centeredCube (z i) (r i) (hr i))), 0 ≤ inner ℝ x (GF i omega x))
    (C0 : ℝ) (hC0 : 1 ≤ C0) (hcomp : aux_lem_endpoints_compare z r hr GE GF C0 omega) :
    aux_lem_endpoints_support_4_upperTest z r hr GE GF C0 omega ∧
      aux_lem_endpoints_support_4_upperTest z r hr GF GE C0 omega := by
  constructor
  · rw [aux_lem_endpoints_support_4_upperTest_iff z r hr GE GF omega hsymE hposE C0 (by linarith)]
    intro i u hu
    obtain ⟨hdom, hineq⟩ := hcomp i
    have hFu_mem : u ∈ limitFormDomain (GF i omega) := hdom ▸ hu
    have hFu : limitFormEnergy (GF i omega) u < ⊤ := hFu_mem
    have hFnT : limitFormEnergy (GF i omega) u ≠ ⊤ := ne_of_lt hFu
    have hFnB : limitFormEnergy (GF i omega) u ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg (GF i omega) u))
    have hF : (limitFormEnergy (GF i omega) u).toReal ≤
        C0 * (limitFormEnergy (GE i omega) u).toReal := (hineq u hu).2
    rw [← EReal.coe_toReal hFnT hFnB]
    exact EReal.coe_le_coe_iff.mpr hF
  · rw [aux_lem_endpoints_support_4_upperTest_iff z r hr GF GE omega hsymF hposF C0 (by linarith)]
    intro i u hu
    obtain ⟨hdom, hineq⟩ := hcomp i
    have huE_mem : u ∈ limitFormDomain (GE i omega) := hdom.symm ▸ hu
    have huE : limitFormEnergy (GE i omega) u < ⊤ := huE_mem
    have hEnT : limitFormEnergy (GE i omega) u ≠ ⊤ := ne_of_lt huE
    have hEnB : limitFormEnergy (GE i omega) u ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (limitFormEnergy_nonneg (GE i omega) u))
    have hCF : C0⁻¹ * (limitFormEnergy (GE i omega) u).toReal ≤
        (limitFormEnergy (GF i omega) u).toReal := (hineq u huE_mem).1
    have hEF : (limitFormEnergy (GE i omega) u).toReal ≤
        C0 * (limitFormEnergy (GF i omega) u).toReal :=
      (inv_mul_le_iff₀ (by linarith : (0 : ℝ) < C0)).mp hCF
    rw [← EReal.coe_toReal hEnT hEnB]
    exact EReal.coe_le_coe_iff.mpr hEF

end Paper
