module

public import SubdiffusiveProcess.Paper.prop_conc_resampled_layer_coefficient

@[expose] public section

/-! # Resampling an infrared layer: the anchored coefficient factorization

Sibling of `prop_conc_resampled_layer_coefficient` (layers `j ≤ 0`, contained in the finite cutoff) for the
infrared layers `j ≥ 1`, which enter only through the infrared potential `H = lim_L ∑_{n ≤ L} (ω_n - ω_n(0))`.
Replacing `ω_j` by `y` shifts `H` by the anchored difference `(y - y 0) - (ω_j - ω_j 0)` (a.s., both limits
existing), and leaves the finite-cutoff layers `ω_{-n}`, `n ≥ 0`, unchanged; so every cutoff coefficient is
multiplied by `exp ((y - y 0) - (ω_j - ω_j 0))`, for every cutoff `N` (no condition `|j| ≤ N`).  The relative
response is invariant under the constant `y 0 - ω_j 0`, so this weight is equivalent to `exp (y - ω_j)`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace Paper
noncomputable section

variable {d : ℕ}

/-- The change of the anchored infrared potential when the layer `j` is replaced by `eta`. -/
def aux_prop_conc_resampled_infrared_shift (om : BilateralField d) (j : ℤ)
    (eta : C(SpatialCoordinates d, ℝ)) : C(SpatialCoordinates d, ℝ) :=
  (eta - ContinuousMap.const _ (eta 0)) - (om j - ContinuousMap.const _ (om j 0))

theorem aux_prop_conc_resampled_infrared_shift_apply (om : BilateralField d) (j : ℤ)
    (eta : C(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d) :
    aux_prop_conc_resampled_infrared_shift om j eta x = (eta x - eta 0) - (om j x - om j 0) := by
  simp [aux_prop_conc_resampled_infrared_shift]

/-! ## 1. Deterministic shift of the partial sums, the potential and the coefficient -/

/-- Once the partial sum contains the infrared layer `j ≥ 1` it is shifted by the anchored difference. -/
theorem aux_prop_conc_resampled_infrared_partialSum_update {j : ℤ} (hj : 1 ≤ j)
    (om : BilateralField d) (eta : C(SpatialCoordinates d, ℝ)) {L : ℕ} (hL : j ≤ (L : ℤ)) :
    infraredPartialSum (Function.update om j eta) L =
      infraredPartialSum om L + aux_prop_conc_resampled_infrared_shift om j eta := by
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, Int.ofNat (n₀ + 1) = j :=
    ⟨j.toNat - 1, by simp only [Int.ofNat_eq_natCast]; omega⟩
  have hn₀' : ((n₀ : ℤ) + 1) = j := by simpa only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] using hn₀
  have hmem : n₀ ∈ Finset.range L := by rw [Finset.mem_range]; omega
  unfold infraredPartialSum
  have hdiff : (∑ n ∈ Finset.range L,
        ((Function.update om j eta) (Int.ofNat (n + 1)) -
          ContinuousMap.const _ ((Function.update om j eta) (Int.ofNat (n + 1)) 0))) -
      (∑ n ∈ Finset.range L,
        (om (Int.ofNat (n + 1)) - ContinuousMap.const _ (om (Int.ofNat (n + 1)) 0))) =
      aux_prop_conc_resampled_infrared_shift om j eta := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single_of_mem n₀ hmem]
    · rw [hn₀, Function.update_self]
      rfl
    · intro n _ hn
      have hne : Int.ofNat (n + 1) ≠ j := by
        intro h; apply hn
        have h' : ((n : ℤ) + 1) = j := by
          simpa only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] using h
        omega
      rw [Function.update_of_ne hne, sub_self]
  exact (eq_add_of_sub_eq hdiff).trans (add_comm _ _)

/-- The infrared layer `j ≥ 1` does not occur in the finite-cutoff layers, so the cutoff potential shifts by
the anchored difference whenever `H` does. -/
theorem aux_prop_conc_resampled_infrared_cutoffPotential_update
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (j : ℤ) (N : ℕ) (hj : 1 ≤ j)
    (om : BilateralField d) (eta : C(SpatialCoordinates d, ℝ))
    (hH : H (Function.update om j eta) = H om + aux_prop_conc_resampled_infrared_shift om j eta)
    (x : SpatialCoordinates d) :
    cutoffPotential H (Function.update om j eta) N x =
      cutoffPotential H om N x + ((eta x - eta 0) - (om j x - om j 0)) := by
  have hsum : ∑ n ∈ Finset.range (N + 1), (Function.update om j eta) (-(Int.ofNat n)) x =
      ∑ n ∈ Finset.range (N + 1), om (-(Int.ofNat n)) x := by
    apply Finset.sum_congr rfl
    intro n _
    have hne : (-(Int.ofNat n)) ≠ j := by
      have := Int.natCast_nonneg n
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [Function.update_of_ne hne]
  simp only [cutoffPotential]
  rw [hH, hsum, ContinuousMap.add_apply, aux_prop_conc_resampled_infrared_shift_apply]
  ring

theorem aux_prop_conc_resampled_infrared_cutoffCoefficient_of_H_shift
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (j : ℤ) (N : ℕ) (hj : 1 ≤ j)
    (om : BilateralField d) (eta : C(SpatialCoordinates d, ℝ))
    (hH : H (Function.update om j eta) = H om + aux_prop_conc_resampled_infrared_shift om j eta)
    (x : SpatialCoordinates d) :
    cutoffCoefficient M H (Function.update om j eta) N x =
      Real.exp ((eta x - eta 0) - (om j x - om j 0)) * cutoffCoefficient M H om N x := by
  have hexp : cutoffPotential H (Function.update om j eta) N x -
        (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P =
      (cutoffPotential H om N x - (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
        ((eta x - eta 0) - (om j x - om j 0)) := by
    rw [aux_prop_conc_resampled_infrared_cutoffPotential_update H j N hj om eta hH x]
    ring
  simp only [cutoffCoefficient]
  rw [hexp, Real.exp_add]
  ring

/-! ## 2. The a.e. shift of the infrared limit -/

theorem aux_prop_conc_resampled_infrared_H_shift_ae
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (j : ℤ) (hj : 1 ≤ j) :
    ∀ᵐ z ∂((chaosSampleLaw M).toMeasure.prod (chaosSampleLaw M).toMeasure),
      H (Function.update z.1 j (z.2 j)) =
        H z.1 + aux_prop_conc_resampled_infrared_shift z.1 j (z.2 j) := by
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have hμ : μ = Measure.infinitePi (fun i : ℤ =>
      (scaledLayerLaw d (chaosRootFieldLaw M) i :
        Measure C(SpatialCoordinates d, ℝ))) := rfl
  have hconv : ∀ᵐ v ∂μ, Tendsto (infraredPartialSum v) atTop (𝓝 (H v)) := hIR.2
  have h1 : ∀ᵐ z ∂(μ.prod μ), Tendsto (infraredPartialSum z.1) atTop (𝓝 (H z.1)) :=
    measurePreserving_fst.quasiMeasurePreserving.ae hconv
  have h2 : ∀ᵐ z ∂(μ.prod μ),
      Tendsto (infraredPartialSum (Function.update z.1 j (z.2 j))) atTop
        (𝓝 (H (Function.update z.1 j (z.2 j)))) := by
    have hmp := SubdiffusiveProcess.Probability.measurePreserving_update_infinitePi
      (fun i : ℤ => (scaledLayerLaw d (chaosRootFieldLaw M) i :
        Measure C(SpatialCoordinates d, ℝ))) j
    have hmp' : MeasurePreserving
        (fun z : BilateralField d × BilateralField d => Function.update z.1 j (z.2 j))
        (μ.prod μ) μ := by
      rw [hμ]
      exact hmp
    exact hmp'.quasiMeasurePreserving.ae hconv
  filter_upwards [h1, h2] with z hz1 hz2
  have hev : (fun L => infraredPartialSum (Function.update z.1 j (z.2 j)) L) =ᶠ[atTop]
      (fun L => infraredPartialSum z.1 L + aux_prop_conc_resampled_infrared_shift z.1 j (z.2 j)) := by
    filter_upwards [eventually_ge_atTop j.toNat] with L hL
    exact aux_prop_conc_resampled_infrared_partialSum_update hj z.1 (z.2 j) (by omega)
  exact tendsto_nhds_unique (hz2.congr' hev) (hz1.add_const _)

/-! ## 3. The coefficient identity on the chaos sample law and on the layer law -/

theorem aux_prop_conc_resampled_infrared_cutoffCoefficient_pair_ae
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (j : ℤ) (N : ℕ) (hj : 1 ≤ j) :
    ∀ᵐ z ∂((chaosSampleLaw M).toMeasure.prod (chaosSampleLaw M).toMeasure),
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H (Function.update z.1 j (z.2 j)) N x =
          Real.exp ((z.2 j x - z.2 j 0) - (z.1 j x - z.1 j 0)) * cutoffCoefficient M H z.1 N x := by
  filter_upwards [aux_prop_conc_resampled_infrared_H_shift_ae M H hIR j hj] with z hz
  exact fun x => aux_prop_conc_resampled_infrared_cutoffCoefficient_of_H_shift M H j N hj
    z.1 (z.2 j) hz x

theorem aux_prop_conc_resampled_infrared_cutoffCoefficient_ae
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (j : ℤ) (N : ℕ) (hj : 1 ≤ j) :
    ∀ᵐ w ∂((chaosSampleLaw M).toMeasure.prod
        (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure),
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H (Function.update w.1 j w.2) N x =
          Real.exp ((w.2 x - w.2 0) - (w.1 j x - w.1 j 0)) * cutoffCoefficient M H w.1 N x := by
  let μ : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let νlayer : Measure (C(SpatialCoordinates d, ℝ)) :=
    (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure
  have hμ : μ = Measure.infinitePi (fun i : ℤ =>
      (scaledLayerLaw d (chaosRootFieldLaw M) i :
        Measure C(SpatialCoordinates d, ℝ))) := rfl
  have hlayer : νlayer = (scaledLayerLaw d (chaosRootFieldLaw M) j :
      Measure C(SpatialCoordinates d, ℝ)) := rfl
  have hmap_eval : Measure.map (fun e : BilateralField d => e j) μ = νlayer := by
    rw [hμ, hlayer]
    exact Measure.infinitePi_map_eval _ j
  have hg_meas : Measurable fun z : BilateralField d × BilateralField d => (z.1, z.2 j) :=
    Measurable.prod (f := fun z : BilateralField d × BilateralField d => (z.1, z.2 j))
      measurable_fst ((measurable_pi_apply j).comp measurable_snd)
  have hφ : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
      f - ContinuousMap.const (SpatialCoordinates d) (f 0)) :=
    continuous_id.sub (ContinuousMap.continuous_const'.comp (continuous_eval_const 0))
  have hshift : Measurable fun w : BilateralField d × C(SpatialCoordinates d, ℝ) =>
      aux_prop_conc_resampled_infrared_shift w.1 j w.2 :=
    (hφ.measurable.comp measurable_snd).sub
      (hφ.measurable.comp ((measurable_pi_apply j).comp measurable_fst))
  have hpred : MeasurableSet
      {w : BilateralField d × C(SpatialCoordinates d, ℝ) |
        H (Function.update w.1 j w.2) =
          H w.1 + aux_prop_conc_resampled_infrared_shift w.1 j w.2} :=
    measurableSet_eq_fun (hIR.1.comp (aux_prop_conc_resampled_update_measurable j))
      ((hIR.1.comp measurable_fst).add hshift)
  have hg_map : Measure.map (fun z : BilateralField d × BilateralField d => (z.1, z.2 j))
      (μ.prod μ) = μ.prod νlayer := by
    have h := Measure.map_prod_map μ μ measurable_id (measurable_pi_apply j)
    rw [Measure.map_id, hmap_eval] at h
    exact h.symm
  have hpush : ∀ᵐ w ∂(μ.prod νlayer),
      H (Function.update w.1 j w.2) =
        H w.1 + aux_prop_conc_resampled_infrared_shift w.1 j w.2 := by
    have hsym := aux_prop_conc_resampled_infrared_H_shift_ae M H hIR j hj
    have hae := (ae_map_iff hg_meas.aemeasurable hpred).mpr hsym
    rwa [hg_map] at hae
  filter_upwards [hpush] with w hw
  exact fun x => aux_prop_conc_resampled_infrared_cutoffCoefficient_of_H_shift M H j N hj
    w.1 w.2 hw x

/-! ## 4. Consumer forms: measure-preserving field and fixed layer -/

theorem aux_prop_conc_resampled_infrared_coefficient_cutoff_ae
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (j : ℤ) (N : ℕ) (hj : 1 ≤ j) :
    ∀ᵐ ω ∂P, ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure,
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H (Function.update (field ω) j y) N x =
          Real.exp ((y x - y 0) - (field ω j x - field ω j 0)) *
            cutoffCoefficient M H (field ω) N x := by
  let νlayer : Measure (C(SpatialCoordinates d, ℝ)) :=
    (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure
  have hchaos := aux_prop_conc_resampled_infrared_cutoffCoefficient_ae M H hIR j N hj
  have hmp : MeasurePreserving (Prod.map field id) (P.prod νlayer)
      ((chaosSampleLaw M).toMeasure.prod νlayer) :=
    MeasurePreserving.prod hfield (MeasurePreserving.id νlayer)
  have hpull : ∀ᵐ w ∂(P.prod νlayer),
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H (Function.update (field w.1) j w.2) N x =
          Real.exp ((w.2 x - w.2 0) - (field w.1 j x - field w.1 j 0)) *
            cutoffCoefficient M H (field w.1) N x :=
    hmp.quasiMeasurePreserving.ae hchaos
  exact Measure.ae_ae_of_ae_prod hpull

/-- Fixed-layer reversed-order form of the infrared coefficient factorization. -/
theorem aux_prop_conc_resampled_infrared_coefficient_for_layer
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (j : ℤ) (N : ℕ) (hj : 1 ≤ j) :
    ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure, ∀ᵐ ω ∂P,
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H (Function.update (field ω) j y) N x =
          Real.exp ((y x - y 0) - (field ω j x - field ω j 0)) *
            cutoffCoefficient M H (field ω) N x := by
  let νlayer : Measure (C(SpatialCoordinates d, ℝ)) :=
    (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense (SpatialCoordinates d)
  have hDne : D.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hcl : closure D = Set.univ := hDd.closure_eq
    rw [h, closure_empty] at hcl
    exact (Set.notMem_empty (0 : SpatialCoordinates d)) (hcl ▸ Set.mem_univ _)
  obtain ⟨e, he⟩ := hDc.exists_eq_range hDne
  have hjoint := aux_prop_conc_resampled_infrared_coefficient_cutoff_ae P M H hIR field hfield j N hj
  have hLmeas : ∀ n : ℕ, Measurable fun z : Ω × C(SpatialCoordinates d, ℝ) =>
      cutoffCoefficient M H (Function.update (field z.1) j z.2) N (e n) := fun n =>
    (aux_prop_conc_resampled_measurable_cutoffCoefficient M H hIR.1 N (e n)).comp
      ((aux_prop_conc_resampled_update_measurable j).comp
        (Measurable.prod (f := fun z : Ω × C(SpatialCoordinates d, ℝ) => (field z.1, z.2))
          (hfield.measurable.comp measurable_fst) measurable_snd))
  have hRmeas : ∀ n : ℕ, Measurable fun z : Ω × C(SpatialCoordinates d, ℝ) =>
      Real.exp ((z.2 (e n) - z.2 0) - (field z.1 j (e n) - field z.1 j 0)) *
        cutoffCoefficient M H (field z.1) N (e n) := by
    intro n
    have hyq : Measurable fun z : Ω × C(SpatialCoordinates d, ℝ) => z.2 (e n) :=
      (continuous_eval_const (e n)).measurable.comp measurable_snd
    have hy0 : Measurable fun z : Ω × C(SpatialCoordinates d, ℝ) => z.2 0 :=
      (continuous_eval_const (0 : SpatialCoordinates d)).measurable.comp measurable_snd
    have hoq : Measurable fun z : Ω × C(SpatialCoordinates d, ℝ) => field z.1 j (e n) :=
      (continuous_eval_const (e n)).measurable.comp
        ((measurable_pi_apply j).comp (hfield.measurable.comp measurable_fst))
    have ho0 : Measurable fun z : Ω × C(SpatialCoordinates d, ℝ) => field z.1 j 0 :=
      (continuous_eval_const (0 : SpatialCoordinates d)).measurable.comp
        ((measurable_pi_apply j).comp (hfield.measurable.comp measurable_fst))
    have hc : Measurable fun z : Ω × C(SpatialCoordinates d, ℝ) =>
        cutoffCoefficient M H (field z.1) N (e n) :=
      (aux_prop_conc_resampled_measurable_cutoffCoefficient M H hIR.1 N (e n)).comp
        (hfield.measurable.comp measurable_fst)
    exact (Real.continuous_exp.measurable.comp ((hyq.sub hy0).sub (hoq.sub ho0))).mul hc
  have hmeas : MeasurableSet {z : Ω × C(SpatialCoordinates d, ℝ) |
      ∀ n : ℕ,
        cutoffCoefficient M H (Function.update (field z.1) j z.2) N (e n) =
          Real.exp ((z.2 (e n) - z.2 0) - (field z.1 j (e n) - field z.1 j 0)) *
            cutoffCoefficient M H (field z.1) N (e n)} := by
    have hset : {z : Ω × C(SpatialCoordinates d, ℝ) |
        ∀ n : ℕ,
          cutoffCoefficient M H (Function.update (field z.1) j z.2) N (e n) =
            Real.exp ((z.2 (e n) - z.2 0) - (field z.1 j (e n) - field z.1 j 0)) *
              cutoffCoefficient M H (field z.1) N (e n)}
        = ⋂ n : ℕ, {z : Ω × C(SpatialCoordinates d, ℝ) |
          cutoffCoefficient M H (Function.update (field z.1) j z.2) N (e n) =
            Real.exp ((z.2 (e n) - z.2 0) - (field z.1 j (e n) - field z.1 j 0)) *
              cutoffCoefficient M H (field z.1) N (e n)} := by
      ext z
      simp
    rw [hset]
    exact MeasurableSet.iInter fun n => measurableSet_eq_fun (hLmeas n) (hRmeas n)
  have h2 : ∀ᵐ z ∂(P.prod νlayer), ∀ n : ℕ,
      cutoffCoefficient M H (Function.update (field z.1) j z.2) N (e n) =
        Real.exp ((z.2 (e n) - z.2 0) - (field z.1 j (e n) - field z.1 j 0)) *
          cutoffCoefficient M H (field z.1) N (e n) :=
    (Measure.ae_prod_iff_ae_ae hmeas).mpr
      (hjoint.mono fun ω hω => hω.mono fun y hy n => hy (e n))
  have hmeas' : MeasurableSet {z : C(SpatialCoordinates d, ℝ) × Ω |
      ∀ n : ℕ,
        cutoffCoefficient M H (Function.update (field z.2) j z.1) N (e n) =
          Real.exp ((z.1 (e n) - z.1 0) - (field z.2 j (e n) - field z.2 j 0)) *
            cutoffCoefficient M H (field z.2) N (e n)} := by
    have hp := hmeas.preimage measurable_swap
    exact hp
  have h3 : ∀ᵐ y ∂νlayer, ∀ᵐ ω ∂P, ∀ n : ℕ,
      cutoffCoefficient M H (Function.update (field ω) j y) N (e n) =
        Real.exp ((y (e n) - y 0) - (field ω j (e n) - field ω j 0)) *
          cutoffCoefficient M H (field ω) N (e n) := by
    have hswap : ∀ᵐ z ∂(νlayer.prod P), ∀ n : ℕ,
        cutoffCoefficient M H (Function.update (field z.2) j z.1) N (e n) =
          Real.exp ((z.1 (e n) - z.1 0) - (field z.2 j (e n) - field z.2 j 0)) *
            cutoffCoefficient M H (field z.2) N (e n) :=
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae h2
    exact (Measure.ae_prod_iff_ae_ae hmeas').mp hswap
  filter_upwards [h3] with y hy
  filter_upwards [hy] with ω hω
  intro x
  refine aux_prop_conc_resampled_eq_of_dense hDd
    (aux_prop_conc_resampled_continuous_cutoffCoefficient M H (Function.update (field ω) j y) N)
    ((Real.continuous_exp.comp
        ((y.continuous.sub continuous_const).sub
          ((field ω j).continuous.sub continuous_const))).mul
      (aux_prop_conc_resampled_continuous_cutoffCoefficient M H (field ω) N)) ?_ x
  intro x' hx'
  have hx'' : x' ∈ Set.range e := he ▸ hx'
  obtain ⟨n, rfl⟩ := hx''
  exact hω n

/-- Fixed-layer `.val` form on the observation cell (the `hweight` shape of the weighted-convergence packets)
for the infrared layer `j ≥ 1`, with the anchored weight `exp ((y - y 0) - (ω_j - ω_j 0))`. -/
theorem prop_conc_resampled_infrared_coefficient
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (j : ℤ) (N : ℕ) (hj : 1 ≤ j)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure, ∀ᵐ ω ∂P,
      (Lane4.cutoffPositiveCoefficient M H (Function.update (field ω) j y) N z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => Real.exp ((y x - y 0) - (field ω j x - field ω j 0)) *
          (Lane4.cutoffPositiveCoefficient M H (field ω) N z hr).val x) := by
  filter_upwards [aux_prop_conc_resampled_infrared_coefficient_for_layer P M H hIR field hfield
    j N hj] with y hy
  filter_upwards [hy] with ω hxy
  have h1 := SubdiffusiveProcess.FiniteStopping.cutoffCoefficient_ae M H
    (Function.update (field ω) j y) N z hr
  have h2 := SubdiffusiveProcess.FiniteStopping.cutoffCoefficient_ae M H (field ω) N z hr
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hxy x, hx2]

end
end Paper

