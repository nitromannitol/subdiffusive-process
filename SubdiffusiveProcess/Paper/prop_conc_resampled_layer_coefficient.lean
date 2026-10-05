module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.FiniteStopping.CutoffRestrictions
public import SubdiffusiveProcess.Probability.ResamplingSum
public import SubdiffusiveProcess.Probability.ResampledLimit

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess.Paper
noncomputable section

variable {d : ℕ}

/-! ## 1. Deterministic coefficient factorization -/

/-- A single non-positive layer `j ≤ 0` does not occur in the infrared partial sums, so updating it
leaves every partial sum unchanged. -/
theorem aux_prop_conc_resampled_infraredPartialSum_update {j : ℤ} (hj : j ≤ 0)
    (om : BilateralField d) (eta : C(SpatialCoordinates d, ℝ)) :
    infraredPartialSum (Function.update om j eta) = infraredPartialSum om := by
  funext L
  unfold infraredPartialSum
  apply Finset.sum_congr rfl
  intro n _
  have hne : Int.ofNat (n + 1) ≠ j := by
    have hpos : (0 : ℤ) < Int.ofNat (n + 1) := by
      change (0 : ℤ) < ((n + 1 : ℕ) : ℤ)
      exact_mod_cast Nat.succ_pos n
    omega
  rw [Function.update_of_ne hne]

/-- Updating a layer `j ≤ 0` which the cutoff `N` already contains (`j.natAbs ≤ N`) changes the
cutoff potential by exactly the layer difference, whenever the infrared limit is unchanged. -/
theorem aux_prop_conc_resampled_cutoffPotential_update
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (j : ℤ) (N : ℕ) (hj : j ≤ 0)
    (hjN : j.natAbs ≤ N) (om : BilateralField d) (eta : C(SpatialCoordinates d, ℝ))
    (hH : H (Function.update om j eta) = H om) (x : SpatialCoordinates d) :
    cutoffPotential H (Function.update om j eta) N x =
      cutoffPotential H om N x + (eta x - om j x) := by
  have hm : j.natAbs ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hjm : j = -((j.natAbs : ℤ)) := by omega
  have hdiff : (∑ n ∈ Finset.range (N + 1),
        (Function.update om j eta) (-(Int.ofNat n)) x) -
      (∑ n ∈ Finset.range (N + 1), om (-(Int.ofNat n)) x) = eta x - om j x := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single_of_mem j.natAbs hm]
    · have harg : (-(Int.ofNat j.natAbs)) = j := by
        simpa only [Int.ofNat_eq_natCast] using hjm.symm
      rw [harg, Function.update_self]
    · intro n _ hn
      have hne : (-(Int.ofNat n)) ≠ j := by
        intro hcon
        have h1 : (-(Int.ofNat n) : ℤ).natAbs = j.natAbs := by rw [hcon]
        have h2 : n = j.natAbs := by simpa [Int.ofNat_eq_natCast] using h1
        exact hn h2
      rw [Function.update_of_ne hne, sub_self]
  have hsum : (∑ n ∈ Finset.range (N + 1),
        (Function.update om j eta) (-(Int.ofNat n)) x) =
      (∑ n ∈ Finset.range (N + 1), om (-(Int.ofNat n)) x) + (eta x - om j x) :=
    (eq_add_of_sub_eq hdiff).trans (add_comm _ _)
  simp only [cutoffPotential]
  rw [hH, hsum]
  ring

/-- Exact resampling factorization of the cutoff coefficient: replacing layer `j ≤ 0` (already
present in the cutoff `N`) by `eta` multiplies the coefficient by `exp (eta x - ω j x)`, whenever
the infrared limit `H` is invariant under the update. -/
theorem aux_prop_conc_resampled_cutoffCoefficient_of_H_invariant
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (j : ℤ) (N : ℕ) (hj : j ≤ 0)
    (hjN : j.natAbs ≤ N) (om : BilateralField d) (eta : C(SpatialCoordinates d, ℝ))
    (hH : H (Function.update om j eta) = H om) (x : SpatialCoordinates d) :
    cutoffCoefficient M H (Function.update om j eta) N x =
      Real.exp (eta x - om j x) * cutoffCoefficient M H om N x := by
  have hexp : cutoffPotential H (Function.update om j eta) N x -
        (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
      (cutoffPotential H om N x - (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
        (eta x - om j x) := by
    rw [aux_prop_conc_resampled_cutoffPotential_update H j N hj hjN om eta hH x]
    ring
  simp only [cutoffCoefficient]
  rw [hexp, Real.exp_add]
  ring

/-! ## 2. Measurability and the a.e. infrared invariance -/

/-- Updating one layer is measurable in the field and the new layer value. -/
theorem aux_prop_conc_resampled_update_measurable
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] (j : ℤ) :
    Measurable fun z : BilateralField d × C(SpatialCoordinates d, ℝ) =>
      Function.update z.1 j z.2 := by
  rw [measurable_pi_iff]
  intro i
  by_cases hij : i = j
  · subst hij
    simpa only [Function.update_self] using
      (measurable_snd : Measurable fun z : BilateralField d × C(SpatialCoordinates d, ℝ) => z.2)
  · simpa only [Function.update_of_ne hij, Function.comp_apply] using!
      ((measurable_pi_apply i).comp measurable_fst)

/-- The infrared limit `H` is invariant under replacing a non-positive layer by that of an
independent copy, almost surely for the chaos sample law. -/
theorem aux_prop_conc_resampled_H_invariant_ae
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (j : ℤ) (hj : j ≤ 0) :
    ∀ᵐ z ∂((chaosSampleLaw M).toMeasure.prod (chaosSampleLaw M).toMeasure),
      H (Function.update z.1 j (z.2 j)) = H z.1 := by
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
  have hpartial : infraredPartialSum (Function.update z.1 j (z.2 j)) =
      infraredPartialSum z.1 :=
    aux_prop_conc_resampled_infraredPartialSum_update hj z.1 (z.2 j)
  rw [hpartial] at hz2
  exact tendsto_nhds_unique hz2 hz1

/-! ## 3. The coefficient identity on the chaos sample law and on the layer law -/

/-- On the chaos sample law paired with an independent copy, the resampled level-`N` cutoff
coefficient is the exact exponential weight times the original coefficient. -/
theorem aux_prop_conc_resampled_cutoffCoefficient_pair_ae
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (j : ℤ) (N : ℕ) (hj : j ≤ 0) (hjN : j.natAbs ≤ N) :
    ∀ᵐ z ∂((chaosSampleLaw M).toMeasure.prod (chaosSampleLaw M).toMeasure),
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H (Function.update z.1 j (z.2 j)) N x =
          Real.exp (z.2 j x - z.1 j x) * cutoffCoefficient M H z.1 N x := by
  filter_upwards [aux_prop_conc_resampled_H_invariant_ae M H hIR j hj] with z hz
  exact fun x => aux_prop_conc_resampled_cutoffCoefficient_of_H_invariant M H j N hj hjN
    z.1 (z.2 j) hz x

/-- The same identity with the new layer drawn from the *layer law* `scaledLayerLaw j`, i.e. after
projecting the second coordinate of the chaos sample law to the copied layer. -/
theorem aux_prop_conc_resampled_cutoffCoefficient_ae
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (j : ℤ) (N : ℕ) (hj : j ≤ 0) (hjN : j.natAbs ≤ N) :
    ∀ᵐ w ∂((chaosSampleLaw M).toMeasure.prod
        (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure),
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H (Function.update w.1 j w.2) N x =
          Real.exp (w.2 x - w.1 j x) * cutoffCoefficient M H w.1 N x := by
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
  have hpred : MeasurableSet
      {w : BilateralField d × C(SpatialCoordinates d, ℝ) |
        H (Function.update w.1 j w.2) = H w.1} :=
    measurableSet_eq_fun (hIR.1.comp (aux_prop_conc_resampled_update_measurable j))
      (hIR.1.comp measurable_fst)
  have hg_map : Measure.map (fun z : BilateralField d × BilateralField d => (z.1, z.2 j))
      (μ.prod μ) = μ.prod νlayer := by
    have h := Measure.map_prod_map μ μ measurable_id (measurable_pi_apply j)
    rw [Measure.map_id, hmap_eval] at h
    exact h.symm
  have hpush : ∀ᵐ w ∂(μ.prod νlayer),
      H (Function.update w.1 j w.2) = H w.1 := by
    have hsym := aux_prop_conc_resampled_H_invariant_ae M H hIR j hj
    have hae := (ae_map_iff hg_meas.aemeasurable hpred).mpr hsym
    rwa [hg_map] at hae
  filter_upwards [hpush] with w hw
  exact fun x => aux_prop_conc_resampled_cutoffCoefficient_of_H_invariant M H j N hj hjN
    w.1 w.2 hw x

/-! ## 4. Consumer forms: arbitrary measure-preserving field, and the `PositiveCoefficient` value -/

/-- Coefficient factorization along the field map of the represented space (the shape of
`in_joint_extracted_candidates`): for a.e. `ω` and a.e. layer value `y`, the coefficient of the
resampled field is the exact exponential weight times the coefficient of the original field. -/
theorem aux_prop_conc_resampled_layer_coefficient_cutoff_ae
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (j : ℤ) (N : ℕ) (hj : j ≤ 0) (hjN : j.natAbs ≤ N) :
    ∀ᵐ ω ∂P, ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure,
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H (Function.update (field ω) j y) N x =
          Real.exp (y x - field ω j x) * cutoffCoefficient M H (field ω) N x := by
  let νlayer : Measure (C(SpatialCoordinates d, ℝ)) :=
    (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure
  have hchaos := aux_prop_conc_resampled_cutoffCoefficient_ae M H hIR j N hj hjN
  have hmp : MeasurePreserving (Prod.map field id) (P.prod νlayer)
      ((chaosSampleLaw M).toMeasure.prod νlayer) :=
    MeasurePreserving.prod hfield (MeasurePreserving.id νlayer)
  have hpull : ∀ᵐ w ∂(P.prod νlayer),
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H (Function.update (field w.1) j w.2) N x =
          Real.exp (w.2 x - field w.1 j x) * cutoffCoefficient M H (field w.1) N x :=
    hmp.quasiMeasurePreserving.ae hchaos
  exact Measure.ae_ae_of_ae_prod hpull

/-- The `.val` form of the coefficient factorization on the observation cell: the weighted
coefficient sequence consumed by the weighted-convergence lemmas as their `hweight` hypothesis. -/
theorem aux_prop_conc_resampled_layer_coefficient_positive_ae
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (j : ℤ) (N : ℕ) (hj : j ≤ 0) (hjN : j.natAbs ≤ N)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (Function.update (field ω) j y) N z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => Real.exp (y x - field ω j x) *
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (field ω) N z hr).val x) := by
  filter_upwards [aux_prop_conc_resampled_layer_coefficient_cutoff_ae P M H hIR field hfield j N hj hjN]
    with ω hy
  filter_upwards [hy] with y hxy
  have h1 := SubdiffusiveProcess.FiniteStopping.cutoffCoefficient_ae M H
    (Function.update (field ω) j y) N z hr
  have h2 := SubdiffusiveProcess.FiniteStopping.cutoffCoefficient_ae M H (field ω) N z hr
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hxy x, hx2]

/-! ## 5. Analysis inputs for the reversed quantifier order -/

/-- `cutoffCoefficient` is continuous in the spatial variable. -/
theorem aux_prop_conc_resampled_continuous_cutoffCoefficient
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ) :
    Continuous fun x : SpatialCoordinates d => cutoffCoefficient M H om N x := by
  have hpot : Continuous fun x : SpatialCoordinates d => cutoffPotential H om N x := by
    unfold cutoffPotential
    exact (H om).continuous.add
      (continuous_finsetSum _ fun n _ => (om (-(Int.ofNat n))).continuous)
  simp only [cutoffCoefficient]
  exact continuous_const.mul (Real.continuous_exp.comp (hpot.sub continuous_const))

/-- `cutoffCoefficient` is measurable in the field variable. -/
theorem aux_prop_conc_resampled_measurable_cutoffCoefficient
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (q : SpatialCoordinates d) :
    Measurable fun om : BilateralField d => cutoffCoefficient M H om N q := by
  have hpot : Measurable fun om : BilateralField d => cutoffPotential H om N q := by
    unfold cutoffPotential
    refine ((continuous_eval_const q).measurable.comp hH).add ?_
    exact Finset.measurable_sum _ fun n _ =>
      (continuous_eval_const q).measurable.comp (measurable_pi_apply _)
  simp only [cutoffCoefficient]
  exact measurable_const.mul (Real.continuous_exp.measurable.comp (hpot.sub measurable_const))

/-- Two continuous functions agreeing on a dense set agree everywhere. -/
theorem aux_prop_conc_resampled_eq_of_dense {D : Set (SpatialCoordinates d)} (hD : Dense D)
    {f g : SpatialCoordinates d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x ∈ D, f x = g x) : ∀ x, f x = g x := by
  have hcl : IsClosed {x | f x = g x} := isClosed_eq hf hg
  have hsub : closure D ⊆ {x | f x = g x} := hcl.closure_subset_iff.mpr h
  rw [hD.closure_eq] at hsub
  exact fun x => hsub (Set.mem_univ x)

/-- The resampling weight `exp (y - om j)` is continuous and positive on the cell closure (the
`rho` facts required by the weighted-convergence lemmas). -/
theorem aux_prop_conc_resampled_weight_continuous_pos
    (y : C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (j : ℤ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun x : SpatialCoordinates d => Real.exp (y x - om j x))
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
    ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      0 < Real.exp (y x - om j x) :=
  ⟨(Real.continuous_exp.comp (y.continuous.sub (om j).continuous)).continuousOn,
    fun _ _ => Real.exp_pos _⟩

/-! ## 6. Fixed-layer form: the weighted-convergence `hweight` shape

The weighted-convergence lemmas take, for a *fixed* layer draw `y`, the coefficient relation
`∀ᵐ om ∂(chaosSampleLaw M).toMeasure, (b n om).val =ᵐ rho om * (cutoffPositiveCoefficient … om …).val`
with `rho om := fun x => exp (y x - om j x)` and `b n om := cutoffPositiveCoefficient … (update om j y) …`.
The theorem below gives exactly that quantifier order (`∀ᵐ y`, then `∀ᵐ ω`). -/

/-- Fixed-layer reversed-order form of the coefficient factorization. -/
theorem aux_prop_conc_resampled_layer_coefficient_cutoff_for_layer
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (j : ℤ) (N : ℕ) (hj : j ≤ 0) (hjN : j.natAbs ≤ N) :
    ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure, ∀ᵐ ω ∂P,
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H (Function.update (field ω) j y) N x =
          Real.exp (y x - field ω j x) * cutoffCoefficient M H (field ω) N x := by
  let νlayer : Measure (C(SpatialCoordinates d, ℝ)) :=
    (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure
  -- a dense enumeration of the spatial coordinates
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense (SpatialCoordinates d)
  have hDne : D.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hcl : closure D = Set.univ := hDd.closure_eq
    rw [h, closure_empty] at hcl
    exact (Set.notMem_empty (0 : SpatialCoordinates d)) (hcl ▸ Set.mem_univ _)
  obtain ⟨e, he⟩ := hDc.exists_eq_range hDne
  -- the joint statement, enumerated on a countable set
  have hjoint := aux_prop_conc_resampled_layer_coefficient_cutoff_ae P M H hIR field hfield j N hj hjN
  -- the enumerated predicate is measurable
  have hLmeas : ∀ n : ℕ, Measurable fun z : Ω × C(SpatialCoordinates d, ℝ) =>
      cutoffCoefficient M H (Function.update (field z.1) j z.2) N (e n) := fun n =>
    (aux_prop_conc_resampled_measurable_cutoffCoefficient M H hIR.1 N (e n)).comp
      ((aux_prop_conc_resampled_update_measurable j).comp
        (Measurable.prod (f := fun z : Ω × C(SpatialCoordinates d, ℝ) => (field z.1, z.2))
          (hfield.measurable.comp measurable_fst) measurable_snd))
  have hRmeas : ∀ n : ℕ, Measurable fun z : Ω × C(SpatialCoordinates d, ℝ) =>
      Real.exp (z.2 (e n) - field z.1 j (e n)) * cutoffCoefficient M H (field z.1) N (e n) := by
    intro n
    have hyq : Measurable fun z : Ω × C(SpatialCoordinates d, ℝ) => z.2 (e n) :=
      (continuous_eval_const (e n)).measurable.comp measurable_snd
    have hoq : Measurable fun z : Ω × C(SpatialCoordinates d, ℝ) => field z.1 j (e n) :=
      (continuous_eval_const (e n)).measurable.comp
        ((measurable_pi_apply j).comp (hfield.measurable.comp measurable_fst))
    have hc : Measurable fun z : Ω × C(SpatialCoordinates d, ℝ) =>
        cutoffCoefficient M H (field z.1) N (e n) :=
      (aux_prop_conc_resampled_measurable_cutoffCoefficient M H hIR.1 N (e n)).comp
        (hfield.measurable.comp measurable_fst)
    exact (Real.continuous_exp.measurable.comp (hyq.sub hoq)).mul hc
  have hmeas : MeasurableSet {z : Ω × C(SpatialCoordinates d, ℝ) |
      ∀ n : ℕ,
        cutoffCoefficient M H (Function.update (field z.1) j z.2) N (e n) =
          Real.exp (z.2 (e n) - field z.1 j (e n)) * cutoffCoefficient M H (field z.1) N (e n)} := by
    have hset : {z : Ω × C(SpatialCoordinates d, ℝ) |
        ∀ n : ℕ,
          cutoffCoefficient M H (Function.update (field z.1) j z.2) N (e n) =
            Real.exp (z.2 (e n) - field z.1 j (e n)) * cutoffCoefficient M H (field z.1) N (e n)}
        = ⋂ n : ℕ, {z : Ω × C(SpatialCoordinates d, ℝ) |
          cutoffCoefficient M H (Function.update (field z.1) j z.2) N (e n) =
            Real.exp (z.2 (e n) - field z.1 j (e n)) * cutoffCoefficient M H (field z.1) N (e n)} := by
      ext z
      simp
    rw [hset]
    exact MeasurableSet.iInter fun n => measurableSet_eq_fun (hLmeas n) (hRmeas n)
  have h2 : ∀ᵐ z ∂(P.prod νlayer), ∀ n : ℕ,
      cutoffCoefficient M H (Function.update (field z.1) j z.2) N (e n) =
        Real.exp (z.2 (e n) - field z.1 j (e n)) * cutoffCoefficient M H (field z.1) N (e n) :=
    (Measure.ae_prod_iff_ae_ae hmeas).mpr
      (hjoint.mono fun ω hω => hω.mono fun y hy n => hy (e n))
  -- swap the two a.e. quantifiers
  have hmeas' : MeasurableSet {z : C(SpatialCoordinates d, ℝ) × Ω |
      ∀ n : ℕ,
        cutoffCoefficient M H (Function.update (field z.2) j z.1) N (e n) =
          Real.exp (z.1 (e n) - field z.2 j (e n)) * cutoffCoefficient M H (field z.2) N (e n)} := by
    have hp := hmeas.preimage measurable_swap
    simpa only [Set.preimage_ofPred_eq, Prod.swap_prod_mk, Prod.swap] using! hp
  have h3 : ∀ᵐ y ∂νlayer, ∀ᵐ ω ∂P, ∀ n : ℕ,
      cutoffCoefficient M H (Function.update (field ω) j y) N (e n) =
        Real.exp (y (e n) - field ω j (e n)) * cutoffCoefficient M H (field ω) N (e n) := by
    have hswap : ∀ᵐ z ∂(νlayer.prod P), ∀ n : ℕ,
        cutoffCoefficient M H (Function.update (field z.2) j z.1) N (e n) =
          Real.exp (z.1 (e n) - field z.2 j (e n)) * cutoffCoefficient M H (field z.2) N (e n) :=
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae h2
    exact (Measure.ae_prod_iff_ae_ae hmeas').mp hswap
  -- extend from the dense set to all points
  filter_upwards [h3] with y hy
  filter_upwards [hy] with ω hω
  intro x
  refine aux_prop_conc_resampled_eq_of_dense hDd
    (aux_prop_conc_resampled_continuous_cutoffCoefficient M H (Function.update (field ω) j y) N)
    ((Real.continuous_exp.comp ((y.continuous).sub ((field ω j).continuous))).mul
      (aux_prop_conc_resampled_continuous_cutoffCoefficient M H (field ω) N)) ?_ x
  intro x' hx'
  have hx'' : x' ∈ Set.range e := he ▸ hx'
  obtain ⟨n, rfl⟩ := hx''
  exact hω n

/-- Fixed-layer `.val` form on the observation cell: the exact `hweight` hypothesis shape of the
weighted-convergence lemmas, for a.e. fixed layer draw `y`. -/
theorem prop_conc_resampled_layer_coefficient
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hIR : InfraredCharacterization M H)
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (j : ℤ) (N : ℕ) (hj : j ≤ 0) (hjN : j.natAbs ≤ N)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ y ∂(scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure, ∀ᵐ ω ∂P,
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (Function.update (field ω) j y) N z hr).val
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => Real.exp (y x - field ω j x) *
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (field ω) N z hr).val x) := by
  filter_upwards [aux_prop_conc_resampled_layer_coefficient_cutoff_for_layer P M H hIR field hfield
    j N hj hjN] with y hy
  filter_upwards [hy] with ω hxy
  have h1 := SubdiffusiveProcess.FiniteStopping.cutoffCoefficient_ae M H
    (Function.update (field ω) j y) N z hr
  have h2 := SubdiffusiveProcess.FiniteStopping.cutoffCoefficient_ae M H (field ω) N z hr
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hxy x, hx2]

end
end SubdiffusiveProcess.Paper
