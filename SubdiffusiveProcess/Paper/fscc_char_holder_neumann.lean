import SubdiffusiveProcess.Paper.fscc_holder_predicates
import SubdiffusiveProcess.Paper.prop_growth_large_root
import SubdiffusiveProcess.Paper.cor_neumann_source
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.lem_as_regularity_affine_transport
import SubdiffusiveProcess.Paper.lane4_reference_point_moments
import SubdiffusiveProcess.Paper.reference_coefficients
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.ChaosRootFieldLaw
import SubdiffusiveProcess.Main.ScaledLayerLaw
import SubdiffusiveProcess.Main.LayerScaling
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.CutoffPotential
import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.MeanZero
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Sobolev.ResponseComparison
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Lane4.Bridge
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The mean-zero Neumann Hölder branch for the characterized infrared field, at every exponent `α ∈ (0,1)`

Paper `mfd:lem-finite-source-comparison`: the bound of `cor_neumann_source` on the unit Neumann cube,
transported to every triadic root cube `Q(z, 3^j)` by the affine scale shift `S_{m,w}`, `m = -j`, for
every cutoff `J ≥ max 0 (-j)`.  (`lem_finite_source_comparison_cells` keeps the finitely many small
cutoffs `J < -j`.)  The predicate is that of `fscc_holder_predicates`.

The T-transport toolkit (`aux_transport_*`: the scale shift `S_{m,w}` of the bilateral field for every
`m : ℤ`, the infrared and coefficient identities) and the transport pipeline (`aux_fscc_holNeuH_*`:
core transfer, reference moments) were extracted from `lem_finite_source_comparison_cells`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology Metric ProbabilityTheory
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace Paper




/-! ## (T1) `S_{m,w}` for every `m : ℤ`, both signs -/

/-- The chart `y ↦ w + 3^{-m} y`, for any integer depth `m` (extends
`aux_lem_as_coarse_shallow_grid_cellMap`, which is stated only for `m : ℕ`, to both signs). -/
def aux_transport_cellMap {d : ℕ} (m : ℤ) (w : SpatialCoordinates d) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨cubeDilation w 0 ((3 : ℝ) ^ (-m)), continuous_cubeDilation w 0 _⟩

theorem aux_transport_cellMap_apply {d : ℕ} (m : ℤ) (w y : SpatialCoordinates d) :
    aux_transport_cellMap m w y = w + (3 : ℝ) ^ (-m) • y := by
  funext i
  simp [aux_transport_cellMap, cubeDilation_apply]

/-- `S_{m,w}`: layer `j` of the shifted field is layer `j - m` read in the chart
`y ↦ w + 3^{-m} y` (paper 4511--4518, extended to both signs of `m`). -/
def aux_transport_S {d : ℕ} (m : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) :
    BilateralField d :=
  fun j => (om (j - m)).comp (aux_transport_cellMap m w)

theorem aux_transport_S_apply {d : ℕ} (m : ℤ) (w : SpatialCoordinates d) (om : BilateralField d)
    (i : ℤ) (y : SpatialCoordinates d) :
    aux_transport_S m w om i y = om (i - m) (w + (3 : ℝ) ^ (-m) • y) := by
  simp only [aux_transport_S, ContinuousMap.comp_apply, aux_transport_cellMap_apply]

section MeasurePreservingS

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_transport_S_measurable (m : ℤ) (w : SpatialCoordinates d) :
    Measurable (aux_transport_S (d := d) m w) := by
  have hc : Measurable fun f : C(SpatialCoordinates d, ℝ) =>
      f.comp (aux_transport_cellMap m w) := by fun_prop
  exact measurable_pi_lambda _ fun j => hc.comp (measurable_pi_apply (j - m))

/-- **Scale/translation-shift invariance**, both signs of `m`, any centre `w`.  Direct
generalization of `lem_as_coarse_shallow_grid_scale_shift` (there `k : ℕ` only) to `m : ℤ`;
the proof is unchanged except that the `k → (k:ℤ)` cast steps disappear. -/
theorem aux_transport_S_measurePreserving (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ)
    (w : SpatialCoordinates d) :
    MeasurePreserving (aux_transport_S m w)
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure := by
  set D := aux_transport_cellMap (d := d) m w with hD
  set ν := chaosRootFieldLaw model with hν
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun j => (scaledLayerLaw d ν j).toMeasure
  have hroot : ∀ z : SpatialCoordinates d, MeasurePreserving
      (fun f : C(SpatialCoordinates d, ℝ) =>
        f.comp (⟨fun x => x + z, continuous_id.add continuous_const⟩ :
          C(SpatialCoordinates d, SpatialCoordinates d)))
      ν.toMeasure ν.toMeasure := by
    intro z
    simpa [hν, chaosRootFieldLaw] using (gmc_zero_field_law_stationary model z)
  have hcompD : Measurable fun f : C(SpatialCoordinates d, ℝ) => f.comp D := by fun_prop
  have hlayer : ∀ j : ℤ,
      Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp D) (laws (j - m)) = laws j := by
    intro j
    let z : SpatialCoordinates d := (3 : ℝ) ^ (-(j - m)) • w
    let translateZ : C(SpatialCoordinates d, SpatialCoordinates d) :=
      ⟨fun x => x + z, continuous_id.add continuous_const⟩
    have hpow : (3 : ℝ) ^ (-(j - m)) * (3 : ℝ) ^ (-m) = (3 : ℝ) ^ (-j) := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      ring
    have hcomm :
        (fun f : C(SpatialCoordinates d, ℝ) => f.comp D) ∘ (layerScaling d (j - m)) =
          (layerScaling d j) ∘
            (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ) := by
      funext f
      ext x
      dsimp [ContinuousMap.compRightContinuousMap, layerScaling, ContinuousMap.comp,
        hD, aux_transport_cellMap, translateZ, z]
      congr 1
      ext i
      rw [hD]
      simp only [aux_transport_cellMap, ContinuousMap.coe_mk,
        cubeDilation_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, sub_zero,
        Pi.zero_apply]
      rw [mul_add, ← mul_assoc, hpow]
      ring
    change Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp D)
        (Measure.map (layerScaling d (j - m)) ν.toMeasure) =
      Measure.map (layerScaling d j) ν.toMeasure
    calc
      Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp D)
          (Measure.map (layerScaling d (j - m)) ν.toMeasure) =
          Measure.map ((fun f : C(SpatialCoordinates d, ℝ) => f.comp D) ∘
            layerScaling d (j - m)) ν.toMeasure :=
        Measure.map_map hcompD (layerScaling d (j - m)).continuous.measurable
      _ = Measure.map ((layerScaling d j) ∘
            (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ)) ν.toMeasure := by
        rw [hcomm]
      _ = Measure.map (layerScaling d j)
          (Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ)
            ν.toMeasure) :=
        (Measure.map_map (layerScaling d j).continuous.measurable (by fun_prop)).symm
      _ = Measure.map (layerScaling d j) ν.toMeasure := by
        rw [(hroot z).map_eq]
  have hre : Measure.map (fun (omC : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => omC (j - m))
      (Measure.infinitePi laws) = Measure.infinitePi (fun j => laws (j - m)) := by
    have h := Measure.infinitePi_map_piCongrLeft (fun j : ℤ => laws (j - m)) (Equiv.addRight m)
    have e1 : (fun a : ℤ => (fun j : ℤ => laws (j - m)) (Equiv.addRight m a)) = laws := by
      funext a
      simp
    have e2 : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ => C(SpatialCoordinates d, ℝ))
        (Equiv.addRight m)) =
        fun (omC : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => omC (j - m) := by
      funext omC j
      simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, sub_eq_add_neg]
    rw [e1, e2] at h
    exact h
  have hco := Measure.infinitePi_map_pi (μ := fun j => laws (j - m))
    (f := fun _ : ℤ => fun f : C(SpatialCoordinates d, ℝ) => f.comp D) (fun _ => hcompD)
  refine ⟨aux_transport_S_measurable m w, ?_⟩
  have hsplit : aux_transport_S (d := d) m w =
      (fun (x : ℤ → C(SpatialCoordinates d, ℝ)) (i : ℤ) => (x i).comp D) ∘
        (fun (omC : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => omC (j - m)) := rfl
  change Measure.map (aux_transport_S m w) (Measure.infinitePi laws) = Measure.infinitePi laws
  have hg : Measurable (fun (x : ℤ → C(SpatialCoordinates d, ℝ)) (i : ℤ) => (x i).comp D) :=
    measurable_pi_lambda _ fun i => hcompD.comp (measurable_pi_apply i)
  have hf : Measurable (fun (omC : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => omC (j - m)) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (j - m)
  have hco' : Measure.map (fun (x : ℤ → C(SpatialCoordinates d, ℝ)) (i : ℤ) => (x i).comp D)
      (Measure.infinitePi fun j => laws (j - m)) =
      Measure.infinitePi fun i => Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp D)
        (laws (i - m)) := hco
  rw [hsplit, ← Measure.map_map hg hf, hre, hco']
  congr 1
  funext j
  exact hlayer j

end MeasurePreservingS

/-! ## (T2) Band transfer: `S_{m,w}` is measurable from the `Icc (a-m) (b-m)`-comap to the
`Icc a b`-comap, and preserves `eLpNorm`. -/

/-- The value-window projection reading layers `Icc a b` (the shape lem_band's own `hband`
premises use: `fun omega => fun j : Set.Icc lo hi => omega (j:ℤ)`). -/
def aux_transport_window {d : ℕ} (a b : ℤ) (om : BilateralField d) :
    ↥(Set.Icc a b) → C(SpatialCoordinates d, ℝ) := fun j => om (j : ℤ)

section BandTransfer

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_transport_window_measurable (a b : ℤ) :
    Measurable (aux_transport_window (d := d) a b) :=
  measurable_pi_lambda _ fun j => measurable_pi_apply (j : ℤ)

theorem aux_transport_window_le_top (a b : ℤ) :
    MeasurableSpace.comap (aux_transport_window (d := d) a b) inferInstance ≤
      (inferInstance : MeasurableSpace (BilateralField d)) :=
  (aux_transport_window_measurable a b).comap_le

/-- The reindexing map realizing `window a b ∘ S = reindex ∘ window (a-m) (b-m)`: reads
layer `j - m` in the chart `y ↦ w + 3^{-m} y`. -/
def aux_transport_reindex {d : ℕ} (m : ℤ) (w : SpatialCoordinates d) (a b : ℤ)
    (g : ↥(Set.Icc (a - m) (b - m)) → C(SpatialCoordinates d, ℝ)) :
    ↥(Set.Icc a b) → C(SpatialCoordinates d, ℝ) :=
  fun j => (g ⟨(j : ℤ) - m, by
      have hj := j.2
      rw [Set.mem_Icc] at hj ⊢
      omega⟩).comp (aux_transport_cellMap m w)

theorem aux_transport_reindex_measurable (m : ℤ) (w : SpatialCoordinates d) (a b : ℤ) :
    Measurable (aux_transport_reindex (d := d) m w a b) := by
  refine measurable_pi_lambda _ fun j => ?_
  have hc : Measurable fun f : C(SpatialCoordinates d, ℝ) =>
      f.comp (aux_transport_cellMap m w) := by fun_prop
  exact hc.comp (measurable_pi_apply _)

theorem aux_transport_window_comp_S (m : ℤ) (w : SpatialCoordinates d) (a b : ℤ)
    (om : BilateralField d) :
    aux_transport_window a b (aux_transport_S m w om) =
      aux_transport_reindex m w a b (aux_transport_window (a - m) (b - m) om) := by
  funext j
  simp only [aux_transport_window, aux_transport_reindex, aux_transport_S]

/-- The core measurability transfer: `S_{m,w}` pulls the `Icc a b`-comap σ-algebra back to
a sub-σ-algebra of the `Icc (a-m) (b-m)`-comap. -/
theorem aux_transport_comap_le (m : ℤ) (w : SpatialCoordinates d) (a b : ℤ) :
    (MeasurableSpace.comap (aux_transport_window (d := d) a b) inferInstance).comap
        (aux_transport_S m w) ≤
      MeasurableSpace.comap (aux_transport_window (d := d) (a - m) (b - m)) inferInstance := by
  rw [MeasurableSpace.comap_comp]
  have hfac : aux_transport_window a b ∘ aux_transport_S m w =
      aux_transport_reindex m w a b ∘ aux_transport_window (a - m) (b - m) := by
    funext om
    exact aux_transport_window_comp_S m w a b om
  rw [hfac, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (aux_transport_reindex_measurable m w a b).comap_le

theorem aux_transport_S_measurable_window (m : ℤ) (w : SpatialCoordinates d) (a b : ℤ) :
    Measurable[MeasurableSpace.comap (aux_transport_window (d := d) (a - m) (b - m))
        inferInstance,
      MeasurableSpace.comap (aux_transport_window (d := d) a b) inferInstance]
      (aux_transport_S m w) :=
  Measurable.of_comap_le (aux_transport_comap_le m w a b)

/-- **Band transfer, measurability half**: if `Y` is `AEStronglyMeasurable` for the
`Icc a b`-comap, then `Y ∘ S_{m,w}` is `AEStronglyMeasurable` for the `Icc (a-m) (b-m)`-comap
(both w.r.t. the same `chaosSampleLaw`). -/
theorem aux_transport_band_aestronglyMeasurable (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (m : ℤ) (w : SpatialCoordinates d) (a b : ℤ) {Y : BilateralField d → ℝ}
    (hY : AEStronglyMeasurable[MeasurableSpace.comap (aux_transport_window (d := d) a b)
        inferInstance] Y (chaosSampleLaw model).toMeasure) :
    AEStronglyMeasurable[MeasurableSpace.comap
        (aux_transport_window (d := d) (a - m) (b - m)) inferInstance]
      (Y ∘ aux_transport_S m w) (chaosSampleLaw model).toMeasure := by
  obtain ⟨g, hg_sm, hg_eq⟩ := hY
  refine ⟨g ∘ aux_transport_S m w,
    hg_sm.comp_measurable (aux_transport_S_measurable_window m w a b), ?_⟩
  exact (aux_transport_S_measurePreserving model m w).quasiMeasurePreserving.ae hg_eq

/-- **Band transfer, norm half**: `eLpNorm` is unchanged by `∘ S_{m,w}` (measure preservation
alone; the comap hypothesis only upgrades the ambient `AEStronglyMeasurable` needed here). -/
theorem aux_transport_band_eLpNorm (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (m : ℤ) (w : SpatialCoordinates d) (a b : ℤ) (p : ℝ≥0∞) {Y : BilateralField d → ℝ}
    (hY : AEStronglyMeasurable[MeasurableSpace.comap (aux_transport_window (d := d) a b)
        inferInstance] Y (chaosSampleLaw model).toMeasure) :
    eLpNorm (Y ∘ aux_transport_S m w) p (chaosSampleLaw model).toMeasure =
      eLpNorm Y p (chaosSampleLaw model).toMeasure := by
  obtain ⟨g, hg_sm, hg_eq⟩ := hY
  have hYamb : AEStronglyMeasurable Y (chaosSampleLaw model).toMeasure :=
    ⟨g, hg_sm.mono (aux_transport_window_le_top a b), hg_eq⟩
  exact eLpNorm_comp_measurePreserving hYamb (aux_transport_S_measurePreserving model m w)

end BandTransfer




/-- `retained`, exactly `lem_band`'s own `let` (`ret` of the audit, specialized to a field and
a point). -/
def aux_transport_ret (m : ℤ) (f : ℤ → ℝ) : ℝ :=
  if 0 ≤ m then ∑ j ∈ Finset.Ico (0 : ℤ) m, f (-j) else -∑ j ∈ Finset.Ico m (0 : ℤ), f (-j)

/-- `retained n z om`, exactly `lem_band`'s own `let`. -/
def aux_transport_retained {d : ℕ} (n : ℤ) (z : SpatialCoordinates d) (om : BilateralField d) :
    ℝ := aux_transport_ret n (fun j => om j z)

theorem aux_transport_retained_eq {d : ℕ} (n : ℤ) (z : SpatialCoordinates d)
    (om : BilateralField d) :
    aux_transport_retained n z om =
      (if 0 ≤ n then ∑ j ∈ Finset.Ico (0 : ℤ) n, om (-j) z
       else -∑ j ∈ Finset.Ico n (0 : ℤ), om (-j) z) := rfl

theorem aux_transport_sum_range_shift (G : ℤ → ℝ) (a : ℤ) (t : ℕ) :
    ∑ k ∈ Finset.range t, G (a + k) = ∑ j ∈ Finset.Ico a (a + t), G j := by
  refine Finset.sum_nbij' (fun k : ℕ => a + (k : ℤ)) (fun j : ℤ => (j - a).toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Ico]; omega
  · intro j hj; simp only [Finset.mem_Ico] at hj
    simp only [Finset.mem_range]; omega
  · intro k _; simp
  · intro j hj; simp only [Finset.mem_Ico] at hj; simp only; omega
  · intro k _; rfl

/-- Cutoff-potential transport (AUD1 `potential_transport`): `Σ_{j=0}^N f(-j) =
Σ_{k=0}^{N-m} f(-k-m) + ret m f`, for every integer `m ≤ N`, both signs of `m`. -/
theorem aux_transport_potential_sum (f : ℤ → ℝ) (N : ℕ) (m : ℤ) (hm : m ≤ (N : ℤ)) :
    ∑ j ∈ Finset.range (N + 1), f (-(Int.ofNat j)) =
      ∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1), f (-(Int.ofNat k) - m) +
        aux_transport_ret m f := by
  have hL : ∑ j ∈ Finset.range (N + 1), f (-(Int.ofNat j)) =
      ∑ j ∈ Finset.Ico (0 : ℤ) ((N : ℤ) + 1), f (-j) := by
    have := aux_transport_sum_range_shift (fun j => f (-j)) 0 (N + 1)
    simpa using this
  have hR : ∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1), f (-(Int.ofNat k) - m) =
      ∑ j ∈ Finset.Ico m ((N : ℤ) + 1), f (-j) := by
    have h1 := aux_transport_sum_range_shift (fun j => f (-j)) m (((N : ℤ) - m).toNat + 1)
    have h2 : m + ((((N : ℤ) - m).toNat + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by omega
    rw [h2] at h1
    rw [← h1]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1; simp; ring
  rw [hL, hR]
  unfold aux_transport_ret
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0]
    have hU : Finset.Ico (0 : ℤ) ((N : ℤ) + 1) =
        Finset.Ico (0 : ℤ) m ∪ Finset.Ico m ((N : ℤ) + 1) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
    have hD : Disjoint (Finset.Ico (0 : ℤ) m) (Finset.Ico m ((N : ℤ) + 1)) :=
      Finset.disjoint_left.2 (by intro x hx hx'; simp only [Finset.mem_Ico] at hx hx'; omega)
    rw [hU, Finset.sum_union hD]; ring
  · rw [if_neg h0]
    have hU : Finset.Ico m ((N : ℤ) + 1) =
        Finset.Ico m (0 : ℤ) ∪ Finset.Ico (0 : ℤ) ((N : ℤ) + 1) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
    have hD : Disjoint (Finset.Ico m (0 : ℤ)) (Finset.Ico (0 : ℤ) ((N : ℤ) + 1)) :=
      Finset.disjoint_left.2 (by intro x hx hx'; simp only [Finset.mem_Ico] at hx hx'; omega)
    rw [hU, Finset.sum_union hD]; ring

/-- Infrared partial-sum transport (AUD1 `infrared_transport`), both signs of `m`. -/
theorem aux_transport_infrared_sum (F : ℤ → ℝ) (m : ℤ) (L : ℕ) (hL : m ≤ (L : ℤ)) :
    ∑ n ∈ Finset.range L, F ((Int.ofNat (n + 1)) - m) =
      ∑ n ∈ Finset.range (((L : ℤ) - m).toNat), F (Int.ofNat (n + 1)) +
        aux_transport_ret m F := by
  have hA : ∑ n ∈ Finset.range L, F ((Int.ofNat (n + 1)) - m) =
      ∑ j ∈ Finset.Ico (1 - m) (1 - m + L), F j := by
    rw [← aux_transport_sum_range_shift F (1 - m) L]
    refine Finset.sum_congr rfl (fun k _ => ?_); congr 1; simp; ring
  have hB : ∑ n ∈ Finset.range (((L : ℤ) - m).toNat), F (Int.ofNat (n + 1)) =
      ∑ j ∈ Finset.Ico 1 (1 - m + L), F j := by
    have h1 := aux_transport_sum_range_shift F 1 (((L : ℤ) - m).toNat)
    have h2 : (1 : ℤ) + ((((L : ℤ) - m).toNat : ℕ) : ℤ) = 1 - m + L := by omega
    rw [h2] at h1; rw [← h1]
    refine Finset.sum_congr rfl (fun k _ => ?_); congr 1; simp; ring
  rw [hA, hB]; unfold aux_transport_ret
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0]
    have hrefl : ∑ j ∈ Finset.Ico (0 : ℤ) m, F (-j) = ∑ i ∈ Finset.Ico (1 - m) 1, F i := by
      refine Finset.sum_nbij' (fun j => -j) (fun i => -i) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
      · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
      · intro j _; simp
      · intro i _; simp
      · intro j _; rfl
    rw [hrefl]
    have hU : Finset.Ico (1 - m) (1 - m + L) = Finset.Ico (1 - m) 1 ∪ Finset.Ico 1 (1 - m + L) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
    have hD : Disjoint (Finset.Ico (1 - m) 1) (Finset.Ico 1 (1 - m + L)) :=
      Finset.disjoint_left.2 (by intro x hx hx'; simp only [Finset.mem_Ico] at hx hx'; omega)
    rw [hU, Finset.sum_union hD]; ring
  · rw [if_neg h0]
    have hrefl : ∑ j ∈ Finset.Ico m (0 : ℤ), F (-j) = ∑ i ∈ Finset.Ico 1 (1 - m), F i := by
      refine Finset.sum_nbij' (fun j => -j) (fun i => -i) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
      · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
      · intro j _; simp
      · intro i _; simp
      · intro j _; rfl
    rw [hrefl]
    have hU : Finset.Ico 1 (1 - m + L) = Finset.Ico 1 (1 - m) ∪ Finset.Ico (1 - m) (1 - m + L) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
    have hD : Disjoint (Finset.Ico 1 (1 - m)) (Finset.Ico (1 - m) (1 - m + L)) :=
      Finset.disjoint_left.2 (by intro x hx hx'; simp only [Finset.mem_Ico] at hx hx'; omega)
    rw [hU, Finset.sum_union hD]; ring

theorem aux_transport_ret_sub (m : ℤ) (f g : ℤ → ℝ) :
    aux_transport_ret m (fun i => f i - g i) = aux_transport_ret m f - aux_transport_ret m g := by
  unfold aux_transport_ret; split_ifs <;> simp [Finset.sum_sub_distrib] <;> ring

theorem aux_transport_toNat_tendsto (m : ℤ) :
    Tendsto (fun L : ℕ => (((L : ℤ) - m).toNat)) atTop atTop := by
  apply tendsto_atTop_atTop.2
  intro K
  refine ⟨(K + m.toNat + 1), fun L hL => ?_⟩
  omega

/-! ## (T3) Infrared transport -/

theorem aux_transport_infraredPartialSum_apply {d : ℕ} (om : BilateralField d) (L : ℕ)
    (z : SpatialCoordinates d) :
    infraredPartialSum om L z =
      ∑ n ∈ Finset.range L, (om (Int.ofNat (n + 1)) z - om (Int.ofNat (n + 1)) 0) := by
  simp [infraredPartialSum, ContinuousMap.sum_apply]

theorem aux_transport_infraredPartialSum_diff {d : ℕ} (om : BilateralField d) (K : ℕ)
    (x w : SpatialCoordinates d) :
    ∑ n ∈ Finset.range K, (om (Int.ofNat (n + 1)) x - om (Int.ofNat (n + 1)) w) =
      infraredPartialSum om K x - infraredPartialSum om K w := by
  rw [aux_transport_infraredPartialSum_apply, aux_transport_infraredPartialSum_apply,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem aux_transport_infraredPartialSum_S {d : ℕ} (m : ℤ) (w : SpatialCoordinates d)
    (om : BilateralField d) (L : ℕ) (hL : m ≤ (L : ℤ)) (y : SpatialCoordinates d) :
    infraredPartialSum (aux_transport_S m w om) L y =
      (infraredPartialSum om ((L : ℤ) - m).toNat (w + (3 : ℝ) ^ (-m) • y) -
          infraredPartialSum om ((L : ℤ) - m).toNat w) +
        (aux_transport_retained m (w + (3 : ℝ) ^ (-m) • y) om -
          aux_transport_retained m w om) := by
  set x := w + (3 : ℝ) ^ (-m) • y with hx
  rw [aux_transport_infraredPartialSum_apply]
  have hstep : ∀ n : ℕ,
      aux_transport_S m w om (Int.ofNat (n + 1)) y - aux_transport_S m w om (Int.ofNat (n + 1)) 0 =
        om (Int.ofNat (n + 1) - m) x - om (Int.ofNat (n + 1) - m) w := by
    intro n
    simp only [aux_transport_S_apply]
    have h0 : w + (3 : ℝ) ^ (-m) • (0 : SpatialCoordinates d) = w := by simp
    rw [h0]
  simp_rw [hstep]
  have hF := aux_transport_infrared_sum (fun j => om j x - om j w) m L hL
  simp only at hF
  rw [hF, aux_transport_infraredPartialSum_diff]
  have hret : aux_transport_ret m (fun j => om j x - om j w) =
      aux_transport_retained m x om - aux_transport_retained m w om :=
    aux_transport_ret_sub m (fun j => om j x) (fun j => om j w)
  rw [hret]

/-- **Infrared transport**: `H(S_{m,w} ω)(y) = H(ω)(x) - H(ω)(w) + retained(m,x,ω) -
retained(m,w,ω)` a.s., `x = w + 3^{-m} y`, both signs of `m`. -/
theorem aux_transport_infrared {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) (m : ℤ) (w : SpatialCoordinates d) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ y : SpatialCoordinates d,
        H (aux_transport_S m w om) y =
          H om (w + (3 : ℝ) ^ (-m) • y) - H om w +
            aux_transport_retained m (w + (3 : ℝ) ^ (-m) • y) om -
              aux_transport_retained m w om := by
  have h1 := hH.2
  have h2 := (aux_transport_S_measurePreserving M m w).quasiMeasurePreserving.ae hH.2
  filter_upwards [h1, h2] with om hom hom' y
  set x := w + (3 : ℝ) ^ (-m) • y with hx
  have hA : Tendsto (fun L : ℕ => infraredPartialSum (aux_transport_S m w om) L y) atTop
      (𝓝 (H (aux_transport_S m w om) y)) := by
    have hev : Tendsto (fun f : C(SpatialCoordinates d, ℝ) => f y)
        (𝓝 (H (aux_transport_S m w om))) (𝓝 (H (aux_transport_S m w om) y)) :=
      (continuous_eval_const _).tendsto _
    exact hev.comp hom'
  have hLx : Tendsto (fun L : ℕ => infraredPartialSum om (((L : ℤ) - m).toNat) x) atTop
      (𝓝 (H om x)) := by
    have hevx : Tendsto (fun f : C(SpatialCoordinates d, ℝ) => f x) (𝓝 (H om)) (𝓝 (H om x)) :=
      (continuous_eval_const _).tendsto _
    exact (hevx.comp hom).comp (aux_transport_toNat_tendsto m)
  have hLw : Tendsto (fun L : ℕ => infraredPartialSum om (((L : ℤ) - m).toNat) w) atTop
      (𝓝 (H om w)) := by
    have hevw : Tendsto (fun f : C(SpatialCoordinates d, ℝ) => f w) (𝓝 (H om)) (𝓝 (H om w)) :=
      (continuous_eval_const _).tendsto _
    exact (hevw.comp hom).comp (aux_transport_toNat_tendsto m)
  have hB : Tendsto (fun L : ℕ => infraredPartialSum (aux_transport_S m w om) L y) atTop
      (𝓝 ((H om x - H om w) + (aux_transport_retained m x om - aux_transport_retained m w om))) := by
    have hlim : Tendsto (fun L : ℕ =>
        (infraredPartialSum om (((L : ℤ) - m).toNat) x -
            infraredPartialSum om (((L : ℤ) - m).toNat) w) +
          (aux_transport_retained m x om - aux_transport_retained m w om)) atTop
        (𝓝 ((H om x - H om w) + (aux_transport_retained m x om - aux_transport_retained m w om))) :=
      (hLx.sub hLw).add_const _
    have heq : ∀ᶠ L : ℕ in atTop, m ≤ (L : ℤ) := by
      filter_upwards [Filter.eventually_ge_atTop m.toNat] with L hL
      omega
    refine hlim.congr' ?_
    filter_upwards [heq] with L hL
    exact (aux_transport_infraredPartialSum_S m w om L hL y).symm
  have hval := tendsto_nhds_unique hA hB
  linarith [hval]

/-! ## (T4) Coefficient identity -/

/-- `kappa`, exactly `lem_band`'s own `let`. -/
def aux_transport_kappa {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (J : ℕ) : ℝ :=
  Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M J

/-- `reference N n z om`, exactly `lem_band`'s own `let`. -/
def aux_transport_reference {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (n : ℤ)
    (z : SpatialCoordinates d) (om : BilateralField d) : ℝ :=
  aux_transport_kappa M (((N : ℤ) - n).toNat) / aux_transport_kappa M N *
    Real.exp (H om z + aux_transport_retained n z om)

theorem aux_transport_reference_pos {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (n : ℤ)
    (z : SpatialCoordinates d) (om : BilateralField d) :
    0 < aux_transport_reference M H N n z om := by
  unfold aux_transport_reference aux_transport_kappa
  have h1 : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (((N : ℤ) - n).toNat) :=
    SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _
  have h2 : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  positivity

/-- The finite potential-sum step (no `H`) underlying `aux_transport_coefficient`. -/
theorem aux_transport_potential {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) (m : ℤ) (w : SpatialCoordinates d) (N : ℕ)
    (hm : m ≤ (N : ℤ)) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ y : SpatialCoordinates d,
      cutoffPotential H om N (w + (3 : ℝ) ^ (-m) • y) =
        cutoffPotential H (aux_transport_S m w om) (((N : ℤ) - m).toNat) y +
          H om w + aux_transport_retained m w om := by
  filter_upwards [aux_transport_infrared hH m w] with om hom y
  set x := w + (3 : ℝ) ^ (-m) • y with hx
  have hSk : ∀ k : ℕ, (aux_transport_S m w om) (-(Int.ofNat k)) y = om (-(Int.ofNat k) - m) x := by
    intro k; exact aux_transport_S_apply m w om (-(Int.ofNat k)) y
  have hshift := aux_transport_potential_sum (fun j => om j x) N m hm
  simp only at hshift
  have hret : aux_transport_ret m (fun j => om j x) = aux_transport_retained m x om := rfl
  rw [hret] at hshift
  have hpsum : ∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1), (aux_transport_S m w om)
      (-(Int.ofNat k)) y =
      ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x - aux_transport_retained m x om := by
    rw [show (∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1), (aux_transport_S m w om)
        (-(Int.ofNat k)) y) =
        ∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1), om (-(Int.ofNat k) - m) x from
      Finset.sum_congr rfl (fun k _ => hSk k)]
    linarith [hshift]
  unfold cutoffPotential
  rw [hpsum, hom y]
  ring

/-- **Coefficient identity**: `A_N(ω)(w + 3^{-m}y) = reference(N,m,w,ω) ·
A_{N-m}^{S_{m,w}ω}(y)` a.s., both signs of `m` (paper 4511--4518's cell factorization,
`aux_lem_as_coarse_shallow_grid_cutoff_factor`, extended to both signs and to the true
infrared `H`). -/
theorem aux_transport_coefficient {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ) (w : SpatialCoordinates d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (N : ℕ) (hm : m ≤ (N : ℤ)) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ y : SpatialCoordinates d,
      cutoffCoefficient M H om N (w + (3 : ℝ) ^ (-m) • y) =
        aux_transport_reference M H N m w om *
          cutoffCoefficient M H (aux_transport_S m w om) (((N : ℤ) - m).toNat) y := by
  filter_upwards [aux_transport_potential hH m w N hm] with om hom y
  have hpot := hom y
  set K := ((N : ℤ) - m).toNat with hKdef
  have hNsub : (K : ℝ) = (N : ℝ) - (m : ℝ) := by
    have hnn : (0 : ℤ) ≤ (N : ℤ) - m := by omega
    have hKZ : (K : ℤ) = (N : ℤ) - m := by rw [hKdef]; exact Int.toNat_of_nonneg hnn
    exact_mod_cast hKZ
  have hposK : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M K := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M K
  have hposN : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hne1 : SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≠ 0 := hposN.ne'
  have hne2 : SubdiffusiveProcess.CoarseGrainingVocab.ahom M K ≠ 0 := hposK.ne'
  have hL1 : cutoffCoefficient M H om N (w + (3 : ℝ) ^ (-m) • y) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      Real.exp (cutoffPotential H om N (w + (3 : ℝ) ^ (-m) • y)) := by
    unfold cutoffCoefficient
    rw [Real.exp_sub]
    field_simp
  have hR1 : cutoffCoefficient M H (aux_transport_S m w om) K y *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M K *
      Real.exp (((K : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      Real.exp (cutoffPotential H (aux_transport_S m w om) K y) := by
    unfold cutoffCoefficient
    rw [Real.exp_sub]
    field_simp
  have hexppot : Real.exp (cutoffPotential H om N (w + (3 : ℝ) ^ (-m) • y)) =
      Real.exp (cutoffPotential H (aux_transport_S m w om) K y) *
        Real.exp (H om w + aux_transport_retained m w om) := by
    rw [hpot, ← Real.exp_add]
    congr 1
    ring
  have hcombine : cutoffCoefficient M H om N (w + (3 : ℝ) ^ (-m) • y) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      (cutoffCoefficient M H (aux_transport_S m w om) K y *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M K *
          Real.exp (((K : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) *
        Real.exp (H om w + aux_transport_retained m w om) := by
    rw [hL1, hR1, hexppot]
  unfold aux_transport_reference aux_transport_kappa
  have hexpN : Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≠ 0 :=
    (Real.exp_pos _).ne'
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hexpN hne1)]
  linear_combination hcombine

/-! ## Chart-level packaging: "the two charts agree a.e. on every descendant of the
origin cube" (T4's chart-object form, via `in_J`'s `chart`/`chart_eq`). -/

/-- `cubeDilation` is quasi-measure-preserving from the unit cube to the cube of side `r`. -/
theorem aux_transport_cubeDilation_qmp {d : ℕ} (z z' : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (h1 : (0 : ℝ) < 1) :
    Measure.QuasiMeasurePreserving (cubeDilation z z' r)
      (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  refine ⟨(continuous_cubeDilation z z' r).measurable, ?_⟩
  rw [map_cubeDilation_restrict z z' hr h1]
  exact Measure.smul_absolutelyContinuous

theorem aux_transport_chart_agree {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (N : ℕ) (m : ℤ) (hm : m ≤ (N : ℤ)) (w : SpatialCoordinates d)
    (sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n)) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ Q : Homogenization.TriadicCube d,
        Homogenization.openCubeSet Q ⊆
          Homogenization.openCubeSet (Homogenization.originCube d 0) →
        ∀ᵐ pt ∂ volume.restrict (Homogenization.openCubeSet Q),
          ((I.chart w ((3 : ℝ) ^ (-m)) (sidePos m)
              (Lane4.cutoffPositiveCoefficient M H om N w (sidePos m)) w
              ((3 : ℝ) ^ (-m))).coeffOn Q).toCoeffField pt =
            ((I.chart 0 1 one_pos
              (scalePositiveCoefficient (aux_transport_reference M H N m w om)
                (aux_transport_reference_pos M H N m w om)
                (Lane4.cutoffPositiveCoefficient M H (aux_transport_S m w om)
                  (((N : ℤ) - m).toNat) 0 one_pos))
              0 1).coeffOn Q).toCoeffField pt := by
  filter_upwards [aux_transport_coefficient M m w hH N hm] with om hom Q hQ
  set K := ((N : ℤ) - m).toNat with hKdef
  set r : ℝ := (3 : ℝ) ^ (-m) with hrdef
  set A' := Lane4.cutoffPositiveCoefficient M H (aux_transport_S m w om) K 0 one_pos with hA'def
  set ref := aux_transport_reference M H N m w om with hrefdef
  have hrefpos := aux_transport_reference_pos M H N m w om
  have hb : (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) =
      Homogenization.openCubeSet (Homogenization.originCube d 0) := by
    have h0 := centeredCube_zero_eq_openCubeSet_originCube (d := d) 0 (by norm_num)
    simpa using h0
  have hQ' : Homogenization.openCubeSet Q ⊆
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    rw [hb]; exact hQ
  have hACR : volume.restrict (Homogenization.openCubeSet Q) ≪
      volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) :=
    (Measure.restrict_mono hQ' (le_refl volume)).absolutelyContinuous
  have hRval : ∀ᵐ x ∂ volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      ∀ hx : x ∈ centeredCube (0 : SpatialCoordinates d) 1 one_pos,
        A'.val x = cutoffCoefficientCM M H (aux_transport_S m w om) K 0 one_pos
          ⟨x, centeredCube_subset_closedCube 0 one_pos hx⟩ / 1 :=
    @normalizedContinuousPositiveCoefficient_coeFn d
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos)
      (closedCube (0 : SpatialCoordinates d) 1 one_pos) ⟨centeredCube_subset_closedCube 0 one_pos⟩
      (cutoffCoefficientCM M H (aux_transport_S m w om) K 0 one_pos)
      (cutoffCoefficientCM_pos M H (aux_transport_S m w om) K 0 one_pos) 1 one_pos
  have hLmapsTo := cubeDilation_mapsTo w (0 : SpatialCoordinates d) (sidePos m) one_pos
  have hqmpL := aux_transport_cubeDilation_qmp w (0 : SpatialCoordinates d) (sidePos m) one_pos
  have hLval : ∀ᵐ x ∂ volume.restrict (centeredCube w r (sidePos m) : Set (SpatialCoordinates d)),
      ∀ hx : x ∈ centeredCube w r (sidePos m),
        (Lane4.cutoffPositiveCoefficient M H om N w (sidePos m)).val x =
          cutoffCoefficientCM M H om N w (sidePos m)
            ⟨x, centeredCube_subset_closedCube w (sidePos m) hx⟩ / 1 :=
    @normalizedContinuousPositiveCoefficient_coeFn d
      (centeredCube w r (sidePos m)) (closedCube w r (sidePos m))
      ⟨centeredCube_subset_closedCube w (sidePos m)⟩
      (cutoffCoefficientCM M H om N w (sidePos m))
      (cutoffCoefficientCM_pos M H om N w (sidePos m)) 1 one_pos
  have hLval' := hqmpL.ae hLval
  have hAsc := scalePositiveCoefficient_coeFn ref hrefpos A'
  have hLchart := I.chart_eq w r (sidePos m) (Lane4.cutoffPositiveCoefficient M H om N w
      (sidePos m)) w r (sidePos m) Set.Subset.rfl Q hQ
  have hRchart := I.chart_eq 0 1 one_pos (scalePositiveCoefficient ref hrefpos A') 0 1 one_pos
    Set.Subset.rfl Q hQ
  have hmemQ : ∀ᵐ pt ∂ volume.restrict (Homogenization.openCubeSet Q),
      pt ∈ Homogenization.openCubeSet Q :=
    ae_restrict_mem (Homogenization.measurableSet_openCubeSet Q)
  filter_upwards [hLchart, hRchart, hACR.ae_le hRval, hACR.ae_le hLval', hACR.ae_le hAsc, hmemQ]
    with pt hLpt hRpt hRcoeFn hLcoeFn hAcoeFn hptQ
  have hptC : pt ∈ (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) := hQ' hptQ
  have hLmem : cubeDilation w 0 r pt ∈
      (centeredCube w r (sidePos m) : Set (SpatialCoordinates d)) := hLmapsTo pt hptC
  rw [hLpt, hRpt]
  have hcoordL : (fun i => w i + r * pt i) = cubeDilation w 0 r pt := by
    funext i; simp [cubeDilation_apply]
  have hcoordR : (fun i => (0 : SpatialCoordinates d) i + 1 * pt i) = pt := by
    funext i; simp
  rw [hcoordL, hcoordR]
  have key : (Lane4.cutoffPositiveCoefficient M H om N w (sidePos m)).val
      (cubeDilation w 0 r pt) = (scalePositiveCoefficient ref hrefpos A').val pt := by
    rw [hAcoeFn, hRcoeFn hptC, hLcoeFn hLmem]
    show cutoffCoefficient M H om N (cubeDilation w 0 r pt) / 1 =
        ref * (cutoffCoefficient M H (aux_transport_S m w om) K pt / 1)
    rw [div_one, div_one]
    rw [show cubeDilation w 0 r pt = w + r • pt from by funext i; simp [cubeDilation_apply]]
    exact hom pt
  exact congrArg Homogenization.scalarMatrix key

/-! ## New for B-NH: affine transport of the a.e.-cube data both ways

`T := cubeDilation z z0 r` carries the unit Neumann cube `Q1` onto the general root cube
`Q = centeredCube z r hr`.  `lem_as_regularity_affine_transport` already pulls `SolvesNeumann`
data *down* from `Q` to `Q1` (giving `a1`, `F1`, `v1` on `Q1`).  To go back *up* -- recovering a
Hölder representative on `Q` from one on `Q1` -- we need the reverse a.e. transfer.  This does
NOT need `T` to be shown invertible as a measure isomorphism: the *exact* (not merely quasi-)
pushforward relation `map T (volume.restrict Q1) = c • volume.restrict Q` already supplied by
`map_cubeDilation_restrict`, combined with `MeasureTheory.ae_map_iff` and
`Measure.ae_smul_measure_iff`, gives both directions of the a.e. transfer directly. -/

/-- Transporting an a.e.-`Q`(root cube) statement to an a.e.-`Q1`(unit Neumann cube) statement
and back, through `T := cubeDilation z z0 r`. -/
theorem aux_fscc_holNeuH_ae_iff {d : ℕ} (z z0 : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {p : SpatialCoordinates d → Prop} (hp : MeasurableSet {x | p x}) :
    (∀ᵐ y ∂ volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), p y) ↔
      ∀ᵐ x ∂ volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        p (cubeDilation z z0 r x) := by
  have hmap := map_cubeDilation_restrict z z0 hr one_pos
  have hmeas : Measurable (cubeDilation z z0 r) := (continuous_cubeDilation z z0 r).measurable
  have hc : (ENNReal.ofReal |(r ^ d)⁻¹| : ℝ≥0∞) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  rw [← ae_map_iff hmeas.aemeasurable hp, hmap, MeasureTheory.Measure.ae_smul_measure_iff hc]

/-- Transport a *global* `alpha`-Hölder representative from the unit cube (any centre `zq`,
side `1`) to a general cube of side `r`, via `U := U1 ∘ cubeDilation zq z r⁻¹`, for **any**
`r > 0` (both `r ≥ 1` and `r < 1`; unlike `aux_prop_growth_large_root_holder_transport_gen`,
which needs `r ≥ 1`, since there the target-cube ratio is compared *without* a scale factor).
The Hölder seminorm picks up the scale factor `r ^ (-alpha)`, computed from the *exact*
pointwise relation `(ratio at (x,y)) = r ^ (-alpha) * (ratio at (x', y'))`, `x' y'` the
`r⁻¹`-dilated points, via `sqrt_sum_sq_cubeDilation`. -/
theorem aux_fscc_holNeuH_holder_transport {d : ℕ} (z zq : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) {alpha : ℝ} (halpha : 0 ≤ alpha) (U1 : SpatialCoordinates d → ℝ)
    (hU1c : ContinuousOn U1 (closedCube zq 1 one_pos : Set (SpatialCoordinates d)))
    (hU1h : IsHolderOn alpha (closedCube zq 1 one_pos : Set (SpatialCoordinates d)) U1) :
    let U : SpatialCoordinates d → ℝ := fun y => U1 (cubeDilation zq z r⁻¹ y)
    ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
      IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
      holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
        r ^ (-alpha) *
          holderSeminorm alpha (closedCube zq 1 one_pos : Set (SpatialCoordinates d)) U1 := by
  intro U
  have hmaps : Set.MapsTo (cubeDilation zq z r⁻¹) (closedCube z r hr : Set (SpatialCoordinates d))
      (closedCube zq 1 one_pos : Set (SpatialCoordinates d)) :=
    fun _ hx => aux_prop_growth_large_root_cubeDilation_inv_mem_closedCube_gen z zq hr one_pos hr
      (by ring) hx
  have hUc : ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) :=
    hU1c.comp' (continuous_cubeDilation zq z r⁻¹).continuousOn hmaps
  have hinj : ∀ x, cubeDilation z zq r (cubeDilation zq z r⁻¹ x) = x := by
    intro x
    have hrne : r ≠ 0 := hr.ne'
    funext i; simp only [cubeDilation_apply]; field_simp; ring
  have hralpha : 0 < r ^ (-alpha) := Real.rpow_pos_of_pos hr _
  have hkey : ∀ v ∈ holderRatioSet alpha (closedCube z r hr : Set (SpatialCoordinates d)) U,
      ∃ w ∈ holderRatioSet alpha
          (closedCube zq 1 one_pos : Set (SpatialCoordinates d)) U1, v = r ^ (-alpha) * w := by
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    set x' := cubeDilation zq z r⁻¹ x with hx'
    set y' := cubeDilation zq z r⁻¹ y with hy'
    have hx'y' : x' ≠ y' := by
      intro h; apply hxy; rw [← hinj x, ← hinj y]; exact congrArg _ h
    have hxmem : x' ∈ (closedCube zq 1 one_pos : Set (SpatialCoordinates d)) :=
      aux_prop_growth_large_root_cubeDilation_inv_mem_closedCube_gen z zq hr one_pos hr
        (by ring) hx
    have hymem : y' ∈ (closedCube zq 1 one_pos : Set (SpatialCoordinates d)) :=
      aux_prop_growth_large_root_cubeDilation_inv_mem_closedCube_gen z zq hr one_pos hr
        (by ring) hy
    set e' : ℝ := Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2) with he'
    have he'pos : 0 < e' := by
      rw [he', Real.sqrt_pos]
      obtain ⟨i, hi⟩ : ∃ i, x' i ≠ y' i := by
        by_contra hcon; push_neg at hcon; exact hx'y' (funext hcon)
      exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2
          (sub_ne_zero.2 hi)))) (Finset.single_le_sum (f := fun j => (x' j - y' j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i))
    have hdist : Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2) = r⁻¹ *
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := sqrt_sum_sq_cubeDilation zq z (inv_pos.2 hr) x y
    have heE : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) = r * e' := by
      rw [he', hdist]; field_simp
    refine ⟨|U1 x' - U1 y'| / e' ^ alpha, ⟨x', hxmem, y', hymem, hx'y', rfl⟩, ?_⟩
    have hUxy : U x - U y = U1 x' - U1 y' := rfl
    rw [hUxy, heE, Real.mul_rpow hr.le he'pos.le, Real.rpow_neg hr.le]
    field_simp
  have hbound : ∀ v ∈ holderRatioSet alpha (closedCube z r hr : Set (SpatialCoordinates d)) U,
      v ≤ r ^ (-alpha) *
        holderSeminorm alpha (closedCube zq 1 one_pos : Set (SpatialCoordinates d)) U1 := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := hkey v hv
    have hwle : w ≤ holderSeminorm alpha (closedCube zq 1 one_pos : Set (SpatialCoordinates d))
        U1 := le_csSup hU1h hw
    rw [hvw]
    exact mul_le_mul_of_nonneg_left hwle hralpha.le
  have hbdd : BddAbove (holderRatioSet alpha (closedCube z r hr : Set (SpatialCoordinates d)) U) :=
    ⟨r ^ (-alpha) * holderSeminorm alpha (closedCube zq 1 one_pos : Set (SpatialCoordinates d))
      U1, hbound⟩
  have hcAlpha0 : 0 ≤ r ^ (-alpha) *
      holderSeminorm alpha (closedCube zq 1 one_pos : Set (SpatialCoordinates d)) U1 :=
    mul_nonneg hralpha.le
      (aux_fscc_holder_predicates_holderSeminorm_nonneg alpha _ U1)
  exact ⟨hUc, hbdd, Real.sSup_le hbound hcAlpha0⟩

/-- `IsHolderOn` + a direct `holderSeminorm ≤ C` bound (no `cAlphaNorm` detour) give the
difference-quotient bound. Same computation as
`aux_lem_finite_source_comparison_cells_holder_dist`, starting one step later (that lemma's
first line derives `holderSeminorm ≤ C` from a `cAlphaNorm` hypothesis; here it is the
hypothesis directly). -/
theorem aux_fscc_holNeuH_holder_dist_of_seminorm {d : ℕ}
    (S : Set (SpatialCoordinates d)) (U : SpatialCoordinates d → ℝ) (alpha C : ℝ)
    (halpha : 0 < alpha) (hH : IsHolderOn alpha S U)
    (hsemi : holderSeminorm alpha S U ≤ C) :
    ∀ x ∈ S, ∀ y ∈ S, |U x - U y| ≤ Real.sqrt d ^ alpha * C * dist x y ^ alpha := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero, dist_self]
    rw [Real.zero_rpow halpha.ne']
    simp
  · set e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with he
    have hepos : 0 < e := by
      rw [he, Real.sqrt_pos]
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra hcon
        push_neg at hcon
        exact hxy (funext hcon)
      have hj' : 0 < (x j - y j) ^ 2 := by
        have : x j - y j ≠ 0 := sub_ne_zero.2 hj
        positivity
      exact lt_of_lt_of_le hj' (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j))
    have heα : 0 < e ^ alpha := Real.rpow_pos_of_pos hepos alpha
    have hratio : |U x - U y| / e ^ alpha ≤ holderSeminorm alpha S U :=
      le_csSup hH ⟨x, hx, y, hy, hxy, rfl⟩
    have h1 : |U x - U y| ≤ C * e ^ alpha := by
      have := (div_le_iff₀ heα).1 (hratio.trans hsemi)
      linarith
    have h2 : e ^ alpha ≤ Real.sqrt d ^ alpha * dist x y ^ alpha := by
      rw [← Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg]
      exact Real.rpow_le_rpow hepos.le (aux_fscc_holder_predicates_euclid_le x y)
        halpha.le
    have hC0 : 0 ≤ C :=
      (aux_fscc_holder_predicates_holderSeminorm_nonneg _ _ _).trans hsemi
    calc |U x - U y| ≤ C * e ^ alpha := h1
      _ ≤ C * (Real.sqrt d ^ alpha * dist x y ^ alpha) := by gcongr
      _ = Real.sqrt d ^ alpha * C * dist x y ^ alpha := by ring

/-- The value of `cutoffPositiveCoefficient` is the *global* `cutoffCoefficient` function,
evaluated pointwise, a.e. on its own cube (no normalization, no shift). -/
theorem aux_fscc_holNeuH_cutoffPos_val {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂ volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient model H omega N z hr).val x =
        cutoffCoefficient model H omega N x := by
  have h := @normalizedContinuousPositiveCoefficient_coeFn d (centeredCube z r hr)
    (closedCube z r hr) ⟨centeredCube_subset_closedCube z hr⟩
    (cutoffCoefficientCM model H omega N z hr) (cutoffCoefficientCM_pos model H omega N z hr)
    1 one_pos
  filter_upwards [h, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxmem
  unfold cutoffPositiveCoefficient
  rw [hx hxmem]
  simp [cutoffCoefficientCM]

/-- **Coefficient identification**: an arbitrary `PositiveCoefficient` on the unit cube (any
centre `z0`) that a.e. agrees with `cutoffCoefficient model H omega N` at the chart points
`w + 3^{-m} • x` equals the scaled, layer-shifted `cutoffPositiveCoefficient`, a.e.-`omega`. -/
theorem aux_fscc_holNeuH_coeff_ident {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H)
    (m : ℤ) (w : SpatialCoordinates d) (N : ℕ) (hm : m ≤ (N : ℤ)) (z0 : SpatialCoordinates d) :
    ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
      ∀ a1 : PositiveCoefficient (centeredCube z0 1 one_pos),
        (∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
          (a1.val : SpatialCoordinates d → ℝ) x =
            cutoffCoefficient model H omega N (w + (3 : ℝ) ^ (-m) • x)) →
        a1 = scalePositiveCoefficient (aux_transport_reference model H N m w omega)
          (aux_transport_reference_pos model H N m w omega)
          (cutoffPositiveCoefficient model H (aux_transport_S m w omega) ((N : ℤ) - m).toNat
            z0 one_pos) := by
  filter_upwards [aux_transport_coefficient model m w hH N hm] with omega hom a1 ha1
  have hA2 := aux_fscc_holNeuH_cutoffPos_val model H (aux_transport_S m w omega)
    ((N : ℤ) - m).toNat z0 one_pos
  have hval : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      (a1.val : SpatialCoordinates d → ℝ) x =
        (scalePositiveCoefficient (aux_transport_reference model H N m w omega)
          (aux_transport_reference_pos model H N m w omega)
          (cutoffPositiveCoefficient model H (aux_transport_S m w omega) ((N : ℤ) - m).toNat
            z0 one_pos)).val x := by
    filter_upwards [ha1, hA2,
      scalePositiveCoefficient_coeFn (aux_transport_reference model H N m w omega)
        (aux_transport_reference_pos model H N m w omega)
        (cutoffPositiveCoefficient model H (aux_transport_S m w omega) ((N : ℤ) - m).toNat
          z0 one_pos)] with x hx1 hx2 hx3
    rw [hx1, hx3, hx2, hom x]
  exact Subtype.ext (Lp.ext hval)

/-- Undo a positive scalar coefficient rescaling on the source of a Neumann problem: if
`a1 = scalePositiveCoefficient c hc a2` and `a1` solves the Neumann problem with source `F1`,
then `a2` solves it with source `F1 / c`. The `hident` substitution is isolated in its own
small lemma (rather than `rw`-ing it into a large accumulated goal) to keep elaboration fast. -/
theorem aux_fscc_holNeuH_solvesNeumann_unscale {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (c : ℝ) (hc : 0 < c) (a1 a2 : PositiveCoefficient Ω)
    (hident : a1 = scalePositiveCoefficient c hc a2)
    (F1 : SpatialCoordinates d → ℝ) (v1 : meanZeroSobolevGraph Ω)
    (hsolve : SolvesNeumann a1 F1 v1) :
    SolvesNeumann a2 (fun x => F1 x / c) v1 := by
  subst hident
  intro psi
  have h := hsolve psi
  rw [sobolevCoefficientForm_scale] at h
  have hne : c ≠ 0 := hc.ne'
  have heq : (∫ x in (Ω : Set (SpatialCoordinates d)), F1 x / c * (psi : SobolevData Ω).1 x) =
      c⁻¹ * ∫ x in (Ω : Set (SpatialCoordinates d)), F1 x * (psi : SobolevData Ω).1 x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [div_mul_eq_mul_div, div_eq_inv_mul]
  rw [heq, ← h]
  field_simp

/-- **Core per-`(J, omega)` content of B-NH**, isolated into its own declaration (elaborating
the whole chain inside one big accumulated tactic block times out at 200000 heartbeats): given
the coefficient identification at this `omega` (`hcoeff`) and the pulled-back
`cor_neumann_source` Hölder fact at this `omega` (`hcorS`, at cutoff `N` for the shifted field
`S_{m,w} omega`), produce the actual `holNeu` fact on the general cube `(z, r)`, `r = 3^{-m}`,
`m ≤ J`. -/
theorem aux_fscc_holNeuH_core {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z z0 w : SpatialCoordinates d) (m : ℤ) (r : ℝ) (hr : 0 < r) (alpha : ℝ) (halpha : 0 < alpha)
    (hz0 : z0 = fun _ : Fin d => (1 / 2 : ℝ))
    (hTeq : ∀ x : SpatialCoordinates d, cubeDilation z z0 r x = w + (3 : ℝ) ^ (-m) • x)
    (hinjQ : ∀ x : SpatialCoordinates d, cubeDilation z0 z r⁻¹ (cubeDilation z z0 r x) = x)
    (Kcor : ℕ → BilateralField d → ℝ) (J : ℕ) (omega : BilateralField d)
    (hcoeff : ∀ a1 : PositiveCoefficient (centeredCube z0 1 one_pos),
      (∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        (a1.val : SpatialCoordinates d → ℝ) x =
          cutoffCoefficient model H omega J (w + (3 : ℝ) ^ (-m) • x)) →
      a1 = scalePositiveCoefficient (aux_transport_reference model H J m w omega)
        (aux_transport_reference_pos model H J m w omega)
        (cutoffPositiveCoefficient model H (aux_transport_S m w omega) ((J : ℤ) - m).toNat
          z0 one_pos))
    (hcorS : ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        |F x| ≤ Kf) →
      (∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ v : meanZeroSobolevGraph (centeredCube z0 1 one_pos),
        SolvesNeumann
          (cutoffPositiveCoefficient model H (aux_transport_S m w omega) N z0 one_pos) F v →
        ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
          IsHolderOn alpha (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) U ∧
          ((v : SobolevData (centeredCube z0 1 one_pos)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))] U ∧
          cAlphaNorm alpha (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) U ≤
            Kcor N (aux_transport_S m w omega) * Kf)
    (hq : Measure.QuasiMeasurePreserving (cubeDilation z z0 r)
      (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    aux_fscc_holder_predicates_holNeu d z r hr
      (cutoffPositiveCoefficient model H omega J z hr) alpha
      (Real.sqrt d ^ alpha * Kcor ((J : ℤ) - m).toNat (aux_transport_S m w omega) *
        r ^ (2 - alpha) / aux_transport_reference model H J m w omega) := by
  subst hz0
  intro F Kf hKf hF hFb hFint u hsol
  obtain ⟨a1, ha1, -, hNeumannPart⟩ :=
    lem_as_regularity_affine_transport d model H omega J z r hr
  obtain ⟨F1, v1, hF1def, hF1meas, hF1b, hF1z, hsolve1, hv1val, hv1grad, -⟩ :=
    hNeumannPart F Kf hKf hF.aemeasurable
      (ae_restrict_of_forall_mem (centeredCube z r hr).isOpen.measurableSet hFb) hFint u hsol
  unfold unitNeumannCube at hF1meas hF1b hF1z hv1val
  have ha1' : ∀ᵐ x ∂ volume.restrict (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
      (a1.val : SpatialCoordinates d → ℝ) x =
        cutoffCoefficient model H omega J (w + (3 : ℝ) ^ (-m) • x) := by
    filter_upwards [ha1, hq.ae (aux_fscc_holNeuH_cutoffPos_val model H omega J z hr)]
      with x hx1 hx2
    rw [hx1, hx2, hTeq]
  clear ha1 hNeumannPart hsol hF hFb hFint hF1def
  set K : ℕ := ((J : ℤ) - m).toNat with hKdef
  set ref := aux_transport_reference model H J m w omega with hrefdef
  have hrefpos := aux_transport_reference_pos model H J m w omega
  have hident := hcoeff a1 ha1'
  have hsolve2 := aux_fscc_holNeuH_solvesNeumann_unscale ref hrefpos a1
    (cutoffPositiveCoefficient model H (aux_transport_S m w omega) K (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) hident
    F1 v1 hsolve1
  have hF1'meas : AEMeasurable (fun x => F1 x / ref)
      (volume.restrict (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d))) :=
    hF1meas.div_const ref
  have hF1'b : ∀ᵐ x ∂ volume.restrict (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
      |F1 x / ref| ≤ r ^ 2 * Kf / ref := by
    filter_upwards [hF1b] with x hx
    rw [abs_div, abs_of_pos hrefpos]
    exact div_le_div_of_nonneg_right hx hrefpos.le
  have hF1'z : (∫ x in (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)), F1 x / ref) =
      0 := by
    rw [show (fun x => F1 x / ref) = fun x => ref⁻¹ * F1 x from by
        funext x; ring, integral_const_mul, hF1z, mul_zero]
  have hKfref0 : 0 ≤ r ^ 2 * Kf / ref := div_nonneg (by positivity) hrefpos.le
  obtain ⟨U, hUcont, hUhol, hUeq, hUcalpha⟩ :=
    hcorS K (fun x => F1 x / ref) (r ^ 2 * Kf / ref) hKfref0 hF1'meas hF1'b hF1'z v1 hsolve2
  have hsemi0 : holderSeminorm alpha
      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) U ≤
        Kcor K (aux_transport_S m w omega) * (r ^ 2 * Kf / ref) :=
    (aux_fscc_holder_predicates_holderSeminorm_le _ _ U).trans hUcalpha
  obtain ⟨hUcO, hUholQ, hsemiQ⟩ :=
    aux_fscc_holNeuH_holder_transport z (fun _ : Fin d => (1 / 2 : ℝ)) hr halpha.le U
      hUcont.continuousOn hUhol
  set Ufinal : SpatialCoordinates d → ℝ := fun y => U (cubeDilation (fun _ : Fin d => (1 / 2 : ℝ)) z r⁻¹ y) with hUfd
  have hsemiQ' : holderSeminorm alpha
      (closedCube z r hr : Set (SpatialCoordinates d)) Ufinal ≤
      r ^ (-alpha) * (Kcor K (aux_transport_S m w omega) * (r ^ 2 * Kf / ref)) :=
    hsemiQ.trans (mul_le_mul_of_nonneg_left hsemi0 (Real.rpow_nonneg hr.le _))
  have hdiff := aux_fscc_holNeuH_holder_dist_of_seminorm
    (closedCube z r hr : Set (SpatialCoordinates d)) Ufinal alpha
    (r ^ (-alpha) * (Kcor K (aux_transport_S m w omega) * (r ^ 2 * Kf / ref)))
    halpha hUholQ hsemiQ'
  have hUv : ∀ᵐ x ∂ volume.restrict (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
      (u : SobolevData (centeredCube z r hr)).1 (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x) = U x := by
    filter_upwards [hUeq, hv1val] with x hx1 hx2
    rw [← hx1, hx2]
  have hUfinalCont : Continuous Ufinal := hUcont.comp (continuous_cubeDilation (fun _ : Fin d => (1 / 2 : ℝ)) z r⁻¹)
  have hp : MeasurableSet {y : SpatialCoordinates d |
      (u : SobolevData (centeredCube z r hr)).1 y = Ufinal y} :=
    measurableSet_eq_fun
      (Lp.stronglyMeasurable (u : SobolevData (centeredCube z r hr)).1).measurable
      hUfinalCont.measurable
  refine ⟨Ufinal, hUcO, ?_, ?_⟩
  · refine (aux_fscc_holNeuH_ae_iff z (fun _ : Fin d => (1 / 2 : ℝ)) hr hp).mpr ?_
    filter_upwards [hUv] with x hx
    show (u : SobolevData (centeredCube z r hr)).1 (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x) =
      Ufinal (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x)
    rw [hUfd]
    show (u : SobolevData (centeredCube z r hr)).1 (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x) =
      U (cubeDilation (fun _ : Fin d => (1 / 2 : ℝ)) z r⁻¹
        (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x))
    rw [hinjQ x]
    exact hx
  · intro x hx y hy
    have hb := hdiff x hx y hy
    have hpow : r ^ (-alpha) * r ^ 2 = r ^ (2 - alpha) := by
      have h2 : (r : ℝ) ^ (2 : ℕ) = r ^ (2 : ℝ) := (Real.rpow_natCast r 2).symm
      rw [h2, ← Real.rpow_add hr]
      congr 1; ring
    calc |Ufinal x - Ufinal y| ≤
          Real.sqrt d ^ alpha *
            (r ^ (-alpha) * (Kcor K (aux_transport_S m w omega) * (r ^ 2 * Kf / ref))) *
            dist x y ^ alpha := hb
      _ = Real.sqrt d ^ alpha * Kcor K (aux_transport_S m w omega) *
            (r ^ (-alpha) * r ^ 2) * Kf / ref * dist x y ^ alpha := by ring
      _ = Real.sqrt d ^ alpha * Kcor K (aux_transport_S m w omega) * r ^ (2 - alpha) /
            ref * Kf * dist x y ^ alpha := by rw [hpow]; ring

/-- `aux_lane4_reference_point_moments_layer_abs`, generalized from `j = -(i:ℤ)` (`i : ℕ`)
to any integer `j`: the underlying mechanism (`layerScaling`'s pushforward of the common
shell-0 potential field via `isBigO_gammaTwo_potentialCoordinate_apply`, which is uniform in
the evaluation point) does not depend on the sign of the layer index, only on the point
`(3:ℝ)^(-j) • x` at which the common field is sampled. -/
theorem aux_fscc_holNeuH_layer_abs_j
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℤ)
    (x : SpatialCoordinates d) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun f : C(SpatialCoordinates d, ℝ) => Real.exp (t * |f x|))
      (scaledLayerLaw d (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P |>.map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)
        j).toMeasure ∧
    (∫ f : C(SpatialCoordinates d, ℝ), Real.exp (t * |f x|)
      ∂(scaledLayerLaw d (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P |>.map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)
        j).toMeasure) ≤
      4 * Real.exp (t ^ 2 * (((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) ^ 2) / 2) := by
  let μ := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) := ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let ν := SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P |>.map
    forget.continuous.measurable.aemeasurable
  let sc := SubdiffusiveProcess.layerScaling d j
  let E : C(SpatialCoordinates d, ℝ) → ℝ := fun f => |f x|
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ :=
    fun g => |g ((3 : ℝ) ^ (-j) • x)|
  let Y : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ :=
    fun o => |o 0 ((3 : ℝ) ^ (-j) • x)|
  have hX : Measurable X :=
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval _).norm
  have hY : Measurable Y :=
    ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval _).comp
      (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate 0)).norm
  have hE : Measurable E := by
    have heval : Measurable (fun f : C(SpatialCoordinates d, ℝ) => f x) :=
      (continuous_eval_const x).measurable
    simpa [E, Real.norm_eq_abs] using heval.norm
  have hscaled : Measure.map E (scaledLayerLaw d ν j).toMeasure =
      Measure.map X μ := by
    change Measure.map E (Measure.map sc (Measure.map forget μ)) = Measure.map X μ
    rw [Measure.map_map sc.continuous.measurable forget.continuous.measurable,
      Measure.map_map hE (sc.continuous.measurable.comp forget.continuous.measurable)]
    congr 1
  have hbase : Measure.map (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
      g ((3 : ℝ) ^ (-j) • x)) μ =
      Measure.map (fun o : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        o 0 ((3 : ℝ) ^ (-j) • x)) M.P.toMeasure := by
    change Measure.map (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
        g ((3 : ℝ) ^ (-j) • x))
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure = _
    rw [show (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure =
      Measure.map (fun o : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => o 0)
        M.P.toMeasure by rfl]
    rw [Measure.map_map
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval _)
      (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate 0)]
    rfl
  have hmap : Measure.map X μ = Measure.map Y M.P.toMeasure := by
    calc
      Measure.map X μ = Measure.map (fun z : ℝ => |z|)
          (Measure.map (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
            g ((3 : ℝ) ^ (-j) • x)) μ) := by
              rw [Measure.map_map (by
                simpa [Real.norm_eq_abs] using
                  (measurable_id.norm : Measurable (fun z : ℝ => ‖z‖)))
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval _)]
              rfl
      _ = Measure.map (fun z : ℝ => |z|)
          (Measure.map (fun o : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
            o 0 ((3 : ℝ) ^ (-j) • x)) M.P.toMeasure) := by rw [hbase]
      _ = Measure.map Y M.P.toMeasure := by
            simpa [Y, Function.comp_def] using
              (Measure.map_map (by
                simpa [Real.norm_eq_abs] using
                  (measurable_id.norm : Measurable (fun z : ℝ => ‖z‖)))
                ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval _).comp
                  (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate 0)))
  have hzero : Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma 2) X
      (((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
    have hnative := SubdiffusiveProcess.CoarseGrainingVocab.isBigO_gammaTwo_potentialCoordinate_apply
      M 0 ((3 : ℝ) ^ (-j) • x)
    have hwith : Homogenization.IndependentSums.IsBigOWith μ
        (Homogenization.IndependentSums.gammaSigma 2) X
        (((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) :=
      SubdiffusiveProcess.CoarseGrainingVocab.isBigOWith_of_map_eq hX
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval _ |>.comp
          (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate 0) |>.norm)
        hmap hnative
    simpa [Homogenization.IndependentSums.IsBigO, X, abs_abs] using hwith
  let phi : ℝ → ℝ := fun z => Real.exp (t * |z|)
  have hphi : Measurable phi := by fun_prop
  have hExp := SubdiffusiveProcess.CoarseGrainingVocab.integral_exp_abs_sub_const_le
    (mu := μ) (X := X)
    (A := ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) (b := 0)
    (by have hδ := M.shellPrefix.delta_pos; positivity) ht hX.aemeasurable hzero
  have hphiMapX : Integrable phi (Measure.map X μ) := by
    apply (integrable_map_measure hphi.aestronglyMeasurable hX.aemeasurable).2
    simpa [phi, X, Function.comp_def, abs_abs] using hExp.1
  have hphiMapE : Integrable phi
      (Measure.map E (scaledLayerLaw d ν j).toMeasure) := by
    rw [hscaled]
    exact hphiMapX
  have hcomp : Integrable (phi ∘ E)
      (scaledLayerLaw d ν j).toMeasure :=
    (integrable_map_measure hphi.aestronglyMeasurable hE.aemeasurable).mp hphiMapE
  constructor
  · simpa [phi, E, Function.comp_def] using hcomp
  · calc
      (∫ f : C(SpatialCoordinates d, ℝ), Real.exp (t * |(f x)|)
          ∂(scaledLayerLaw d ν j).toMeasure) =
          ∫ z, phi z ∂Measure.map E
            (scaledLayerLaw d ν j).toMeasure := by
              simpa [phi, E, Function.comp_def] using
                (integral_map hE.aemeasurable hphi.aestronglyMeasurable
                  (μ := (scaledLayerLaw d ν j).toMeasure)).symm
      _ = ∫ z, phi z ∂Measure.map X μ := by rw [hscaled]
      _ = ∫ g, phi (X g) ∂μ := by
        exact integral_map hX.aemeasurable hphi.aestronglyMeasurable
      _ ≤ _ := by simpa [phi, X, abs_abs] using hExp.2

/-- `aux_lane4_reference_point_moments_layer`, generalized from `j = -(i:ℤ)` to any integer
`j` (same point-uniformity argument as `aux_fscc_holNeuH_layer_abs_j`). -/
theorem aux_fscc_holNeuH_layer_j
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℤ)
    (x : SpatialCoordinates d) (t : ℝ) :
    Integrable (fun f : C(SpatialCoordinates d, ℝ) => Real.exp (t * f x))
      (scaledLayerLaw d (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P |>.map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)
        j).toMeasure ∧
    (∫ f, Real.exp (t * f x)
      ∂(scaledLayerLaw d (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P |>.map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ))).continuous.measurable.aemeasurable)
        j).toMeasure) ≤
      Real.exp ((3 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) *
        (|t| + t^2) * M.delta^2) := by
  let μ := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) := ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let ν := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map
    forget.continuous.measurable.aemeasurable
  let L := (scaledLayerLaw d ν j).toMeasure
  let point : SpatialCoordinates d := (3 : ℝ) ^ (-j) • x
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => g point
  let E : C(SpatialCoordinates d, ℝ) → ℝ := fun f => f x
  have hmap : Measure.map E L = Measure.map X μ := by
    change Measure.map E (Measure.map (SubdiffusiveProcess.layerScaling d j)
      (Measure.map forget μ)) = Measure.map X μ
    rw [Measure.map_map (SubdiffusiveProcess.layerScaling d j).continuous.measurable
      forget.continuous.measurable,
      Measure.map_map (continuous_eval_const x).measurable
        ((SubdiffusiveProcess.layerScaling d j).continuous.measurable.comp
          forget.continuous.measurable)]
    congr 1
  have hXm : Measurable X :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval _
  have hEm : Measurable E := (continuous_eval_const x).measurable
  let c : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹
  have hc0 : 0 ≤ c := by
    dsimp [c]
    have hh : 0 ≤ 1 + Real.log 2 := by
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      linarith
    exact Real.rpow_nonneg hh _
  have hbase : Integrable (fun g => Real.exp (t * X g)) μ ∧
      (∫ g, Real.exp (t * X g) ∂μ) ≤
        Real.exp ((3 + c^2) * (|t| + t^2) * M.delta^2) := by
    rcases le_or_gt (|t| * M.delta) 1 with hsmall | hlarge
    · have h := SubdiffusiveProcess.fineLayer_exp_moment_le t M point hsmall
      constructor
      · simpa [X, point, μ] using h.1
      · apply le_trans h.2
        apply Real.exp_le_exp.mpr
        have hlog2 : Real.log 2 / 2 ≤ 1 := by
          have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
          linarith
        have hb : Real.log 2 / 2 * t^2 ≤ (3 + c^2) * (|t| + t^2) := by
          have ht2 : t^2 ≤ |t| + t^2 := by linarith [abs_nonneg t]
          have hc : 0 ≤ c^2 := sq_nonneg c
          nlinarith [mul_nonneg hc (by positivity : 0 ≤ |t| + t^2)]
        exact mul_le_mul_of_nonneg_right hb (sq_nonneg M.delta)
    · let absphi : ℝ → ℝ := fun z => Real.exp (|t| * |z|)
      have habs := aux_fscc_holNeuH_layer_abs_j M j x |t|
        (abs_nonneg t)
      have habsMeas : Measurable (fun z : ℝ => Real.exp (|t| * |z|)) := by
        fun_prop
      have hphi : Measurable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
          Real.exp (t * X g)) := (measurable_const.mul hXm).exp
      have hmajor : ∀ g, Real.exp (t * X g) ≤ absphi (X g) := by
        intro g
        apply Real.exp_le_exp.mpr
        calc
          t * X g ≤ |t * X g| := le_abs_self _
          _ = |t| * |X g| := abs_mul _ _
      have habsMapE : Integrable (fun z => Real.exp (|t| * |z|))
          (Measure.map E L) :=
        (integrable_map_measure habsMeas.aestronglyMeasurable hEm.aemeasurable).2
          (by simpa [absphi, E, Function.comp_def] using habs.1)
      have habsMapX : Integrable (fun z => Real.exp (|t| * |z|))
          (Measure.map X μ) := by simpa [hmap] using habsMapE
      have habsμ : Integrable (fun g => absphi (X g)) μ :=
        (integrable_map_measure habsMeas.aestronglyMeasurable hXm.aemeasurable).1
          (by simpa [absphi] using habsMapX)
      have htarget : Integrable (fun g => Real.exp (t * X g)) μ := by
        refine habsμ.mono' hphi.aestronglyMeasurable ?_
        filter_upwards [] with g
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact hmajor g
      constructor
      · exact htarget
      · calc
          ∫ g, Real.exp (t * X g) ∂μ ≤ ∫ g, absphi (X g) ∂μ :=
            integral_mono htarget habsμ hmajor
          _ ≤ 4 * Real.exp (|t|^2 * (c * M.delta)^2 / 2) := by
            calc
              ∫ g, absphi (X g) ∂μ =
                  ∫ z, Real.exp (|t| * |z|) ∂Measure.map X μ := by
                    exact (integral_map hXm.aemeasurable habsMeas.aestronglyMeasurable).symm
              _ = ∫ z, Real.exp (|t| * |z|) ∂Measure.map E L := by rw [hmap]
              _ = ∫ f, Real.exp (|t| * |f x|) ∂L := by
                    exact integral_map hEm.aemeasurable habsMeas.aestronglyMeasurable
              _ ≤ _ := by simpa [L, absphi, c] using habs.2
          _ ≤ Real.exp ((3 + c^2) * (|t| + t^2) * M.delta^2) := by
            rw [show (4 : ℝ) * Real.exp (|t|^2 * (c * M.delta)^2 / 2) =
              Real.exp (Real.log 4 + |t|^2 * (c * M.delta)^2 / 2) by
                rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]]
            apply Real.exp_le_exp.mpr
            have hlog4 : Real.log 4 ≤ 3 := by
              have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
              linarith
            have hlarge2 : 1 < t^2 * M.delta^2 := by
              rw [← sq_abs t]
              nlinarith [hlarge]
            have hlogpart : Real.log 4 ≤ 3 * t^2 * M.delta^2 := by
              have htd : 1 ≤ t^2 * M.delta^2 := hlarge2.le
              nlinarith
            have hquad : |t|^2 * (c * M.delta)^2 / 2 ≤
                c^2 * t^2 * M.delta^2 := by
              rw [sq_abs]
              nlinarith [sq_nonneg (c * M.delta)]
            have hsum : t^2 ≤ |t| + t^2 := by linarith [abs_nonneg t]
            have hc : 0 ≤ c^2 := sq_nonneg c
            have hδ : 0 ≤ M.delta^2 := sq_nonneg M.delta
            have h1 : 3 * t^2 * M.delta^2 ≤
                3 * (|t| + t^2) * M.delta^2 := by gcongr
            have h2 : c^2 * t^2 * M.delta^2 ≤
                c^2 * (|t| + t^2) * M.delta^2 := by gcongr
            nlinarith
  have hphiX : Measurable (fun z : ℝ => Real.exp (t * z)) := by fun_prop
  have hMapX : Integrable (fun z : ℝ => Real.exp (t * z)) (Measure.map X μ) :=
    (integrable_map_measure hphiX.aestronglyMeasurable hXm.aemeasurable).2 hbase.1
  have hMapE : Integrable (fun z : ℝ => Real.exp (t * z)) (Measure.map E L) := by
    simpa [hmap] using hMapX
  have hL : Integrable (fun f : C(SpatialCoordinates d, ℝ) => Real.exp (t * E f)) L :=
    (integrable_map_measure hphiX.aestronglyMeasurable hEm.aemeasurable).1 hMapE
  constructor
  · simpa [L, E] using hL
  · calc
      ∫ f : C(SpatialCoordinates d, ℝ), Real.exp (t * E f) ∂L =
          ∫ z, Real.exp (t * z) ∂Measure.map E L := by
            exact (integral_map hEm.aemeasurable hphiX.aestronglyMeasurable).symm
      _ = ∫ z, Real.exp (t * z) ∂Measure.map X μ := by rw [hmap]
      _ = ∫ g, Real.exp (t * X g) ∂μ := by
            exact integral_map hXm.aemeasurable hphiX.aestronglyMeasurable
      _ ≤ _ := hbase.2

/-- `aux_lane4_reference_point_moments_sum`, generalized from `S = Finset.range k` read at
negative indices `-(i:ℤ)` to an arbitrary finite set `S : Finset ℤ` of (already signed, already
distinct) layer indices, summing `omega j x` for `j ∈ S` directly. Same proof, using
`aux_fscc_holNeuH_layer_j` (any integer layer) in place of `aux_lane4_reference_point_moments_layer`
(negative layers only) for the per-layer bound. -/
theorem aux_fscc_holNeuH_sum_set
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (S : Finset ℤ)
    (x : SpatialCoordinates d) (ε : ℝ) :
    Integrable (fun omega : BilateralField d =>
      Real.exp (ε * (∑ j ∈ S, (omega j) x -
        (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)))
      (chaosSampleLaw M).toMeasure ∧
    (∫ omega : BilateralField d, Real.exp (ε *
      (∑ j ∈ S, (omega j) x -
        (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
      ∂(chaosSampleLaw M).toMeasure) ≤
      Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) *
        (|ε| + ε^2) * M.delta^2 * (S.card : ℝ)) := by
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) := ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let ν := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map
    forget.continuous.measurable.aemeasurable
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  let P : Measure (BilateralField d) := Measure.infinitePi laws
  have hS : iIndepFun
      (fun i : S => fun omega : BilateralField d => omega (i : ℤ)) P := by
    have hfull : iIndepFun
        (fun j : ℤ => fun omega : BilateralField d => omega j) P := by
      dsimp only [P]
      exact iIndepFun_infinitePi (fun _ => measurable_id)
    apply hfull.precomp
    intro i₁ i₂ hi
    exact Subtype.ext hi
  let F : S → C(SpatialCoordinates d, ℝ) → ℝ := fun i f =>
    Real.exp (ε * f x)
  have hFmeas (i : S) : Measurable (F i) := by
    dsimp [F]
    apply Measurable.exp
    exact measurable_const.mul (continuous_eval_const x).measurable
  have hfactor :
      (∫ omega, ∏ i : S, F i (omega (i : ℤ)) ∂P) =
        ∏ i : S, ∫ omega, F i (omega (i : ℤ)) ∂P := by
    refine hS.integral_fun_prod_comp ?_ (fun i => ?_)
    · intro i
      exact (measurable_pi_apply (i : ℤ)).aemeasurable
    · exact (hFmeas i).aestronglyMeasurable
  let C0 : ℝ := 3 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2
  let B : ℝ := Real.exp (C0 * (|ε| + ε^2) * M.delta^2)
  have hcoord (i : S) :
      Integrable (fun omega : BilateralField d => F i (omega (i : ℤ))) P ∧
      (∫ omega, F i (omega (i : ℤ)) ∂P) ≤ B := by
    let law := (scaledLayerLaw d ν (i : ℤ)).toMeasure
    have hh := aux_fscc_holNeuH_layer_j M (i : ℤ) x ε
    have htarget : Measurable (fun f : C(SpatialCoordinates d, ℝ) => F i f) := hFmeas i
    have heval := measurePreserving_eval_infinitePi laws (i : ℤ)
    have hsource :
        Integrable (fun omega : BilateralField d => F i (omega (i : ℤ))) P := by
      have h := (heval.integrable_comp htarget.aestronglyMeasurable).mpr
        (by simpa [F, law] using hh.1)
      exact h
    constructor
    · exact hsource
    · calc
        (∫ omega, F i (omega (i : ℤ)) ∂P) =
            ∫ f, F i f ∂Measure.map (fun omega : BilateralField d =>
              omega (i : ℤ)) P := by
                rw [integral_map heval.measurable.aemeasurable
                  (hFmeas i).aestronglyMeasurable]
        _ = ∫ f, F i f ∂law := by rw [heval.map_eq]
        _ ≤ B := by simpa [F, law, B, C0] using hh.2
  have hSc : iIndepFun
      (fun i : S => fun omega : BilateralField d =>
        (omega (i : ℤ)) x) P := by
    exact hS.comp (fun _ f => f x) (fun _ => (continuous_eval_const x).measurable)
  have huncenteredInt : Integrable
      (fun omega : BilateralField d =>
        Real.exp (ε * ∑ i : S, (omega (i : ℤ)) x)) P := by
    have h := hSc.integrable_exp_mul_sum (t := ε) (s := Finset.univ)
      (fun i => by
        have hevalx : Measurable (fun f : C(SpatialCoordinates d, ℝ) => f x) :=
          (continuous_eval_const x).measurable
        simpa using hevalx.comp (measurable_pi_apply (i : ℤ)))
      (by
        intro i hi
        simpa [F, Function.comp_def] using (hcoord i).1)
    simpa [Finset.sum_coe_sort] using h
  have hprodBound :
      (∏ i : S, ∫ omega, F i (omega (i : ℤ)) ∂P) ≤ B ^ S.card := by
    calc
      (∏ i : S, ∫ omega, F i (omega (i : ℤ)) ∂P) ≤
          ∏ _i : S, B := by
            gcongr with i
            exact (hcoord i).2
      _ = B ^ S.card := by simp
  have huncenteredBound :
      (∫ omega : BilateralField d,
        Real.exp (ε * ∑ i : S, (omega (i : ℤ)) x) ∂P) ≤ B ^ S.card := by
    calc
      (∫ omega : BilateralField d,
        Real.exp (ε * ∑ i : S, (omega (i : ℤ)) x) ∂P) =
          ∫ omega, ∏ i : S, F i (omega (i : ℤ)) ∂P := by
            apply integral_congr_ae
            filter_upwards [] with omega
            rw [← Real.exp_sum]
            congr 1
            simp [Finset.mul_sum]
      _ = ∏ i : S, ∫ omega, F i (omega (i : ℤ)) ∂P := hfactor
      _ ≤ B ^ S.card := hprodBound
  have hcenteredInt : Integrable
      (fun omega : BilateralField d =>
        Real.exp (ε * (∑ i : S, (omega (i : ℤ)) x -
          (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))) P := by
    have hc := huncenteredInt.const_mul
      (Real.exp (-ε * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
    convert hc using 1
    funext omega
    rw [← Real.exp_add]
    congr 1
    ring
  have hcenteredBound :
      (∫ omega : BilateralField d,
        Real.exp (ε * (∑ i : S, (omega (i : ℤ)) x -
          (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) ∂P) ≤
        Real.exp (|ε| * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * B ^ S.card := by
    have hc := huncenteredBound
    calc
      (∫ omega : BilateralField d,
        Real.exp (ε * (∑ i : S, (omega (i : ℤ)) x -
          (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) ∂P) =
          Real.exp (-ε * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
            (∫ omega : BilateralField d,
              Real.exp (ε * ∑ i : S, (omega (i : ℤ)) x) ∂P) := by
                rw [show (fun omega : BilateralField d =>
                  Real.exp (ε * (∑ i : S, (omega (i : ℤ)) x -
                    (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))) =
                  (fun omega => Real.exp (-ε * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
                    Real.exp (ε * ∑ i : S, (omega (i : ℤ)) x)) by
                      funext omega
                      rw [← Real.exp_add]
                      congr 1
                      ring]
                rw [integral_const_mul]
      _ ≤ Real.exp (-ε * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * B ^ S.card :=
        mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
      _ ≤ Real.exp (|ε| * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * B ^ S.card := by
        have htau : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := M.G4.tauSq_pos.le
        have hexp : Real.exp (-ε * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤
            Real.exp (|ε| * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
          apply Real.exp_le_exp.mpr
          have hk : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
          have hke : -ε * (S.card : ℝ) ≤ |ε| * (S.card : ℝ) :=
            mul_le_mul_of_nonneg_right (neg_le_abs ε) hk
          calc
            -ε * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P =
                (-ε * (S.card : ℝ)) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by ring
            _ ≤ (|ε| * (S.card : ℝ)) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P :=
              mul_le_mul_of_nonneg_right hke htau
            _ = |ε| * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by ring
        exact mul_le_mul_of_nonneg_right hexp (pow_nonneg (Real.exp_pos _).le _)
  have hfinalBound :
      (∫ omega : BilateralField d,
        Real.exp (ε * (∑ i : S, (omega (i : ℤ)) x -
          (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) ∂P) ≤
        Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) *
          (|ε| + ε^2) * M.delta^2 * (S.card : ℝ)) := by
    calc
      _ ≤ Real.exp (|ε| * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * B ^ S.card :=
        hcenteredBound
      _ = Real.exp (|ε| * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
          C0 * (|ε| + ε^2) * M.delta^2 * (S.card : ℝ)) := by
            rw [show B = Real.exp (C0 * (|ε| + ε^2) * M.delta^2) by rfl,
              ← Real.exp_nat_mul, ← Real.exp_add]
            congr 1
            ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ M.delta^2 := by
          have hh := SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
          have hlog : Real.log 2 / 2 ≤ 1 := by
            have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
            linarith
          nlinarith
        have habs : |ε| ≤ |ε| + ε^2 := by linarith [sq_nonneg ε]
        have hk : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
        have hd2 : 0 ≤ M.delta^2 := sq_nonneg _
        dsimp [C0]
        have h1 : |ε| * (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤
            |ε| * (S.card : ℝ) * M.delta^2 := by gcongr
        have h2 : (3 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) *
              (|ε| + ε^2) * M.delta^2 * (S.card : ℝ) +
              |ε| * (S.card : ℝ) * M.delta^2 ≤
            (4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) *
              (|ε| + ε^2) * M.delta^2 * (S.card : ℝ) := by
          have hc : 0 ≤ ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2 := sq_nonneg _
          have hprod := mul_le_mul_of_nonneg_right habs (mul_nonneg hd2 hk)
          nlinarith [hprod]
        nlinarith
  have hsumEq (omega : BilateralField d) :
      (∑ i : S, (omega (i : ℤ)) x) = ∑ j ∈ S, (omega j) x :=
    Finset.sum_coe_sort S (fun j => (omega j) x)
  have hP : (chaosSampleLaw M).toMeasure = P := by
    change Measure.infinitePi (fun j : ℤ =>
      (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure) = P
    simp [P, ν, laws, chaosRootFieldLaw]
  rw [hP]
  refine ⟨hcenteredInt.congr ?_, ?_⟩
  · filter_upwards [] with omega
    rw [hsumEq]
  · calc
      (∫ omega : BilateralField d,
        Real.exp (ε * (∑ j ∈ S, (omega j) x -
          (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) ∂P) =
          ∫ omega : BilateralField d,
            Real.exp (ε * (∑ i : S, (omega (i : ℤ)) x -
              (S.card : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) ∂P := by
                apply integral_congr_ae
                filter_upwards [] with omega
                rw [hsumEq]
      _ ≤ _ := hfinalBound

/-- `aux_fscc_holNeuH_sum_set` reindexed along an arbitrary injection `ι : ℕ → ℤ` on
`Finset.range k` (matches `aux_lane4_reference_point_moments_sum`'s own shape, generalized from
the fixed injection `i ↦ -(i:ℤ)` to any injective `ι`). -/
theorem aux_fscc_holNeuH_sum_inj
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (ι : ℕ → ℤ)
    (hι : Function.Injective ι)
    (x : SpatialCoordinates d) (ε : ℝ) :
    Integrable (fun omega : BilateralField d =>
      Real.exp (ε * (∑ j ∈ Finset.range k, (omega (ι j)) x -
        (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)))
      (chaosSampleLaw M).toMeasure ∧
    (∫ omega : BilateralField d, Real.exp (ε *
      (∑ j ∈ Finset.range k, (omega (ι j)) x -
        (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
      ∂(chaosSampleLaw M).toMeasure) ≤
      Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)^2) *
        (|ε| + ε^2) * M.delta^2 * (k : ℝ)) := by
  have hcard : ((Finset.range k).image ι).card = k := by
    rw [Finset.card_image_of_injective _ hι, Finset.card_range]
  have hsum : ∀ omega : BilateralField d,
      (∑ j ∈ (Finset.range k).image ι, (omega j) x) =
        ∑ j ∈ Finset.range k, (omega (ι j)) x := by
    intro omega
    rw [Finset.sum_image (fun a _ b _ hab => hι hab)]
  have h := aux_fscc_holNeuH_sum_set M ((Finset.range k).image ι) x ε
  rw [hcard] at h
  refine ⟨h.1.congr ?_, ?_⟩
  · filter_upwards [] with omega
    rw [hsum]
  · calc
      (∫ omega : BilateralField d, Real.exp (ε *
        (∑ j ∈ Finset.range k, (omega (ι j)) x -
          (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
        ∂(chaosSampleLaw M).toMeasure) =
          ∫ omega : BilateralField d, Real.exp (ε *
            (∑ j ∈ (Finset.range k).image ι, (omega j) x -
              (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
            ∂(chaosSampleLaw M).toMeasure := by
              apply integral_congr_ae
              filter_upwards [] with omega
              rw [hsum]
      _ ≤ _ := h.2

/-- `retained` for `m ≥ 0`, as a `Finset.range`-indexed sum at the injection `k ↦ -(k:ℤ)`
(matches `aux_fscc_holNeuH_sum_inj`'s shape). -/
theorem aux_fscc_holNeuH_retained_eq_pos {d : ℕ} (m : ℤ) (hm : 0 ≤ m)
    (z : SpatialCoordinates d) (om : BilateralField d) :
    aux_transport_retained m z om =
      ∑ k ∈ Finset.range m.toNat, om (-(k : ℤ)) z := by
  rw [aux_transport_retained_eq, if_pos hm]
  have hshift := aux_transport_sum_range_shift (fun j => om (-j) z) 0 m.toNat
  have hm' : (0 : ℤ) + (m.toNat : ℤ) = m := by
    rw [zero_add, Int.toNat_of_nonneg hm]
  rw [hm'] at hshift
  simpa using hshift.symm

/-- `retained` for `m < 0`, as (minus) a `Finset.range`-indexed sum at the injection
`k ↦ -m - (k:ℤ)` (matches `aux_fscc_holNeuH_sum_inj`'s shape). -/
theorem aux_fscc_holNeuH_retained_eq_neg {d : ℕ} (m : ℤ) (hm : m < 0)
    (z : SpatialCoordinates d) (om : BilateralField d) :
    aux_transport_retained m z om =
      -∑ k ∈ Finset.range (-m).toNat, om (-m - (k : ℤ)) z := by
  rw [aux_transport_retained_eq, if_neg (by omega)]
  congr 1
  have hshift := aux_transport_sum_range_shift (fun j => om (-j) z) m (-m).toNat
  have hm' : m + ((-m).toNat : ℤ) = 0 := by
    rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -m)]; ring
  rw [hm'] at hshift
  rw [← hshift]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 2
  ring

/-- Fourth-moment bound on `exp(-4·retained)` for `m ≥ 0`. -/
theorem aux_fscc_holNeuH_retained_moment_pos
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ) (hm : 0 ≤ m) (w : SpatialCoordinates d) :
    ∃ Bret : ℝ, 0 ≤ Bret ∧
      Integrable (fun om => Real.exp (-4 * aux_transport_retained m w om))
        (chaosSampleLaw model).toMeasure ∧
      (∫ om, Real.exp (-4 * aux_transport_retained m w om)
        ∂(chaosSampleLaw model).toMeasure) ≤ Bret := by
  set k := m.toNat with hkdef
  set ι : ℕ → ℤ := fun i => -(i : ℤ) with hιdef
  have hιinj : Function.Injective ι := fun a b hab => by
    have hh : -(a : ℤ) = -(b : ℤ) := hab
    omega
  obtain ⟨hInt, hBound⟩ := aux_fscc_holNeuH_sum_inj model k ι hιinj w (-4)
  have h20 : |(-4 : ℝ)| + (-4 : ℝ) ^ 2 = 20 := by norm_num
  rw [h20] at hBound
  have heq : ∀ om : BilateralField d, aux_transport_retained m w om =
      ∑ j ∈ Finset.range k, om (ι j) w := fun om => aux_fscc_holNeuH_retained_eq_pos m hm w om
  refine ⟨Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2) * 20 * model.delta ^ 2 * (k : ℝ)),
    by positivity, ?_, ?_⟩
  · have hrw : (fun om : BilateralField d => Real.exp (-4 * aux_transport_retained m w om)) =
        fun om => Real.exp (-4 * ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) *
          Real.exp (-4 * (∑ j ∈ Finset.range k, om (ι j) w -
            (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) := by
      funext om
      rw [heq om, ← Real.exp_add]
      congr 1; ring
    rw [hrw]
    exact hInt.const_mul _
  · have hrw : (∫ om, Real.exp (-4 * aux_transport_retained m w om)
        ∂(chaosSampleLaw model).toMeasure) =
        Real.exp (-4 * ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) *
          (∫ om, Real.exp (-4 * (∑ j ∈ Finset.range k, om (ι j) w -
              (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P))
            ∂(chaosSampleLaw model).toMeasure) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with om
      rw [heq om, ← Real.exp_add]
      congr 1; ring
    rw [hrw]
    have hle1 : Real.exp (-4 * ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      have hτ : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P := model.G4.tauSq_pos.le
      nlinarith
    calc Real.exp (-4 * ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) *
          (∫ om, Real.exp (-4 * (∑ j ∈ Finset.range k, om (ι j) w -
              (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P))
            ∂(chaosSampleLaw model).toMeasure) ≤
        Real.exp (-4 * ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) *
          Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2) * 20 * model.delta ^ 2 * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hBound (Real.exp_pos _).le
      _ ≤ 1 * Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2) * 20 * model.delta ^ 2 * (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hle1 (Real.exp_pos _).le
      _ = _ := one_mul _

/-- Fourth-moment bound on `exp(-4·retained)` for `m < 0`. -/
theorem aux_fscc_holNeuH_retained_moment_neg
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ) (hm : m < 0) (w : SpatialCoordinates d) :
    ∃ Bret : ℝ, 0 ≤ Bret ∧
      Integrable (fun om => Real.exp (-4 * aux_transport_retained m w om))
        (chaosSampleLaw model).toMeasure ∧
      (∫ om, Real.exp (-4 * aux_transport_retained m w om)
        ∂(chaosSampleLaw model).toMeasure) ≤ Bret := by
  set p := (-m).toNat with hpdef
  set ι : ℕ → ℤ := fun i => -m - (i : ℤ) with hιdef
  have hιinj : Function.Injective ι := fun a b hab => by
    have hh : -m - (a : ℤ) = -m - (b : ℤ) := hab
    omega
  obtain ⟨hInt, hBound⟩ := aux_fscc_holNeuH_sum_inj model p ι hιinj w 4
  have h20 : |(4 : ℝ)| + (4 : ℝ) ^ 2 = 20 := by norm_num
  rw [h20] at hBound
  have heq : ∀ om : BilateralField d, aux_transport_retained m w om =
      -∑ j ∈ Finset.range p, om (ι j) w := fun om => aux_fscc_holNeuH_retained_eq_neg m hm w om
  have htau2 : SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P ≤ model.delta ^ 2 := by
    have hh := SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq model
    have hlog : Real.log 2 / 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    nlinarith [sq_nonneg model.delta]
  refine ⟨Real.exp (((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2) * 20 + 4) *
    model.delta ^ 2 * (p : ℝ)), by positivity, ?_, ?_⟩
  · have hrw : (fun om : BilateralField d => Real.exp (-4 * aux_transport_retained m w om)) =
        fun om => Real.exp (4 * ((p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) *
          Real.exp (4 * (∑ j ∈ Finset.range p, om (ι j) w -
            (p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) := by
      funext om
      rw [heq om, ← Real.exp_add]
      congr 1; ring
    rw [hrw]
    exact hInt.const_mul _
  · have hrw : (∫ om, Real.exp (-4 * aux_transport_retained m w om)
        ∂(chaosSampleLaw model).toMeasure) =
        Real.exp (4 * ((p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) *
          (∫ om, Real.exp (4 * (∑ j ∈ Finset.range p, om (ι j) w -
              (p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P))
            ∂(chaosSampleLaw model).toMeasure) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with om
      rw [heq om, ← Real.exp_add]
      congr 1; ring
    rw [hrw]
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
    have hexp4 : Real.exp (4 * ((p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) ≤
        Real.exp (4 * (p : ℝ) * model.delta ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc Real.exp (4 * ((p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) *
          (∫ om, Real.exp (4 * (∑ j ∈ Finset.range p, om (ι j) w -
              (p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P))
            ∂(chaosSampleLaw model).toMeasure) ≤
        Real.exp (4 * ((p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) *
          Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2) * 20 * model.delta ^ 2 * (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hBound (Real.exp_pos _).le
      _ ≤ Real.exp (4 * (p : ℝ) * model.delta ^ 2) *
          Real.exp ((4 + ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) ^ 2) * 20 * model.delta ^ 2 * (p : ℝ)) :=
        mul_le_mul_of_nonneg_right hexp4 (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add]; congr 1; ring

/-- The deterministic `kappa`-ratio inside `aux_transport_reference` is bounded, both directions,
by `exp(±|m|·τ²)`, uniformly in `J` (for `m ≤ J`): `aux_reference_coefficients_kappa_ratio_bounds`
directly for `m ≥ 0`, its reciprocal (applied at `N := J + p`, `k := p := (-m).toNat`) for `m < 0`. -/
theorem aux_fscc_holNeuH_kappa_ratio_bound
    {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ) (J : ℕ) (hmJ : m ≤ (J : ℤ)) :
    Real.exp (-(m.natAbs : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) ≤
      aux_transport_kappa model ((J : ℤ) - m).toNat / aux_transport_kappa model J ∧
    aux_transport_kappa model ((J : ℤ) - m).toNat / aux_transport_kappa model J ≤
      Real.exp ((m.natAbs : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) := by
  have hκpos : ∀ N : ℕ, 0 < aux_transport_kappa model N := by
    intro N
    unfold aux_transport_kappa
    exact mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N)
  rcases le_or_lt 0 m with hm | hm
  · have hkn : m.toNat ≤ J := by omega
    have hb := aux_reference_coefficients_kappa_ratio_bounds d model
      (aux_transport_kappa model) (fun N => rfl) J m.toNat hkn
    have hidx : (J - m.toNat : ℕ) = ((J : ℤ) - m).toNat := by omega
    rw [hidx] at hb
    have habs : (m.natAbs : ℝ) = (m.toNat : ℝ) := by
      have : m.natAbs = m.toNat := by omega
      exact_mod_cast this
    rw [habs, neg_mul]
    exact hb
  · set p := (-m).toNat with hpdef
    have hpJ : ((J : ℤ) - m).toNat = J + p := by omega
    rw [hpJ]
    have hb := aux_reference_coefficients_kappa_ratio_bounds d model
      (aux_transport_kappa model) (fun N => rfl) (J + p) p (by omega)
    have hidx : (J + p - p : ℕ) = J := by omega
    rw [hidx] at hb
    have habs : (m.natAbs : ℝ) = (p : ℝ) := by
      have : m.natAbs = p := by omega
      exact_mod_cast this
    rw [habs, neg_mul]
    obtain ⟨hlo, hhi⟩ := hb
    have hidiv : aux_transport_kappa model J / aux_transport_kappa model (J + p) =
        (aux_transport_kappa model (J + p) / aux_transport_kappa model J)⁻¹ :=
      (inv_div _ _).symm
    rw [hidiv] at hlo hhi
    have hratiopos : 0 < aux_transport_kappa model (J + p) / aux_transport_kappa model J :=
      div_pos (hκpos (J + p)) (hκpos J)
    have hinv_le : ∀ a b : ℝ, 0 < a → a ≤ b → b⁻¹ ≤ a⁻¹ := by
      intro a b ha hab
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le ha hab
    constructor
    · have := hinv_le _ _ (inv_pos.mpr hratiopos) hhi
      rwa [inv_inv, ← Real.exp_neg] at this
    · have := hinv_le _ _ (Real.exp_pos (-((p : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P))) hlo
      rwa [inv_inv, ← Real.exp_neg, neg_neg] at this

/-- Fourth-moment bound on `exp(-4·H(·)(w))` at a general point `w`, via
`exists_uniform_compactExponentialMoment_of_infraredCharacterization` at `Kc := closedBall w 1`
(uniform in `w`, unlike `lane4_reference_point_moments`'s own fixed `closedBall 0 1`). -/
theorem aux_fscc_holNeuH_H_neg4_moment
    {d : ℕ} (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization model H) (w : SpatialCoordinates d) :
    ∃ CHw : ℝ, 0 ≤ CHw ∧
      Integrable (fun om => Real.exp (-4 * H om w)) (chaosSampleLaw model).toMeasure ∧
      (∫ om, Real.exp (-4 * H om w) ∂(chaosSampleLaw model).toMeasure) ≤ CHw := by
  obtain ⟨CH, hCH0, hHmom⟩ :=
    SubdiffusiveProcess.exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  set Kc : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall w 1, ProperSpace.isCompact_closedBall w 1⟩ with hKcdef
  have hwK : w ∈ (Kc : Set (SpatialCoordinates d)) := by
    change w ∈ Metric.closedBall w 1
    exact Metric.mem_closedBall_self (by norm_num)
  have hnorm := hHmom model H hH Kc 4 (by norm_num)
  have htarget : Measurable (fun om : BilateralField d => Real.exp (-4 * H om w)) :=
    (measurable_const.mul ((continuous_eval_const w).measurable.comp hH.1)).exp
  have hdom : ∀ om : BilateralField d, -4 * H om w ≤
      4 * ‖(H om).restrict (Kc : Set (SpatialCoordinates d))‖ := by
    intro om
    have hb := ((H om).restrict (Kc : Set (SpatialCoordinates d))).norm_coe_le_norm ⟨w, hwK⟩
    calc -4 * H om w ≤ |(-4 : ℝ) * H om w| := le_abs_self _
      _ = 4 * |H om w| := by rw [abs_mul]; norm_num
      _ ≤ 4 * ‖(H om).restrict (Kc : Set (SpatialCoordinates d))‖ := by
        rw [← Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have hint : Integrable (fun om => Real.exp (-4 * H om w)) (chaosSampleLaw model).toMeasure := by
    refine hnorm.1.mono' htarget.aestronglyMeasurable ?_
    filter_upwards [] with om
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (hdom om)
  refine ⟨2 * Real.exp (CH Kc * 16 * model.delta ^ 2), by positivity, hint, ?_⟩
  calc (∫ om, Real.exp (-4 * H om w) ∂(chaosSampleLaw model).toMeasure) ≤
      ∫ om, Real.exp (4 * ‖(H om).restrict (Kc : Set (SpatialCoordinates d))‖)
        ∂(chaosSampleLaw model).toMeasure :=
      integral_mono hint hnorm.1 (fun om => Real.exp_le_exp.mpr (hdom om))
    _ ≤ 2 * Real.exp (CH Kc * 4 ^ 2 * model.delta ^ 2) := hnorm.2
    _ = 2 * Real.exp (CH Kc * 16 * model.delta ^ 2) := by norm_num

/-- Converts an integral bound on `F^a` (`F ≥ 0`) to an `eLpNorm` bound at exponent `a`
(generic, no probability-specific content: `aux_U2_ref_band_eLpNorm_of_integral_rpow`). -/
theorem aux_fscc_holNeuH_eLpNorm_of_integral_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (hFm : Measurable F) (hFnonneg : ∀ y, 0 ≤ F y)
    (a : ℝ) (ha : 0 < a) (hFa : Integrable (fun y => (F y) ^ a) μ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : (∫ y, (F y) ^ a ∂μ) ≤ M) :
    eLpNorm F (ENNReal.ofReal a) μ ≤ ENNReal.ofReal (M ^ (1 / a)) := by
  have hane : ENNReal.ofReal a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr ha)
  have hatop : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  have haR : (ENNReal.ofReal a).toReal = a := ENNReal.toReal_ofReal ha.le
  have hpt : ∀ y, ‖F y‖ₑ ^ a = ENNReal.ofReal ((F y) ^ a) := by
    intro y
    rw [Real.enorm_eq_ofReal (hFnonneg y),
      ENNReal.ofReal_rpow_of_nonneg (hFnonneg y) ha.le]
  have hnn : 0 ≤ᵐ[μ] fun y => (F y) ^ a :=
    Filter.Eventually.of_forall (fun y => Real.rpow_nonneg (hFnonneg y) a)
  have hlint : (∫⁻ y, ‖F y‖ₑ ^ a ∂μ) ≤ ENNReal.ofReal M := by
    calc (∫⁻ y, ‖F y‖ₑ ^ a ∂μ) = ∫⁻ y, ENNReal.ofReal ((F y) ^ a) ∂μ :=
          lintegral_congr fun y => hpt y
      _ = ENNReal.ofReal (∫ y, (F y) ^ a ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hFa hnn).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal hM
  rw [eLpNorm_eq_lintegral_rpow_enorm hane hatop, haR]
  calc (∫⁻ y, ‖F y‖ₑ ^ a ∂μ) ^ (1 / a) ≤ (ENNReal.ofReal M) ^ (1 / a) :=
        ENNReal.rpow_le_rpow hlint (by positivity)
    _ = ENNReal.ofReal (M ^ (1 / a)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hM0 (by positivity)]

theorem aux_fscc_holNeuH_retained_measurable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (m : ℤ) (w : SpatialCoordinates d) :
    Measurable (fun om : BilateralField d => aux_transport_retained m w om) := by
  unfold aux_transport_retained aux_transport_ret
  have hterm : ∀ j : ℤ, Measurable (fun om : BilateralField d => (om j) w) := fun j =>
    (continuous_eval_const w).measurable.comp (measurable_pi_apply j)
  split_ifs with hm0
  · exact Finset.measurable_sum _ (fun j _ => hterm (-j))
  · exact (Finset.measurable_sum _ (fun j _ => hterm (-j))).neg

theorem aux_fscc_holNeuH_ref_inv_moment
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization model H)
    (w : SpatialCoordinates d) (m : ℤ) :
    ∃ Cref : ℝ, 0 ≤ Cref ∧
      ∀ J : ℕ, m ≤ (J : ℤ) →
        MemLp (fun om => (aux_transport_reference model H J m w om)⁻¹)
          (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure ∧
        eLpNorm (fun om => (aux_transport_reference model H J m w om)⁻¹)
          (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Cref := by
  obtain ⟨CHw, hCHw0, hHint, hHbound⟩ := aux_fscc_holNeuH_H_neg4_moment hd model H hH w
  obtain ⟨Bret, hBret0, hRetInt, hRetBound⟩ :
      ∃ Bret : ℝ, 0 ≤ Bret ∧
        Integrable (fun om => Real.exp (-4 * aux_transport_retained m w om))
          (chaosSampleLaw model).toMeasure ∧
        (∫ om, Real.exp (-4 * aux_transport_retained m w om)
          ∂(chaosSampleLaw model).toMeasure) ≤ Bret := by
    rcases le_or_lt 0 m with hm | hm
    · exact aux_fscc_holNeuH_retained_moment_pos model m hm w
    · exact aux_fscc_holNeuH_retained_moment_neg model m hm w
  have hRetMeas := aux_fscc_holNeuH_retained_measurable (d := d) m w
  set Msup : ℝ := Real.exp (2 * (m.natAbs : ℝ) *
    SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) * ((CHw + Bret) / 2) with hMsupdef
  have hMsup0 : 0 ≤ Msup := by rw [hMsupdef]; positivity
  set Cref : ℝ := Msup ^ (1 / 2 : ℝ) with hCrefdef
  refine ⟨Cref, Real.rpow_nonneg hMsup0 _, ?_⟩
  intro J hmJ
  have hpt : ∀ om : BilateralField d,
      Real.exp (-2 * H om w) * Real.exp (-2 * aux_transport_retained m w om) ≤
        (Real.exp (-4 * H om w) + Real.exp (-4 * aux_transport_retained m w om)) / 2 := by
    intro om
    have hx2 : Real.exp (-2 * H om w) ^ 2 = Real.exp (-4 * H om w) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have hy2 : Real.exp (-2 * aux_transport_retained m w om) ^ 2 =
        Real.exp (-4 * aux_transport_retained m w om) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    nlinarith [sq_nonneg (Real.exp (-2 * H om w) - Real.exp (-2 * aux_transport_retained m w om)),
      hx2, hy2]
  have hSumInt : Integrable (fun om => Real.exp (-4 * H om w) +
      Real.exp (-4 * aux_transport_retained m w om)) (chaosSampleLaw model).toMeasure :=
    hHint.add hRetInt
  have hProdMeas : Measurable (fun om : BilateralField d =>
      Real.exp (-2 * H om w) * Real.exp (-2 * aux_transport_retained m w om)) := by
    have h1 : Measurable (fun om : BilateralField d => Real.exp (-2 * H om w)) :=
      (measurable_const.mul ((continuous_eval_const w).measurable.comp hH.1)).exp
    have h2 : Measurable (fun om : BilateralField d =>
        Real.exp (-2 * aux_transport_retained m w om)) :=
      (measurable_const.mul hRetMeas).exp
    exact h1.mul h2
  have hProdInt : Integrable (fun om : BilateralField d =>
      Real.exp (-2 * H om w) * Real.exp (-2 * aux_transport_retained m w om))
      (chaosSampleLaw model).toMeasure := by
    refine hSumInt.mono' hProdMeas.aestronglyMeasurable ?_
    filter_upwards [] with om
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
    have h0 : (0:ℝ) ≤ Real.exp (-4 * H om w) + Real.exp (-4 * aux_transport_retained m w om) :=
      by positivity
    linarith [hpt om]
  have hProdBound : (∫ om, Real.exp (-2 * H om w) *
      Real.exp (-2 * aux_transport_retained m w om) ∂(chaosSampleLaw model).toMeasure) ≤
      (CHw + Bret) / 2 := by
    calc (∫ om, Real.exp (-2 * H om w) * Real.exp (-2 * aux_transport_retained m w om)
        ∂(chaosSampleLaw model).toMeasure) ≤
        ∫ om, (Real.exp (-4 * H om w) + Real.exp (-4 * aux_transport_retained m w om)) / 2
          ∂(chaosSampleLaw model).toMeasure :=
        integral_mono hProdInt (hSumInt.div_const 2) hpt
      _ = (∫ om, Real.exp (-4 * H om w) + Real.exp (-4 * aux_transport_retained m w om)
          ∂(chaosSampleLaw model).toMeasure) / 2 := by
        rw [integral_div]
      _ ≤ (CHw + Bret) / 2 := by
        have := integral_add hHint hRetInt
        have hle : (∫ om, Real.exp (-4 * H om w) + Real.exp (-4 * aux_transport_retained m w om)
            ∂(chaosSampleLaw model).toMeasure) ≤ CHw + Bret := by
          rw [this]
          linarith [hHbound, hRetBound]
        linarith
  obtain ⟨hκlo, hκhi⟩ := aux_fscc_holNeuH_kappa_ratio_bound model m J hmJ
  have hκpos : 0 < aux_transport_kappa model ((J : ℤ) - m).toNat / aux_transport_kappa model J := by
    unfold aux_transport_kappa
    have h1 : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom model ((J : ℤ) - m).toNat :=
      SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model _
    have h2 : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom model J := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model J
    positivity
  have hinv_le : ∀ a b : ℝ, 0 < a → a ≤ b → b⁻¹ ≤ a⁻¹ := by
    intro a b ha hab
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le ha hab
  have hκlo' : Real.exp (-((m.natAbs : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) ≤
      aux_transport_kappa model ((J : ℤ) - m).toNat / aux_transport_kappa model J := by
    rw [← neg_mul]; exact hκlo
  have hκinv_bound : (aux_transport_kappa model ((J : ℤ) - m).toNat /
      aux_transport_kappa model J)⁻¹ ≤ Real.exp ((m.natAbs : ℝ) *
      SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) := by
    have hstep := hinv_le _ _ (Real.exp_pos _) hκlo'
    rwa [← Real.exp_neg, neg_neg] at hstep
  set κratio : ℝ := aux_transport_kappa model ((J : ℤ) - m).toNat / aux_transport_kappa model J
    with hκratiodef
  have hrefeq : ∀ om : BilateralField d,
      aux_transport_reference model H J m w om =
        κratio * Real.exp (H om w + aux_transport_retained m w om) := fun _ => rfl
  have hrefpos : ∀ om : BilateralField d, 0 < aux_transport_reference model H J m w om := by
    intro om
    rw [hrefeq om]
    exact mul_pos hκpos (Real.exp_pos _)
  have hsqeq : ∀ om : BilateralField d,
      ((aux_transport_reference model H J m w om)⁻¹) ^ (2 : ℝ) =
        κratio⁻¹ ^ (2 : ℝ) *
          (Real.exp (-2 * H om w) * Real.exp (-2 * aux_transport_retained m w om)) := by
    intro om
    rw [hrefeq om, mul_inv, ← Real.exp_neg,
      Real.mul_rpow (by positivity) (Real.exp_pos _).le]
    congr 1
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
    congr 1
    ring
  have hrefMeas : Measurable (fun om : BilateralField d =>
      aux_transport_reference model H J m w om) := by
    have heq : (fun om : BilateralField d => aux_transport_reference model H J m w om) =
        fun om => κratio * Real.exp (H om w + aux_transport_retained m w om) := funext hrefeq
    rw [heq]
    exact measurable_const.mul
      (((continuous_eval_const w).measurable.comp hH.1).add hRetMeas).exp
  have hFm : Measurable (fun om : BilateralField d =>
      (aux_transport_reference model H J m w om)⁻¹) := hrefMeas.inv
  have hFnonneg : ∀ om : BilateralField d, 0 ≤ (aux_transport_reference model H J m w om)⁻¹ :=
    fun om => inv_nonneg.mpr (hrefpos om).le
  have hFa : Integrable (fun om : BilateralField d =>
      ((aux_transport_reference model H J m w om)⁻¹) ^ (2 : ℝ))
      (chaosSampleLaw model).toMeasure := by
    have heq : (fun om : BilateralField d => ((aux_transport_reference model H J m w om)⁻¹) ^ (2 : ℝ)) =
        fun om => κratio⁻¹ ^ (2 : ℝ) *
          (Real.exp (-2 * H om w) * Real.exp (-2 * aux_transport_retained m w om)) :=
      funext hsqeq
    rw [heq]
    exact hProdInt.const_mul _
  set M : ℝ := κratio⁻¹ ^ (2 : ℝ) * ((CHw + Bret) / 2) with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have : (0:ℝ) ≤ κratio⁻¹ ^ (2:ℝ) := Real.rpow_nonneg (inv_nonneg.mpr hκpos.le) _
    positivity
  have hMbound : (∫ om, ((aux_transport_reference model H J m w om)⁻¹) ^ (2 : ℝ)
      ∂(chaosSampleLaw model).toMeasure) ≤ M := by
    have heq : (∫ om, ((aux_transport_reference model H J m w om)⁻¹) ^ (2 : ℝ)
        ∂(chaosSampleLaw model).toMeasure) =
        κratio⁻¹ ^ (2 : ℝ) * (∫ om, Real.exp (-2 * H om w) *
          Real.exp (-2 * aux_transport_retained m w om) ∂(chaosSampleLaw model).toMeasure) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hsqeq)
    rw [heq, hMdef]
    have hκnn : (0:ℝ) ≤ κratio⁻¹ ^ (2:ℝ) := Real.rpow_nonneg (inv_nonneg.mpr hκpos.le) _
    exact mul_le_mul_of_nonneg_left hProdBound hκnn
  have hEL := aux_fscc_holNeuH_eLpNorm_of_integral_rpow (chaosSampleLaw model).toMeasure
    (fun om => (aux_transport_reference model H J m w om)⁻¹) hFm hFnonneg 2 (by norm_num)
    hFa M hM0 hMbound
  have hMMsup : M ≤ Msup := by
    rw [hMdef, hMsupdef]
    have hκnn : (0:ℝ) ≤ κratio⁻¹ ^ (2:ℝ) := Real.rpow_nonneg (inv_nonneg.mpr hκpos.le) _
    have hκsq_le : κratio⁻¹ ^ (2:ℝ) ≤
        Real.exp (2 * (m.natAbs:ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) := by
      have h1 : κratio⁻¹ ^ (2:ℝ) ≤ (Real.exp ((m.natAbs:ℝ) *
          SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P)) ^ (2:ℝ) :=
        Real.rpow_le_rpow (inv_nonneg.mpr hκpos.le) hκinv_bound (by norm_num)
      rwa [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
        show (m.natAbs:ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P * 2 =
          2 * (m.natAbs:ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P by ring] at h1
    exact mul_le_mul_of_nonneg_right hκsq_le (by positivity)
  have hMhalf_le : M ^ (1 / 2 : ℝ) ≤ Cref := by
    rw [hCrefdef]
    exact Real.rpow_le_rpow hM0 hMMsup (by norm_num)
  refine ⟨⟨hFm.aestronglyMeasurable, ?_⟩, ?_⟩
  · exact lt_of_le_of_lt (hEL.trans (ENNReal.ofReal_le_ofReal hMhalf_le)) ENNReal.ofReal_lt_top
  · exact hEL.trans (ENNReal.ofReal_le_ofReal hMhalf_le)

/-- **H1 close**: combines the cutoff-uniform `p = 2` moment of `Kcor` (pushed through
`S_{m,w}` by measure-preservation) with the `p = 2` moment of `reference⁻¹`
(`aux_fscc_holNeuH_ref_inv_moment`) via Cauchy--Schwarz (`ENNReal.HolderTriple 2 2 1`) into the
cutoff-uniform `p = 1` moment of the product, scaled by the deterministic constants
`sqrt d ^ (1/2)` and `r ^ (3/2)`. -/
theorem aux_fscc_holNeuH_hRefMoment
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ)
    (Kcor : ℕ → BilateralField d → ℝ) (Cb2 : ℝ) (hCb0 : 0 ≤ Cb2)
    (hmemK2 : ∀ N, MemLp (Kcor N) (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure)
    (hnormK2 : ∀ N, eLpNorm (Kcor N) (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Cb2)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization model H)
    (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (alpha : ℝ) :
    ∃ Cref : ℝ, 0 ≤ Cref ∧
      ∀ J : ℕ, m ≤ (J : ℤ) →
        MemLp (fun omega => Real.sqrt d ^ alpha *
              Kcor ((J : ℤ) - m).toNat (aux_transport_S m w omega) * r ^ (2 - alpha) /
              aux_transport_reference model H J m w omega)
            (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ∧
          eLpNorm (fun omega => Real.sqrt d ^ alpha *
              Kcor ((J : ℤ) - m).toNat (aux_transport_S m w omega) * r ^ (2 - alpha) /
              aux_transport_reference model H J m w omega)
            (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Cref := by
  obtain ⟨CrefG, hCrefG0, hRef⟩ := aux_fscc_holNeuH_ref_inv_moment d hd model H hH w m
  set c : ℝ := Real.sqrt d ^ alpha * r ^ (2 - alpha) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  refine ⟨c * (Cb2 * CrefG), by positivity, ?_⟩
  intro J hmJ
  set N : ℕ := ((J : ℤ) - m).toNat with hNdef
  have hSmp := aux_transport_S_measurePreserving model m w
  have hf2 : MemLp (fun omega => Kcor N (aux_transport_S m w omega))
      (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure :=
    (hmemK2 N).comp_measurePreserving hSmp
  have hf2norm : eLpNorm (fun omega => Kcor N (aux_transport_S m w omega))
      (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Cb2 := by
    have heq : eLpNorm (fun omega => Kcor N (aux_transport_S m w omega)) (ENNReal.ofReal 2)
        (chaosSampleLaw model).toMeasure =
        eLpNorm (Kcor N) (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure := by
      simpa [Function.comp_def] using
        eLpNorm_comp_measurePreserving (p := ENNReal.ofReal 2)
          (hmemK2 N).aestronglyMeasurable hSmp
    rw [heq]
    exact hnormK2 N
  obtain ⟨hg2, hg2norm⟩ := hRef J hmJ
  have hp2 : (ENNReal.ofReal (2 : ℝ)) = (2 : ℝ≥0∞) := by norm_num
  have hp1 : (ENNReal.ofReal (1 : ℝ)) = (1 : ℝ≥0∞) := ENNReal.ofReal_one
  rw [hp2] at hf2 hf2norm hg2 hg2norm
  have hmul : MemLp (fun omega => Kcor N (aux_transport_S m w omega) *
      (aux_transport_reference model H J m w omega)⁻¹)
      (1 : ℝ≥0∞) (chaosSampleLaw model).toMeasure := by
    have hraw := MemLp.mul' (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (f := fun omega => (aux_transport_reference model H J m w omega)⁻¹)
      (φ := fun omega => Kcor N (aux_transport_S m w omega)) hg2 hf2
    simpa using hraw
  have hmulnorm : eLpNorm (fun omega => Kcor N (aux_transport_S m w omega) *
      (aux_transport_reference model H J m w omega)⁻¹)
      (1 : ℝ≥0∞) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Cb2 * ENNReal.ofReal CrefG := by
    have hle := eLpNorm_smul_le_mul_eLpNorm (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (f := fun omega => (aux_transport_reference model H J m w omega)⁻¹)
      (φ := fun omega => Kcor N (aux_transport_S m w omega)) hg2.1 hf2.1
    simp only [smul_eq_mul] at hle
    calc eLpNorm (fun omega => Kcor N (aux_transport_S m w omega) *
          (aux_transport_reference model H J m w omega)⁻¹) (1 : ℝ≥0∞)
          (chaosSampleLaw model).toMeasure
        ≤ eLpNorm (fun omega => Kcor N (aux_transport_S m w omega)) (2 : ℝ≥0∞)
            (chaosSampleLaw model).toMeasure *
          eLpNorm (fun omega => (aux_transport_reference model H J m w omega)⁻¹) (2 : ℝ≥0∞)
            (chaosSampleLaw model).toMeasure := hle
      _ ≤ ENNReal.ofReal Cb2 * ENNReal.ofReal CrefG := mul_le_mul' hf2norm hg2norm
  have hgoalfun : (fun omega => Real.sqrt d ^ alpha *
        Kcor N (aux_transport_S m w omega) * r ^ (2 - alpha) /
        aux_transport_reference model H J m w omega) =
      fun omega => c * (Kcor N (aux_transport_S m w omega) *
        (aux_transport_reference model H J m w omega)⁻¹) := by
    funext omega
    rw [hcdef, div_eq_mul_inv]
    ring
  rw [hgoalfun, hp1]
  refine ⟨hmul.const_mul c, ?_⟩
  calc eLpNorm (fun omega => c * (Kcor N (aux_transport_S m w omega) *
        (aux_transport_reference model H J m w omega)⁻¹)) (1 : ℝ≥0∞)
        (chaosSampleLaw model).toMeasure
      ≤ ‖c‖ₑ * eLpNorm (fun omega => Kcor N (aux_transport_S m w omega) *
          (aux_transport_reference model H J m w omega)⁻¹) (1 : ℝ≥0∞)
          (chaosSampleLaw model).toMeasure := by
        simpa [smul_eq_mul] using
          (eLpNorm_const_smul_le (c := c)
            (f := fun omega => Kcor N (aux_transport_S m w omega) *
              (aux_transport_reference model H J m w omega)⁻¹) (p := (1 : ℝ≥0∞))
            (μ := (chaosSampleLaw model).toMeasure))
    _ ≤ ‖c‖ₑ * (ENNReal.ofReal Cb2 * ENNReal.ofReal CrefG) := mul_le_mul_left' hmulnorm _
    _ = ENNReal.ofReal (c * (Cb2 * CrefG)) := by
        rw [Real.enorm_eq_ofReal hc0, ← ENNReal.ofReal_mul hCb0, ← ENNReal.ofReal_mul hc0]


/-- **The mean-zero Neumann Hölder branch for the characterized infrared field, every exponent
`α ∈ (0,1)`, every triadic root `r = 3^j`, every cutoff `J ≥ -j`.** -/
theorem fscc_char_holder_neumann
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d model)
        (Sreg : in_6_16 d model) (_It : in_iteration d model E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization model H → model.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (j : ℤ) (r : ℝ) (hr : 0 < r), r = (3 : ℝ) ^ j →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbank : ℝ),
        (∀ J, MemLp (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
        (∀ J, eLpNorm (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal Cbank) ∧
        ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ, -j ≤ (J : ℤ) →
          aux_fscc_holder_predicates_holNeu d z r hr
            (cutoffPositiveCoefficient model H omega J z hr) alpha (K J omega) := by
  have ht1 : (d : ℝ) - 1 < (d : ℝ) - 1 / 2 := by linarith
  have ht2 : (d : ℝ) - 1 / 2 < d := by linarith
  obtain ⟨delta0, hdelta0, hCor⟩ :=
    cor_neumann_source d hd E P X W D Cp ((d : ℝ) - 1 / 2) alpha 2 ![1, 2] ht1 ht2
      ha0 ha1 (fun i => by fin_cases i <;> norm_num)
  refine ⟨delta0, hdelta0, ?_⟩
  intro model Rm Sreg It H hH hdelta z j r hr hj
  obtain ⟨Kcor, Cbcor, hmemcor, hnormcor, haecor⟩ := hCor model Rm Sreg It H hH hdelta
  set z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ) with hz0def
  set m : ℤ := -j with hmdef
  have hrm : r = (3 : ℝ) ^ (-m) := by rw [hmdef, neg_neg, hj]
  set w : SpatialCoordinates d := fun i => z i - r * z0 i with hwdef
  have hTeq : ∀ x : SpatialCoordinates d, cubeDilation z z0 r x = w + (3 : ℝ) ^ (-m) • x := by
    intro x
    funext i
    simp only [cubeDilation_apply, hwdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hrm]
    ring
  have hinjQ : ∀ x : SpatialCoordinates d, cubeDilation z0 z r⁻¹ (cubeDilation z z0 r x) = x := by
    intro x
    have hrne : r ≠ 0 := hr.ne'
    funext i
    simp only [cubeDilation_apply]
    field_simp
    ring
  have hq := lane4_dilation_quasi_measure_preserving d z z0 r hr one_pos
  have hCoreJ : ∀ J : ℕ, m ≤ (J : ℤ) →
      ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
        aux_fscc_holder_predicates_holNeu d z r hr
          (cutoffPositiveCoefficient model H omega J z hr) alpha
          (Real.sqrt d ^ alpha * Kcor ((J : ℤ) - m).toNat (aux_transport_S m w omega) *
            r ^ (2 - alpha) / aux_transport_reference model H J m w omega) := by
    intro J hmJ
    filter_upwards [aux_fscc_holNeuH_coeff_ident model H hH m w J hmJ z0,
        (aux_transport_S_measurePreserving model m w).quasiMeasurePreserving.ae haecor]
      with omega hcoeff hcorSraw
    exact aux_fscc_holNeuH_core model H z z0 w m r hr alpha ha0 hz0def hTeq hinjQ Kcor J omega
      hcoeff (fun N F Kf hKf hF hFb hFint v hsol => (hcorSraw N F Kf hKf hF hFb hFint v hsol).1) hq
  obtain ⟨Cref, hCref0, hRef⟩ := aux_fscc_holNeuH_hRefMoment hd model m Kcor |Cbcor 1|
    (abs_nonneg _) (fun N => hmemcor 1 N)
    (fun N => (hnormcor 1 N).trans (ENNReal.ofReal_le_ofReal (le_abs_self _))) H hH w r hr alpha
  refine ⟨fun J omega => if m ≤ (J : ℤ) then
      Real.sqrt d ^ alpha * Kcor ((J : ℤ) - m).toNat (aux_transport_S m w omega) *
        r ^ (2 - alpha) / aux_transport_reference model H J m w omega
    else 0, Cref, ?_, ?_, ?_⟩
  · intro J
    by_cases hmJ : m ≤ (J : ℤ)
    · simp only [if_pos hmJ]; exact (hRef J hmJ).1
    · simp only [if_neg hmJ]; exact memLp_const 0
  · intro J
    by_cases hmJ : m ≤ (J : ℤ)
    · simp only [if_pos hmJ]; exact (hRef J hmJ).2
    · simp only [if_neg hmJ]
      rw [show (fun _ : BilateralField d => (0 : ℝ)) = 0 from rfl, eLpNorm_zero]
      exact zero_le _
  · rw [ae_all_iff]
    intro J
    by_cases hmJ : m ≤ (J : ℤ)
    · filter_upwards [hCoreJ J hmJ] with omega hom _
      simpa only [if_pos hmJ] using hom
    · exact Filter.Eventually.of_forall (fun _ hcon => absurd hcon hmJ)

end Paper
