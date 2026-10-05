module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Homogenization.Book.Ch02.Matrices
public import SubdiffusiveProcess.Main.ChaosRootFieldLaw
public import SubdiffusiveProcess.Main.ScaledLayerLaw
public import SubdiffusiveProcess.Main.LayerScaling
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Tactic


@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace SubdiffusiveProcess.Paper

def aux_g9chart_transport_cellMap {d : ℕ} (m : ℤ) (w : SpatialCoordinates d) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨cubeDilation w 0 ((3 : ℝ) ^ (-m)), continuous_cubeDilation w 0 _⟩

theorem aux_g9chart_transport_cellMap_apply {d : ℕ} (m : ℤ) (w y : SpatialCoordinates d) :
    aux_g9chart_transport_cellMap m w y = w + (3 : ℝ) ^ (-m) • y := by
  funext i
  simp [aux_g9chart_transport_cellMap, cubeDilation_apply]

def aux_g9chart_transport_S {d : ℕ} (m : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) :
    BilateralField d :=
  fun j => (om (j - m)).comp (aux_g9chart_transport_cellMap m w)

theorem aux_g9chart_transport_S_apply {d : ℕ} (m : ℤ) (w : SpatialCoordinates d) (om : BilateralField d)
    (i : ℤ) (y : SpatialCoordinates d) :
    aux_g9chart_transport_S m w om i y = om (i - m) (w + (3 : ℝ) ^ (-m) • y) := by
  simp only [aux_g9chart_transport_S, ContinuousMap.comp_apply, aux_g9chart_transport_cellMap_apply]

section MeasurePreservingS

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_g9chart_transport_S_measurable (m : ℤ) (w : SpatialCoordinates d) :
    Measurable (aux_g9chart_transport_S (d := d) m w) := by
  have hc : Measurable fun f : C(SpatialCoordinates d, ℝ) =>
      f.comp (aux_g9chart_transport_cellMap m w) := by fun_prop
  exact Measurable.of_eval fun j => hc.comp (measurable_pi_apply (j - m))

theorem aux_g9chart_transport_S_measurePreserving (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℤ)
    (w : SpatialCoordinates d) :
    MeasurePreserving (aux_g9chart_transport_S m w)
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure := by
  set D := aux_g9chart_transport_cellMap (d := d) m w with hD
  set ν := chaosRootFieldLaw model with hν
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
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
        hD, aux_g9chart_transport_cellMap, translateZ, z]
      congr 1
      ext i
      rw [hD]
      simp only [aux_g9chart_transport_cellMap, ContinuousMap.coe_mk,
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
      simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq]
      rfl
    rw [e1, e2] at h
    exact h
  have hco := Measure.infinitePi_map_pi (μ := fun j => laws (j - m))
    (f := fun _ : ℤ => fun f : C(SpatialCoordinates d, ℝ) => f.comp D) (fun _ => hcompD)
  refine ⟨aux_g9chart_transport_S_measurable m w, ?_⟩
  have hsplit : aux_g9chart_transport_S (d := d) m w =
      (fun (x : ℤ → C(SpatialCoordinates d, ℝ)) (i : ℤ) => (x i).comp D) ∘
        (fun (omC : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => omC (j - m)) := rfl
  change Measure.map (aux_g9chart_transport_S m w) (Measure.infinitePi laws) = Measure.infinitePi laws
  have hg : Measurable (fun (x : ℤ → C(SpatialCoordinates d, ℝ))
      (i : ℤ) => (x i).comp D) :=
    Measurable.of_eval fun i => hcompD.comp (measurable_pi_apply i)
  have hf : Measurable (fun (omC : ℤ → C(SpatialCoordinates d, ℝ))
      (j : ℤ) => omC (j - m)) :=
    Measurable.of_eval fun j => measurable_pi_apply (j - m)
  have hco' : Measure.map (fun (x : ℤ → C(SpatialCoordinates d, ℝ))
      (i : ℤ) => (x i).comp D) (Measure.infinitePi fun j => laws (j - m)) =
      Measure.infinitePi fun i => Measure.map
        (fun f : C(SpatialCoordinates d, ℝ) => f.comp D) (laws (i - m)) := hco
  rw [hsplit, ← Measure.map_map hg hf, hre, hco']
  congr 1
  funext j
  exact hlayer j

end MeasurePreservingS

def aux_g9chart_transport_ret (m : ℤ) (f : ℤ → ℝ) : ℝ :=
  if 0 ≤ m then ∑ j ∈ Finset.Ico (0 : ℤ) m, f (-j) else
    -∑ j ∈ Finset.Ico m (0 : ℤ), f (-j)

def aux_g9chart_transport_retained {d : ℕ} (m : ℤ) (z : SpatialCoordinates d)
    (om : BilateralField d) : ℝ := aux_g9chart_transport_ret m (fun j => om j z)

theorem aux_g9chart_transport_sum_range_shift (G : ℤ → ℝ) (a : ℤ) (t : ℕ) :
    ∑ k ∈ Finset.range t, G (a + k) = ∑ j ∈ Finset.Ico a (a + t), G j := by
  refine Finset.sum_nbij' (fun k : ℕ => a + (k : ℤ)) (fun j : ℤ => (j - a).toNat)
    ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Ico]; omega
  · intro j hj; simp only [Finset.mem_Ico] at hj
    simp only [Finset.mem_range]; omega
  · intro k _; simp
  · intro j hj; simp only [Finset.mem_Ico] at hj; omega
  · intro k _; rfl

theorem aux_g9chart_transport_potential_sum (f : ℤ → ℝ) (N : ℕ) (m : ℤ) (hm : m ≤ (N : ℤ)) :
    ∑ j ∈ Finset.range (N + 1), f (-(Int.ofNat j)) =
      ∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1), f (-(Int.ofNat k) - m) +
        aux_g9chart_transport_ret m f := by
  have hL : ∑ j ∈ Finset.range (N + 1), f (-(Int.ofNat j)) =
      ∑ j ∈ Finset.Ico (0 : ℤ) ((N : ℤ) + 1), f (-j) := by
    have h := aux_g9chart_transport_sum_range_shift (fun j => f (-j)) 0 (N + 1)
    simpa using h
  have hR : ∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1), f (-(Int.ofNat k) - m) =
      ∑ j ∈ Finset.Ico m ((N : ℤ) + 1), f (-j) := by
    have h1 := aux_g9chart_transport_sum_range_shift (fun j => f (-j)) m (((N : ℤ) - m).toNat + 1)
    have h2 : m + ((((N : ℤ) - m).toNat + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by omega
    rw [h2] at h1
    rw [← h1]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1; simp; ring
  rw [hL, hR]
  unfold aux_g9chart_transport_ret
  by_cases h0 : 0 ≤ m
  · rw [ite_eq_left h0]
    have hU : Finset.Ico (0 : ℤ) ((N : ℤ) + 1) =
        Finset.Ico (0 : ℤ) m ∪ Finset.Ico m ((N : ℤ) + 1) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
    have hD : Disjoint (Finset.Ico (0 : ℤ) m) (Finset.Ico m ((N : ℤ) + 1)) :=
      Finset.disjoint_left.2 (by
        intro x hx hx'; simp only [Finset.mem_Ico] at hx hx'; omega)
    rw [hU, Finset.sum_union hD]; ring
  · rw [ite_eq_right h0]
    have hU : Finset.Ico m ((N : ℤ) + 1) =
        Finset.Ico m (0 : ℤ) ∪ Finset.Ico (0 : ℤ) ((N : ℤ) + 1) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
    have hD : Disjoint (Finset.Ico m (0 : ℤ)) (Finset.Ico (0 : ℤ) ((N : ℤ) + 1)) :=
      Finset.disjoint_left.2 (by
        intro x hx hx'; simp only [Finset.mem_Ico] at hx hx'; omega)
    rw [hU, Finset.sum_union hD]; ring

theorem aux_g9chart_transport_infrared_sum (F : ℤ → ℝ) (m : ℤ) (L : ℕ) (hL : m ≤ (L : ℤ)) :
    ∑ n ∈ Finset.range L, F ((Int.ofNat (n + 1)) - m) =
      ∑ n ∈ Finset.range (((L : ℤ) - m).toNat), F (Int.ofNat (n + 1)) +
        aux_g9chart_transport_ret m F := by
  have hA : ∑ n ∈ Finset.range L, F ((Int.ofNat (n + 1)) - m) =
      ∑ j ∈ Finset.Ico (1 - m) (1 - m + L), F j := by
    rw [← aux_g9chart_transport_sum_range_shift F (1 - m) L]
    refine Finset.sum_congr rfl (fun k _ => ?_); congr 1; simp; ring
  have hB : ∑ n ∈ Finset.range (((L : ℤ) - m).toNat), F (Int.ofNat (n + 1)) =
      ∑ j ∈ Finset.Ico 1 (1 - m + L), F j := by
    have h1 := aux_g9chart_transport_sum_range_shift F 1 (((L : ℤ) - m).toNat)
    have h2 : (1 : ℤ) + ((((L : ℤ) - m).toNat : ℕ) : ℤ) = 1 - m + L := by omega
    rw [h2] at h1; rw [← h1]
    refine Finset.sum_congr rfl (fun k _ => ?_); congr 1; simp; ring
  rw [hA, hB]; unfold aux_g9chart_transport_ret
  by_cases h0 : 0 ≤ m
  · rw [ite_eq_left h0]
    have hrefl : ∑ j ∈ Finset.Ico (0 : ℤ) m, F (-j) =
        ∑ i ∈ Finset.Ico (1 - m) 1, F i := by
      refine Finset.sum_nbij' (fun j : ℤ => -j) (fun i : ℤ => -i) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
      · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
      · intro j _; simp
      · intro i _; simp
      · intro j _; rfl
    rw [hrefl]
    have hU : Finset.Ico (1 - m) (1 - m + L) =
        Finset.Ico (1 - m) 1 ∪ Finset.Ico 1 (1 - m + L) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
    have hD : Disjoint (Finset.Ico (1 - m) 1) (Finset.Ico 1 (1 - m + L)) :=
      Finset.disjoint_left.2 (by
        intro x hx hx'; simp only [Finset.mem_Ico] at hx hx'; omega)
    rw [hU, Finset.sum_union hD]; ring
  · rw [ite_eq_right h0]
    have hrefl : ∑ j ∈ Finset.Ico m (0 : ℤ), F (-j) =
        ∑ i ∈ Finset.Ico 1 (1 - m), F i := by
      refine Finset.sum_nbij' (fun j : ℤ => -j) (fun i : ℤ => -i) ?_ ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
      · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
      · intro j _; simp
      · intro i _; simp
      · intro j _; rfl
    rw [hrefl]
    have hU : Finset.Ico 1 (1 - m + L) =
        Finset.Ico 1 (1 - m) ∪ Finset.Ico (1 - m) (1 - m + L) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union]; omega
    have hD : Disjoint (Finset.Ico 1 (1 - m)) (Finset.Ico (1 - m) (1 - m + L)) :=
      Finset.disjoint_left.2 (by
        intro x hx hx'; simp only [Finset.mem_Ico] at hx hx'; omega)
    rw [hU, Finset.sum_union hD]; ring

theorem aux_g9chart_transport_ret_sub (m : ℤ) (f g : ℤ → ℝ) :
    aux_g9chart_transport_ret m (fun i => f i - g i) = aux_g9chart_transport_ret m f - aux_g9chart_transport_ret m g := by
  unfold aux_g9chart_transport_ret
  split_ifs <;> simp [Finset.sum_sub_distrib] ; ring

theorem aux_g9chart_transport_toNat_tendsto (m : ℤ) :
    Tendsto (fun L : ℕ => (((L : ℤ) - m).toNat)) atTop atTop := by
  apply tendsto_atTop_atTop.2
  intro K
  refine ⟨(K + m.toNat + 1), fun L hL => ?_⟩
  omega

theorem aux_g9chart_transport_infraredPartialSum_apply {d : ℕ} (om : BilateralField d) (L : ℕ)
    (z : SpatialCoordinates d) :
    infraredPartialSum om L z =
      ∑ n ∈ Finset.range L, (om (Int.ofNat (n + 1)) z - om (Int.ofNat (n + 1)) 0) := by
  simp [infraredPartialSum, ContinuousMap.sum_apply]

theorem aux_g9chart_transport_infraredPartialSum_diff {d : ℕ} (om : BilateralField d) (K : ℕ)
    (x w : SpatialCoordinates d) :
    ∑ n ∈ Finset.range K, (om (Int.ofNat (n + 1)) x - om (Int.ofNat (n + 1)) w) =
      infraredPartialSum om K x - infraredPartialSum om K w := by
  rw [aux_g9chart_transport_infraredPartialSum_apply, aux_g9chart_transport_infraredPartialSum_apply,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem aux_g9chart_transport_infraredPartialSum_S {d : ℕ} (m : ℤ) (w : SpatialCoordinates d)
    (om : BilateralField d) (L : ℕ) (hL : m ≤ (L : ℤ)) (y : SpatialCoordinates d) :
    infraredPartialSum (aux_g9chart_transport_S m w om) L y =
      (infraredPartialSum om ((L : ℤ) - m).toNat (w + (3 : ℝ) ^ (-m) • y) -
          infraredPartialSum om ((L : ℤ) - m).toNat w) +
        (aux_g9chart_transport_retained m (w + (3 : ℝ) ^ (-m) • y) om -
          aux_g9chart_transport_retained m w om) := by
  set x := w + (3 : ℝ) ^ (-m) • y with hx
  rw [aux_g9chart_transport_infraredPartialSum_apply]
  have hstep : ∀ n : ℕ,
      aux_g9chart_transport_S m w om (Int.ofNat (n + 1)) y -
          aux_g9chart_transport_S m w om (Int.ofNat (n + 1)) 0 =
        om (Int.ofNat (n + 1) - m) x - om (Int.ofNat (n + 1) - m) w := by
    intro n
    simp only [aux_g9chart_transport_S_apply]
    have h0 : w + (3 : ℝ) ^ (-m) • (0 : SpatialCoordinates d) = w := by simp
    rw [h0]
  simp_rw [hstep]
  have hF := aux_g9chart_transport_infrared_sum (fun j => om j x - om j w) m L hL
  rw [hF, aux_g9chart_transport_infraredPartialSum_diff]
  have hret : aux_g9chart_transport_ret m (fun j => om j x - om j w) =
      aux_g9chart_transport_retained m x om - aux_g9chart_transport_retained m w om :=
    aux_g9chart_transport_ret_sub m (fun j => om j x) (fun j => om j w)
  rw [hret]

theorem aux_g9chart_transport_infrared {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) (m : ℤ) (w : SpatialCoordinates d) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ y : SpatialCoordinates d,
        H (aux_g9chart_transport_S m w om) y =
          H om (w + (3 : ℝ) ^ (-m) • y) - H om w +
            aux_g9chart_transport_retained m (w + (3 : ℝ) ^ (-m) • y) om -
              aux_g9chart_transport_retained m w om := by
  have h1 := hH.2
  have h2 := (aux_g9chart_transport_S_measurePreserving M m w).quasiMeasurePreserving.ae hH.2
  filter_upwards [h1, h2] with om hom hom' y
  set x := w + (3 : ℝ) ^ (-m) • y with hx
  have hA : Tendsto (fun L : ℕ => infraredPartialSum (aux_g9chart_transport_S m w om) L y) atTop
      (𝓝 (H (aux_g9chart_transport_S m w om) y)) := by
    have hev : Tendsto (fun f : C(SpatialCoordinates d, ℝ) => f y)
        (𝓝 (H (aux_g9chart_transport_S m w om))) (𝓝 (H (aux_g9chart_transport_S m w om) y)) :=
      (continuous_eval_const _).tendsto _
    exact hev.comp hom'
  have hLx : Tendsto (fun L : ℕ => infraredPartialSum om (((L : ℤ) - m).toNat) x) atTop
      (𝓝 (H om x)) := by
    have hevx : Tendsto (fun f : C(SpatialCoordinates d, ℝ) => f x)
        (𝓝 (H om)) (𝓝 (H om x)) := (continuous_eval_const _).tendsto _
    exact (hevx.comp hom).comp (aux_g9chart_transport_toNat_tendsto m)
  have hLw : Tendsto (fun L : ℕ => infraredPartialSum om (((L : ℤ) - m).toNat) w) atTop
      (𝓝 (H om w)) := by
    have hevw : Tendsto (fun f : C(SpatialCoordinates d, ℝ) => f w)
        (𝓝 (H om)) (𝓝 (H om w)) := (continuous_eval_const _).tendsto _
    exact (hevw.comp hom).comp (aux_g9chart_transport_toNat_tendsto m)
  have hB : Tendsto (fun L : ℕ => infraredPartialSum (aux_g9chart_transport_S m w om) L y) atTop
      (𝓝 ((H om x - H om w) +
        (aux_g9chart_transport_retained m x om - aux_g9chart_transport_retained m w om))) := by
    have hlim : Tendsto (fun L : ℕ =>
        (infraredPartialSum om (((L : ℤ) - m).toNat) x -
            infraredPartialSum om (((L : ℤ) - m).toNat) w) +
          (aux_g9chart_transport_retained m x om - aux_g9chart_transport_retained m w om)) atTop
        (𝓝 ((H om x - H om w) +
          (aux_g9chart_transport_retained m x om - aux_g9chart_transport_retained m w om))) :=
      (hLx.sub hLw).add_const _
    have heq : ∀ᶠ L : ℕ in atTop, m ≤ (L : ℤ) := by
      filter_upwards [Filter.eventually_ge_atTop m.toNat] with L hL
      omega
    refine hlim.congr' ?_
    filter_upwards [heq] with L hL
    exact (aux_g9chart_transport_infraredPartialSum_S m w om L hL y).symm
  have hval := tendsto_nhds_unique hA hB
  linarith [hval]

def aux_g9chart_transport_kappa {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (J : ℕ) : ℝ :=
  Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) * ahom M J

def aux_g9chart_transport_reference {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (m : ℤ)
    (z : SpatialCoordinates d) (om : BilateralField d) : ℝ :=
  aux_g9chart_transport_kappa M (((N : ℤ) - m).toNat) / aux_g9chart_transport_kappa M N *
    Real.exp (H om z + aux_g9chart_transport_retained m z om)

theorem aux_g9chart_transport_reference_pos {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (m : ℤ)
    (z : SpatialCoordinates d) (om : BilateralField d) :
    0 < aux_g9chart_transport_reference M H N m z om := by
  unfold aux_g9chart_transport_reference aux_g9chart_transport_kappa
  have h1 : 0 < ahom M (((N : ℤ) - m).toNat) := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _
  have h2 : 0 < ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  positivity

theorem aux_g9chart_transport_potential {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) (m : ℤ) (w : SpatialCoordinates d) (N : ℕ)
    (hm : m ≤ (N : ℤ)) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ y : SpatialCoordinates d,
      cutoffPotential H om N (w + (3 : ℝ) ^ (-m) • y) =
        cutoffPotential H (aux_g9chart_transport_S m w om) (((N : ℤ) - m).toNat) y +
          H om w + aux_g9chart_transport_retained m w om := by
  filter_upwards [aux_g9chart_transport_infrared hH m w] with om hom y
  set x := w + (3 : ℝ) ^ (-m) • y with hx
  have hSk : ∀ k : ℕ, (aux_g9chart_transport_S m w om) (-(Int.ofNat k)) y =
      om (-(Int.ofNat k) - m) x := by
    intro k; exact aux_g9chart_transport_S_apply m w om (-(Int.ofNat k)) y
  have hshift := aux_g9chart_transport_potential_sum (fun j => om j x) N m hm
  have hret : aux_g9chart_transport_ret m (fun j => om j x) = aux_g9chart_transport_retained m x om := rfl
  rw [hret] at hshift
  have hpsum : ∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1),
      (aux_g9chart_transport_S m w om) (-(Int.ofNat k)) y =
      ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x -
        aux_g9chart_transport_retained m x om := by
    rw [show (∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1),
        (aux_g9chart_transport_S m w om) (-(Int.ofNat k)) y) =
        ∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1),
          om (-(Int.ofNat k) - m) x from
      Finset.sum_congr rfl (fun k _ => hSk k)]
    linarith [hshift]
  unfold cutoffPotential
  rw [hpsum, hom y]
  ring

theorem aux_g9chart_transport_coefficient {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℤ) (w : SpatialCoordinates d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (N : ℕ) (hm : m ≤ (N : ℤ)) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ y : SpatialCoordinates d,
      cutoffCoefficient M H om N (w + (3 : ℝ) ^ (-m) • y) =
        aux_g9chart_transport_reference M H N m w om *
          cutoffCoefficient M H (aux_g9chart_transport_S m w om) (((N : ℤ) - m).toNat) y := by
  filter_upwards [aux_g9chart_transport_potential hH m w N hm] with om hom y
  have hpot := hom y
  set K := ((N : ℤ) - m).toNat with hKdef
  have hNsub : (K : ℝ) = (N : ℝ) - (m : ℝ) := by
    have hnn : (0 : ℤ) ≤ (N : ℤ) - m := by omega
    have hKZ : (K : ℤ) = (N : ℤ) - m := by
      rw [hKdef]; exact Int.toNat_of_nonneg hnn
    exact_mod_cast hKZ
  have hposK : 0 < ahom M K := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M K
  have hposN : 0 < ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hne1 : ahom M N ≠ 0 := hposN.ne'
  have hL1 : cutoffCoefficient M H om N (w + (3 : ℝ) ^ (-m) • y) * ahom M N *
      Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
      Real.exp (cutoffPotential H om N (w + (3 : ℝ) ^ (-m) • y)) := by
    unfold cutoffCoefficient
    rw [Real.exp_sub]
    field_simp
  have hR1 : cutoffCoefficient M H (aux_g9chart_transport_S m w om) K y * ahom M K *
      Real.exp (((K : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
      Real.exp (cutoffPotential H (aux_g9chart_transport_S m w om) K y) := by
    unfold cutoffCoefficient
    rw [Real.exp_sub]
    field_simp
  have hexppot : Real.exp (cutoffPotential H om N (w + (3 : ℝ) ^ (-m) • y)) =
      Real.exp (cutoffPotential H (aux_g9chart_transport_S m w om) K y) *
        Real.exp (H om w + aux_g9chart_transport_retained m w om) := by
    rw [hpot, ← Real.exp_add]
    congr 1
    ring
  have hcombine : cutoffCoefficient M H om N (w + (3 : ℝ) ^ (-m) • y) * ahom M N *
      Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
      (cutoffCoefficient M H (aux_g9chart_transport_S m w om) K y * ahom M K *
          Real.exp (((K : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
        Real.exp (H om w + aux_g9chart_transport_retained m w om) := by
    rw [hL1, hR1, hexppot]
  unfold aux_g9chart_transport_reference aux_g9chart_transport_kappa
  have hexpN : Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≠ 0 :=
    (Real.exp_pos _).ne'
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hexpN hne1)]
  linear_combination hcombine

theorem aux_g9chart_transport_cubeDilation_qmp {d : ℕ} (z z' : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (h1 : (0 : ℝ) < 1) :
    Measure.QuasiMeasurePreserving (cubeDilation z z' r)
      (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  refine ⟨(continuous_cubeDilation z z' r).measurable, ?_⟩
  rw [map_cubeDilation_restrict z z' hr h1]
  exact Measure.smul_absolutelyContinuous

theorem aux_g9chart_transport_chart_agree {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (N : ℕ) (m : ℤ) (hm : m ≤ (N : ℤ)) (w : SpatialCoordinates d)
    (sidePos : ∀ n : ℤ, 0 < (3 : ℝ) ^ (-n)) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ Q : Homogenization.TriadicCube d,
        Homogenization.openCubeSet Q ⊆
          Homogenization.openCubeSet (Homogenization.originCube d 0) →
        ∀ᵐ pt ∂ volume.restrict (Homogenization.openCubeSet Q),
          ((I.chart w ((3 : ℝ) ^ (-m)) (sidePos m)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N w (sidePos m)) w
              ((3 : ℝ) ^ (-m))).coeffOn Q).toCoeffField pt =
            ((I.chart 0 1 one_pos
              (scalePositiveCoefficient (aux_g9chart_transport_reference M H N m w om)
                (aux_g9chart_transport_reference_pos M H N m w om)
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (aux_g9chart_transport_S m w om)
                  (((N : ℤ) - m).toNat) 0 one_pos))
              0 1).coeffOn Q).toCoeffField pt := by
  filter_upwards [aux_g9chart_transport_coefficient M m w hH N hm] with om hom Q hQ
  set K := ((N : ℤ) - m).toNat with hKdef
  set r : ℝ := (3 : ℝ) ^ (-m) with hrdef
  set A' := _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (aux_g9chart_transport_S m w om) K 0 one_pos
    with hA'def
  set ref := aux_g9chart_transport_reference M H N m w om with hrefdef
  have hrefpos := aux_g9chart_transport_reference_pos M H N m w om
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
        A'.val x = cutoffCoefficientCM M H (aux_g9chart_transport_S m w om) K 0 one_pos
          ⟨x, centeredCube_subset_closedCube 0 one_pos hx⟩ / 1 :=
    @normalizedContinuousPositiveCoefficient_coeFn d
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos)
      (closedCube (0 : SpatialCoordinates d) 1 one_pos)
      ⟨centeredCube_subset_closedCube 0 one_pos⟩
      (cutoffCoefficientCM M H (aux_g9chart_transport_S m w om) K 0 one_pos)
      (cutoffCoefficientCM_pos M H (aux_g9chart_transport_S m w om) K 0 one_pos) 1 one_pos
  have hLmapsTo := cubeDilation_mapsTo w (0 : SpatialCoordinates d) (sidePos m) one_pos
  have hqmpL := aux_g9chart_transport_cubeDilation_qmp w (0 : SpatialCoordinates d) (sidePos m) one_pos
  have hLval : ∀ᵐ x ∂ volume.restrict (centeredCube w r (sidePos m) : Set (SpatialCoordinates d)),
      ∀ hx : x ∈ centeredCube w r (sidePos m),
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N w (sidePos m)).val x =
          cutoffCoefficientCM M H om N w (sidePos m)
            ⟨x, centeredCube_subset_closedCube w (sidePos m) hx⟩ / 1 :=
    @normalizedContinuousPositiveCoefficient_coeFn d
      (centeredCube w r (sidePos m)) (closedCube w r (sidePos m))
      ⟨centeredCube_subset_closedCube w (sidePos m)⟩
      (cutoffCoefficientCM M H om N w (sidePos m))
      (cutoffCoefficientCM_pos M H om N w (sidePos m)) 1 one_pos
  have hLval' := hqmpL.ae hLval
  have hAsc := scalePositiveCoefficient_coeFn ref hrefpos A'
  have hLchart := I.chart_eq w r (sidePos m)
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N w (sidePos m)) w r (sidePos m)
    Set.Subset.rfl Q hQ
  have hRchart := I.chart_eq 0 1 one_pos (scalePositiveCoefficient ref hrefpos A')
    0 1 one_pos Set.Subset.rfl Q hQ
  have hmemQ : ∀ᵐ pt ∂ volume.restrict (Homogenization.openCubeSet Q),
      pt ∈ Homogenization.openCubeSet Q :=
    ae_restrict_mem (Homogenization.measurableSet_openCubeSet Q)
  filter_upwards [hLchart, hRchart, hACR.ae_le hRval, hACR.ae_le hLval',
    hACR.ae_le hAsc, hmemQ] with pt hLpt hRpt hRcoeFn hLcoeFn hAcoeFn hptQ
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
  have key : (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om N w (sidePos m)).val
      (cubeDilation w 0 r pt) = (scalePositiveCoefficient ref hrefpos A').val pt := by
    rw [hAcoeFn, hRcoeFn hptC, hLcoeFn hLmem]
    show cutoffCoefficient M H om N (cubeDilation w 0 r pt) / 1 =
        ref * (cutoffCoefficient M H (aux_g9chart_transport_S m w om) K pt / 1)
    rw [div_one, div_one]
    rw [show cubeDilation w 0 r pt = w + r • pt from by
      funext i; simp [cubeDilation_apply]]
    exact hom pt
  exact congrArg Homogenization.scalarMatrix key

def aux_U2_unitChart {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (K : ℕ) :
    Homogenization.Book.Ch02.TriadicCoeffFamily d :=
  I.chart 0 1 one_pos (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1

def aux_U2_lamF {d : ℕ} (sigma : ℝ)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d) : ℝ :=
  Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) sigma
    (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) F

def aux_U2_LamF {d : ℕ} (sigma : ℝ)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d) : ℝ :=
  Homogenization.Book.Ch02.LambdaSq (Homogenization.originCube d 0) sigma
    (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) F

def aux_U2_sigF {d : ℕ} (i j : Fin d)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d) : ℝ :=
  Homogenization.Book.Ch02.sigmaCoarse
    (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
    (F.coeffOn (Homogenization.originCube d 0)) i j

def aux_U2_sigStarInvF {d : ℕ} (i j : Fin d)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d) : ℝ :=
  Homogenization.Book.Ch02.sigmaStarInvCoarse
    (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
    (F.coeffOn (Homogenization.originCube d 0)) i j

def aux_U2_errF {d : ℕ} (s : ℝ)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d) (a0 : ℝ) : ℝ :=
  (SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite (Homogenization.originCube d 0) 0 s
    Homogenization.Book.Ch02.MultiscaleExponent.infinity 2 F a0).toReal

def aux_U2_Scaled {d : ℕ} (c : ℝ)
    (G F : Homogenization.Book.Ch02.TriadicCoeffFamily d) : Prop :=
  ∀ Q : Homogenization.TriadicCube d,
    Homogenization.openCubeSet Q ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      Homogenization.Book.Ch02.CoeffOn.AEScaled c (G.coeffOn Q) (F.coeffOn Q)

theorem aux_U2_lam_eq {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr)) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    I.lam z r hr a z r sigma 2 = aux_U2_lamF sigma (I.chart z r hr a z r) := by
  rw [I.lam_eq z r hr a z r hr subset_rfl sigma hsigma 2 (by norm_num)]
  simp [aux_U2_lamF]

theorem aux_U2_Lam_eq {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr)) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    I.Lam z r hr a z r sigma 2 = aux_U2_LamF sigma (I.chart z r hr a z r) := by
  rw [I.Lam_eq z r hr a z r hr subset_rfl sigma hsigma 2 (by norm_num)]
  simp [aux_U2_LamF]

theorem aux_U2_err_eq {d : ℕ} (I : _root_.SubdiffusiveProcess.Paper.in_J d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr)) (a0 : ℝ) (ha0 : 0 < a0)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    I.err z r hr a z r a0 s 2 = aux_U2_errF s (I.chart z r hr a z r) a0 := by
  rw [I.err_eq z r hr a z r hr subset_rfl s hs 2 (by norm_num) a0 ha0]
  simp [aux_U2_errF]

theorem aux_U2_T4_chart_identity {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (N : ℕ) (m : ℤ) (hm : m ≤ (N : ℤ))
    (w : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ (-m)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      aux_U2_Scaled (aux_g9chart_transport_reference M H N m w omega)
        (aux_U2_unitChart I M H (aux_g9chart_transport_S m w omega) ((N : ℤ) - m).toNat)
        (I.chart w ((3 : ℝ) ^ (-m)) hr
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w ((3 : ℝ) ^ (-m))) := by
  have hA := aux_g9chart_transport_chart_agree I M hH N m hm w (fun n => by positivity)
  filter_upwards [hA] with omega hom Q hQ
  have h1 := hom Q hQ
  have hrefpos := aux_g9chart_transport_reference_pos M H N m w omega
  have h2 := I.chart_eq 0 1 one_pos (scalePositiveCoefficient
    (aux_g9chart_transport_reference M H N m w omega) hrefpos
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (aux_g9chart_transport_S m w omega) ((N : ℤ) - m).toNat
      0 one_pos)) 0 1 one_pos subset_rfl Q hQ
  have h3 := I.chart_eq 0 1 one_pos
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (aux_g9chart_transport_S m w omega) ((N : ℤ) - m).toNat
      0 one_pos) 0 1 one_pos subset_rfl Q hQ
  have h4 := scalePositiveCoefficient_coeFn (aux_g9chart_transport_reference M H N m w omega)
    hrefpos (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (aux_g9chart_transport_S m w omega)
      ((N : ℤ) - m).toNat 0 one_pos)
  have h4' : ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d 0)),
      (scalePositiveCoefficient (aux_g9chart_transport_reference M H N m w omega) hrefpos
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (aux_g9chart_transport_S m w omega)
          ((N : ℤ) - m).toNat 0 one_pos)).val x =
      aux_g9chart_transport_reference M H N m w omega *
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (aux_g9chart_transport_S m w omega)
          ((N : ℤ) - m).toNat 0 one_pos).val x := by
    have hb : (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) =
        Homogenization.openCubeSet (Homogenization.originCube d 0) := by
      have h0 := centeredCube_zero_eq_openCubeSet_originCube (d := d) 0 (by norm_num)
      simpa using h0
    rw [← hb]
    exact h4
  unfold Homogenization.Book.Ch02.CoeffOn.AEScaled
  have h4Q := ae_restrict_of_ae_restrict_of_subset hQ h4'
  filter_upwards [h1, h2, h3, h4Q] with x hx1 hx2 hx3 hx4
  have e0 : (fun i => (0 : SpatialCoordinates d) i + 1 * x i) = x := by
    funext i; simp
  have hx3' :
      ((aux_U2_unitChart I M H (aux_g9chart_transport_S m w omega) ((N : ℤ) - m).toNat).coeffOn
        Q).toCoeffField x = Homogenization.scalarMatrix
        ((_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (aux_g9chart_transport_S m w omega)
          ((N : ℤ) - m).toNat 0 one_pos).val
            (fun i => (0 : SpatialCoordinates d) i + 1 * x i)) := hx3
  rw [hx1, hx2, hx3', e0, hx4]
  simp only [Homogenization.scalarMatrix, smul_smul]

abbrev aux_U2_D {d : ℕ} (n : ℕ) : Finset (Homogenization.TriadicCube d) :=
  Homogenization.descendantsAtScale (Homogenization.originCube d 0)
    ((Homogenization.originCube d 0).scale - (n : ℤ))

theorem aux_U2_D_eq {d : ℕ} (n : ℕ) :
    aux_U2_D (d := d) n = Homogenization.descendantsAtDepth (Homogenization.originCube d 0) n := by
  unfold aux_U2_D Homogenization.descendantsAtScale
  have h1 : (Homogenization.originCube d 0).scale - (n : ℤ) ≤
      (Homogenization.originCube d 0).scale := by
    simp [Homogenization.originCube]
  rw [dite_eq_left h1]
  congr 1
  simp [Homogenization.originCube]

theorem aux_U2_descAtDepth_nonempty {d : ℕ} (Q : Homogenization.TriadicCube d) (n : ℕ) :
    (Homogenization.descendantsAtDepth Q n).Nonempty := by
  induction n with
  | zero => exact ⟨Q, by simp [Homogenization.descendantsAtDepth]⟩
  | succ n ih =>
    simp only [Homogenization.descendantsAtDepth]
    refine ih.biUnion (fun R _ => ?_)
    unfold Homogenization.childCubes
    exact Finset.univ_nonempty.image _

theorem aux_U2_D_nonempty {d : ℕ} (n : ℕ) :
    (aux_U2_D (d := d) n).Nonempty := by
  rw [aux_U2_D_eq]
  exact aux_U2_descAtDepth_nonempty _ n

theorem aux_U2_lamF_inv_eq {d : ℕ} (sigma : ℝ)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d) :
    (aux_U2_lamF sigma F)⁻¹ =
      ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight sigma 2 n *
        (aux_U2_D (d := d) n).sup' (aux_U2_D_nonempty n)
          (fun R => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R F) := by
  unfold aux_U2_lamF Homogenization.Book.Ch02.lambdaSq Homogenization.Book.Ch02.lambdaSqFinite
  have h22 : (2 : ℝ) / 2 = 1 := by norm_num
  simp only [h22, Real.rpow_eq_pow, Real.rpow_one, Real.rpow_neg_one, inv_inv]
  refine tsum_congr (fun n => ?_)
  congr 1
  unfold Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
    Homogenization.Book.Ch02.finsetSupReal
  rw [Finset.sup'_eq_csSup_image]

theorem aux_U2_LamF_eq {d : ℕ} (sigma : ℝ)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d) :
    aux_U2_LamF sigma F =
      ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight sigma 2 n *
        (aux_U2_D (d := d) n).sup' (aux_U2_D_nonempty n)
          (fun R => Homogenization.Book.Ch02.coarseBMatrixNorm R F) := by
  unfold aux_U2_LamF Homogenization.Book.Ch02.LambdaSq Homogenization.Book.Ch02.LambdaSqFinite
  have h22 : (2 : ℝ) / 2 = 1 := by norm_num
  simp only [h22, Real.rpow_eq_pow, Real.rpow_one]
  refine tsum_congr (fun n => ?_)
  congr 1
  unfold Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
    Homogenization.Book.Ch02.finsetSupReal
  rw [Finset.sup'_eq_csSup_image]

theorem aux_U2_responseJ_neumann_scaled {d : ℕ}
    {U : Homogenization.Book.Ch02.Domain d} (c : ℝ) (hc : 0 < c)
    (a b : Homogenization.Book.Ch02.CoeffOn U)
    (h : Homogenization.Book.Ch02.CoeffOn.AEScaled c a b)
    (q : Homogenization.Vec d) :
    Homogenization.Book.Ch02.responseJ U b 0 q =
      c⁻¹ * Homogenization.Book.Ch02.responseJ U a 0 q := by
  rw [(Homogenization.Book.Ch02.responseSubadditivityAndScalingTheory U a).responseJ_homogeneous
    hc h 0 q, smul_zero]
  have hs := Homogenization.Book.Ch02.responseJ_smul (U := U) (a := a) ((Real.sqrt c)⁻¹) 0 q
  rw [smul_zero] at hs
  rw [hs, inv_pow, Real.sq_sqrt hc.le]

theorem aux_U2_sigmaStarInvCoarse_scaled {d : ℕ}
    {U : Homogenization.Book.Ch02.Domain d} (c : ℝ) (hc : 0 < c)
    (a b : Homogenization.Book.Ch02.CoeffOn U)
    (h : Homogenization.Book.Ch02.CoeffOn.AEScaled c a b) :
    Homogenization.Book.Ch02.sigmaStarInvCoarse U b =
      c⁻¹ • Homogenization.Book.Ch02.sigmaStarInvCoarse U a := by
  ext i j
  simp only [Homogenization.Book.Ch02.sigmaStarInvCoarse,
    Homogenization.Book.Ch02.sigmaStarInvEntry, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · rw [aux_U2_responseJ_neumann_scaled c hc a b h]; ring
  · rw [aux_U2_responseJ_neumann_scaled c hc a b h,
      aux_U2_responseJ_neumann_scaled c hc a b h,
      aux_U2_responseJ_neumann_scaled c hc a b h]; ring

theorem aux_U2_bCoarse_scaled {d : ℕ} {U : Homogenization.Book.Ch02.Domain d}
    (c : ℝ) (hc : 0 < c) (a b : Homogenization.Book.Ch02.CoeffOn U)
    (h : Homogenization.Book.Ch02.CoeffOn.AEScaled c a b) :
    Homogenization.Book.Ch02.bCoarse U b = c • Homogenization.Book.Ch02.bCoarse U a := by
  have T := Homogenization.Book.Ch02.responseSubadditivityAndScalingTheory U a
  unfold Homogenization.Book.Ch02.bCoarse Homogenization.Book.Ch02.CoarseMatrices.b
  simp only [Homogenization.Book.Ch02.coarseMatrices_sigma,
    Homogenization.Book.Ch02.coarseMatrices_sigmaStarInv,
    Homogenization.Book.Ch02.coarseMatrices_kappa]
  rw [T.sigma_homogeneous hc h, T.kappa_homogeneous hc h,
    aux_U2_sigmaStarInvCoarse_scaled c hc a b h]
  have hc0 : c ≠ 0 := hc.ne'
  simp only [Homogenization.matTranspose, Matrix.transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, smul_smul]
  congr 1
  rw [show c * (c⁻¹ * c) = c by field_simp]

theorem aux_U2_matrixNorm_smul {d : ℕ} (c : ℝ) (A : Homogenization.Mat d) :
    Homogenization.Book.Ch02.matrixNorm (c • A) = |c| *
      Homogenization.Book.Ch02.matrixNorm A := by
  unfold Homogenization.Book.Ch02.matrixNorm
  rw [map_smul, norm_smul, Real.norm_eq_abs]

theorem aux_U2_desc_sub {d : ℕ} (n : ℕ) (R : Homogenization.TriadicCube d)
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ))) :
    Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) := by
  refine Homogenization.openCubeSet_subset_of_mem_descendantsAtScale ?_ hR
  simp [Homogenization.originCube]

theorem aux_U2_probe_scaled {d : ℕ} (c : ℝ) (hc : 0 < c)
    (G F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (h : aux_U2_Scaled c G F) (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F c =
      SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R G 1 := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax
  congr 1
  funext e
  congr 1
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe SubdiffusiveProcess.CoarseGrainingVocab.J
  rw [(Homogenization.Book.Ch02.responseSubadditivityAndScalingTheory _
    (G.coeffOn R)).responseJ_homogeneous hc (h R hR)]
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  rw [smul_smul, smul_smul, mul_inv_cancel₀ hs.ne', inv_mul_cancel₀ hs.ne',
    Real.sqrt_one, inv_one]

theorem aux_U2_lamF_scaled {d : ℕ} (sigma c : ℝ) (hc : 0 < c)
    (G F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (h : aux_U2_Scaled c G F) : aux_U2_lamF sigma F = c * aux_U2_lamF sigma G := by
  have hcell : ∀ n (R : Homogenization.TriadicCube d), R ∈ aux_U2_D (d := d) n →
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R F =
        c⁻¹ * Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R G := by
    intro n R hR
    unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
    rw [aux_U2_sigmaStarInvCoarse_scaled c hc _ _ (h R (aux_U2_desc_sub n R hR)),
      aux_U2_matrixNorm_smul, abs_of_pos (inv_pos.mpr hc)]
  have hsup : ∀ n, (aux_U2_D (d := d) n).sup' (aux_U2_D_nonempty n)
      (fun R => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R F) =
      c⁻¹ * (aux_U2_D (d := d) n).sup' (aux_U2_D_nonempty n)
        (fun R => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R G) := by
    intro n
    rw [Finset.sup'_congr (aux_U2_D_nonempty n) rfl (fun R hR => hcell n R hR)]
    exact (Finset.mul₀_sup' (inv_pos.mpr hc).le _ _ _).symm
  have hinv : (aux_U2_lamF sigma F)⁻¹ = c⁻¹ * (aux_U2_lamF sigma G)⁻¹ := by
    rw [aux_U2_lamF_inv_eq, aux_U2_lamF_inv_eq, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [hsup n]; ring
  calc aux_U2_lamF sigma F = ((aux_U2_lamF sigma F)⁻¹)⁻¹ := (inv_inv _).symm
    _ = (c⁻¹ * (aux_U2_lamF sigma G)⁻¹)⁻¹ := by rw [hinv]
    _ = c * aux_U2_lamF sigma G := by rw [mul_inv, inv_inv, inv_inv]

theorem aux_U2_LamF_scaled {d : ℕ} (sigma c : ℝ) (hc : 0 < c)
    (G F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (h : aux_U2_Scaled c G F) : aux_U2_LamF sigma F = c * aux_U2_LamF sigma G := by
  have hcell : ∀ n (R : Homogenization.TriadicCube d), R ∈ aux_U2_D (d := d) n →
      Homogenization.Book.Ch02.coarseBMatrixNorm R F =
        c * Homogenization.Book.Ch02.coarseBMatrixNorm R G := by
    intro n R hR
    unfold Homogenization.Book.Ch02.coarseBMatrixNorm
    rw [aux_U2_bCoarse_scaled c hc _ _ (h R (aux_U2_desc_sub n R hR)),
      aux_U2_matrixNorm_smul, abs_of_pos hc]
  have hsup : ∀ n, (aux_U2_D (d := d) n).sup' (aux_U2_D_nonempty n)
      (fun R => Homogenization.Book.Ch02.coarseBMatrixNorm R F) =
      c * (aux_U2_D (d := d) n).sup' (aux_U2_D_nonempty n)
        (fun R => Homogenization.Book.Ch02.coarseBMatrixNorm R G) := by
    intro n
    rw [Finset.sup'_congr (aux_U2_D_nonempty n) rfl (fun R hR => hcell n R hR)]
    exact (Finset.mul₀_sup' hc.le _ _ _).symm
  rw [aux_U2_LamF_eq, aux_U2_LamF_eq, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [hsup n]; ring

theorem aux_U2_sigF_scaled {d : ℕ} (c : ℝ) (hc : 0 < c)
    (G F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (h : aux_U2_Scaled c G F) (i j : Fin d) :
    aux_U2_sigF i j F = c * aux_U2_sigF i j G := by
  have hQ := h (Homogenization.originCube d 0) subset_rfl
  have hh := (Homogenization.Book.Ch02.responseSubadditivityAndScalingTheory
    (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
    (G.coeffOn (Homogenization.originCube d 0))).sigma_homogeneous hc hQ
  unfold aux_U2_sigF
  rw [hh]
  rfl

theorem aux_U2_sigStarInvF_scaled {d : ℕ} (c : ℝ) (hc : 0 < c)
    (G F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (h : aux_U2_Scaled c G F) (i j : Fin d) :
    aux_U2_sigStarInvF i j F = c⁻¹ * aux_U2_sigStarInvF i j G := by
  unfold aux_U2_sigStarInvF
  rw [aux_U2_sigmaStarInvCoarse_scaled c hc _ _ (h (Homogenization.originCube d 0) subset_rfl)]
  rfl

theorem aux_U2_errF_scaled {d : ℕ} (s c : ℝ) (hc : 0 < c)
    (G F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (h : aux_U2_Scaled c G F) : aux_U2_errF s F c = aux_U2_errF s G 1 := by
  have hsup : ∀ l : ℕ, (⨆ R : {R : Homogenization.TriadicCube d // R ∈
      Homogenization.descendantsAtScale (Homogenization.originCube d 0) (0 - (l : ℤ))},
        SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax (R : Homogenization.TriadicCube d) F c) =
      ⨆ R : {R : Homogenization.TriadicCube d // R ∈
        Homogenization.descendantsAtScale (Homogenization.originCube d 0) (0 - (l : ℤ))},
        SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax (R : Homogenization.TriadicCube d) G 1 := by
    intro l
    congr 1
    funext R
    have hR : Homogenization.openCubeSet (R : Homogenization.TriadicCube d) ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0) := by
      refine Homogenization.openCubeSet_subset_of_mem_descendantsAtScale ?_ R.2
      simp [Homogenization.originCube]
    exact aux_U2_probe_scaled c hc G F h R hR
  unfold aux_U2_errF SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
    SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale
    SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale
  dsimp only
  simp_rw [hsup]


/--  (`mfd:lem-prefix-limit`): environment shift and chart transport of the cutoff
coefficient -- shifting the chart center by `w` and rescaling by `3^{-m}` transports the cutoff
coefficient at level `N` to the cutoff coefficient of a shifted environment at level `N - m`, up to
an explicit multiplicative reference-scale factor `aux_g9chart_transport_reference`. -/
theorem lem_prefix_limit_g9_chart_transport {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℤ) (w : SpatialCoordinates d)
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)} (hH : InfraredCharacterization M H)
    (N : ℕ) (hm : m ≤ (N : ℤ)) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ y : SpatialCoordinates d,
      cutoffCoefficient M H om N (w + (3 : ℝ) ^ (-m) • y) =
        aux_g9chart_transport_reference M H N m w om *
          cutoffCoefficient M H (aux_g9chart_transport_S m w om) (((N : ℤ) - m).toNat) y :=
  aux_g9chart_transport_coefficient M m w hH N hm

end SubdiffusiveProcess.Paper
