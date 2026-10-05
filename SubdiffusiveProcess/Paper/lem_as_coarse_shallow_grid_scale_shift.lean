module

public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import Mathlib.Tactic

@[expose] public section

/-!
# The shifted field `Θ_{k,w}` of the retained grid (`mfd:lem-as-coarse`)

For a grid cell `q = w + 3^{-k} Q₀`, the paper writes
`A_N(w + 3^{-k} y) = (κ_{N-k}/κ_N) e^{G_k(w+3^{-k}y)} A^{0,Θ_{k,w}ω}_{N-k}(y)`,
with `G_k = H + ∑_{j<k} g_{-j}`, and applies the unit-cube response bank to
`A^{0,Θ_{k,w}ω}_{N-k}`.  This file supplies the two facts that make that transfer
literal: `Θ_{k,w}` preserves the chaos sample law (so every unit-cube tail estimate holds
with the same constants at every cell), and the coefficient factorization itself.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The cell chart `y ↦ w + 3^{-k} y`. -/
def aux_lem_as_coarse_shallow_grid_cellMap {d : ℕ} (k : ℕ) (w : SpatialCoordinates d) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨cubeDilation w 0 ((3 : ℝ) ^ (-(k : ℤ))), continuous_cubeDilation w 0 _⟩

/-- `Θ_{k,w}`: drop the first `k` generations and zoom into the cell of centre `w` and
side `3^{-k}`.  Layer `j` of the shifted field is layer `j - k` read in the cell chart. -/
def aux_lem_as_coarse_shallow_grid_scaleShift {d : ℕ} (k : ℕ) (w : SpatialCoordinates d)
    (omega : BilateralField d) : BilateralField d :=
  fun j => (omega (j - k)).comp (aux_lem_as_coarse_shallow_grid_cellMap k w)

theorem aux_lem_as_coarse_shallow_grid_scaleShift_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (k : ℕ) (w : SpatialCoordinates d) :
    Measurable (aux_lem_as_coarse_shallow_grid_scaleShift (d := d) k w) := by
  have hc : Measurable fun f : C(SpatialCoordinates d, ℝ) =>
      f.comp (aux_lem_as_coarse_shallow_grid_cellMap k w) := by fun_prop
  exact Measurable.of_eval fun j => hc.comp (measurable_pi_apply (j - k))

/-- **Scale-shift invariance.**  By root stationarity (`a.g1`) and independence of the
layers, `Θ_{k,w}` preserves the chaos sample law, for every depth `k` and centre `w`. -/
theorem lem_as_coarse_shallow_grid_scale_shift {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (w : SpatialCoordinates d) :
    MeasurePreserving (aux_lem_as_coarse_shallow_grid_scaleShift k w)
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure := by
  set D := aux_lem_as_coarse_shallow_grid_cellMap (d := d) k w with hD
  set ν := chaosRootFieldLaw model with hν
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  have hroot : ∀ z : SpatialCoordinates d, MeasurePreserving
      (fun f : C(SpatialCoordinates d, ℝ) =>
        f.comp (⟨fun x => x + z, continuous_id.add continuous_const⟩ :
          C(SpatialCoordinates d, SpatialCoordinates d)))
      ν.toMeasure ν.toMeasure := by
    intro z
    simpa [hν, chaosRootFieldLaw] using! (gmc_zero_field_law_stationary model z)
  have hcompD : Measurable fun f : C(SpatialCoordinates d, ℝ) => f.comp D := by fun_prop
  -- one layer: reading layer `j - k` in the cell chart gives layer `j`
  have hlayer : ∀ j : ℤ,
      Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp D) (laws (j - k)) =
        laws j := by
    intro j
    let z : SpatialCoordinates d := (3 : ℝ) ^ (-(j - (k : ℤ))) • w
    let translateZ : C(SpatialCoordinates d, SpatialCoordinates d) :=
      ⟨fun x => x + z, continuous_id.add continuous_const⟩
    have hpow : (3 : ℝ) ^ (-(j - (k : ℤ))) * (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ (-j) := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      ring
    have hcomm :
        (fun f : C(SpatialCoordinates d, ℝ) => f.comp D) ∘ (layerScaling d (j - k)) =
          (layerScaling d j) ∘
            (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ) := by
      funext f
      ext x
      dsimp [ContinuousMap.compRightContinuousMap, layerScaling, ContinuousMap.comp,
        hD, aux_lem_as_coarse_shallow_grid_cellMap, translateZ, z]
      congr 1
      ext i
      rw [hD]
      simp only [aux_lem_as_coarse_shallow_grid_cellMap, ContinuousMap.coe_mk,
        cubeDilation_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, sub_zero,
        Pi.zero_apply]
      rw [mul_add, ← mul_assoc, hpow]
      ring
    change Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp D)
        (Measure.map (layerScaling d (j - k)) ν.toMeasure) =
      Measure.map (layerScaling d j) ν.toMeasure
    calc
      Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp D)
          (Measure.map (layerScaling d (j - k)) ν.toMeasure) =
          Measure.map ((fun f : C(SpatialCoordinates d, ℝ) => f.comp D) ∘
            layerScaling d (j - k)) ν.toMeasure :=
        Measure.map_map hcompD (layerScaling d (j - k)).continuous.measurable
      _ = Measure.map ((layerScaling d j) ∘
            (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ)) ν.toMeasure := by
        rw [hcomm]
      _ = Measure.map (layerScaling d j)
          (Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ)
            ν.toMeasure) :=
        (Measure.map_map (layerScaling d j).continuous.measurable (by fun_prop)).symm
      _ = Measure.map (layerScaling d j) ν.toMeasure := by
        rw [(hroot z).map_eq]
  -- the layer relabelling `j ↦ j - k`
  have hre : Measure.map (fun (ω : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => ω (j - k))
      (Measure.infinitePi laws) = Measure.infinitePi (fun j => laws (j - k)) := by
    have h := Measure.infinitePi_map_piCongrLeft (fun j : ℤ => laws (j - k))
      (Equiv.addRight (k : ℤ))
    have e1 : (fun a : ℤ => (fun j : ℤ => laws (j - k)) (Equiv.addRight (k : ℤ) a)) =
        laws := by
      funext a
      simp
    have e2 : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ => C(SpatialCoordinates d, ℝ))
        (Equiv.addRight (k : ℤ))) =
        fun (ω : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => ω (j - k) := by
      funext ω j
      have h := Equiv.piCongrLeft_apply (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) (Equiv.addRight (k : ℤ)) ω j
      have hrec {a b : ℤ} (h : a = b) (v : C(SpatialCoordinates d, ℝ)) :
          (Eq.rec (motive := fun _ _ => C(SpatialCoordinates d, ℝ)) v h) = v := by cases h; rfl
      simpa only [MeasurableEquiv.coe_piCongrLeft, Equiv.addRight_symm, sub_eq_add_neg] using! h.trans (hrec _ _)
    rw [e1, e2] at h
    exact h
  have hco := Measure.infinitePi_map_pi (μ := fun j => laws (j - k))
    (f := fun _ : ℤ => fun f : C(SpatialCoordinates d, ℝ) => f.comp D) (fun _ => hcompD)
  refine ⟨aux_lem_as_coarse_shallow_grid_scaleShift_measurable k w, ?_⟩
  have hsplit : aux_lem_as_coarse_shallow_grid_scaleShift (d := d) k w =
      (fun (x : ℤ → C(SpatialCoordinates d, ℝ)) (i : ℤ) => (x i).comp D) ∘
        (fun (ω : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => ω (j - k)) := rfl
  change Measure.map (aux_lem_as_coarse_shallow_grid_scaleShift k w)
      (Measure.infinitePi laws) = Measure.infinitePi laws
  have hg : Measurable (fun (x : ℤ → C(SpatialCoordinates d, ℝ)) (i : ℤ) => (x i).comp D) :=
    Measurable.of_eval fun i => hcompD.comp (measurable_pi_apply i)
  have hf : Measurable (fun (ω : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => ω (j - k)) :=
    Measurable.of_eval fun j => measurable_pi_apply (j - k)
  have hco' : Measure.map (fun (x : ℤ → C(SpatialCoordinates d, ℝ)) (i : ℤ) => (x i).comp D)
      (Measure.infinitePi fun j => laws (j - k)) =
      Measure.infinitePi fun i => Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp D)
        (laws (i - k)) := hco
  rw [hsplit, ← Measure.map_map hg hf, hre, hco']
  congr 1
  funext j
  exact hlayer j

/-- Every event read through `Θ_{k,w}` has the probability of the unshifted event. -/
theorem aux_lem_as_coarse_shallow_grid_scaleShift_prob {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (w : SpatialCoordinates d)
    {S : Set (BilateralField d)} (hS : MeasurableSet S) :
    (chaosSampleLaw model).toMeasure
        (aux_lem_as_coarse_shallow_grid_scaleShift k w ⁻¹' S) =
      (chaosSampleLaw model).toMeasure S :=
  (lem_as_coarse_shallow_grid_scale_shift model k w).measure_preimage
    hS.nullMeasurableSet

/-- The same transfer as an upper bound for an arbitrary (not necessarily measurable) event,
which is the form in which the response-bank tails are stated. -/
theorem aux_lem_as_coarse_shallow_grid_scaleShift_prob_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (w : SpatialCoordinates d)
    (S : Set (BilateralField d)) :
    (chaosSampleLaw model).toMeasure
        (aux_lem_as_coarse_shallow_grid_scaleShift k w ⁻¹' S) ≤
      (chaosSampleLaw model).toMeasure S := by
  set P := (chaosSampleLaw model).toMeasure
  calc P (aux_lem_as_coarse_shallow_grid_scaleShift k w ⁻¹' S)
      ≤ P (aux_lem_as_coarse_shallow_grid_scaleShift k w ⁻¹' toMeasurable P S) :=
        measure_mono (Set.preimage_mono (subset_toMeasurable P S))
    _ = P (toMeasurable P S) :=
        aux_lem_as_coarse_shallow_grid_scaleShift_prob model k w
          (measurableSet_toMeasurable P S)
    _ = P S := measure_toMeasurable S

/-- **Cell factorization** (`mfd:lem-as-coarse`).  On the cell `w + 3^{-k} Q₀` the cutoff
coefficient is the deterministic ratio `â_{N-k}/â_N`, times the coarse factor
`exp(H + ∑_{j<k} g_{-j} - kτ²)`, times the infrared-removed coefficient at cutoff `N - k`
of the shifted field `Θ_{k,w} ω`. -/
theorem aux_lem_as_coarse_shallow_grid_cutoff_factor {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N k : ℕ) (hk : k ≤ N) (w y : SpatialCoordinates d) :
    cutoffCoefficient M H omega N (aux_lem_as_coarse_shallow_grid_cellMap k w y) =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) *
        Real.exp (H omega (aux_lem_as_coarse_shallow_grid_cellMap k w y) +
            ∑ j ∈ Finset.range k,
              omega (-(Int.ofNat j)) (aux_lem_as_coarse_shallow_grid_cellMap k w y) -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          (aux_lem_as_coarse_shallow_grid_scaleShift k w omega) (N - k) y := by
  set x := aux_lem_as_coarse_shallow_grid_cellMap k w y with hx
  set t := _root_.SubdiffusiveProcess.Model.tauSq M.P with ht
  have hsplit : ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j)) x =
      ∑ j ∈ Finset.range k, omega (-(Int.ofNat j)) x +
        ∑ j ∈ Finset.range (N - k + 1), omega (-(Int.ofNat (k + j))) x := by
    have hNk : N + 1 = k + (N - k + 1) := by omega
    rw [hNk, Finset.sum_range_add]
  have hshift : ∀ j : ℕ,
      (aux_lem_as_coarse_shallow_grid_scaleShift k w omega) (-(Int.ofNat j)) y =
        omega (-(Int.ofNat (k + j))) x := by
    intro j
    simp only [aux_lem_as_coarse_shallow_grid_scaleShift, ContinuousMap.comp_apply, hx]
    congr 2
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    ring
  have hcast : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := by
    rw [Nat.cast_sub hk]
  have hpos : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) :=
    SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k)
  have hposN : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  simp only [cutoffCoefficient, cutoffPotential, ContinuousMap.zero_apply, zero_add, hshift]
  rw [hsplit, hcast, ← ht]
  have hexp : Real.exp (H omega x + (∑ j ∈ Finset.range k, omega (-(Int.ofNat j)) x +
        ∑ j ∈ Finset.range (N - k + 1), omega (-(Int.ofNat (k + j))) x) -
        ((N : ℝ) + 1) * t) =
      Real.exp (H omega x + ∑ j ∈ Finset.range k, omega (-(Int.ofNat j)) x - (k : ℝ) * t) *
        Real.exp (∑ j ∈ Finset.range (N - k + 1), omega (-(Int.ofNat (k + j))) x -
          ((N : ℝ) - k + 1) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  field_simp

end SubdiffusiveProcess.Paper




