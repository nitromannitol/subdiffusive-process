module

public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.CellSupMoment
public import Mathlib.Probability.ProductMeasure
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.lem_as_regularity_affine_transport
public import SubdiffusiveProcess.Paper.dilation_coefficient_transport
public import SubdiffusiveProcess.Paper.dilation_quasi_measure_preserving
public import SubdiffusiveProcess.Paper.weak_gradient_chain_rule

@[expose] public section

/-!
# `prop_growth` on every root of side `r > 1`

Derived from `SubdiffusiveProcess.Paper.prop_growth` (roots of side `≤ 1`) by the paper's common scale coupling
(`mfd:prop-growth`, eq. `mfd-A-physical`) and the rescaling step of the proof of
Proposition `mfd:prop-growth` (`mfd:prop-growth`, the Step-1 random constant `c_{N,L'}`).
For `r > 1` pick `j ≥ 1` with `r ≤ 3^j` and put `s = r / 3^j ≤ 1`.  The dilation
`y ↦ 3^j y` maps `centeredCube (3^{-j} z) s` onto the root, the triadic scale shift
`S_j ω = (m ↦ ω(m+j)(3^j ·))` preserves `chaosSampleLaw M`, and almost surely
`A_N^ω(3^j y) = c_N(ω) · A_{N+j}^{S_j ω}(y)` with `c_N, c_N⁻¹ ≤ exp(j|τ²| + |X_j(ω)|)`,
which has all moments by (g2).  `SubdiffusiveProcess.Paper.prop_growth` for the doubled moment list on the cube
of side `s` then transfers back through the unit cube.  The disorder threshold is
`prop_growth`'s threshold for `(t, α, 2·ps)`, fixed before the model and the root; only the
majorant and its moment constants depend on the root.

The general route subsumes the special case of triadic roots `3^j`, including
scale transfer, Hölder transport, coefficient pullback and unit-centre normalization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section LRGShift

open MeasureTheory Filter Topology
open SubdiffusiveProcess


variable {d : ℕ}

/-- The dilation `x ↦ 3^j x`. -/
def aux_prop_growth_large_root_dil (d j : ℕ) : C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨fun x => ((3 : ℝ) ^ j) • x, (by fun_prop)⟩

@[simp] theorem aux_prop_growth_large_root_dil_apply (j : ℕ) (x : SpatialCoordinates d) :
    aux_prop_growth_large_root_dil d j x = ((3 : ℝ) ^ j) • x := rfl

/-- The triadic scale shift: `(S_j ω)(m)(y) = ω(m + j)(3^j y)`. -/
def aux_prop_growth_large_root_scaleShift (j : ℕ) (om : BilateralField d) : BilateralField d :=
  fun m => (om (m + (j : ℤ))).comp (aux_prop_growth_large_root_dil d j)

@[simp] theorem aux_prop_growth_large_root_scaleShift_apply (j : ℕ) (om : BilateralField d) (m : ℤ)
    (y : SpatialCoordinates d) :
    aux_prop_growth_large_root_scaleShift j om m y = om (m + (j : ℤ)) (((3 : ℝ) ^ j) • y) := rfl

/-- Precomposition with the dilation, as a continuous self-map of the field space. -/
def aux_prop_growth_large_root_dilComp (d j : ℕ) : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
  ContinuousMap.compRightContinuousMap ℝ (aux_prop_growth_large_root_dil d j)

theorem aux_prop_growth_large_root_dilComp_apply (j : ℕ) (f : C(SpatialCoordinates d, ℝ)) :
    aux_prop_growth_large_root_dilComp d j f = f.comp (aux_prop_growth_large_root_dil d j) := rfl

section Measure

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_prop_growth_large_root_measurable_dilComp (j : ℕ) : Measurable (aux_prop_growth_large_root_dilComp d j) :=
  (aux_prop_growth_large_root_dilComp d j).continuous.measurable

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- The dilation composes the layer scalings: `3^{-(m+j)} · 3^j = 3^{-m}`. -/
theorem aux_prop_growth_large_root_dilComp_comp_layerScaling {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (j : ℕ) (m : ℤ) :
    (aux_prop_growth_large_root_dilComp d j) ∘ (layerScaling d (m + (j : ℤ))) = layerScaling d m := by
  funext f
  ext x
  simp only [Function.comp_apply, aux_prop_growth_large_root_dilComp_apply, layerScaling,
    ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, aux_prop_growth_large_root_dil_apply]
  congr 1
  rw [smul_smul]
  congr 1
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  ring

theorem aux_prop_growth_large_root_map_scaledLayerLaw_dilComp (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ))
    (j : ℕ) (m : ℤ) :
    ((scaledLayerLaw d ν (m + (j : ℤ)) : Measure C(SpatialCoordinates d, ℝ))).map
        (aux_prop_growth_large_root_dilComp d j) = (scaledLayerLaw d ν m : Measure C(SpatialCoordinates d, ℝ)) := by
  simp only [scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (aux_prop_growth_large_root_measurable_dilComp j) (layerScaling d _).continuous.measurable,
    aux_prop_growth_large_root_dilComp_comp_layerScaling]

theorem aux_prop_growth_large_root_chaosSampleLaw_eq (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) : Measure (BilateralField d)) =
      Measure.infinitePi (fun n : ℤ =>
        (scaledLayerLaw d (chaosRootFieldLaw M) n : Measure C(SpatialCoordinates d, ℝ))) := rfl

/-- Reindexing by `m ↦ m + j`. -/
theorem aux_prop_growth_large_root_measurePreserving_reindex_add {X : Type*} [MeasurableSpace X]
    (laws : ℤ → Measure X) [∀ n, IsProbabilityMeasure (laws n)] (j : ℤ) :
    MeasurePreserving (fun om : ℤ → X => fun m : ℤ => om (m + j))
      (Measure.infinitePi laws) (Measure.infinitePi (fun m : ℤ => laws (m + j))) := by
  let e : ℤ ≃ ℤ := Equiv.subRight j
  have he : (MeasurableEquiv.piCongrLeft (fun _ : ℤ => X) e : (ℤ → X) → (ℤ → X)) =
      (fun om : ℤ → X => fun m : ℤ => om (m + j)) := by
    funext om m
    simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, e, cast_eq]
    rfl
  have hmap := Measure.infinitePi_map_piCongrLeft
    (μ := fun m : ℤ => laws (m + j)) e
  refine ⟨?_, ?_⟩
  · rw [← he]
    exact (MeasurableEquiv.piCongrLeft (fun _ : ℤ => X) e).measurable
  · rw [← he]
    simpa only [e, Equiv.subRight_apply, sub_add_cancel] using hmap

/-- **The scale shift preserves the chaos sample law.** -/
theorem aux_prop_growth_large_root_measurePreserving_scaleShift (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) :
    MeasurePreserving (aux_prop_growth_large_root_scaleShift (d := d) j)
      ((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) : Measure (BilateralField d))
      ((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) :
        Measure (BilateralField d)) := by
  rw [aux_prop_growth_large_root_chaosSampleLaw_eq]
  set laws : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun n =>
    (scaledLayerLaw d (chaosRootFieldLaw M) n : Measure C(SpatialCoordinates d, ℝ)) with hlaws
  have hre := aux_prop_growth_large_root_measurePreserving_reindex_add laws (j : ℤ)
  have hpi : MeasurePreserving (fun (x : ℤ → C(SpatialCoordinates d, ℝ)) (i : ℤ) =>
      aux_prop_growth_large_root_dilComp d j (x i))
      (Measure.infinitePi (fun m : ℤ => laws (m + (j : ℤ))))
      (Measure.infinitePi laws) := by
    refine ⟨measurable_pi_iff.mpr fun i =>
      (aux_prop_growth_large_root_measurable_dilComp j).comp (measurable_pi_apply i), ?_⟩
    rw [Measure.infinitePi_map_pi _ (fun _ => aux_prop_growth_large_root_measurable_dilComp j)]
    congr 1
    funext m
    exact aux_prop_growth_large_root_map_scaledLayerLaw_dilComp (chaosRootFieldLaw M) j m
  have hcomp := hpi.comp hre
  convert hcomp using 1
  ext om i y
  rfl

end Measure

/-! ## Infrared partial sums -/

/-- The first `j` anchored infrared layers, read at `x`. -/
theorem aux_prop_growth_large_root_infraredPartialSum_apply (om : BilateralField d) (L : ℕ) (x : SpatialCoordinates d) :
    infraredPartialSum om L x =
      ∑ n ∈ Finset.range L, (om (Int.ofNat (n + 1)) x - om (Int.ofNat (n + 1)) 0) := by
  simp [infraredPartialSum, ContinuousMap.sum_apply]

/-- The partial infrared sums split exactly under the scale shift. -/
theorem aux_prop_growth_large_root_infraredPartialSum_scaleShift (j L : ℕ) (om : BilateralField d)
    (y : SpatialCoordinates d) :
    infraredPartialSum om (j + L) (((3 : ℝ) ^ j) • y) =
      infraredPartialSum om j (((3 : ℝ) ^ j) • y) + infraredPartialSum (aux_prop_growth_large_root_scaleShift j om) L y := by
  rw [aux_prop_growth_large_root_infraredPartialSum_apply, aux_prop_growth_large_root_infraredPartialSum_apply, aux_prop_growth_large_root_infraredPartialSum_apply,
    Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [aux_prop_growth_large_root_scaleShift_apply, smul_zero]
  have h : (Int.ofNat (j + n + 1)) = Int.ofNat (n + 1) + (j : ℤ) := by
    simp only [Int.ofNat_eq_natCast]; push_cast; ring
  rw [h]

/-- **Infrared compatibility of the scale shift.**  Almost surely,
`H ω (3^j y) = IR_j(ω)(3^j y) + H (S_j ω) y` for every `y`. -/
theorem aux_prop_growth_large_root_ae_infrared_scaleShift [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) (j : ℕ) :
    ∀ᵐ om ∂((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) :
        Measure (BilateralField d)),
      ∀ y : SpatialCoordinates d,
        H om (((3 : ℝ) ^ j) • y) =
          infraredPartialSum om j (((3 : ℝ) ^ j) • y) + H (aux_prop_growth_large_root_scaleShift j om) y := by
  have h1 := hH.2
  have h2 := (aux_prop_growth_large_root_measurePreserving_scaleShift M j).quasiMeasurePreserving.ae hH.2
  filter_upwards [h1, h2] with om hom hom' y
  have hA : Tendsto (fun L : ℕ => infraredPartialSum om (j + L) (((3 : ℝ) ^ j) • y)) atTop
      (𝓝 (H om (((3 : ℝ) ^ j) • y))) := by
    have hev : Tendsto (fun f : C(SpatialCoordinates d, ℝ) => f (((3 : ℝ) ^ j) • y))
        (𝓝 (H om)) (𝓝 (H om (((3 : ℝ) ^ j) • y))) :=
      (continuous_eval_const _).tendsto _
    have hshift : Tendsto (fun L : ℕ => j + L) atTop atTop :=
      tendsto_atTop_mono (fun L => Nat.le_add_left L j) tendsto_id
    exact hev.comp (hom.comp hshift)
  have hB : Tendsto (fun L : ℕ => infraredPartialSum om (j + L) (((3 : ℝ) ^ j) • y)) atTop
      (𝓝 (infraredPartialSum om j (((3 : ℝ) ^ j) • y) + H (aux_prop_growth_large_root_scaleShift j om) y)) := by
    have hev : Tendsto (fun f : C(SpatialCoordinates d, ℝ) => f y)
        (𝓝 (H (aux_prop_growth_large_root_scaleShift j om))) (𝓝 (H (aux_prop_growth_large_root_scaleShift j om) y)) :=
      (continuous_eval_const _).tendsto _
    have := (hev.comp hom').const_add (infraredPartialSum om j (((3 : ℝ) ^ j) • y))
    refine this.congr fun L => ?_
    simp only [Function.comp_apply]
    rw [aux_prop_growth_large_root_infraredPartialSum_scaleShift]
  exact tendsto_nhds_unique hA hB

end LRGShift

section LRGCoef

open MeasureTheory Filter Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity


variable {d : ℕ}

/-- The anchored infrared value `X_j(ω) = Σ_{n<j} ω(n+1)(0)`. -/
def aux_prop_growth_large_root_irAnchor (j : ℕ) (om : BilateralField d) : ℝ :=
  ∑ n ∈ Finset.range j, om (Int.ofNat (n + 1)) 0

/-- The infrared event at one sample. -/
def aux_prop_growth_large_root_IRShiftAt (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (j : ℕ)
    (om : BilateralField d) : Prop :=
  ∀ y : SpatialCoordinates d,
    H om (((3 : ℝ) ^ j) • y) =
      infraredPartialSum om j (((3 : ℝ) ^ j) • y) + H (aux_prop_growth_large_root_scaleShift j om) y

theorem aux_prop_growth_large_root_infraredPartialSum_eq_sub (om : BilateralField d) (j : ℕ) (x : SpatialCoordinates d) :
    infraredPartialSum om j x =
      (∑ n ∈ Finset.range j, om (Int.ofNat (n + 1)) x) - aux_prop_growth_large_root_irAnchor j om := by
  rw [aux_prop_growth_large_root_infraredPartialSum_apply, Finset.sum_sub_distrib, aux_prop_growth_large_root_irAnchor]

/-- The low block of the shifted ultraviolet sum is the first `j` infrared layers. -/
theorem aux_prop_growth_large_root_sum_low_block (om : BilateralField d) (j : ℕ) (y : SpatialCoordinates d) :
    (∑ i ∈ Finset.range j, aux_prop_growth_large_root_scaleShift j om (-(Int.ofNat i)) y) =
      ∑ n ∈ Finset.range j, om (Int.ofNat (n + 1)) (((3 : ℝ) ^ j) • y) := by
  rw [← Finset.sum_range_reflect (fun n => om (Int.ofNat (n + 1)) (((3 : ℝ) ^ j) • y)) j]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij : i < j := Finset.mem_range.1 hi
  simp only [aux_prop_growth_large_root_scaleShift_apply]
  congr 2
  simp only [Int.ofNat_eq_natCast]
  omega

theorem aux_prop_growth_large_root_cutoffPotential_scaleShift (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (j N : ℕ) (hIR : aux_prop_growth_large_root_IRShiftAt H j om) (y : SpatialCoordinates d) :
    cutoffPotential H om N (((3 : ℝ) ^ j) • y) =
      cutoffPotential H (aux_prop_growth_large_root_scaleShift j om) (N + j) y - aux_prop_growth_large_root_irAnchor j om := by
  unfold cutoffPotential
  have hsplit : (∑ i ∈ Finset.range (N + j + 1), aux_prop_growth_large_root_scaleShift j om (-(Int.ofNat i)) y) =
      (∑ i ∈ Finset.range j, aux_prop_growth_large_root_scaleShift j om (-(Int.ofNat i)) y) +
        ∑ k ∈ Finset.range (N + 1), om (-(Int.ofNat k)) (((3 : ℝ) ^ j) • y) := by
    rw [show N + j + 1 = j + (N + 1) by omega, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [aux_prop_growth_large_root_scaleShift_apply]
    congr 2
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [hsplit, aux_prop_growth_large_root_sum_low_block, hIR y, aux_prop_growth_large_root_infraredPartialSum_eq_sub]
  ring

/-- The Step-1 random constant `c = (â_{N+j}/â_N) exp(j τ² − X_j)`. -/
def aux_prop_growth_large_root_shiftConst (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j N : ℕ) (om : BilateralField d) : ℝ :=
  SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
    Real.exp ((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P - aux_prop_growth_large_root_irAnchor j om)

/-- **Scale covariance of `A_N`** on the infrared event. -/
theorem aux_prop_growth_large_root_cutoffCoefficient_scaleShift (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (j N : ℕ)
    (hIR : aux_prop_growth_large_root_IRShiftAt H j om) (hpos : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j))
    (y : SpatialCoordinates d) :
    cutoffCoefficient M H om N (((3 : ℝ) ^ j) • y) =
      aux_prop_growth_large_root_shiftConst M j N om * cutoffCoefficient M H (aux_prop_growth_large_root_scaleShift j om) (N + j) y := by
  unfold cutoffCoefficient aux_prop_growth_large_root_shiftConst
  rw [aux_prop_growth_large_root_cutoffPotential_scaleShift H om j N hIR y]
  have hne : SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) ≠ 0 := hpos.ne'
  have hexp : Real.exp ((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P - aux_prop_growth_large_root_irAnchor j om) *
      Real.exp (cutoffPotential H (aux_prop_growth_large_root_scaleShift j om) (N + j) y -
        (((N + j : ℕ) : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
      Real.exp (cutoffPotential H (aux_prop_growth_large_root_scaleShift j om) (N + j) y - aux_prop_growth_large_root_irAnchor j om -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  calc (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
        Real.exp (cutoffPotential H (aux_prop_growth_large_root_scaleShift j om) (N + j) y - aux_prop_growth_large_root_irAnchor j om -
          ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
      = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
        (Real.exp ((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P - aux_prop_growth_large_root_irAnchor j om) *
          Real.exp (cutoffPotential H (aux_prop_growth_large_root_scaleShift j om) (N + j) y -
            (((N + j : ℕ) : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by rw [hexp]
    _ = _ := by field_simp

/-- The Step-1 envelope `exp(j|τ²| + |X_j|)`. -/
def aux_prop_growth_large_root_shiftEnv (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (om : BilateralField d) : ℝ :=
  Real.exp ((j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P| + |aux_prop_growth_large_root_irAnchor j om|)

theorem aux_prop_growth_large_root_one_le_shiftEnv (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ)
    (om : BilateralField d) : 1 ≤ aux_prop_growth_large_root_shiftEnv M j om :=
  Real.one_le_exp (add_nonneg (mul_nonneg (Nat.cast_nonneg j) (abs_nonneg _)) (abs_nonneg _))

section Bounds

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_prop_growth_large_root_ahom_pos_of (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (m : ℕ) : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M m :=
  lt_of_lt_of_le (Real.exp_pos _) (Rm.ahom_lower m)

theorem aux_prop_growth_large_root_shiftConst_pos (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (j N : ℕ) (om : BilateralField d) : 0 < aux_prop_growth_large_root_shiftConst M j N om :=
  mul_pos (div_pos (aux_prop_growth_large_root_ahom_pos_of M Rm _) (aux_prop_growth_large_root_ahom_pos_of M Rm _)) (Real.exp_pos _)

theorem aux_prop_growth_large_root_shiftConst_le (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (j N : ℕ) (hj : 0 < j) (om : BilateralField d) : aux_prop_growth_large_root_shiftConst M j N om ≤ aux_prop_growth_large_root_shiftEnv M j om := by
  have hord := (Rm.ahom_ordering N (N + j) (by omega)).1
  have hratio : SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≤ 1 :=
    (div_le_one (aux_prop_growth_large_root_ahom_pos_of M Rm N)).2 hord
  unfold aux_prop_growth_large_root_shiftConst aux_prop_growth_large_root_shiftEnv
  calc SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        Real.exp ((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P - aux_prop_growth_large_root_irAnchor j om)
      ≤ 1 * Real.exp ((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P - aux_prop_growth_large_root_irAnchor j om) :=
        mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le
    _ ≤ _ := by
      rw [one_mul]
      apply Real.exp_le_exp.2
      have h1 : (j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P ≤
          (j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg j)
      have h2 : -aux_prop_growth_large_root_irAnchor j om ≤ |aux_prop_growth_large_root_irAnchor j om| := neg_le_abs _
      linarith

theorem aux_prop_growth_large_root_shiftConst_inv_le (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (j N : ℕ) (hj : 0 < j) (om : BilateralField d) :
    (aux_prop_growth_large_root_shiftConst M j N om)⁻¹ ≤ aux_prop_growth_large_root_shiftEnv M j om := by
  have hord := (Rm.ahom_ordering N (N + j) (by omega)).2
  have hpN := aux_prop_growth_large_root_ahom_pos_of M Rm N
  have hpNj := aux_prop_growth_large_root_ahom_pos_of M Rm (N + j)
  have hcast : ((N + j : ℕ) : ℝ) - (N : ℝ) = j := by push_cast; ring
  rw [hcast] at hord
  unfold aux_prop_growth_large_root_shiftConst aux_prop_growth_large_root_shiftEnv
  rw [mul_inv, inv_div, ← Real.exp_neg]
  calc SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + j) *
        Real.exp (-((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P - aux_prop_growth_large_root_irAnchor j om))
      ≤ Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (j : ℝ)) *
        Real.exp (-((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P - aux_prop_growth_large_root_irAnchor j om)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        rw [div_le_iff₀ hpNj]
        exact hord
    _ = Real.exp ((j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P + aux_prop_growth_large_root_irAnchor j om) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      have h1 : (j : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P ≤
          (j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg j)
      have h2 : aux_prop_growth_large_root_irAnchor j om ≤ |aux_prop_growth_large_root_irAnchor j om| := le_abs_self _
      linarith

/-! ## Exponential moments of the anchor -/

theorem aux_prop_growth_large_root_measurable_eval_layer (m : ℤ) (x : SpatialCoordinates d) :
    Measurable (fun om : BilateralField d => om m x) :=
  (continuous_eval_const x).measurable.comp (measurable_pi_apply m)

theorem aux_prop_growth_large_root_measurable_irAnchor (j : ℕ) : Measurable (aux_prop_growth_large_root_irAnchor (d := d) j) := by
  unfold aux_prop_growth_large_root_irAnchor
  exact Finset.measurable_sum _ fun n _ => aux_prop_growth_large_root_measurable_eval_layer _ _

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- (g2): every exponential moment of `|g₀(0)|` is finite. -/
theorem aux_prop_growth_large_root_integrable_exp_mul_abs_zero {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (c : ℝ)
    (hc : 0 ≤ c) :
    Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => Real.exp (c * |g 0|))
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  set E : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ :=
    _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable with hEdef
  set Z : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun g =>
    Real.exp ((M.delta⁻¹ * max (E g) 0) ^ (2 : ℝ)) with hZdef
  have hZint : Integrable Z (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
    simpa [hZdef, hEdef, SubdiffusiveProcess.OGammaLE] using M.G2.regularity_expectation.1
  have h0 : (0 : Homogenization.Vec d) ∈ Metric.closedBall
      (Homogenization.cubeCenter (Homogenization.originCube d 0))
      (Homogenization.cubeRadius (Homogenization.originCube d 0)) := by
    have hc0 : Homogenization.cubeCenter (Homogenization.originCube d 0) = 0 := by
      funext i
      simp [Homogenization.cubeCenter, Homogenization.originCube]
    rw [hc0]
    exact Metric.mem_closedBall_self (Homogenization.cubeRadius_pos _).le
  have hmeasEv : Measurable fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => g 0 := by
    have hforget : Continuous fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
        (g.1.1 : C(SpatialCoordinates d, ℝ)) := continuous_subtype_val.fst
    exact ((continuous_eval_const (0 : SpatialCoordinates d)).comp hforget).measurable
  have hmeas : Measurable fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      Real.exp (c * |g 0|) := (measurable_const.mul (continuous_abs.measurable.comp hmeasEv)).exp
  have hdom : ∀ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
      Real.exp (c * |g 0|) ≤ Real.exp ((c * M.delta) ^ 2 / 4) * Z g := by
    intro g
    have hE0 : 0 ≤ E g := _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg g
    have hg0 : |g 0| ≤ E g :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.abs_apply_le_g2Observable_of_mem_closedBall g h0
    have hZg : Z g = Real.exp ((M.delta⁻¹ * E g) ^ (2 : ℕ)) := by
      simp only [hZdef, max_eq_left hE0]
      congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hZg, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hexpand : (c * M.delta) ^ 2 / 4 + (M.delta⁻¹ * E g) ^ (2 : ℕ) - c * E g
        = (E g - c * M.delta ^ 2 / 2) ^ 2 / M.delta ^ 2 := by
      field_simp
      ring
    have h2 : 0 ≤ (c * M.delta) ^ 2 / 4 + (M.delta⁻¹ * E g) ^ (2 : ℕ) - c * E g := by
      rw [hexpand]; positivity
    have h3 : c * |g 0| ≤ c * E g := mul_le_mul_of_nonneg_left hg0 hc
    linarith
  refine (hZint.const_mul (Real.exp ((c * M.delta) ^ 2 / 4))).mono'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact hdom g

/-- Every layer value at the origin has the law of `g₀(0)`. -/
theorem aux_prop_growth_large_root_integrable_exp_mul_abs_layer (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℤ) (c : ℝ)
    (hc : 0 ≤ c) :
    Integrable (fun om : BilateralField d => Real.exp (c * |om m 0|))
      ((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) :
        Measure (BilateralField d)) := by
  rw [aux_prop_growth_large_root_chaosSampleLaw_eq]
  set laws : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun n =>
    (scaledLayerLaw d (chaosRootFieldLaw M) n : Measure C(SpatialCoordinates d, ℝ)) with hlaws
  set F : C(SpatialCoordinates d, ℝ) → ℝ := fun f => Real.exp (c * |f 0|) with hF
  have hFm : Measurable F :=
    (measurable_const.mul (continuous_abs.measurable.comp
      (continuous_eval_const (0 : SpatialCoordinates d)).measurable)).exp
  have hev := measurePreserving_eval_infinitePi laws m
  have h1 : Integrable F (laws m) := by
    simp only [hlaws, scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
    rw [integrable_map_measure hFm.aestronglyMeasurable
      (layerScaling d m).continuous.measurable.aemeasurable]
    have hcomp : F ∘ (layerScaling d m) = F := by
      funext f
      simp [hF, layerScaling]
    rw [hcomp]
    simp only [chaosRootFieldLaw, ProbabilityMeasure.toMeasure_map]
    rw [integrable_map_measure hFm.aestronglyMeasurable
      (ContinuousMap.continuous _).measurable.aemeasurable]
    exact aux_prop_growth_large_root_integrable_exp_mul_abs_zero M c hc
  exact (hev.integrable_comp hFm.aestronglyMeasurable).2 h1

theorem aux_prop_growth_large_root_exp_mul_sum_le (a : ℕ → ℝ) (_ha : ∀ n, 0 ≤ a n) (c : ℝ) (hc : 0 ≤ c) (j : ℕ)
    (hj : 0 < j) :
    Real.exp (c * ∑ n ∈ Finset.range j, a n) ≤
      ∑ n ∈ Finset.range j, Real.exp (c * j * a n) := by
  have hne : (Finset.range j).Nonempty := Finset.nonempty_range_iff.2 (by omega)
  obtain ⟨n0, hn0, hmax⟩ := Finset.exists_max_image (Finset.range j) a hne
  have hsum : (∑ n ∈ Finset.range j, a n) ≤ j * a n0 := by
    have := Finset.sum_le_card_nsmul (Finset.range j) a (a n0) hmax
    simpa [Finset.card_range, nsmul_eq_mul] using this
  calc Real.exp (c * ∑ n ∈ Finset.range j, a n) ≤ Real.exp (c * j * a n0) := by
        apply Real.exp_le_exp.2
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hsum hc
    _ ≤ ∑ n ∈ Finset.range j, Real.exp (c * j * a n) :=
        Finset.single_le_sum (f := fun n => Real.exp (c * j * a n))
          (fun n _ => (Real.exp_pos _).le) hn0

/-- **All exponential moments of the anchor.** -/
theorem aux_prop_growth_large_root_integrable_exp_mul_abs_irAnchor (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ)
    (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun om : BilateralField d => Real.exp (c * |aux_prop_growth_large_root_irAnchor j om|))
      ((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) :
        Measure (BilateralField d)) := by
  have hmeas : Measurable fun om : BilateralField d => Real.exp (c * |aux_prop_growth_large_root_irAnchor j om|) :=
    (measurable_const.mul (continuous_abs.measurable.comp (aux_prop_growth_large_root_measurable_irAnchor j))).exp
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [aux_prop_growth_large_root_irAnchor, Finset.range_zero, Finset.sum_empty, abs_zero, mul_zero,
      Real.exp_zero]
    exact integrable_const _
  have hsum : Integrable (fun om : BilateralField d => ∑ n ∈ Finset.range j,
      Real.exp (c * j * |om (Int.ofNat (n + 1)) 0|))
      ((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) :
        Measure (BilateralField d)) :=
    integrable_finsetSum _ fun n _ =>
      aux_prop_growth_large_root_integrable_exp_mul_abs_layer M _ _ (mul_nonneg hc (Nat.cast_nonneg j))
  refine hsum.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun om => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (c * |aux_prop_growth_large_root_irAnchor j om|)
      ≤ Real.exp (c * ∑ n ∈ Finset.range j, |om (Int.ofNat (n + 1)) 0|) := by
        apply Real.exp_le_exp.2
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hc
    _ ≤ _ := aux_prop_growth_large_root_exp_mul_sum_le (fun n => |om (Int.ofNat (n + 1)) 0|) (fun n => abs_nonneg _) c hc j hj

/-- `aux_prop_growth_large_root_shiftEnv` has every finite moment. -/
theorem aux_prop_growth_large_root_memLp_shiftEnv (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    MemLp (aux_prop_growth_large_root_shiftEnv M j) (ENNReal.ofReal q)
      ((chaosSampleLaw M : ProbabilityMeasure (BilateralField d)) :
        Measure (BilateralField d)) := by
  have hmeas : Measurable (aux_prop_growth_large_root_shiftEnv (d := d) M j) :=
    (measurable_const.add (continuous_abs.measurable.comp (aux_prop_growth_large_root_measurable_irAnchor j))).exp
  have hq0 : (ENNReal.ofReal q) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  rw [← integrable_norm_rpow_iff hmeas.aestronglyMeasurable hq0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)]
  have hint := (aux_prop_growth_large_root_integrable_exp_mul_abs_irAnchor M j q (by linarith)).const_mul
    (Real.exp (q * ((j : ℝ) * |_root_.SubdiffusiveProcess.Model.tauSq M.P|)))
  refine hint.congr (Filter.Eventually.of_forall fun om => ?_)
  simp only [aux_prop_growth_large_root_shiftEnv, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  rw [← Real.exp_add, ← Real.exp_mul]
  congr 1
  ring

end Bounds

/-! ## The coefficient on the dilated unit cube -/

theorem aux_prop_growth_large_root_cutoffPositiveCoefficient_val_ae [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N z hr).val x = cutoffCoefficient M H om N x := by
  have h := @normalizedContinuousPositiveCoefficient_coeFn d (centeredCube z r hr)
    (closedCube z r hr) ⟨centeredCube_subset_closedCube z hr⟩
    (cutoffCoefficientCM M H om N z hr) (cutoffCoefficientCM_pos M H om N z hr) 1 one_pos
  filter_upwards [h, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxm
  rw [cutoffPositiveCoefficient, hx hxm, div_one]
  rfl

end LRGCoef

section LRGTransport

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.Paper
open scoped ENNReal NNReal BigOperators ContDiff Pointwise


variable {d : ℕ}

/-- **Dirichlet transport** `centeredCube z r → centeredCube z0 1` along
`x ↦ z + r (x - z0)`, for an arbitrary coefficient and centre. -/
theorem aux_prop_growth_large_root_dirichlet_transport (z z0 : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (a1 : PositiveCoefficient (centeredCube z0 1 one_pos))
    (ha1 : ∀ᵐ x ∂(volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))),
      (a1.val : SpatialCoordinates d → ℝ) x =
        (a.val : SpatialCoordinates d → ℝ) (cubeDilation z z0 r x))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (_hKf : 0 ≤ Kf)
    (hF : AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFbound : ∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hCphi : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (htrace : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (hsolve : SolvesDirichlet a F b u) :
    ∃ (F1 phi1 : SpatialCoordinates d → ℝ)
      (b1 u1 : weakSobolevGraph (centeredCube z0 1 one_pos)),
      F1 = (fun x => r ^ 2 * F (cubeDilation z z0 r x)) ∧
      AEMeasurable F1 (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))) ∧
      (∀ᵐ x ∂(volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))),
        |F1 x| ≤ r ^ 2 * Kf) ∧
      phi1 = (fun x => phi (cubeDilation z z0 r x)) ∧
      ContDiff ℝ 2 phi1 ∧
      (∃ Cphi1 : ℝ, c2Norm (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) phi1 ≤ Cphi1 ∧
        Cphi1 ≤ (1 + r + r ^ 2) * Cphi) ∧
      ((b1 : SobolevData (centeredCube z0 1 one_pos)).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))] phi1 ∧
      SolvesDirichlet a1 F1 b1 u1 ∧
      ((b1 : SobolevData (centeredCube z0 1 one_pos)).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))]
        (fun x => (b : SobolevData (centeredCube z r hr)).1 (cubeDilation z z0 r x)) ∧
      ((u1 : SobolevData (centeredCube z0 1 one_pos)).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))]
        (fun x => (u : SobolevData (centeredCube z r hr)).1 (cubeDilation z z0 r x)) ∧
      (∀ i : Fin d,
        ((u1 : SobolevData (centeredCube z0 1 one_pos)).2 i : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))]
          (fun x => r * (u : SobolevData (centeredCube z r hr)).2 i (cubeDilation z z0 r x))) ∧
      (∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho →
        localGradientEnergy a1
            (s := Metric.ball x rho ∩ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet)
            (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos))) =
          r ^ ((2 : ℝ) - (d : ℝ)) *
            localGradientEnergy a
              (s := Metric.ball (cubeDilation z z0 r x) (r * rho) ∩
                (centeredCube z r hr : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (centeredCube z r hr)))) := by
  obtain ⟨b1, hbval, hbgrad⟩ :=
    aux_lem_as_regularity_affine_transport_weak_pullback d z z0 r hr one_pos b
  obtain ⟨u1, huval, hugrad⟩ :=
    aux_lem_as_regularity_affine_transport_weak_pullback d z z0 r hr one_pos u
  let F1 : SpatialCoordinates d → ℝ := fun x => r ^ 2 * F (cubeDilation z z0 r x)
  let phi1 : SpatialCoordinates d → ℝ := fun x => phi (cubeDilation z z0 r x)
  have hq := dilation_quasi_measure_preserving d z z0 r hr one_pos
  have hF1 : AEMeasurable F1
      (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))) := by
    have hcomp := hF.comp_quasiMeasurePreserving hq
    simpa [F1, Function.comp_def] using hcomp.const_mul (r ^ 2)
  have hFbound1 : ∀ᵐ x ∂volume.restrict
      (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      |F1 x| ≤ r ^ 2 * Kf := by
    filter_upwards [hq.ae hFbound] with x hx
    simp only [F1, abs_mul, abs_of_nonneg (sq_nonneg r)]
    exact mul_le_mul_of_nonneg_left hx (sq_nonneg r)
  have hphi1 := aux_lem_as_regularity_affine_transport_c2_chain_rule
    d z z0 r hr phi hphi
  have hCphi1 := aux_lem_as_regularity_affine_transport_c2_norm_bound
    d z z0 r hr one_pos phi hphi Cphi hCphi
  have htrace1 :
      ((b1 : SobolevData (centeredCube z0 1 one_pos)).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))] phi1 := by
    filter_upwards [hbval, hq.ae htrace] with x hbx htx
    rw [hbx, htx]
  let k : killedSobolevGraph (centeredCube z r hr) :=
    ⟨(u : SobolevData (centeredCube z r hr)) - (b : SobolevData (centeredCube z r hr)),
      hsolve.1⟩
  obtain ⟨k1, hkval, hkgrad⟩ :=
    aux_lem_as_regularity_affine_transport_killed_pullback d z z0 r hr one_pos k
  have hdiff :
      ((u1 : SobolevData (centeredCube z0 1 one_pos)) -
        (b1 : SobolevData (centeredCube z0 1 one_pos))) = (k1 : SobolevData (centeredCube z0 1 one_pos)) := by
    apply aux_lem_as_regularity_affine_transport_sobolevData_eq_of_ae
    · filter_upwards [Lp.coeFn_sub
          ((u1 : SobolevData (centeredCube z0 1 one_pos)).1)
          ((b1 : SobolevData (centeredCube z0 1 one_pos)).1),
        huval, hbval, hkval,
        hq.ae (Lp.coeFn_sub (u : SobolevData (centeredCube z r hr)).1
          (b : SobolevData (centeredCube z r hr)).1)] with x hux huT hbT hkx hsub
      have hux' : ((u1 : SobolevData (centeredCube z0 1 one_pos)) -
          (b1 : SobolevData (centeredCube z0 1 one_pos))).1 x =
          ((u1 : SobolevData (centeredCube z0 1 one_pos)).1 -
            (b1 : SobolevData (centeredCube z0 1 one_pos)).1) x := by
        simp only [Prod.fst_sub]
      rw [hux', hux]
      simp only [Pi.sub_apply]
      rw [huT, hbT, hkx]
      simpa [k] using hsub.symm
    · intro i
      filter_upwards [Lp.coeFn_sub
          ((u1 : SobolevData (centeredCube z0 1 one_pos)).2 i)
          ((b1 : SobolevData (centeredCube z0 1 one_pos)).2 i),
        hugrad i, hbgrad i, hkgrad i,
        hq.ae (Lp.coeFn_sub ((u : SobolevData (centeredCube z r hr)).2 i)
          ((b : SobolevData (centeredCube z r hr)).2 i))] with x hux huT hbT hkx hsub
      have hux' : ((u1 : SobolevData (centeredCube z0 1 one_pos)) -
          (b1 : SobolevData (centeredCube z0 1 one_pos))).2 i x =
          ((u1 : SobolevData (centeredCube z0 1 one_pos)).2 i -
            (b1 : SobolevData (centeredCube z0 1 one_pos)).2 i) x := by
        simp only [Prod.snd_sub, Pi.sub_apply]
      rw [hux', hux]
      simp only [Pi.sub_apply]
      rw [huT, hbT, hkx]
      calc
        r * ((u : SobolevData (centeredCube z r hr)).2 i) (cubeDilation z z0 r x) -
            r * ((b : SobolevData (centeredCube z r hr)).2 i) (cubeDilation z z0 r x) =
            r * (((u : SobolevData (centeredCube z r hr)).2 i) (cubeDilation z z0 r x) -
              ((b : SobolevData (centeredCube z r hr)).2 i) (cubeDilation z z0 r x)) := by ring
        _ = r * ((k : SobolevData (centeredCube z r hr)).2 i) (cubeDilation z z0 r x) := by
          exact congrArg (fun q : ℝ => r * q) (by simpa [k] using hsub.symm)
  have hkill :
      (u1 : SobolevData (centeredCube z0 1 one_pos)) -
          (b1 : SobolevData (centeredCube z0 1 one_pos)) ∈
        killedSobolevGraph (centeredCube z0 1 one_pos) := by
    rw [hdiff]
    exact k1.property
  have hsolve1 : SolvesDirichlet a1 F1 b1 u1 := by
    refine ⟨hkill, ?_⟩
    intro psi1
    obtain ⟨psi, hpsival⟩ :=
      aux_lem_as_regularity_affine_transport_killed_pushforward
        d z z0 r hr one_pos psi1
    let psiW : weakSobolevGraph (centeredCube z r hr) :=
      ⟨psi.val, killedSobolevGraph_le_weakSobolevGraph psi.property⟩
    let psi1W : weakSobolevGraph (centeredCube z0 1 one_pos) :=
      ⟨psi1.val, killedSobolevGraph_le_weakSobolevGraph psi1.property⟩
    have hform := aux_lem_as_regularity_affine_transport_form_scaling
      d z z0 r hr one_pos
      a a1 u psiW u1 psi1W ha1 huval hpsival
    let fp : SpatialCoordinates d → ℝ := fun y =>
      F y * (psi : SobolevData (centeredCube z r hr)).1 y
    have hsolvePsi :
        sobolevCoefficientForm a
            (u : SobolevData (centeredCube z r hr))
            (psiW : SobolevData (centeredCube z r hr)) =
          ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y := by
      simpa [psiW, fp] using hsolve.2 psi
    have hfp : AEMeasurable fp
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
      exact hF.mul (Lp.aestronglyMeasurable
        (psi : SobolevData (centeredCube z r hr)).1).aemeasurable
    have hscale := aux_lem_as_regularity_affine_transport_integral_scaling
      d z z0 r hr one_pos fp hfp
    let psi1val : SpatialCoordinates d → ℝ := fun y =>
      (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y
    have hbase :
        (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
          F (cubeDilation z z0 r y) *
            (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y) =
          ∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
            fp (cubeDilation z z0 r y) := by
      apply integral_congr_ae
      refine hpsival.mono ?_
      intro y hy
      dsimp [fp]
      rw [hy]
    have hsource :
        (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y) =
          r ^ d *
            (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
              F (cubeDilation z z0 r y) * psi1.val.1 y) := by
      calc
        (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y) =
            r ^ d * ((r ^ d)⁻¹ *
              (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y)) := by
          exact aux_lem_as_regularity_affine_transport_pow_inv_mul d r _ hr
        _ = r ^ d *
            (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
              fp (cubeDilation z z0 r y)) := by rw [hscale]
        _ = r ^ d *
            (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
              F (cubeDilation z z0 r y) * psi1.val.1 y) := by
          exact congrArg (fun q : ℝ => r ^ d * q) hbase.symm
    have hpow := aux_lem_as_regularity_affine_transport_pow_split d r hr
    have hR : r ^ ((d : ℝ) - 2) ≠ 0 :=
      (Real.rpow_pos_of_pos hr _).ne'
    have hform' :
        sobolevCoefficientForm a1 (u1 : SobolevData (centeredCube z0 1 one_pos))
            (psi1 : SobolevData (centeredCube z0 1 one_pos)) =
          r ^ 2 *
            (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
              F (cubeDilation z z0 r y) * psi1.val.1 y) := by
      apply mul_left_cancel₀ hR
      calc
        r ^ ((d : ℝ) - 2) *
            sobolevCoefficientForm a1
              (u1 : SobolevData (centeredCube z0 1 one_pos))
              (psi1 : SobolevData (centeredCube z0 1 one_pos)) =
            sobolevCoefficientForm
              a
              (u : SobolevData (centeredCube z r hr))
              (psi : SobolevData (centeredCube z r hr)) := hform.symm
        _ = r ^ ((d : ℝ) - 2) * (r ^ 2 *
            (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
              F (cubeDilation z z0 r y) *
                (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y)) := by
          rw [hsolvePsi, hsource, hpow] ; ring
    calc
      sobolevCoefficientForm a1 (u1 : SobolevData (centeredCube z0 1 one_pos))
          (psi1 : SobolevData (centeredCube z0 1 one_pos)) =
          r ^ 2 *
            (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
              F (cubeDilation z z0 r y) *
                (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y) := hform'
      _ = ∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
          F1 y * (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        dsimp [F1]
        ring
  refine ⟨F1, phi1, b1, u1, rfl, hF1, hFbound1, rfl, hphi1.1,
    ⟨(1 + r + r ^ 2) * Cphi, hCphi1, le_rfl⟩, htrace1, hsolve1,
    hbval, huval, hugrad, ?_⟩
  intro x rho hrho
  exact aux_lem_as_regularity_affine_transport_local_energy_scaling
    d z z0 r hr one_pos a a1
    (sobolevGradient (u : SobolevData (centeredCube z r hr)))
    (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos))) ha1 hugrad x rho hrho

/-! ## Scaling the coefficient by a constant -/

theorem aux_prop_growth_large_root_sobolevCoefficientForm_scale {Ω : Opens (SpatialCoordinates d)}
    (a b : PositiveCoefficient Ω) (c : ℝ)
    (h : ∀ᵐ x ∂(volume.restrict (Ω : Set (SpatialCoordinates d))),
      (a.val : SpatialCoordinates d → ℝ) x = c * (b.val : SpatialCoordinates d → ℝ) x)
    (u v : SobolevData Ω) :
    sobolevCoefficientForm a u v = c * sobolevCoefficientForm b u v := by
  rw [sobolevCoefficientForm_eq_sum_integral, sobolevCoefficientForm_eq_sum_integral,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (h.mono fun x hx => ?_)
  simp only
  rw [hx]
  ring

/-- `-∇·(a∇u) = F` with `a = c b` is `-∇·(b∇u) = c⁻¹ F`. -/
theorem aux_prop_growth_large_root_solvesDirichlet_scale {Ω : Opens (SpatialCoordinates d)}
    (a b : PositiveCoefficient Ω) (c : ℝ) (hc : 0 < c)
    (h : ∀ᵐ x ∂(volume.restrict (Ω : Set (SpatialCoordinates d))),
      (a.val : SpatialCoordinates d → ℝ) x = c * (b.val : SpatialCoordinates d → ℝ) x)
    (F : SpatialCoordinates d → ℝ) (bd u : weakSobolevGraph Ω)
    (hs : SolvesDirichlet a F bd u) :
    SolvesDirichlet b (fun x => c⁻¹ * F x) bd u := by
  refine ⟨hs.1, fun ψ => ?_⟩
  have h2 := hs.2 ψ
  rw [aux_prop_growth_large_root_sobolevCoefficientForm_scale a b c h] at h2
  have h3 : (∫ x in (Ω : Set (SpatialCoordinates d)),
      c⁻¹ * F x * (ψ : SobolevData Ω).1 x) =
      c⁻¹ * ∫ x in (Ω : Set (SpatialCoordinates d)), F x * (ψ : SobolevData Ω).1 x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [h3, ← h2, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

theorem aux_prop_growth_large_root_localGradientEnergy_scale {Ω : Opens (SpatialCoordinates d)}
    (a b : PositiveCoefficient Ω) (c : ℝ)
    (h : ∀ᵐ x ∂(volume.restrict (Ω : Set (SpatialCoordinates d))),
      (a.val : SpatialCoordinates d → ℝ) x = c * (b.val : SpatialCoordinates d → ℝ) x)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s) (g : HilbertGradient Ω) :
    localGradientEnergy a hs g = c * localGradientEnergy b hs g := by
  rw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae ((ae_restrict_of_ae h).mono fun x hx => ?_)
  simp only
  rw [hx]
  ring

/-! ## Hölder transport back to the root -/

/-- Comparison of real suprema through a dominating family. -/
theorem aux_prop_growth_large_root_sSup_le_sSup_of_dominated {S T : Set ℝ} (hT : BddAbove T)
    (hT0 : ∀ w ∈ T, 0 ≤ w) (h : ∀ v ∈ S, ∃ w ∈ T, v ≤ w) :
    BddAbove S ∧ sSup S ≤ sSup T := by
  have hsT : 0 ≤ sSup T := Real.sSup_nonneg hT0
  refine ⟨⟨sSup T, fun v hv => ?_⟩, Real.sSup_le (fun v hv => ?_) hsT⟩
  · obtain ⟨w, hw, hvw⟩ := h v hv
    exact hvw.trans (le_csSup hT hw)
  · obtain ⟨w, hw, hvw⟩ := h v hv
    exact hvw.trans (le_csSup hT hw)

theorem aux_prop_growth_large_root_cubeDilation_inv_left (z z0 : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (y : SpatialCoordinates d) :
    cubeDilation z z0 r (cubeDilation z0 z r⁻¹ y) = y := by
  funext i
  rw [cubeDilation_apply, cubeDilation_apply]
  field_simp
  ring

/-- Pull an a.e. identity on the unit cube back to the root through the dilation. -/
theorem aux_prop_growth_large_root_ae_root_of_ae_unit (z z0 : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {p : SpatialCoordinates d → Prop}
    (h : ∀ᵐ x ∂(volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))),
      p (cubeDilation z z0 r x)) :
    ∀ᵐ y ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))), p y := by
  have hmap := map_cubeDilation_restrict z z0 hr one_pos
  have hcoe : (cubeDilationEquiv z z0 hr.ne' : SpatialCoordinates d → SpatialCoordinates d) =
      cubeDilation z z0 r := by
    funext x; exact cubeDilationEquiv_apply z z0 hr.ne' x
  have h1 : ∀ᵐ y ∂(Measure.map (cubeDilationEquiv z z0 hr.ne')
      (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))), p y := by
    rw [(cubeDilationEquiv z z0 hr.ne').measurableEmbedding.ae_map_iff]
    simpa [hcoe] using h
  rw [hcoe, hmap] at h1
  have hc : ENNReal.ofReal |(r ^ d)⁻¹| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.2 (inv_ne_zero (pow_ne_zero _ hr.ne'))
  exact (Measure.ae_ennreal_smul_measure_iff hc).1 h1

end LRGTransport

section LRGMain

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.Paper
open scoped ENNReal NNReal BigOperators ContDiff Pointwise


variable {d : ℕ}

/-! ## Verbatim supplier bodies -/

/-- The one-sample body of `prop_growth` at the root `centeredCube z r hr` (verbatim
`CB.GrowthAt`). -/
def aux_prop_growth_large_root_GrowthAt [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t alpha : ℝ)
    (om : BilateralField d) (K : ℕ → ℝ) : Prop :=
  ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf →
    AEMeasurable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
    (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      |F x| ≤ Kf) →
  ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
    ContDiff ℝ 2 phi →
    c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
  ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
    ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
    SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
    (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
      0 < rad → rad ≤ 1 →
      localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter
            (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        K N * (Kf + Cphi) ^ 2 * rad ^ t) ∧
    (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
      cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
        K N * (Kf + Cphi))

/-- The full conclusion of `prop_growth` at one root (verbatim `CB.GrowthBody`). -/
def aux_prop_growth_large_root_GrowthBody [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ) : Prop :=
  (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
  (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
    ENNReal.ofReal (Cbound i)) ∧
  (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
  ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, aux_prop_growth_large_root_GrowthAt M H z r hr t alpha om (fun N => K N om)

/-- `aux_prop_growth_large_root_GrowthAt` for an abstract coefficient family. -/
def aux_prop_growth_large_root_GrowthAtCoef (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t alpha : ℝ)
    (A : ℕ → PositiveCoefficient (centeredCube z r hr)) (K : ℕ → ℝ) : Prop :=
  ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf →
    AEMeasurable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
    (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      |F x| ≤ Kf) →
  ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
    ContDiff ℝ 2 phi →
    c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
  ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
    ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
    SolvesDirichlet (A N) F b u →
    (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
      0 < rad → rad ≤ 1 →
      localGradientEnergy (A N)
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter
            (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        K N * (Kf + Cphi) ^ 2 * rad ^ t) ∧
    (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
      cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
        K N * (Kf + Cphi))

/-! ## Deterministic transfer -/

theorem aux_prop_growth_large_root_c2Norm_nonneg' (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
    0 ≤ c2Norm S f := by
  unfold c2Norm
  refine add_nonneg (add_nonneg ?_ ?_) ?_ <;>
  · apply Real.sSup_nonneg
    rintro v ⟨x, -, rfl⟩
    positivity

theorem aux_prop_growth_large_root_cubeDilation_inv_right (z z0 : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (x : SpatialCoordinates d) :
    cubeDilation z0 z r⁻¹ (cubeDilation z z0 r x) = x := by
  funext i
  rw [cubeDilation_apply, cubeDilation_apply]
  field_simp
  ring

theorem aux_prop_growth_large_root_cubeDilation_inv_mem_centeredCube (z z0 : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {y : SpatialCoordinates d} (hy : y ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    cubeDilation z0 z r⁻¹ y ∈ (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)) := by
  change dist (cubeDilation z0 z r⁻¹ y) z0 < 1 / 2
  have hy' : dist y z < r / 2 := hy
  have heq : cubeDilation z0 z r⁻¹ y - z0 = r⁻¹ • (y - z) := by
    funext i
    simp [cubeDilation_apply, Pi.smul_apply, smul_eq_mul]
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr),
    ← dist_eq_norm]
  calc r⁻¹ * dist y z < r⁻¹ * (r / 2) := mul_lt_mul_of_pos_left hy' (inv_pos.2 hr)
    _ = 1 / 2 := by field_simp

/-- The pure-real part of the energy transfer. -/
theorem aux_prop_growth_large_root_energy_real {r c E m K Kf Cphi Kf' Cphi' rad t D L R2 : ℝ} (hr1 : 1 ≤ r)
    (hc : 0 < c) (hcm : c * m ^ 2 ≤ E) (hK : 0 ≤ K) (hsum : 0 ≤ Kf' + Cphi')
    (hsum' : Kf' + Cphi' ≤ R2 * m * (Kf + Cphi)) (hrad : 0 < rad) (ht : D - 2 < t)
    (hL : L ≤ K * (Kf' + Cphi') ^ 2 * (rad / r) ^ t) :
    r ^ (D - 2) * (c * L) ≤ R2 ^ 2 * E * K * (Kf + Cphi) ^ 2 * rad ^ t := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hpow : r ^ (D - 2) * (rad / r) ^ t = r ^ (D - 2 - t) * rad ^ t := by
    rw [Real.div_rpow hrad.le hr0.le, Real.rpow_sub hr0 (D - 2) t]
    field_simp
  have hpow1 : r ^ (D - 2 - t) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr1 (by linarith)
  have hrt : 0 ≤ rad ^ t := Real.rpow_nonneg hrad.le _
  have hsq : (Kf' + Cphi') ^ 2 ≤ (R2 * m * (Kf + Cphi)) ^ 2 :=
    pow_le_pow_left₀ hsum hsum' 2
  have hrD : 0 ≤ r ^ (D - 2) := Real.rpow_nonneg hr0.le _
  have hrt' : 0 ≤ (rad / r) ^ t := Real.rpow_nonneg (div_nonneg hrad.le hr0.le) _
  calc r ^ (D - 2) * (c * L)
      ≤ r ^ (D - 2) * (c * (K * (Kf' + Cphi') ^ 2 * (rad / r) ^ t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL hc.le) hrD
    _ ≤ r ^ (D - 2) * (c * (K * (R2 * m * (Kf + Cphi)) ^ 2 * (rad / r) ^ t)) := by
        apply mul_le_mul_of_nonneg_left _ hrD
        apply mul_le_mul_of_nonneg_left _ hc.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hK) hrt'
    _ = (c * m ^ 2) * (R2 ^ 2 * K * (Kf + Cphi) ^ 2) * (r ^ (D - 2) * (rad / r) ^ t) := by
        ring
    _ = (c * m ^ 2) * (R2 ^ 2 * K * (Kf + Cphi) ^ 2) * (r ^ (D - 2 - t) * rad ^ t) := by
        rw [hpow]
    _ ≤ E * (R2 ^ 2 * K * (Kf + Cphi) ^ 2) * (1 * rad ^ t) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hcm (by positivity))
          (mul_le_mul_of_nonneg_right hpow1 hrt) (by positivity)
        exact mul_nonneg (le_trans (by positivity) hcm) (by positivity)
    _ = R2 ^ 2 * E * K * (Kf + Cphi) ^ 2 * rad ^ t := by ring

/-- `c · max(1, c⁻¹)² = max(c, c⁻¹)`. -/
theorem aux_prop_growth_large_root_mul_max_sq_le {c E : ℝ} (hc : 0 < c) (hcE : c ≤ E) (hcE' : c⁻¹ ≤ E) :
    c * (max 1 c⁻¹) ^ 2 ≤ E := by
  rcases le_total 1 c⁻¹ with h | h
  · rw [max_eq_right h, sq, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    exact hcE'
  · rw [max_eq_left h, one_pow, mul_one]
    exact hcE

end LRGMain

section LRGGrowth

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.Paper
open scoped ENNReal NNReal BigOperators ContDiff Pointwise


variable {d : ℕ}

theorem aux_prop_growth_large_root_holderTriple_double (p : ℝ) (hp : 0 < p) :
    ENNReal.HolderTriple (ENNReal.ofReal (2 * p)) (ENNReal.ofReal (2 * p))
      (ENNReal.ofReal p) := by
  constructor
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos hp,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/-- The moment half of the construction, at one order and one cutoff. -/
theorem aux_prop_growth_large_root_moment_step [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (R : ℝ) (hR : 0 ≤ R) (p : ℝ) (hp : 1 ≤ p)
    (G : BilateralField d → ℝ) (Cb : ℝ)
    (hG : MemLp G (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure)
    (hGb : eLpNorm G (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb) :
    MemLp (fun om => R * aux_prop_growth_large_root_shiftEnv M j om * G (aux_prop_growth_large_root_scaleShift j om)) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => R * aux_prop_growth_large_root_shiftEnv M j om * G (aux_prop_growth_large_root_scaleShift j om)) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (R * (eLpNorm (aux_prop_growth_large_root_shiftEnv M j) (ENNReal.ofReal (2 * p))
          (chaosSampleLaw M).toMeasure).toReal * Cb) := by
  have := aux_prop_growth_large_root_holderTriple_double p (by linarith)
  have hS := aux_prop_growth_large_root_measurePreserving_scaleShift M j
  have hE := aux_prop_growth_large_root_memLp_shiftEnv M j (2 * p) (by linarith)
  have hGS : MemLp (G ∘ aux_prop_growth_large_root_scaleShift j) (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure :=
    hG.comp_measurePreserving hS
  have hprod : MemLp (aux_prop_growth_large_root_shiftEnv M j • (G ∘ aux_prop_growth_large_root_scaleShift j)) (ENNReal.ofReal p)
      (chaosSampleLaw M).toMeasure := hE.smul hGS
  have hfun : (fun om => R * aux_prop_growth_large_root_shiftEnv M j om * G (aux_prop_growth_large_root_scaleShift j om)) =
      R • (aux_prop_growth_large_root_shiftEnv M j • (G ∘ aux_prop_growth_large_root_scaleShift j)) := by
    funext om
    change _ = R * (aux_prop_growth_large_root_shiftEnv M j om * G (aux_prop_growth_large_root_scaleShift j om))
    ring
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hprod.const_smul R
  · rw [hfun, eLpNorm_const_smul]
    have hH : eLpNorm (aux_prop_growth_large_root_shiftEnv M j • (G ∘ aux_prop_growth_large_root_scaleShift j)) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ≤
        eLpNorm (aux_prop_growth_large_root_shiftEnv M j) (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure *
          eLpNorm (G ∘ aux_prop_growth_large_root_scaleShift j) (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure :=
      eLpNorm_smul_le_mul_eLpNorm hE.aestronglyMeasurable hGS.aestronglyMeasurable
    have hcomp : eLpNorm (G ∘ aux_prop_growth_large_root_scaleShift j) (ENNReal.ofReal (2 * p))
        (chaosSampleLaw M).toMeasure =
        eLpNorm G (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure :=
      eLpNorm_comp_measurePreserving hG.aestronglyMeasurable hS
    have hEfin : eLpNorm (aux_prop_growth_large_root_shiftEnv M j) (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≠ ⊤ :=
      hE.eLpNorm_lt_top.ne
    rw [hcomp] at hH
    have hEt : 0 ≤ (eLpNorm (aux_prop_growth_large_root_shiftEnv M j) (ENNReal.ofReal (2 * p))
        (chaosSampleLaw M).toMeasure).toReal := ENNReal.toReal_nonneg
    calc ‖R‖ₑ * eLpNorm (aux_prop_growth_large_root_shiftEnv M j • (G ∘ aux_prop_growth_large_root_scaleShift j)) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure
        ≤ ENNReal.ofReal R * (ENNReal.ofReal (eLpNorm (aux_prop_growth_large_root_shiftEnv M j) (ENNReal.ofReal (2 * p))
            (chaosSampleLaw M).toMeasure).toReal * ENNReal.ofReal Cb) := by
          rw [Real.enorm_eq_ofReal hR, ENNReal.ofReal_toReal hEfin]
          exact mul_le_mul_right (hH.trans (mul_le_mul_right hGb _)) _
      _ = _ := by
          rw [← ENNReal.ofReal_mul hEt, ← ENNReal.ofReal_mul hR, mul_assoc]

end LRGGrowth

section LRGGeneral

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.Paper
open scoped ENNReal NNReal BigOperators ContDiff Pointwise


variable {d : ℕ}

/-! ## Affine identities -/

theorem aux_prop_growth_large_root_cubeDilation_comp_inv (z z0 zq : SpatialCoordinates d) {r s : ℝ} (hs : 0 < s)
    (y : SpatialCoordinates d) :
    cubeDilation z z0 r (cubeDilation z0 zq s⁻¹ y) = cubeDilation z zq (r / s) y := by
  funext i
  simp only [cubeDilation_apply]
  field_simp
  ring

theorem aux_prop_growth_large_root_cubeDilation_psi_comp (z z0 zq : SpatialCoordinates d) {r s : ℝ} (hr : 0 < r)
    (_hs : 0 < s) (x : SpatialCoordinates d) :
    cubeDilation zq z (r / s)⁻¹ (cubeDilation z z0 r x) = cubeDilation zq z0 s x := by
  funext i
  simp only [cubeDilation_apply]
  field_simp
  ring

theorem aux_prop_growth_large_root_cubeDilation_mem_closedCube_gen (z zq : SpatialCoordinates d) {r s lam : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hlam : 0 < lam) (hrs : r = lam * s)
    {y : SpatialCoordinates d} (hy : y ∈ (closedCube zq s hs : Set (SpatialCoordinates d))) :
    cubeDilation z zq lam y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
  change dist (cubeDilation z zq lam y) z ≤ r / 2
  have hy' : dist y zq ≤ s / 2 := hy
  have heq : cubeDilation z zq lam y - z = lam • (y - zq) := by
    funext i
    simp [cubeDilation_apply, Pi.smul_apply, smul_eq_mul]
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos hlam, ← dist_eq_norm, hrs]
  nlinarith

theorem aux_prop_growth_large_root_cubeDilation_inv_mem_closedCube_gen (z zq : SpatialCoordinates d) {r s lam : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hlam : 0 < lam) (hrs : r = lam * s)
    {y : SpatialCoordinates d} (hy : y ∈ (closedCube z r hr : Set (SpatialCoordinates d))) :
    cubeDilation zq z lam⁻¹ y ∈ (closedCube zq s hs : Set (SpatialCoordinates d)) := by
  change dist (cubeDilation zq z lam⁻¹ y) zq ≤ s / 2
  have hy' : dist y z ≤ r / 2 := hy
  have heq : cubeDilation zq z lam⁻¹ y - zq = lam⁻¹ • (y - z) := by
    funext i
    simp [cubeDilation_apply, Pi.smul_apply, smul_eq_mul]
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hlam),
    ← dist_eq_norm]
  calc lam⁻¹ * dist y z ≤ lam⁻¹ * (r / 2) :=
        mul_le_mul_of_nonneg_left hy' (inv_pos.2 hlam).le
    _ = s / 2 := by rw [hrs]; field_simp

/-! ## The inverse dilation is quasi-measure-preserving -/

theorem aux_prop_growth_large_root_qmp_inv (z z0 : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (cubeDilation z0 z r⁻¹)
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))) := by
  refine ⟨(continuous_cubeDilation z0 z r⁻¹).measurable, ?_⟩
  have hmap := map_cubeDilation_restrict z z0 hr one_pos
  set c : ℝ≥0∞ := ENNReal.ofReal |(r ^ d)⁻¹| with hc
  have hc0 : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.2 (inv_ne_zero (pow_ne_zero _ hr.ne'))
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hQ : volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) =
      c⁻¹ • Measure.map (cubeDilation z z0 r)
        (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))) := by
    rw [hmap, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]
  rw [hQ, Measure.map_smul _ (continuous_cubeDilation z0 z r⁻¹).measurable.aemeasurable, Measure.map_map (continuous_cubeDilation z0 z r⁻¹).measurable
    (continuous_cubeDilation z z0 r).measurable]
  have hid : (cubeDilation z0 z r⁻¹ ∘ cubeDilation z z0 r) = id := by
    funext x
    exact aux_prop_growth_large_root_cubeDilation_inv_right z z0 hr x
  rw [hid, Measure.map_id]
  exact Measure.smul_absolutelyContinuous

/-! ## Dirichlet pushforward from the unit cube -/

/-- **Dirichlet pushforward** `centeredCube z0 1 → centeredCube zq s` along the inverse of
`T' x = zq + s (x - z0)`. -/
theorem aux_prop_growth_large_root_dirichlet_pushforward (zq z0 : SpatialCoordinates d) {s : ℝ} (hs : 0 < s)
    (a : PositiveCoefficient (centeredCube zq s hs))
    (a1 : PositiveCoefficient (centeredCube z0 1 one_pos))
    (ha1 : ∀ᵐ x ∂(volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))),
      (a1.val : SpatialCoordinates d → ℝ) x =
        (a.val : SpatialCoordinates d → ℝ) (cubeDilation zq z0 s x))
    (G : SpatialCoordinates d → ℝ)
    (hG : AEMeasurable G (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))))
    (phi1 : SpatialCoordinates d → ℝ)
    (b1 v1 : weakSobolevGraph (centeredCube z0 1 one_pos))
    (htrace1 : ((b1 : SobolevData (centeredCube z0 1 one_pos)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))] phi1)
    (hsolve : SolvesDirichlet a1 G b1 v1) :
    ∃ b' v' : weakSobolevGraph (centeredCube zq s hs),
      ((b' : SobolevData (centeredCube zq s hs)).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube zq s hs : Set (SpatialCoordinates d))]
        (fun y => phi1 (cubeDilation z0 zq s⁻¹ y)) ∧
      (∀ᵐ x ∂(volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))),
        (v1 : SobolevData (centeredCube z0 1 one_pos)).1 x =
          (v' : SobolevData (centeredCube zq s hs)).1 (cubeDilation zq z0 s x)) ∧
      (∀ i : Fin d, ∀ᵐ x ∂(volume.restrict (centeredCube z0 1 one_pos :
          Set (SpatialCoordinates d))),
        ((v1 : SobolevData (centeredCube z0 1 one_pos)).2 i : SpatialCoordinates d → ℝ) x =
          s * ((v' : SobolevData (centeredCube zq s hs)).2 i : SpatialCoordinates d → ℝ)
            (cubeDilation zq z0 s x)) ∧
      AEMeasurable (fun y => (s ^ 2)⁻¹ * G (cubeDilation z0 zq s⁻¹ y))
        (volume.restrict (centeredCube zq s hs : Set (SpatialCoordinates d))) ∧
      SolvesDirichlet a (fun y => (s ^ 2)⁻¹ * G (cubeDilation z0 zq s⁻¹ y)) b' v' := by
  have hq := dilation_quasi_measure_preserving d zq z0 s hs one_pos
  have hqi := aux_prop_growth_large_root_qmp_inv zq z0 hs
  obtain ⟨b', hb'⟩ := aux_lem_as_regularity_affine_transport_weak_pushforward d zq z0 s hs
    one_pos b1
  obtain ⟨v', hv'⟩ := aux_lem_as_regularity_affine_transport_weak_pushforward d zq z0 s hs
    one_pos v1
  have hb'g := weak_gradient_chain_rule d zq z0 s hs one_pos
    (b' : SobolevData (centeredCube zq s hs)) (b1 : SobolevData (centeredCube z0 1 one_pos))
    b'.property b1.property hb'
  have hv'g := weak_gradient_chain_rule d zq z0 s hs one_pos
    (v' : SobolevData (centeredCube zq s hs)) (v1 : SobolevData (centeredCube z0 1 one_pos))
    v'.property v1.property hv'
  -- the killed difference
  let k1 : killedSobolevGraph (centeredCube z0 1 one_pos) :=
    ⟨(v1 : SobolevData (centeredCube z0 1 one_pos)) -
      (b1 : SobolevData (centeredCube z0 1 one_pos)), hsolve.1⟩
  obtain ⟨k', hk'⟩ := aux_lem_as_regularity_affine_transport_killed_pushforward d zq z0 s hs
    one_pos k1
  have hk'g := weak_gradient_chain_rule d zq z0 s hs one_pos
    (k' : SobolevData (centeredCube zq s hs)) (k1 : SobolevData (centeredCube z0 1 one_pos))
    (killedSobolevGraph_le_weakSobolevGraph k'.property)
    (killedSobolevGraph_le_weakSobolevGraph k1.property) hk'
  have hdiff : (v' : SobolevData (centeredCube zq s hs)) -
      (b' : SobolevData (centeredCube zq s hs)) = (k' : SobolevData (centeredCube zq s hs)) := by
    apply aux_lem_as_regularity_affine_transport_sobolevData_eq_of_ae
    · apply aux_prop_growth_large_root_ae_root_of_ae_unit zq z0 hs
        (p := fun y => (((v' : SobolevData (centeredCube zq s hs)) -
          (b' : SobolevData (centeredCube zq s hs))).1 : SpatialCoordinates d → ℝ) y =
          ((k' : SobolevData (centeredCube zq s hs)).1 : SpatialCoordinates d → ℝ) y)
      filter_upwards [hq.ae (Lp.coeFn_sub ((v' : SobolevData (centeredCube zq s hs)).1)
          ((b' : SobolevData (centeredCube zq s hs)).1)),
        Lp.coeFn_sub ((v1 : SobolevData (centeredCube z0 1 one_pos)).1)
          ((b1 : SobolevData (centeredCube z0 1 one_pos)).1), hb', hv', hk'] with
        x hsub hsub1 hbx hvx hkx
      have e1 : (((v' : SobolevData (centeredCube zq s hs)) -
          (b' : SobolevData (centeredCube zq s hs))).1 : SpatialCoordinates d → ℝ)
          (cubeDilation zq z0 s x) =
          (((v' : SobolevData (centeredCube zq s hs)).1 -
            (b' : SobolevData (centeredCube zq s hs)).1 : DomainL2 (centeredCube zq s hs)) :
              SpatialCoordinates d → ℝ) (cubeDilation zq z0 s x) := rfl
      rw [e1, hsub, Pi.sub_apply, ← hvx, ← hbx, ← hkx]
      change _ = ((((v1 : SobolevData (centeredCube z0 1 one_pos)).1 -
        (b1 : SobolevData (centeredCube z0 1 one_pos)).1 : DomainL2 (centeredCube z0 1 one_pos)) :
          SpatialCoordinates d → ℝ) x)
      rw [hsub1, Pi.sub_apply]
    · intro i
      apply aux_prop_growth_large_root_ae_root_of_ae_unit zq z0 hs
        (p := fun y => ((((v' : SobolevData (centeredCube zq s hs)) -
          (b' : SobolevData (centeredCube zq s hs))).2 i : DomainL2 (centeredCube zq s hs)) :
            SpatialCoordinates d → ℝ) y =
          (((k' : SobolevData (centeredCube zq s hs)).2 i : DomainL2 (centeredCube zq s hs)) :
            SpatialCoordinates d → ℝ) y)
      filter_upwards [hq.ae (Lp.coeFn_sub ((v' : SobolevData (centeredCube zq s hs)).2 i)
          ((b' : SobolevData (centeredCube zq s hs)).2 i)),
        Lp.coeFn_sub ((v1 : SobolevData (centeredCube z0 1 one_pos)).2 i)
          ((b1 : SobolevData (centeredCube z0 1 one_pos)).2 i), hb'g i, hv'g i, hk'g i] with
        x hsub hsub1 hbx hvx hkx
      have e1 : ((((v' : SobolevData (centeredCube zq s hs)) -
          (b' : SobolevData (centeredCube zq s hs))).2 i : DomainL2 (centeredCube zq s hs)) :
            SpatialCoordinates d → ℝ) (cubeDilation zq z0 s x) =
          ((((v' : SobolevData (centeredCube zq s hs)).2 i -
            (b' : SobolevData (centeredCube zq s hs)).2 i : DomainL2 (centeredCube zq s hs))) :
              SpatialCoordinates d → ℝ) (cubeDilation zq z0 s x) := rfl
      rw [e1, hsub, Pi.sub_apply]
      have hkx' : ((k1 : SobolevData (centeredCube z0 1 one_pos)).2 i : SpatialCoordinates d → ℝ) x =
          ((((v1 : SobolevData (centeredCube z0 1 one_pos)).2 i -
            (b1 : SobolevData (centeredCube z0 1 one_pos)).2 i : DomainL2 (centeredCube z0 1 one_pos))) :
              SpatialCoordinates d → ℝ) x := rfl
      rw [hsub1, Pi.sub_apply] at hkx'
      change (sobolevGradient (k1 : SobolevData (centeredCube z0 1 one_pos)) i) x = _ at hkx
      change (sobolevGradient (v1 : SobolevData (centeredCube z0 1 one_pos)) i) x = _ at hvx
      change (sobolevGradient (b1 : SobolevData (centeredCube z0 1 one_pos)) i) x = _ at hbx
      have e2 : (sobolevGradient (k1 : SobolevData (centeredCube z0 1 one_pos)) i) x =
          (sobolevGradient (v1 : SobolevData (centeredCube z0 1 one_pos)) i) x -
            (sobolevGradient (b1 : SobolevData (centeredCube z0 1 one_pos)) i) x := hkx'
      rw [hkx, hvx, hbx] at e2
      change _ = (sobolevGradient (k' : SobolevData (centeredCube zq s hs)) i)
        (cubeDilation zq z0 s x)
      apply mul_left_cancel₀ hs.ne'
      rw [e2, mul_sub]
      rfl
  refine ⟨b', v', ?_, hv', hv'g, ?_, ?_⟩
  · apply aux_prop_growth_large_root_ae_root_of_ae_unit zq z0 hs
      (p := fun y => ((b' : SobolevData (centeredCube zq s hs)).1 : SpatialCoordinates d → ℝ) y =
        phi1 (cubeDilation z0 zq s⁻¹ y))
    filter_upwards [hb', htrace1] with x hbx htx
    rw [aux_prop_growth_large_root_cubeDilation_inv_right zq z0 hs x, ← hbx, htx]
  · exact (hG.comp_quasiMeasurePreserving hqi).const_mul _
  · refine ⟨?_, fun psi => ?_⟩
    · rw [hdiff]; exact k'.property
    obtain ⟨psi1, hpsi1, -⟩ := aux_lem_as_regularity_affine_transport_killed_pullback d zq z0 s
      hs one_pos psi
    let psiW : weakSobolevGraph (centeredCube zq s hs) :=
      ⟨psi.val, killedSobolevGraph_le_weakSobolevGraph psi.property⟩
    let psi1W : weakSobolevGraph (centeredCube z0 1 one_pos) :=
      ⟨psi1.val, killedSobolevGraph_le_weakSobolevGraph psi1.property⟩
    have hform := aux_lem_as_regularity_affine_transport_form_scaling d zq z0 s hs one_pos
      a a1 v' psiW v1 psi1W ha1 hv' hpsi1
    have hsol := hsolve.2 psi1
    let f : SpatialCoordinates d → ℝ := fun y =>
      (s ^ 2)⁻¹ * G (cubeDilation z0 zq s⁻¹ y) * (psi : SobolevData (centeredCube zq s hs)).1 y
    have hf : AEMeasurable f
        (volume.restrict (centeredCube zq s hs : Set (SpatialCoordinates d))) :=
      ((hG.comp_quasiMeasurePreserving hqi).const_mul _).mul
        (Lp.aestronglyMeasurable (psi : SobolevData (centeredCube zq s hs)).1).aemeasurable
    have hscale := aux_lem_as_regularity_affine_transport_integral_scaling d zq z0 s hs
      one_pos f hf
    have hbase : (∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        f (cubeDilation zq z0 s x)) = (s ^ 2)⁻¹ *
          ∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
            G x * (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hpsi1] with x hx
      simp only [f]
      rw [aux_prop_growth_large_root_cubeDilation_inv_right zq z0 hs x, hx]
      ring
    have hpow := aux_lem_as_regularity_affine_transport_pow_split d s hs
    change sobolevCoefficientForm a (v' : SobolevData (centeredCube zq s hs))
      (psiW : SobolevData (centeredCube zq s hs)) = ∫ y in (centeredCube zq s hs :
        Set (SpatialCoordinates d)), f y
    rw [hform, hsol]
    have hsd : (s ^ d : ℝ) ≠ 0 := pow_ne_zero _ hs.ne'
    calc s ^ ((d : ℝ) - 2) * ∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
          G x * (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 x
        = s ^ d * ((s ^ 2)⁻¹ * ∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
          G x * (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 x) := by
          rw [hpow]; field_simp
      _ = s ^ d * ((s ^ d)⁻¹ * ∫ y in (centeredCube zq s hs : Set (SpatialCoordinates d)),
          f y) := by rw [← hbase, hscale]
      _ = _ := by field_simp

/-! ## Datum and Hölder transports between cubes of sides `s` and `r = λ s` -/

theorem aux_prop_growth_large_root_c2Norm_comp_le (z zq : SpatialCoordinates d) {r s lam : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hlam : 0 < lam) (hrs : r = lam * s) (phi : SpatialCoordinates d → ℝ)
    (hphi : ContDiff ℝ 2 phi) (Cphi : ℝ)
    (hCphi : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi) :
    c2Norm (closedCube zq s hs : Set (SpatialCoordinates d))
      (fun x => phi (cubeDilation z zq lam x)) ≤ (1 + lam + lam ^ 2) * Cphi := by
  have hmap : ∀ x ∈ (closedCube zq s hs : Set (SpatialCoordinates d)),
      cubeDilation z zq lam x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) :=
    fun x hx => aux_prop_growth_large_root_cubeDilation_mem_closedCube_gen z zq hr hs hlam hrs hx
  have hz : z ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    change dist z z ≤ r / 2
    simp only [dist_self]
    linarith
  have hz' : zq ∈ (closedCube zq s hs : Set (SpatialCoordinates d)) := by
    change dist zq zq ≤ s / 2
    simp only [dist_self]
    linarith
  have hcompact : IsCompact (closedCube z r hr : Set (SpatialCoordinates d)) :=
    (closedCube z r hr).isCompact
  have hbdd0 := aux_lem_as_regularity_affine_transport_sup_bdd
    (closedCube z r hr : Set (SpatialCoordinates d)) hcompact (fun x => |phi x|)
    (continuous_abs.comp hphi.continuous)
  have hfd : ContDiff ℝ 1 (fderiv ℝ phi) :=
    (contDiff_succ_iff_fderiv.mp hphi).2.2
  have hbdd1 := aux_lem_as_regularity_affine_transport_sup_bdd
    (closedCube z r hr : Set (SpatialCoordinates d)) hcompact
    (fun x => ‖fderiv ℝ phi x‖)
    (continuous_norm.comp (hphi.continuous_fderiv (by norm_num)))
  have hbdd2 := aux_lem_as_regularity_affine_transport_sup_bdd
    (closedCube z r hr : Set (SpatialCoordinates d)) hcompact
    (fun x => ‖fderiv ℝ (fderiv ℝ phi) x‖)
    (continuous_norm.comp (hfd.continuous_fderiv (by norm_num)))
  obtain ⟨_, _, hderiv_bound, hsecond_bound⟩ :=
    aux_lem_as_regularity_affine_transport_c2_chain_rule d z zq lam hlam phi hphi
  have ht0 := aux_lem_as_regularity_affine_transport_sup_comp_le
    (closedCube zq s hs : Set (SpatialCoordinates d))
    (closedCube z r hr : Set (SpatialCoordinates d)) (cubeDilation z zq lam)
    (fun x => |phi (cubeDilation z zq lam x)|) (fun x => |phi x|) 1
    ⟨zq, hz'⟩ (by norm_num) hmap hbdd0 (by intro x hx; simp)
  have ht1 := aux_lem_as_regularity_affine_transport_sup_comp_le
    (closedCube zq s hs : Set (SpatialCoordinates d))
    (closedCube z r hr : Set (SpatialCoordinates d)) (cubeDilation z zq lam)
    (fun x => ‖fderiv ℝ (fun y => phi (cubeDilation z zq lam y)) x‖)
    (fun x => ‖fderiv ℝ phi x‖) lam
    ⟨zq, hz'⟩ hlam.le hmap hbdd1 (by intro x hx; exact hderiv_bound x)
  have ht2 := aux_lem_as_regularity_affine_transport_sup_comp_le
    (closedCube zq s hs : Set (SpatialCoordinates d))
    (closedCube z r hr : Set (SpatialCoordinates d)) (cubeDilation z zq lam)
    (fun x => ‖fderiv ℝ (fderiv ℝ (fun y => phi (cubeDilation z zq lam y))) x‖)
    (fun x => ‖fderiv ℝ (fderiv ℝ phi) x‖) (lam ^ 2)
    ⟨zq, hz'⟩ (sq_nonneg lam) hmap hbdd2 (by intro x hx; exact hsecond_bound x)
  change
    sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), v = |phi x|} +
        sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          v = ‖fderiv ℝ phi x‖} +
        sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          v = ‖fderiv ℝ (fderiv ℝ phi) x‖} ≤ Cphi at hCphi
  change
    sSup {v : ℝ | ∃ x ∈ (closedCube zq s hs : Set (SpatialCoordinates d)),
        v = |phi (cubeDilation z zq lam x)|} +
      sSup {v : ℝ | ∃ x ∈ (closedCube zq s hs : Set (SpatialCoordinates d)),
        v = ‖fderiv ℝ (fun y => phi (cubeDilation z zq lam y)) x‖} +
      sSup {v : ℝ | ∃ x ∈ (closedCube zq s hs : Set (SpatialCoordinates d)),
        v = ‖fderiv ℝ (fderiv ℝ (fun y => phi (cubeDilation z zq lam y))) x‖} ≤
      (1 + lam + lam ^ 2) * Cphi
  have hs0 : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = |phi x|} :=
    (abs_nonneg (phi z)).trans (le_csSup hbdd0 ⟨z, hz, rfl⟩)
  have hs1 : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = ‖fderiv ℝ phi x‖} :=
    (norm_nonneg (fderiv ℝ phi z)).trans (le_csSup hbdd1 ⟨z, hz, rfl⟩)
  have hs2 : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = ‖fderiv ℝ (fderiv ℝ phi) x‖} :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ phi) z)).trans (le_csSup hbdd2 ⟨z, hz, rfl⟩)
  have hfac : 0 ≤ 1 + lam + lam ^ 2 := by positivity
  have hweighted :
      sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), v = |phi x|} +
          lam * sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
            v = ‖fderiv ℝ phi x‖} +
          lam ^ 2 * sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
            v = ‖fderiv ℝ (fderiv ℝ phi) x‖} ≤
        (1 + lam + lam ^ 2) *
          (sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), v = |phi x|} +
            sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              v = ‖fderiv ℝ phi x‖} +
            sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              v = ‖fderiv ℝ (fderiv ℝ phi) x‖}) := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ lam + lam ^ 2) hs0,
      mul_nonneg (by positivity : 0 ≤ 1 + lam ^ 2) hs1,
      mul_nonneg (by positivity : 0 ≤ 1 + lam) hs2]
  nlinarith [ht0, ht1, ht2, hweighted, mul_le_mul_of_nonneg_left hCphi hfac]

/-- **Hölder transport** from the cube of side `s` to the root of side `r = λ s`, `λ ≥ 1`. -/
theorem aux_prop_growth_large_root_holder_transport_gen (z zq : SpatialCoordinates d) {r s lam : ℝ} (hr : 0 < r)
    (hs : 0 < s) (hlam1 : 1 ≤ lam) (hrs : r = lam * s)
    {alpha : ℝ} (halpha : 0 ≤ alpha) (U1 : SpatialCoordinates d → ℝ) (hU1c : Continuous U1)
    (hU1h : IsHolderOn alpha (closedCube zq s hs : Set (SpatialCoordinates d)) U1) :
    let U : SpatialCoordinates d → ℝ := fun y => U1 (cubeDilation zq z lam⁻¹ y)
    Continuous U ∧
      IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
      cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
        cAlphaNorm alpha (closedCube zq s hs : Set (SpatialCoordinates d)) U1 := by
  intro U
  have hlam : 0 < lam := lt_of_lt_of_le one_pos hlam1
  have hUc : Continuous U := hU1c.comp (continuous_cubeDilation zq z lam⁻¹)
  have hinvpos : 0 < lam⁻¹ := inv_pos.2 hlam
  have hinj : ∀ x, cubeDilation z zq lam (cubeDilation zq z lam⁻¹ x) = x := by
    intro x; funext i; simp only [cubeDilation_apply]; field_simp; ring
  have hratio : ∀ v ∈ holderRatioSet alpha (closedCube z r hr : Set (SpatialCoordinates d)) U,
      ∃ w ∈ holderRatioSet alpha (closedCube zq s hs : Set (SpatialCoordinates d)) U1,
        v ≤ w := by
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    set x' := cubeDilation zq z lam⁻¹ x
    set y' := cubeDilation zq z lam⁻¹ y
    have hx'y' : x' ≠ y' := by
      intro h
      apply hxy
      rw [← hinj x, ← hinj y]
      exact congrArg _ h
    have hdist := sqrt_sum_sq_cubeDilation zq z hinvpos x y
    refine ⟨|U1 x' - U1 y'| / (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ alpha,
      ⟨x', aux_prop_growth_large_root_cubeDilation_inv_mem_closedCube_gen z zq hr hs hlam hrs hx, y',
        aux_prop_growth_large_root_cubeDilation_inv_mem_closedCube_gen z zq hr hs hlam hrs hy, hx'y', rfl⟩, ?_⟩
    have hs0 : 0 < Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2) := by
      apply Real.sqrt_pos.2
      obtain ⟨i, hi⟩ : ∃ i, x' i ≠ y' i := by
        by_contra hne
        push Not at hne
        exact hx'y' (funext hne)
      exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _)
          (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hi))))
        (Finset.single_le_sum (f := fun j => (x' j - y' j) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i))
    have hS : Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) =
        lam * Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2) := by
      rw [hdist]; field_simp
    change |U1 x' - U1 y'| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ≤ _
    rw [hS]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (Real.rpow_pos_of_pos hs0 _)
    rw [Real.mul_rpow hlam.le hs0.le]
    exact le_mul_of_one_le_left (Real.rpow_nonneg hs0.le _) (Real.one_le_rpow hlam1 halpha)
  have hratio0 : ∀ w ∈ holderRatioSet alpha (closedCube zq s hs :
      Set (SpatialCoordinates d)) U1, 0 ≤ w := by
    rintro w ⟨x, -, y, -, -, rfl⟩
    exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  obtain ⟨hbdd, hsup⟩ := aux_prop_growth_large_root_sSup_le_sSup_of_dominated hU1h hratio0 hratio
  have hval : ∀ v ∈ {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = |U x|}, ∃ w ∈ {v : ℝ | ∃ x ∈ (closedCube zq s hs : Set (SpatialCoordinates d)),
      v = |U1 x|}, v ≤ w := by
    rintro v ⟨x, hx, rfl⟩
    exact ⟨|U1 (cubeDilation zq z lam⁻¹ x)|,
      ⟨_, aux_prop_growth_large_root_cubeDilation_inv_mem_closedCube_gen z zq hr hs hlam hrs hx, rfl⟩, le_rfl⟩
  have hvalbdd : BddAbove {v : ℝ | ∃ x ∈ (closedCube zq s hs : Set (SpatialCoordinates d)),
      v = |U1 x|} :=
    aux_lem_as_regularity_affine_transport_sup_bdd _ (closedCube zq s hs).isCompact
      (fun x => |U1 x|) (continuous_abs.comp hU1c)
  have hval0 : ∀ w ∈ {v : ℝ | ∃ x ∈ (closedCube zq s hs : Set (SpatialCoordinates d)),
      v = |U1 x|}, 0 ≤ w := by
    rintro w ⟨x, -, rfl⟩
    exact abs_nonneg _
  obtain ⟨-, hvsup⟩ := aux_prop_growth_large_root_sSup_le_sSup_of_dominated hvalbdd hval0 hval
  refine ⟨hUc, hbdd, ?_⟩
  unfold cAlphaNorm holderSeminorm
  exact add_le_add hvsup hsup

end LRGGeneral

section LRGLarge

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.Paper
open scoped ENNReal NNReal BigOperators ContDiff Pointwise


variable {d : ℕ}

theorem aux_prop_growth_large_root_sum_real {c lam Kf Cphi m : ℝ} (hlam : 0 ≤ lam) (hKf : 0 ≤ Kf) (hC : 0 ≤ Cphi)
    (hmc : c⁻¹ ≤ m) (hm1 : 1 ≤ m) :
    c⁻¹ * (lam ^ 2 * Kf) + (1 + lam + lam ^ 2) * Cphi ≤
      (1 + lam + lam ^ 2) * m * (Kf + Cphi) := by
  have hR : 0 ≤ 1 + lam + lam ^ 2 := by positivity
  have hl : lam ^ 2 ≤ 1 + lam + lam ^ 2 := by linarith
  have h1 : c⁻¹ * (lam ^ 2 * Kf) ≤ m * ((1 + lam + lam ^ 2) * Kf) :=
    mul_le_mul hmc (mul_le_mul_of_nonneg_right hl hKf) (by positivity)
      (le_trans zero_le_one hm1)
  have h2 : (1 + lam + lam ^ 2) * Cphi ≤ m * ((1 + lam + lam ^ 2) * Cphi) :=
    le_mul_of_one_le_left (mul_nonneg hR hC) hm1
  calc c⁻¹ * (lam ^ 2 * Kf) + (1 + lam + lam ^ 2) * Cphi
      ≤ m * ((1 + lam + lam ^ 2) * Kf) + m * ((1 + lam + lam ^ 2) * Cphi) := add_le_add h1 h2
    _ = (1 + lam + lam ^ 2) * m * (Kf + Cphi) := by ring

theorem aux_prop_growth_large_root_holder_real {K lam m E X : ℝ} (hK : 0 ≤ K) (hlam : 0 ≤ lam) (hm0 : 0 ≤ m)
    (hmE : m ≤ E) (hX : 0 ≤ X) :
    K * ((1 + lam + lam ^ 2) * m * X) ≤ (1 + lam + lam ^ 2) ^ 2 * E * K * X := by
  have hR1 : 1 ≤ 1 + lam + lam ^ 2 := by nlinarith
  have hRR : 1 + lam + lam ^ 2 ≤ (1 + lam + lam ^ 2) ^ 2 := by nlinarith
  have hRm : (1 + lam + lam ^ 2) * m ≤ (1 + lam + lam ^ 2) ^ 2 * E :=
    mul_le_mul hRR hmE hm0 (by positivity)
  calc K * ((1 + lam + lam ^ 2) * m * X) = K * X * ((1 + lam + lam ^ 2) * m) := by ring
    _ ≤ K * X * ((1 + lam + lam ^ 2) ^ 2 * E) :=
        mul_le_mul_of_nonneg_left hRm (mul_nonneg hK hX)
    _ = (1 + lam + lam ^ 2) ^ 2 * E * K * X := by ring

/-- **General deterministic transfer**: root of side `r = λ s` (`λ ≥ 1`) from the cube of
side `s`, through the unit cube `centeredCube z0 1`. -/
theorem aux_prop_growth_large_root_growthAt_transfer_gen {z z0 zq : SpatialCoordinates d} {r s lam : ℝ} (hr : 0 < r)
    (hs : 0 < s) (hlam1 : 1 ≤ lam) (hrs : r = lam * s)
    {t alpha : ℝ} (ht : (d : ℝ) - 2 < t) (halpha : 0 ≤ alpha)
    (A : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A' : ℕ → PositiveCoefficient (centeredCube zq s hs))
    (c : ℕ → ℝ) (E : ℝ) (hc : ∀ N, 0 < c N) (hcE : ∀ N, c N ≤ E) (hcE' : ∀ N, (c N)⁻¹ ≤ E)
    (hE1 : 1 ≤ E)
    (hcoef : ∀ N, ∀ᵐ x ∂(volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))),
      ((A N).val : SpatialCoordinates d → ℝ) (cubeDilation z z0 r x) =
        c N * ((A' N).val : SpatialCoordinates d → ℝ) (cubeDilation zq z0 s x))
    (K' : ℕ → ℝ) (hK1 : ∀ N, 1 ≤ K' N)
    (hG : aux_prop_growth_large_root_GrowthAtCoef zq s hs t alpha A' K') :
    aux_prop_growth_large_root_GrowthAtCoef z r hr t alpha A (fun N => (1 + lam + lam ^ 2) ^ 2 * E * K' N) := by
  intro N F Kf hKf hF hFb phi Cphi hphi hCphi b u htrace hsolve
  have hlam : 0 < lam := lt_of_lt_of_le one_pos hlam1
  have hlamrs : r / s = lam := by rw [hrs]; field_simp
  have hcN := hc N
  have hcinv : 0 < (c N)⁻¹ := inv_pos.2 hcN
  have hdct := _root_.SubdiffusiveProcess.Paper.dilation_coefficient_transport d z z0 r hr one_pos (A N)
  obtain ⟨a1, ha1⟩ := hdct
  have hdct' := _root_.SubdiffusiveProcess.Paper.dilation_coefficient_transport d zq z0 s hs one_pos (A' N)
  obtain ⟨a1', ha1'⟩ := hdct'
  have hscale : ∀ᵐ x ∂(volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))),
      (a1.val : SpatialCoordinates d → ℝ) x = c N * (a1'.val : SpatialCoordinates d → ℝ) x := by
    filter_upwards [ha1, ha1', hcoef N] with x h1 h2 h3
    rw [h1, h2, h3]
  have htr := aux_prop_growth_large_root_dirichlet_transport z z0 r hr (A N) a1 ha1 F Kf hKf hF hFb phi Cphi hphi hCphi
    b u htrace hsolve
  obtain ⟨F1, phi1, b1, u1, -, hF1m, hF1b, hphi1def, -, -, htrace1, hsolve1,
    -, hu1, -, henergy⟩ := htr
  have hsolve' := aux_prop_growth_large_root_solvesDirichlet_scale a1 a1' (c N) hcN hscale F1 b1 u1 hsolve1
  have hpf := aux_prop_growth_large_root_dirichlet_pushforward zq z0 hs (A' N) a1' ha1' (fun x => (c N)⁻¹ * F1 x)
    (hF1m.const_mul _) phi1 b1 u1 htrace1 hsolve'
  obtain ⟨b', v', htr', hv', hv'g, hG'm, hsolveQ⟩ := hpf
  -- the pushed source and datum
  have hKf' : 0 ≤ (s ^ 2)⁻¹ * ((c N)⁻¹ * (r ^ 2 * Kf)) := by positivity
  have hG'b : ∀ᵐ y ∂(volume.restrict (centeredCube zq s hs : Set (SpatialCoordinates d))),
      |(s ^ 2)⁻¹ * ((c N)⁻¹ * F1 (cubeDilation z0 zq s⁻¹ y))| ≤
        (s ^ 2)⁻¹ * ((c N)⁻¹ * (r ^ 2 * Kf)) := by
    apply aux_prop_growth_large_root_ae_root_of_ae_unit zq z0 hs
      (p := fun y => |(s ^ 2)⁻¹ * ((c N)⁻¹ * F1 (cubeDilation z0 zq s⁻¹ y))| ≤
        (s ^ 2)⁻¹ * ((c N)⁻¹ * (r ^ 2 * Kf)))
    filter_upwards [hF1b] with x hx
    rw [aux_prop_growth_large_root_cubeDilation_inv_right zq z0 hs x, abs_mul, abs_mul, abs_of_pos (inv_pos.2 (by positivity)),
      abs_of_pos hcinv]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx hcinv.le)
      (inv_pos.2 (by positivity)).le
  have hphieq : (fun y => phi1 (cubeDilation z0 zq s⁻¹ y)) =
      fun y => phi (cubeDilation z zq lam y) := by
    funext y
    rw [hphi1def]
    show phi (cubeDilation z z0 r (cubeDilation z0 zq s⁻¹ y)) = phi (cubeDilation z zq lam y)
    rw [aux_prop_growth_large_root_cubeDilation_comp_inv z z0 zq hs y, hlamrs]
  have hphi' : ContDiff ℝ 2 (fun y => phi1 (cubeDilation z0 zq s⁻¹ y)) := by
    rw [hphieq]
    exact (aux_lem_as_regularity_affine_transport_c2_chain_rule d z zq lam hlam phi hphi).1
  have hc2' : c2Norm (closedCube zq s hs : Set (SpatialCoordinates d))
      (fun y => phi1 (cubeDilation z0 zq s⁻¹ y)) ≤ (1 + lam + lam ^ 2) * Cphi := by
    rw [hphieq]
    exact aux_prop_growth_large_root_c2Norm_comp_le z zq hr hs hlam hrs phi hphi Cphi hCphi
  have hG1 := hG N (fun y => (s ^ 2)⁻¹ * ((c N)⁻¹ * F1 (cubeDilation z0 zq s⁻¹ y)))
    ((s ^ 2)⁻¹ * ((c N)⁻¹ * (r ^ 2 * Kf))) hKf' hG'm hG'b
    (fun y => phi1 (cubeDilation z0 zq s⁻¹ y)) ((1 + lam + lam ^ 2) * Cphi) hphi' hc2'
    b' v' htr' hsolveQ
  obtain ⟨hGe, hGh⟩ := hG1
  -- the real bookkeeping
  have hCphi0 : 0 ≤ Cphi := (aux_prop_growth_large_root_c2Norm_nonneg' _ _).trans hCphi
  have hKfeq : (s ^ 2)⁻¹ * ((c N)⁻¹ * (r ^ 2 * Kf)) = (c N)⁻¹ * (lam ^ 2 * Kf) := by
    rw [hrs]; field_simp
  set m : ℝ := max 1 (c N)⁻¹ with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmc : (c N)⁻¹ ≤ m := le_max_right _ _
  have hmE : m ≤ E := max_le hE1 (hcE' N)
  have hcm : c N * m ^ 2 ≤ E := aux_prop_growth_large_root_mul_max_sq_le hcN (hcE N) (hcE' N)
  have hsum0 : 0 ≤ (s ^ 2)⁻¹ * ((c N)⁻¹ * (r ^ 2 * Kf)) + (1 + lam + lam ^ 2) * Cphi := by
    positivity
  have hsum : (s ^ 2)⁻¹ * ((c N)⁻¹ * (r ^ 2 * Kf)) + (1 + lam + lam ^ 2) * Cphi ≤
      (1 + lam + lam ^ 2) * m * (Kf + Cphi) := by
    rw [hKfeq]
    exact aux_prop_growth_large_root_sum_real hlam.le hKf hCphi0 hmc hm1
  have hK'0 : 0 ≤ K' N := le_trans zero_le_one (hK1 N)
  refine ⟨?_, ?_⟩
  · -- energy at every radius `≤ 1`
    intro x rad hx hrad0 hrad1
    have hx1 := aux_prop_growth_large_root_cubeDilation_inv_mem_centeredCube z z0 hr hx
    have hTx : cubeDilation z z0 r (cubeDilation z0 z r⁻¹ x) = x :=
      aux_prop_growth_large_root_cubeDilation_inv_left z z0 hr x
    have hρ0 : 0 < rad / r := div_pos hrad0 hr
    have hE := henergy (cubeDilation z0 z r⁻¹ x) (rad / r) hρ0
    have hrr : r * (rad / r) = rad := by field_simp
    rw [hTx, hrr] at hE
    have hloc := aux_prop_growth_large_root_localGradientEnergy_scale a1 a1' (c N) hscale
      (Metric.isOpen_ball.measurableSet.inter (centeredCube z0 1 one_pos).isOpen.measurableSet)
      (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos)))
      (s := Metric.ball (cubeDilation z0 z r⁻¹ x) (rad / r) ∩
        (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
    have hloc2 := aux_lem_as_regularity_affine_transport_local_energy_scaling d zq z0 s hs
      one_pos (A' N) a1' (sobolevGradient (v' : SobolevData (centeredCube zq s hs)))
      (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos))) ha1' hv'g
      (cubeDilation z0 z r⁻¹ x) (rad / r) hρ0
    have hsρ : s * (rad / r) = rad / lam := by rw [hrs]; field_simp
    rw [hsρ] at hloc2
    have hmem' := cubeDilation_mapsTo zq z0 hs one_pos _ hx1
    have hρ0' : 0 < rad / lam := div_pos hrad0 hlam
    have hρ1' : rad / lam ≤ 1 := (div_le_one hlam).2 (hrad1.trans hlam1)
    have hGx := hGe (cubeDilation zq z0 s (cubeDilation z0 z r⁻¹ x)) (rad / lam) hmem' hρ0' hρ1'
    have hpowrs : r ^ ((d : ℝ) - 2) * s ^ ((2 : ℝ) - (d : ℝ)) = lam ^ ((d : ℝ) - 2) := by
      rw [hrs, Real.mul_rpow hlam.le hs.le, mul_assoc, ← Real.rpow_add hs]
      norm_num
    have hinv : localGradientEnergy (A N)
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z r hr))) =
        lam ^ ((d : ℝ) - 2) * (c N * localGradientEnergy (A' N)
          (s := Metric.ball (cubeDilation zq z0 s (cubeDilation z0 z r⁻¹ x)) (rad / lam) ∩
            (centeredCube zq s hs : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube zq s hs).isOpen.measurableSet)
          (sobolevGradient (v' : SobolevData (centeredCube zq s hs)))) := by
      have h1 : localGradientEnergy (A N)
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) =
          r ^ ((d : ℝ) - 2) * localGradientEnergy a1
            (s := Metric.ball (cubeDilation z0 z r⁻¹ x) (rad / r) ∩
              (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
            (Metric.isOpen_ball.measurableSet.inter
              (centeredCube z0 1 one_pos).isOpen.measurableSet)
            (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos))) := by
        rw [hE, ← mul_assoc, ← Real.rpow_add hr]
        norm_num
      rw [h1, hloc, hloc2, ← hpowrs]
      ring
    rw [hinv]
    exact aux_prop_growth_large_root_energy_real hlam1 hcN hcm hK'0 hsum0 hsum hrad0 ht hGx
  · -- the Hölder representative
    obtain ⟨U1, hU1c, hU1u, hU1h, hU1n⟩ := hGh
    have hht := aux_prop_growth_large_root_holder_transport_gen z zq hr hs hlam1 hrs halpha U1 hU1c hU1h
    obtain ⟨hUc, hUh, hUn⟩ := hht
    have hq' := dilation_quasi_measure_preserving d zq z0 s hs one_pos
    refine ⟨fun y => U1 (cubeDilation zq z lam⁻¹ y), hUc, ?_, hUh, ?_⟩
    · apply aux_prop_growth_large_root_ae_root_of_ae_unit z z0 hr
        (p := fun y => ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) y =
          U1 (cubeDilation zq z lam⁻¹ y))
      filter_upwards [hu1, hv', hq'.ae hU1u] with x h1 h2 h3
      rw [← hlamrs, aux_prop_growth_large_root_cubeDilation_psi_comp z z0 zq hr hs x, ← h1, h2, h3]
    · refine hUn.trans (hU1n.trans ?_)
      exact (mul_le_mul_of_nonneg_left hsum hK'0).trans
        (aux_prop_growth_large_root_holder_real hK'0 hlam.le (le_trans zero_le_one hm1) hmE (add_nonneg hKf hCphi0))

/-! ## The coefficient identity on the unit cube -/

theorem aux_prop_growth_large_root_cubeDilation_origin (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (x : SpatialCoordinates d) : cubeDilation z (r⁻¹ • z) r x = r • x := by
  funext i
  rw [cubeDilation_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem aux_prop_growth_large_root_coeff_pullback_gen [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (j N : ℕ)
    (hIR : aux_prop_growth_large_root_IRShiftAt H j om) (z : SpatialCoordinates d) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hrs : r = (3 : ℝ) ^ j * s) :
    ∀ᵐ x ∂volume.restrict (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N z hr).val (cubeDilation z (r⁻¹ • z) r x) =
        aux_prop_growth_large_root_shiftConst M j N om *
          (cutoffPositiveCoefficient M H (aux_prop_growth_large_root_scaleShift j om) (N + j) (((3 : ℝ) ^ j)⁻¹ • z)
            hs).val (cubeDilation (((3 : ℝ) ^ j)⁻¹ • z) (r⁻¹ • z) s x) := by
  have hq := _root_.SubdiffusiveProcess.Paper.dilation_quasi_measure_preserving d z (r⁻¹ • z) r hr one_pos
  have hq' := _root_.SubdiffusiveProcess.Paper.dilation_quasi_measure_preserving d (((3 : ℝ) ^ j)⁻¹ • z)
    (r⁻¹ • z) s hs one_pos
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hT' : ∀ x : SpatialCoordinates d,
      cubeDilation (((3 : ℝ) ^ j)⁻¹ • z) (r⁻¹ • z) s x = s • x := by
    intro x
    funext i
    rw [cubeDilation_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hrs]
    field_simp
    ring
  filter_upwards [hq.ae (aux_prop_growth_large_root_cutoffPositiveCoefficient_val_ae M H om N z hr),
    hq'.ae (aux_prop_growth_large_root_cutoffPositiveCoefficient_val_ae M H (aux_prop_growth_large_root_scaleShift j om) (N + j)
      (((3 : ℝ) ^ j)⁻¹ • z) hs)] with x hx hx'
  rw [hx, hx', aux_prop_growth_large_root_cubeDilation_origin z hr x, hT' x]
  have hrx : r • x = ((3 : ℝ) ^ j) • (s • x) := by rw [smul_smul, hrs]
  rw [hrx]
  exact aux_prop_growth_large_root_cutoffCoefficient_scaleShift M H om j N hIR (aux_prop_growth_large_root_ahom_pos_of M Rm _) (s • x)

/-! ## The exact large-root supplier -/

/-- Verbatim copy of the prior development's `CB.LargeRootGrowth`: `prop_growth` with its side
restriction `r ≤ 1` replaced by `1 < r`. -/
def aux_prop_growth_large_root_LargeRootGrowth (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) : Prop :=
  ∀ (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
      (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), 1 < r →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        aux_prop_growth_large_root_GrowthBody M H z r hr t alpha k ps K Cbound

/-- **`prop_growth` on every root of side `r > 1`**, from the specified standing inputs
(through `SubdiffusiveProcess.Paper.prop_growth` on cubes of side `≤ 1`).  The threshold is `prop_growth`'s
for the doubled moment list. -/
theorem aux_prop_growth_large_root_largeRootGrowth (d : ℕ) (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd) : aux_prop_growth_large_root_LargeRootGrowth d Jc := by
  intro t alpha k ps h1 h2 h3 h4 h5
  have hPG := _root_.SubdiffusiveProcess.Paper.prop_growth d hd Jc Pc Xc W Cp Sf t alpha k (fun i => 2 * ps i)
    h1 h2 h3 h4 (fun i => by linarith [h5 i])
  obtain ⟨δ0, hδ0, hPG'⟩ := hPG
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm Sreg It H hIR hδ z r hr hr1
  -- the triadic level
  have hj : ∃ j : ℕ, r ≤ (3 : ℝ) ^ j := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt r (by norm_num : (1 : ℝ) < 3)
    exact ⟨n, hn.le⟩
  obtain ⟨j, hrj⟩ := hj
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp at hrj; linarith
    · exact h
  have hs : 0 < r / (3 : ℝ) ^ j := div_pos hr h3j
  have hs1 : r / (3 : ℝ) ^ j ≤ 1 := (div_le_one h3j).2 hrj
  have hrs : r = (3 : ℝ) ^ j * (r / (3 : ℝ) ^ j) := by field_simp
  have hU := hPG' M Rm Sreg It H hIR hδ (((3 : ℝ) ^ j)⁻¹ • z) (r / (3 : ℝ) ^ j) hs hs1
  obtain ⟨K', Cb', hmem', hbd', hK1', hG'⟩ := hU
  have hS := aux_prop_growth_large_root_measurePreserving_scaleShift M j
  have hR2 : 1 ≤ 1 + (3 : ℝ) ^ j + ((3 : ℝ) ^ j) ^ 2 := by
    linarith [pow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) j, sq_nonneg ((3 : ℝ) ^ j)]
  have hR2sq : 1 ≤ (1 + (3 : ℝ) ^ j + ((3 : ℝ) ^ j) ^ 2) ^ 2 := one_le_pow₀ hR2
  refine ⟨fun N om => (1 + (3 : ℝ) ^ j + ((3 : ℝ) ^ j) ^ 2) ^ 2 * aux_prop_growth_large_root_shiftEnv M j om *
      K' (N + j) (aux_prop_growth_large_root_scaleShift j om),
    fun i => (1 + (3 : ℝ) ^ j + ((3 : ℝ) ^ j) ^ 2) ^ 2 *
      (eLpNorm (aux_prop_growth_large_root_shiftEnv M j) (ENNReal.ofReal (2 * ps i))
        (chaosSampleLaw M).toMeasure).toReal * Cb' i, ?_, ?_, ?_, ?_⟩
  · intro i N
    exact (aux_prop_growth_large_root_moment_step M j _ (by positivity) (ps i) (h5 i) (K' (N + j)) (Cb' i)
      (hmem' i (N + j)) (hbd' i (N + j))).1
  · intro i N
    exact (aux_prop_growth_large_root_moment_step M j _ (by positivity) (ps i) (h5 i) (K' (N + j)) (Cb' i)
      (hmem' i (N + j)) (hbd' i (N + j))).2
  · filter_upwards [hS.quasiMeasurePreserving.ae hK1'] with om hom N
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hR2sq (aux_prop_growth_large_root_one_le_shiftEnv M j om)) (hom (N + j))
  · filter_upwards [aux_prop_growth_large_root_ae_infrared_scaleShift hIR j, hS.quasiMeasurePreserving.ae hG',
      hS.quasiMeasurePreserving.ae hK1'] with om hir hg hk1
    have hl1 : (1 : ℝ) ≤ (3 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    exact aux_prop_growth_large_root_growthAt_transfer_gen (z0 := r⁻¹ • z) hr hs hl1 hrs (by linarith) h3.le
      (fun N => cutoffPositiveCoefficient M H om N z hr)
      (fun N => cutoffPositiveCoefficient M H (aux_prop_growth_large_root_scaleShift j om) (N + j)
        (((3 : ℝ) ^ j)⁻¹ • z) hs)
      (fun N => aux_prop_growth_large_root_shiftConst M j N om) (aux_prop_growth_large_root_shiftEnv M j om)
      (fun N => aux_prop_growth_large_root_shiftConst_pos M Rm j N om) (fun N => aux_prop_growth_large_root_shiftConst_le M Rm j N hj0 om)
      (fun N => aux_prop_growth_large_root_shiftConst_inv_le M Rm j N hj0 om) (aux_prop_growth_large_root_one_le_shiftEnv M j om)
      (fun N => aux_prop_growth_large_root_coeff_pullback_gen M Rm H om j N hir z hr hs hrs)
      (fun N => K' (N + j) (aux_prop_growth_large_root_scaleShift j om)) (fun N => hk1 (N + j))
      (fun N => hg (N + j))

end LRGLarge

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity



theorem prop_growth_large_root :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_Cp : CampanatoInput d)
    (_S : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), 1 < r →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              K N om * (Kf + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K N om * (Kf + Cphi)) := by
  intro d hd _ _ E _P _X _W _Cp _S t alpha k ps h1 h2 h3 h4 h5
  exact aux_prop_growth_large_root_largeRootGrowth d hd E _P _X _W _Cp _S t alpha k ps
    h1 h2 h3 h4 h5

end SubdiffusiveProcess.Paper
