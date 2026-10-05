module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteInfimumCovariance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ShellLawTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StrictDecayConstants

@[expose] public section

/-!
# The outer weight of Step 3 is the unit-scale constant `q_R`

paper label `e.strict.decay.qR.def` ends the inductive step with

> Taking the remaining expectation, the scaling relation
> `g_{NR} =law g_0(3^{-NR} .)` and `e.strict.decay.qR.def` give
> `E[p . A_N^{(R)}(U) p] <= q_R^{N+1} |p|^2`.

The quantity whose expectation has to be identified with `q_R` is the
**discrete** minimum of the outer layer on the triadic mesh of the parent
simplex.  Two ingredients meet here:

* the geometric covariance of `DiscreteInfimumCovariance.lean`, which bounds the
  normalized discrete minimum at scale `k` by the unit-scale one read through
  the affine map `phi y = 3^k y + z`;
* the law transport of `ShellLawTransport.lean`, which says that the field
  `B_k(phi .)` has the law of `B_0(. + w)` and hence, by stationarity, of `B_0`.

Their composition is `integral_normalized_kuhnDirichletInf_shellFactor_le`:

```text
E[ |U|⁻¹ Q_{mesh(U)}(B_k) (U) (p) ]  <=  q_R(p) ,
```

for every triadic simplex `U` of size `3^k` and every `p`, where `mesh(U)` is
the depth-`R` triadic sub-mesh of `U` transported from the unit simplex.

## Scope

Only the direction the induction uses is proved.  The reverse inequality is
true but needs the surjectivity of the cell transport, which is not used
anywhere and is not proved.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Homogenization.Book Kuhn MeasureTheory ProbabilityTheory Set
open _root_.SubdiffusiveProcess.Model

noncomputable section

variable {d : ℕ}

/-! ## The parent cell and its transported mesh -/

/-- The triadic simplex of size `3^k`, index `c` and order `pi`. -/
def dilatedCell (k : ℕ) (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) : KuhnCell d :=
  ⟨⟨(k : ℤ), c⟩, pi⟩

/-- The depth-`R` triadic mesh of `dilatedCell k c pi`, transported from the
unit simplex. -/
def dilatedSubMesh (k R : ℕ) (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) :
    Finset (KuhnCell d) :=
  (Kuhn.triadicSubMesh (originKuhnCell d pi 0) R).image (Kuhn.dilateKuhnCell k R c)

theorem supportCube_originKuhnCell_zero (pi : Equiv.Perm (Fin d)) :
    (originKuhnCell d pi 0).supportCube = originCube d 0 := rfl

theorem scale_originKuhnCell_zero (pi : Equiv.Perm (Fin d)) :
    (originKuhnCell d pi 0).supportCube.scale = -((0 : ℕ) : ℤ) := by
  simp [originKuhnCell, originCube]

theorem scale_of_mem_triadicSubMesh_unit {R : ℕ} {pi : Equiv.Perm (Fin d)}
    {V : KuhnCell d} (hV : V ∈ Kuhn.triadicSubMesh (originKuhnCell d pi 0) R) :
    V.supportCube.scale = -(R : ℤ) := by
  have h := Kuhn.supportCube_scale_of_mem_triadicSubMesh hV
  rw [h, supportCube_originKuhnCell_zero]
  simp [originCube]

theorem triadicSubMesh_unit_subset (R : ℕ) (pi : Equiv.Perm (Fin d)) :
    Kuhn.triadicSubMesh (originKuhnCell d pi 0) R ⊆ unitMesh d (-(R : ℤ)) := by
  intro V hV
  have h := Kuhn.triadicSubMesh_subset (originKuhnCell d pi 0) R hV
  rw [supportCube_originKuhnCell_zero] at h
  have hscale : (originCube d 0).scale - (R : ℤ) = -(R : ℤ) := by simp [originCube]
  rw [hscale] at h
  exact h

theorem eq_dilateKuhnCell_zero (k : ℕ) (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) :
    Kuhn.dilateKuhnCell k 0 c (originKuhnCell d pi 0) = dilatedCell k c pi := by
  simp [Kuhn.dilateKuhnCell, originKuhnCell, originCube, dilatedCell]

/-- The parent simplex is the affine image of the unit simplex. -/
theorem openCarrier_dilatedCell (k : ℕ) (c : Fin d → ℤ)
    (pi : Equiv.Perm (Fin d)) :
    (dilatedCell k c pi).openCarrier =
      Kuhn.cellAffineMap k c '' (originKuhnCell d pi 0).openCarrier := by
  rw [← eq_dilateKuhnCell_zero k c pi]
  exact Kuhn.openCarrier_dilateKuhnCell (scale_originKuhnCell_zero pi)

theorem dilatedSubMesh_eq_image (k R : ℕ) (c : Fin d → ℤ)
    (pi : Equiv.Perm (Fin d)) :
    dilatedSubMesh k R c pi =
      (Kuhn.triadicSubMesh (originKuhnCell d pi 0) R).image
        (Kuhn.dilateKuhnCell k R c) := rfl

theorem scale_of_mem_dilatedSubMesh {k R : ℕ} {c : Fin d → ℤ}
    {pi : Equiv.Perm (Fin d)} {T : KuhnCell d} (hT : T ∈ dilatedSubMesh k R c pi) :
    T.supportCube.scale = (k : ℤ) - (R : ℤ) := by
  obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hT
  rw [Kuhn.dilateKuhnCell_scale, scale_of_mem_triadicSubMesh_unit hV]
  ring

theorem openCarrier_subset_of_mem_dilatedSubMesh {k R : ℕ} {c : Fin d → ℤ}
    {pi : Equiv.Perm (Fin d)} {T : KuhnCell d} (hT : T ∈ dilatedSubMesh k R c pi) :
    T.openCarrier ⊆ (dilatedCell k c pi).openCarrier := by
  obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hT
  rw [Kuhn.openCarrier_dilateKuhnCell (scale_of_mem_triadicSubMesh_unit hV),
    openCarrier_dilatedCell]
  exact Set.image_mono (Kuhn.openCarrier_subset_of_mem_triadicSubMesh hV)

/-- The transported mesh covers the parent simplex. -/
theorem openCarrier_dilatedCell_subset_iUnion (k R : ℕ) (c : Fin d → ℤ)
    (pi : Equiv.Perm (Fin d)) :
    (dilatedCell k c pi).openCarrier ⊆
      ⋃ T ∈ (dilatedSubMesh k R c pi : Set (KuhnCell d)), T.carrier := by
  intro x hx
  rw [openCarrier_dilatedCell] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨V, hV, hyV⟩ : ∃ V ∈ (Kuhn.triadicSubMesh (originKuhnCell d pi 0) R :
      Set (KuhnCell d)), y ∈ V.carrier := by
    simpa only [Set.mem_iUnion, exists_prop] using
      Kuhn.openCarrier_subset_iUnion_triadicSubMesh (originKuhnCell d pi 0) R hy
  refine Set.mem_iUnion.mpr ⟨Kuhn.dilateKuhnCell k R c V,
    Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨V, Finset.mem_coe.mp hV, rfl⟩)
  · exact (Kuhn.mem_carrier_dilateKuhnCell_iff
      (scale_of_mem_triadicSubMesh_unit (Finset.mem_coe.mp hV))).2 hyV

/-! ## The deterministic covariance at the parent simplex -/

theorem continuous_cellAffineMap (k : ℕ) (c : Fin d → ℤ) :
    Continuous (Kuhn.cellAffineMap (d := d) k c) := by
  refine continuous_pi fun i => ?_
  exact continuous_const.add (continuous_const.mul (continuous_apply i))

/-- **The normalized discrete minimum at scale `k` is bounded by the unit-scale
one.** -/
theorem normalized_kuhnDirichletInf_dilatedCell_le (k R : ℕ) (c : Fin d → ℤ)
    (pi : Equiv.Perm (Fin d)) {B : Vec d → ℝ} (hB : Continuous B)
    (hB0 : ∀ x, 0 ≤ B x) (p : Vec d) :
    (volume (dilatedCell k c pi).openCarrier).toReal⁻¹ *
        kuhnDirichletInf B (dilatedSubMesh k R c pi)
          (dilatedCell k c pi).openCarrier p ≤
      (volume (originKuhnCell d pi 0).openCarrier).toReal⁻¹ *
        kuhnDirichletInf (fun y => B (Kuhn.cellAffineMap k c y))
          (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0).openCarrier p := by
  have hUmeas : MeasurableSet (originKuhnCell d pi 0).openCarrier :=
    (isOpen_openCarrier _).measurableSet
  have hvol : 0 < (volume (originKuhnCell d pi 0).openCarrier).toReal :=
    volume_toReal_pos (kuhnCellDomain (originKuhnCell d pi 0))
  have hstep1 := normalized_kuhnDirichletInf_dilate_le k R c
    (S₀ := Kuhn.triadicSubMesh (originKuhnCell d pi 0) R)
    (fun V hV => scale_of_mem_triadicSubMesh_unit hV) hUmeas hvol hB hB0 p
  rw [← openCarrier_dilatedCell, ← dilatedSubMesh_eq_image] at hstep1
  refine hstep1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine kuhnDirichletInf_mono_subset (triadicSubMesh_unit_subset R pi) ?_
    (hB.comp (continuous_cellAffineMap k c)) (fun x => hB0 _) p
  intro V hV hVn
  have hpart : V ∈ triadicSimplexPartition
      (originKuhnCell d pi 0).supportCube
      ((originKuhnCell d pi 0).supportCube.scale - (R : ℤ)) := by
    rw [supportCube_originKuhnCell_zero]
    have hscale : (originCube d 0).scale - (R : ℤ) = -(R : ℤ) := by simp [originCube]
    rw [hscale]
    exact hV
  have hempty := Kuhn.inter_openCarrier_eq_empty_of_notMem_triadicSubMesh
    (R := R) hpart hVn
  rw [hempty]
  simp

/-! ## The law transport -/

/-- The unit-scale discrete functional of one layer. -/
def unitDiscreteInf (M : GMCModel d) (R : ℕ) (pi : Equiv.Perm (Fin d)) (p : Vec d)
    (g : PotentialField d) : ℝ :=
  (volume (originKuhnCell d pi 0).openCarrier).toReal⁻¹ *
    kuhnDirichletInf (shellWeight M g) (unitMesh d (-(R : ℤ)))
      (originKuhnCell d pi 0).openCarrier p

/-- The same functional read through the affine map. -/
def dilatedDiscreteInf (M : GMCModel d) (R k : ℕ) (c : Fin d → ℤ)
    (pi : Equiv.Perm (Fin d)) (p : Vec d) (g : PotentialField d) : ℝ :=
  (volume (originKuhnCell d pi 0).openCarrier).toReal⁻¹ *
    kuhnDirichletInf (fun y => shellWeight M g (Kuhn.cellAffineMap k c y))
      (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0).openCarrier p

theorem measurable_unitDiscreteInf (M : GMCModel d) (R : ℕ)
    (pi : Equiv.Perm (Fin d)) (p : Vec d) :
    Measurable (unitDiscreteInf M R pi p) := by
  refine Measurable.const_mul ?_ _
  refine measurable_kuhnDirichletInf
    (fun g => Real.continuous_exp.comp ((g.contDiff_one.continuous).sub
      continuous_const))
    (fun g x => (Real.exp_pos _).le) fun V _ => ?_
  exact measurable_cellSup V
    (fun g => Real.continuous_exp.comp ((g.contDiff_one.continuous).sub
      continuous_const))
    fun y => ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval y).sub measurable_const).exp

theorem measurable_dilatedDiscreteInf (M : GMCModel d) (R k : ℕ) (c : Fin d → ℤ)
    (pi : Equiv.Perm (Fin d)) (p : Vec d) :
    Measurable (dilatedDiscreteInf M R k c pi p) := by
  refine Measurable.const_mul ?_ _
  refine measurable_kuhnDirichletInf
    (fun g => Real.continuous_exp.comp (((g.contDiff_one.continuous).comp
      (continuous_cellAffineMap k c)).sub continuous_const))
    (fun g x => (Real.exp_pos _).le) fun V _ => ?_
  exact measurable_cellSup V
    (fun g => Real.continuous_exp.comp (((g.contDiff_one.continuous).comp
      (continuous_cellAffineMap k c)).sub continuous_const))
    fun y => ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval
      (Kuhn.cellAffineMap k c y)).sub measurable_const).exp

/-- The triadic shift the affine map induces on the unit-scale field. -/
def cellShift (k : ℕ) (c : Fin d → ℤ) : Vec d :=
  (((3 : ℝ) ^ k)⁻¹) • cubeCenter (⟨(k : ℤ), c⟩ : TriadicCube d)

theorem inv_smul_cellAffineMap (k : ℕ) (c : Fin d → ℤ) (y : Vec d) :
    (((3 : ℝ) ^ k)⁻¹) • Kuhn.cellAffineMap k c y = y + cellShift k c := by
  have ha : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  rw [Kuhn.cellAffineMap_eq_smul_add, smul_add, cellShift, zpow_natCast,
    smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- **The key pointwise identity**: the affine reading of a scaled field is the
translated reading of the unit-scale field. -/
theorem shellWeight_triadicScale_cellAffineMap (M : GMCModel d) (k : ℕ)
    (c : Fin d → ℤ) (g : PotentialField d) :
    (fun y => shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g)
        (Kuhn.cellAffineMap k c y)) =
      shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.translate (cellShift k c) g) := by
  funext y
  show Real.exp (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g
    (Kuhn.cellAffineMap k c y) - tauSq M.P) = _
  rw [_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale_apply, inv_smul_cellAffineMap]
  rfl

theorem dilatedDiscreteInf_triadicScale (M : GMCModel d) (R k : ℕ) (c : Fin d → ℤ)
    (pi : Equiv.Perm (Fin d)) (p : Vec d) (g : PotentialField d) :
    dilatedDiscreteInf M R k c pi p (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) =
      unitDiscreteInf M R pi p (_root_.SubdiffusiveProcess.Model.PotentialField.translate (cellShift k c) g) := by
  rw [dilatedDiscreteInf, unitDiscreteInf,
    shellWeight_triadicScale_cellAffineMap M k c g]

/-! ## Integrability -/

theorem integrable_apply_layer_iff (M : GMCModel d) (k : ℕ)
    {F : PotentialField d → ℝ} (hF : Measurable F) :
    Integrable (fun omega : PotentialSample d => F (omega k)) M.P.toMeasure ↔
      Integrable (fun g : PotentialField d => F (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g))
        (zeroPotentialLaw M.P).toMeasure := by
  have hscale := congrArg ProbabilityMeasure.toMeasure (M.shellPrefix.marginal_scaling k)
  change (potentialMarginalLaw M.P k).toMeasure =
    Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k) (zeroPotentialLaw M.P).toMeasure at hscale
  have hcoord : (potentialMarginalLaw M.P k).toMeasure =
      Measure.map (fun omega : PotentialSample d => omega k) M.P.toMeasure := rfl
  have h1 : Integrable (fun omega : PotentialSample d => F (omega k)) M.P.toMeasure ↔
      Integrable F (Measure.map (fun omega : PotentialSample d => omega k)
        M.P.toMeasure) :=
    (integrable_map_measure hF.aestronglyMeasurable
      (measurable_potentialCoordinate k).aemeasurable).symm
  have h2 : Integrable F (Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
        (zeroPotentialLaw M.P).toMeasure) ↔
      Integrable (fun g : PotentialField d => F (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g))
        (zeroPotentialLaw M.P).toMeasure :=
    integrable_map_measure hF.aestronglyMeasurable
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k).aemeasurable
  rw [h1, ← hcoord, hscale, h2]

theorem integrable_apply_zero_iff (M : GMCModel d) {F : PotentialField d → ℝ}
    (hF : Measurable F) :
    Integrable (fun omega : PotentialSample d => F (omega 0)) M.P.toMeasure ↔
      Integrable F (zeroPotentialLaw M.P).toMeasure := by
  have hcoord : (zeroPotentialLaw M.P).toMeasure =
      Measure.map (fun omega : PotentialSample d => omega 0) M.P.toMeasure := rfl
  rw [hcoord]
  exact (integrable_map_measure hF.aestronglyMeasurable
    (measurable_potentialCoordinate 0).aemeasurable).symm

theorem integrable_comp_translate_iff (M : GMCModel d) (z : Vec d)
    {F : PotentialField d → ℝ} (hF : Measurable F) :
    Integrable (fun g : PotentialField d => F (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g))
        (zeroPotentialLaw M.P).toMeasure ↔
      Integrable F (zeroPotentialLaw M.P).toMeasure := by
  have hstat := M.G1.stationary z
  have h := integrable_map_measure hF.aestronglyMeasurable
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z).aemeasurable
      (μ := (zeroPotentialLaw M.P).toMeasure)
  have hcomp : (fun g : PotentialField d => F (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)) =
      F ∘ _root_.SubdiffusiveProcess.Model.PotentialField.translate z := rfl
  rw [hcomp, ← h, hstat]

/-! ## The expectation identity -/

theorem integral_dilatedDiscreteInf (M : GMCModel d) (R k : ℕ) (c : Fin d → ℤ)
    (pi : Equiv.Perm (Fin d)) (p : Vec d) :
    ∫ omega, dilatedDiscreteInf M R k c pi p (omega k) ∂M.P.toMeasure =
      qRSlope M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) p := by
  have hmd := measurable_dilatedDiscreteInf M R k c pi p
  have hmu := measurable_unitDiscreteInf M R pi p
  calc ∫ omega, dilatedDiscreteInf M R k c pi p (omega k) ∂M.P.toMeasure
      = ∫ g, dilatedDiscreteInf M R k c pi p (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g)
          ∂(zeroPotentialLaw M.P).toMeasure :=
        integral_apply_layer_eq_integral_triadicScale M k hmd
    _ = ∫ g, unitDiscreteInf M R pi p
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate (cellShift k c) g)
          ∂(zeroPotentialLaw M.P).toMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        exact dilatedDiscreteInf_triadicScale M R k c pi p g
    _ = ∫ g, unitDiscreteInf M R pi p g ∂(zeroPotentialLaw M.P).toMeasure :=
        integral_comp_translate_eq M (cellShift k c) hmu
    _ = ∫ omega, unitDiscreteInf M R pi p (omega 0) ∂M.P.toMeasure :=
        (integral_apply_zero_eq_integral_zeroPotentialLaw M hmu).symm
    _ = qRSlope M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) p := by
        rw [qRSlope, ← integral_const_mul]
        rfl

theorem integrable_dilatedDiscreteInf (M : GMCModel d) (R k : ℕ) (c : Fin d → ℤ)
    (pi : Equiv.Perm (Fin d)) (p : Vec d) :
    Integrable (fun omega : PotentialSample d =>
      dilatedDiscreteInf M R k c pi p (omega k)) M.P.toMeasure := by
  have hmd := measurable_dilatedDiscreteInf M R k c pi p
  have hmu := measurable_unitDiscreteInf M R pi p
  have hmut : Measurable fun g : PotentialField d =>
      unitDiscreteInf M R pi p (_root_.SubdiffusiveProcess.Model.PotentialField.translate (cellShift k c) g) :=
    hmu.comp (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate (cellShift k c))
  have hunit : Integrable (fun omega : PotentialSample d =>
      unitDiscreteInf M R pi p (omega 0)) M.P.toMeasure := by
    refine Integrable.const_mul ?_ _
    refine integrable_kuhnDirichletInf_shellFactor M ?_ _ p
    intro V hV
    exact closedCarrier_subset_of_mem_unitMesh (by omega) hV
  rw [integrable_apply_layer_iff M k hmd]
  have hfun : (fun g : PotentialField d =>
      dilatedDiscreteInf M R k c pi p (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g)) =
      fun g => unitDiscreteInf M R pi p
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate (cellShift k c) g) :=
    funext fun g => dilatedDiscreteInf_triadicScale M R k c pi p g
  rw [hfun, integrable_comp_translate_iff M (cellShift k c) hmu,
    ← integrable_apply_zero_iff M hmu]
  exact hunit

/-! ## The statement Step 3 consumes -/

/-- **The outer weight of paper label `p.homogenized.coefficient.strict.decay` is the unit-scale
constant.**  For every triadic simplex of size `3^k` and every slope, the
expected normalized discrete minimum of the layer `B_k` on the depth-`R` mesh is
at most `q_R(p)`. -/
theorem integral_normalized_kuhnDirichletInf_shellFactor_le (M : GMCModel d)
    (R k : ℕ) (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) (p : Vec d) :
    ∫ omega, (volume (dilatedCell k c pi).openCarrier).toReal⁻¹ *
        kuhnDirichletInf (shellFactor M k omega) (dilatedSubMesh k R c pi)
          (dilatedCell k c pi).openCarrier p ∂M.P.toMeasure ≤
      qRSlope M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) p := by
  rw [← integral_dilatedDiscreteInf M R k c pi p]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun omega => ?_)
    (integrable_dilatedDiscreteInf M R k c pi p)
    (Filter.Eventually.of_forall fun omega => ?_)
  · refine mul_nonneg (by positivity) ?_
    exact kuhnDirichletInf_nonneg (continuous_shellFactor M k omega)
      (fun x => (shellFactor_pos M k omega x).le) p
  · exact normalized_kuhnDirichletInf_dilatedCell_le k R c pi
      (continuous_shellFactor M k omega)
      (fun x => (shellFactor_pos M k omega x).le) p

/-! ## The transported `(g2)` moment of a cell weight -/

/-- **(g2) at the layer `k`.**  The cell weight of `B_k` on a cell of the
transported mesh is integrable, because its law is that of the unit-scale cell
weight on the corresponding unit cell. -/
theorem integrable_cellSup_shellFactor_dilateKuhnCell (M : GMCModel d) (R k : ℕ)
    (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) {V : KuhnCell d}
    (hV : V ∈ Kuhn.triadicSubMesh (originKuhnCell d pi 0) R) :
    Integrable (fun omega : PotentialSample d =>
      cellSup (shellFactor M k omega) (Kuhn.dilateKuhnCell k R c V))
      M.P.toMeasure := by
  have hcontd : ∀ g : PotentialField d,
      Continuous fun y => shellWeight M g (Kuhn.cellAffineMap k c y) := fun g =>
    Real.continuous_exp.comp (((g.contDiff_one.continuous).comp
      (continuous_cellAffineMap k c)).sub continuous_const)
  have hcontu : ∀ g : PotentialField d, Continuous (shellWeight M g) := fun g =>
    Real.continuous_exp.comp ((g.contDiff_one.continuous).sub continuous_const)
  have hmd : Measurable fun g : PotentialField d =>
      cellSup (fun y => shellWeight M g (Kuhn.cellAffineMap k c y)) V :=
    measurable_cellSup V hcontd fun y =>
      ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval
        (Kuhn.cellAffineMap k c y)).sub measurable_const).exp
  have hmu : Measurable fun g : PotentialField d => cellSup (shellWeight M g) V :=
    measurable_cellSup V hcontu fun y =>
      ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval y).sub measurable_const).exp
  have hunit : Integrable (fun omega : PotentialSample d =>
      cellSup (shellWeight M (omega 0)) V) M.P.toMeasure :=
    integrable_cellSup_shellFactor M
      (closedCarrier_subset_of_mem_unitMesh (by omega)
        (triadicSubMesh_unit_subset R pi hV))
  have hrewrite : (fun omega : PotentialSample d =>
      cellSup (shellFactor M k omega) (Kuhn.dilateKuhnCell k R c V)) =
      fun omega : PotentialSample d =>
        cellSup (fun y => shellWeight M (omega k) (Kuhn.cellAffineMap k c y)) V := by
    funext omega
    exact Kuhn.cellSup_dilateKuhnCell (scale_of_mem_triadicSubMesh_unit hV)
      (shellFactor M k omega)
  rw [hrewrite, integrable_apply_layer_iff M k hmd]
  have hfun : (fun g : PotentialField d =>
      cellSup (fun y => shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g)
        (Kuhn.cellAffineMap k c y)) V) =
      fun g => cellSup (shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.translate (cellShift k c) g)) V := by
    funext g
    rw [shellWeight_triadicScale_cellAffineMap M k c g]
  rw [hfun, integrable_comp_translate_iff M (cellShift k c) hmu,
    ← integrable_apply_zero_iff M hmu]
  exact hunit

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
