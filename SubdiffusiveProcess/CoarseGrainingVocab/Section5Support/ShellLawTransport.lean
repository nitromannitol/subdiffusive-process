module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerCoefficient

@[expose] public section

/-!
# Transporting the shell law through the continuum Dirichlet minimum

Step 3 of the strict-decay proof  compares the
outer weight `B_{NR}` on the generation-`NR` simplex with the unit-scale
constant `q_R`, using the two exact symmetries of the model:

* the marginal scaling `g_k =law g_0(3^{-k} .)`
  (`ShellLawPrefix.marginal_scaling`), and
* the stationarity of the unit-scale layer (`ShellLawG1.stationary`).

Both are statements about the *law of one layer*, so they transport through any
measurable functional of that layer.  The functional Step 3 needs is the
normalized continuum Dirichlet minimum, and the reason the transport lands on
the *same* number rather than a rescaled one is the dilation covariance proved
in `DirichletInfimumCovariance.lean`: dilating the field by `3^{-k}` and the
domain by `3^{k}` leaves the volume-averaged minimum unchanged.

## What this file proves

* `integral_apply_layer_eq_integral_triadicScale` -- the marginal-scaling
  transport of an arbitrary measurable functional of one layer;
* `integral_comp_translate_eq` -- the stationarity transport;
* `dirichletInfOn_exp_triadicScale` -- the pointwise identity that the
  normalized minimum of `B_{g(3^{-k} .)}` on `spx_k` is that of `B_g` on
  `spx_0`;
* **`integral_normalized_dirichletInfOn_shellFactor_eq`** -- the law equality
  Step 3 consumes,

  ```text
  E[ (|spx_k|)⁻¹ min_{spx_k} B_k |nabla u|^2 ]
    = E[ (|spx_0|)⁻¹ min_{spx_0} B_0 |nabla u|^2 ] ;
  ```

* `integral_dirichletInfOn_shellFactor_translateSet_eq` -- the same for a
  translated domain, from stationarity.

## Scope

The measurability of `g |-> dirichletInfOn (B_g) U p` is a hypothesis, not a
claim: it is exactly what the countable-family device of
`DirichletInfimumMeasurability.lean` supplies
(`measurable_dirichletInfOn_of_measurable_kuhnDirichletInf`), and keeping it as
a hypothesis makes this file independent of which mesh family discharges it.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Homogenization.Book Kuhn MeasureTheory ProbabilityTheory
open _root_.SubdiffusiveProcess.Model

open scoped Pointwise

noncomputable section

variable {d : ℕ}

/-! ## The origin simplex at scale `m` -/

/-- The Kuhn cell carrying the simplex `spx_m^pi(0)`. -/
def originKuhnCell (d : ℕ) (pi : Equiv.Perm (Fin d)) (m : ℤ) : KuhnCell d :=
  ⟨originCube d m, pi⟩

/-- `spx_m^pi(0) = 3^m spx_0^pi(0)`. -/
theorem openCarrier_originKuhnCell (pi : Equiv.Perm (Fin d)) (m : ℤ) :
    (originKuhnCell d pi m).openCarrier = ((3 : ℝ) ^ m) • orderedUnitSimplex pi := by
  have hcenter : cubeCenter (originCube d m) = (0 : Vec d) := by
    funext i
    simp [cubeCenter, originCube]
  simp only [originKuhnCell, KuhnCell.openCarrier, triadicSimplex, hcenter]
  ext y
  simp [Set.mem_smul_set, originCube]

theorem isOpen_openCarrier_originKuhnCell (pi : Equiv.Perm (Fin d)) (m : ℤ) :
    IsOpen (originKuhnCell d pi m).openCarrier :=
  isOpen_openCarrier _

/-- The triadic dilation by `3^{-k}` pulls the unit-scale simplex back to the
scale-`k` simplex. -/
theorem preimage_dilateVec_openCarrier_originKuhnCell (pi : Equiv.Perm (Fin d))
    (k : ℕ) :
    Ch02.dilateVec (d := d) (-(k : ℤ)) ⁻¹' (originKuhnCell d pi 0).openCarrier =
      (originKuhnCell d pi (k : ℤ)).openCarrier := by
  rw [preimage_dilateVec, openCarrier_originKuhnCell, openCarrier_originKuhnCell]
  have hfac : Ch02.triadicDilationFactor (-(k : ℤ)) = ((3 : ℝ) ^ (k : ℤ))⁻¹ := by
    simp [Ch02.triadicDilationFactor, zpow_neg]
  rw [hfac, inv_inv]
  simp

/-! ## Transport of a functional of one layer -/

/-- **The marginal-scaling transport** (`ShellLawPrefix.marginal_scaling`): the
expectation of any measurable functional of the layer `g_k` is the expectation
of its `3^{-k}`-dilate under the unit-scale law. -/
theorem integral_apply_layer_eq_integral_triadicScale (M : GMCModel d) (k : ℕ)
    {F : PotentialField d → ℝ} (hF : Measurable F) :
    ∫ omega, F (omega k) ∂M.P.toMeasure =
      ∫ g, F (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) ∂(zeroPotentialLaw M.P).toMeasure := by
  have hscale := congrArg ProbabilityMeasure.toMeasure (M.shellPrefix.marginal_scaling k)
  change (potentialMarginalLaw M.P k).toMeasure =
    Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k) (zeroPotentialLaw M.P).toMeasure at hscale
  have hcoord : (potentialMarginalLaw M.P k).toMeasure =
      Measure.map (fun omega : PotentialSample d => omega k) M.P.toMeasure := rfl
  calc ∫ omega, F (omega k) ∂M.P.toMeasure
      = ∫ y, F y ∂(Measure.map (fun omega : PotentialSample d => omega k) M.P.toMeasure) :=
        (integral_map (measurable_potentialCoordinate k).aemeasurable
          hF.aestronglyMeasurable).symm
    _ = ∫ y, F y ∂(Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
          (zeroPotentialLaw M.P).toMeasure) := by rw [← hcoord, hscale]
    _ = ∫ g, F (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) ∂(zeroPotentialLaw M.P).toMeasure :=
        integral_map (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k).aemeasurable
          hF.aestronglyMeasurable

/-- The layer `g_0` has the unit-scale law. -/
theorem integral_apply_zero_eq_integral_zeroPotentialLaw (M : GMCModel d)
    {F : PotentialField d → ℝ} (hF : Measurable F) :
    ∫ omega, F (omega 0) ∂M.P.toMeasure =
      ∫ g, F g ∂(zeroPotentialLaw M.P).toMeasure := by
  have hcoord : (zeroPotentialLaw M.P).toMeasure =
      Measure.map (fun omega : PotentialSample d => omega 0) M.P.toMeasure := rfl
  rw [hcoord]
  exact (integral_map (measurable_potentialCoordinate 0).aemeasurable
    hF.aestronglyMeasurable).symm

/-- **The stationarity transport** (`ShellLawG1.stationary`). -/
theorem integral_comp_translate_eq (M : GMCModel d) (z : Vec d)
    {F : PotentialField d → ℝ} (hF : Measurable F) :
    ∫ g, F (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) ∂(zeroPotentialLaw M.P).toMeasure =
      ∫ g, F g ∂(zeroPotentialLaw M.P).toMeasure := by
  have hstat := M.G1.stationary z
  calc ∫ g, F (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) ∂(zeroPotentialLaw M.P).toMeasure
      = ∫ y, F y ∂(Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate z)
          (zeroPotentialLaw M.P).toMeasure) :=
        (integral_map (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z).aemeasurable
          hF.aestronglyMeasurable).symm
    _ = ∫ g, F g ∂(zeroPotentialLaw M.P).toMeasure := by rw [hstat]

/-! ## The functional: the normalized continuum minimum of a shell factor -/

/-- The mean-one shell weight built from one layer. -/
def shellWeight (M : GMCModel d) (g : PotentialField d) (x : Vec d) : ℝ :=
  Real.exp (g x - tauSq M.P)

theorem shellWeight_nonneg (M : GMCModel d) (g : PotentialField d) (x : Vec d) :
    0 ≤ shellWeight M g x :=
  (Real.exp_pos _).le

theorem shellFactor_eq_shellWeight (M : GMCModel d) (k : ℕ)
    (omega : PotentialSample d) : shellFactor M k omega = shellWeight M (omega k) := rfl

/-- **The pointwise covariance of the functional.**  Dilating the field by
`3^{-k}` and the domain by `3^{k}` leaves the volume-averaged Dirichlet minimum
unchanged. -/
theorem dirichletInfOn_exp_triadicScale (M : GMCModel d) (pi : Equiv.Perm (Fin d))
    (p : Vec d) (k : ℕ) (g : PotentialField d) :
    (volume (originKuhnCell d pi (k : ℤ)).openCarrier).toReal⁻¹ *
        dirichletInfOn (shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g))
          (originKuhnCell d pi (k : ℤ)).openCarrier p =
      (volume (originKuhnCell d pi 0).openCarrier).toReal⁻¹ *
        dirichletInfOn (shellWeight M g) (originKuhnCell d pi 0).openCarrier p := by
  have hmeas : MeasurableSet (originKuhnCell d pi 0).openCarrier :=
    (isOpen_openCarrier_originKuhnCell pi 0).measurableSet
  have hcomp : shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) =
      fun x => shellWeight M g (Ch02.dilateVec (-(k : ℤ)) x) := by
    funext x
    have hfac : Ch02.dilateVec (d := d) (-(k : ℤ)) x = (((3 : ℝ) ^ k)⁻¹) • x := by
      simp [Ch02.dilateVec, Ch02.triadicDilationFactor, zpow_neg]
    rw [hfac]
    rfl
  have hpre := preimage_dilateVec_openCarrier_originKuhnCell (d := d) pi k
  have hcov := normalized_dirichletInfOn_dilateVec (B := shellWeight M g)
    (U := (originKuhnCell d pi 0).openCarrier) (p := p) (-(k : ℤ)) hmeas
    (shellWeight_nonneg M g)
  rw [hpre] at hcov
  rw [hcomp]
  exact hcov

/-! ## The law equality Step 3 consumes -/

/-- **The scaling and stationarity of the model, pushed through the continuum
minimum.**  The expected volume-averaged Dirichlet minimum of the shell factor
`B_k` on the scale-`k` simplex equals that of `B_0` on the unit simplex.  This
identifies the outer weight with the
unit-scale constant. -/
theorem integral_normalized_dirichletInfOn_shellFactor_eq (M : GMCModel d)
    (pi : Equiv.Perm (Fin d)) (p : Vec d) (k : ℕ)
    (hk : Measurable fun g : PotentialField d =>
      dirichletInfOn (shellWeight M g) (originKuhnCell d pi (k : ℤ)).openCarrier p)
    (h0 : Measurable fun g : PotentialField d =>
      dirichletInfOn (shellWeight M g) (originKuhnCell d pi 0).openCarrier p) :
    ∫ omega, (volume (originKuhnCell d pi (k : ℤ)).openCarrier).toReal⁻¹ *
        dirichletInfOn (shellFactor M k omega)
          (originKuhnCell d pi (k : ℤ)).openCarrier p ∂M.P.toMeasure =
      ∫ omega, (volume (originKuhnCell d pi 0).openCarrier).toReal⁻¹ *
        dirichletInfOn (shellFactor M 0 omega)
          (originKuhnCell d pi 0).openCarrier p ∂M.P.toMeasure := by
  have hFk : Measurable fun g : PotentialField d =>
      (volume (originKuhnCell d pi (k : ℤ)).openCarrier).toReal⁻¹ *
        dirichletInfOn (shellWeight M g) (originKuhnCell d pi (k : ℤ)).openCarrier p :=
    hk.const_mul _
  have hF0 : Measurable fun g : PotentialField d =>
      (volume (originKuhnCell d pi 0).openCarrier).toReal⁻¹ *
        dirichletInfOn (shellWeight M g) (originKuhnCell d pi 0).openCarrier p :=
    h0.const_mul _
  calc ∫ omega, (volume (originKuhnCell d pi (k : ℤ)).openCarrier).toReal⁻¹ *
          dirichletInfOn (shellFactor M k omega)
            (originKuhnCell d pi (k : ℤ)).openCarrier p ∂M.P.toMeasure
      = ∫ g, (volume (originKuhnCell d pi (k : ℤ)).openCarrier).toReal⁻¹ *
          dirichletInfOn (shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g))
            (originKuhnCell d pi (k : ℤ)).openCarrier p
          ∂(zeroPotentialLaw M.P).toMeasure :=
        integral_apply_layer_eq_integral_triadicScale M k hFk
    _ = ∫ g, (volume (originKuhnCell d pi 0).openCarrier).toReal⁻¹ *
          dirichletInfOn (shellWeight M g) (originKuhnCell d pi 0).openCarrier p
          ∂(zeroPotentialLaw M.P).toMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        exact dirichletInfOn_exp_triadicScale M pi p k g
    _ = ∫ omega, (volume (originKuhnCell d pi 0).openCarrier).toReal⁻¹ *
          dirichletInfOn (shellFactor M 0 omega)
            (originKuhnCell d pi 0).openCarrier p ∂M.P.toMeasure :=
        (integral_apply_zero_eq_integral_zeroPotentialLaw M hF0).symm

/-! ## Stationarity of every layer -/

/-- Translation commutes with the triadic scaling, at the rescaled shift. -/
theorem translate_triadicScale (k : ℕ) (z : Vec d) (g : PotentialField d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.translate z (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) =
      _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate ((((3 : ℝ) ^ k)⁻¹) • z) g) := by
  apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
  intro x
  simp [smul_add]

/-- **Every layer is stationary**, not just the unit-scale one: the marginal
scaling conjugates the translation of `g_k` into a translation of `g_0`. -/
theorem integral_apply_layer_comp_translate_eq (M : GMCModel d) (k : ℕ) (z : Vec d)
    {F : PotentialField d → ℝ} (hF : Measurable F) :
    ∫ omega, F (_root_.SubdiffusiveProcess.Model.PotentialField.translate z (omega k)) ∂M.P.toMeasure =
      ∫ omega, F (omega k) ∂M.P.toMeasure := by
  have hFt : Measurable fun g : PotentialField d => F (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) :=
    hF.comp (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z)
  have hFs : Measurable fun g : PotentialField d =>
      F (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) :=
    hF.comp (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k)
  calc ∫ omega, F (_root_.SubdiffusiveProcess.Model.PotentialField.translate z (omega k)) ∂M.P.toMeasure
      = ∫ g, F (_root_.SubdiffusiveProcess.Model.PotentialField.translate z (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g))
          ∂(zeroPotentialLaw M.P).toMeasure :=
        integral_apply_layer_eq_integral_triadicScale M k hFt
    _ = ∫ g, F (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate ((((3 : ℝ) ^ k)⁻¹) • z) g))
          ∂(zeroPotentialLaw M.P).toMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        exact congrArg F (translate_triadicScale k z g)
    _ = ∫ g, F (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) ∂(zeroPotentialLaw M.P).toMeasure :=
        integral_comp_translate_eq M ((((3 : ℝ) ^ k)⁻¹) • z) hFs
    _ = ∫ omega, F (omega k) ∂M.P.toMeasure :=
        (integral_apply_layer_eq_integral_triadicScale M k hF).symm

/-! ## An arbitrary triadic simplex -/

/-- Every triadic simplex is the translate of the origin simplex of the same
scale by the centre of its support cube. -/
theorem openCarrier_eq_translateSet_originKuhnCell (T : KuhnCell d) :
    T.openCarrier =
      translateSet (cubeCenter T.supportCube)
        (originKuhnCell d T.order T.supportCube.scale).openCarrier := by
  rw [openCarrier_originKuhnCell]
  simp only [KuhnCell.openCarrier, triadicSimplex]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨((3 : ℝ) ^ T.supportCube.scale) • x, ⟨x, hx, rfl⟩, by rw [add_comm]⟩
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by rw [add_comm]⟩

/-- **The law equality at an arbitrary triadic simplex.**  For every triadic
simplex `T` of size `3^k`,

```text
E[ (|T|)⁻¹ min_T B_k |nabla u|^2 ] = E[ (|spx_0|)⁻¹ min_{spx_0} B_0 |nabla u|^2 ] ,
```

by the marginal scaling and the stationarity of the layer `g_k`.  This is the
identification of the outer weight  with the
unit-scale constant `q_*`. -/
theorem integral_normalized_dirichletInfOn_shellFactor_cell_eq (M : GMCModel d)
    (T : KuhnCell d) (k : ℕ) (hscale : T.supportCube.scale = (k : ℤ)) (p : Vec d)
    (hk : Measurable fun g : PotentialField d =>
      dirichletInfOn (shellWeight M g)
        (originKuhnCell d T.order (k : ℤ)).openCarrier p)
    (h0 : Measurable fun g : PotentialField d =>
      dirichletInfOn (shellWeight M g) (originKuhnCell d T.order 0).openCarrier p) :
    ∫ omega, (volume T.openCarrier).toReal⁻¹ *
        dirichletInfOn (shellFactor M k omega) T.openCarrier p ∂M.P.toMeasure =
      ∫ omega, (volume (originKuhnCell d T.order 0).openCarrier).toReal⁻¹ *
        dirichletInfOn (shellFactor M 0 omega)
          (originKuhnCell d T.order 0).openCarrier p ∂M.P.toMeasure := by
  set V : Set (Vec d) := (originKuhnCell d T.order (k : ℤ)).openCarrier with hVdef
  set z : Vec d := cubeCenter T.supportCube with hzdef
  have hVmeas : MeasurableSet V :=
    (isOpen_openCarrier_originKuhnCell T.order (k : ℤ)).measurableSet
  have hTV : T.openCarrier = translateSet z V := by
    rw [hVdef, hzdef, ← hscale]
    exact openCarrier_eq_translateSet_originKuhnCell T
  have hvol : volume T.openCarrier = volume V := by
    rw [hTV]; exact volume_translateSet_eq z V
  have hH : Measurable fun g : PotentialField d =>
      (volume V).toReal⁻¹ * dirichletInfOn (shellWeight M g) V p := hk.const_mul _
  have hkey : ∀ g : PotentialField d,
      (volume T.openCarrier).toReal⁻¹ *
          dirichletInfOn (shellWeight M g) T.openCarrier p =
        (volume V).toReal⁻¹ *
          dirichletInfOn (shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)) V p := by
    intro g
    have hcomp : shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) =
        fun x => shellWeight M g (x + z) := rfl
    rw [hcomp, dirichletInfOn_comp_add_right (B := shellWeight M g) (U := V) (p := p) z
      hVmeas (shellWeight_nonneg M g), hvol, hTV]
  calc ∫ omega, (volume T.openCarrier).toReal⁻¹ *
          dirichletInfOn (shellFactor M k omega) T.openCarrier p ∂M.P.toMeasure
      = ∫ omega, (volume V).toReal⁻¹ *
          dirichletInfOn (shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.translate z (omega k))) V p
          ∂M.P.toMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
        exact hkey (omega k)
    _ = ∫ omega, (volume V).toReal⁻¹ *
          dirichletInfOn (shellWeight M (omega k)) V p ∂M.P.toMeasure :=
        integral_apply_layer_comp_translate_eq M k z hH
    _ = ∫ omega, (volume (originKuhnCell d T.order 0).openCarrier).toReal⁻¹ *
          dirichletInfOn (shellFactor M 0 omega)
            (originKuhnCell d T.order 0).openCarrier p ∂M.P.toMeasure :=
        integral_normalized_dirichletInfOn_shellFactor_eq M T.order p k hk h0

/-- **Stationarity through the minimum.**  Translating the domain does not
change the expected Dirichlet minimum of the unit-scale shell factor. -/
theorem integral_dirichletInfOn_shellFactor_translateSet_eq (M : GMCModel d)
    {U : Set (Vec d)} (hU : MeasurableSet U) (z : Vec d) (p : Vec d)
    (hmeas : Measurable fun g : PotentialField d =>
      dirichletInfOn (shellWeight M g) U p) :
    ∫ omega, dirichletInfOn (shellFactor M 0 omega) (translateSet z U) p
        ∂M.P.toMeasure =
      ∫ omega, dirichletInfOn (shellFactor M 0 omega) U p ∂M.P.toMeasure := by
  have hshift : ∀ g : PotentialField d,
      dirichletInfOn (shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)) U p =
        dirichletInfOn (shellWeight M g) (translateSet z U) p := by
    intro g
    have hcomp : shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) =
        fun x => shellWeight M g (x + z) := rfl
    rw [hcomp]
    exact dirichletInfOn_comp_add_right (B := shellWeight M g) (U := U) (p := p) z hU
      (shellWeight_nonneg M g)
  have hmeasT : Measurable fun g : PotentialField d =>
      dirichletInfOn (shellWeight M g) (translateSet z U) p := by
    have : (fun g : PotentialField d =>
        dirichletInfOn (shellWeight M g) (translateSet z U) p) =
      fun g => dirichletInfOn (shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)) U p :=
      funext fun g => (hshift g).symm
    rw [this]
    exact hmeas.comp (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z)
  calc ∫ omega, dirichletInfOn (shellFactor M 0 omega) (translateSet z U) p
        ∂M.P.toMeasure
      = ∫ g, dirichletInfOn (shellWeight M g) (translateSet z U) p
          ∂(zeroPotentialLaw M.P).toMeasure :=
        integral_apply_zero_eq_integral_zeroPotentialLaw M hmeasT
    _ = ∫ g, dirichletInfOn (shellWeight M (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)) U p
          ∂(zeroPotentialLaw M.P).toMeasure := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        exact (hshift g).symm
    _ = ∫ g, dirichletInfOn (shellWeight M g) U p
          ∂(zeroPotentialLaw M.P).toMeasure := integral_comp_translate_eq M z hmeas
    _ = ∫ omega, dirichletInfOn (shellFactor M 0 omega) U p ∂M.P.toMeasure :=
        (integral_apply_zero_eq_integral_zeroPotentialLaw M hmeas).symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
