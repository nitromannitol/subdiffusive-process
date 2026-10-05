module

public import SubdiffusiveProcess.Assumptions.PotentialField
public import Homogenization.Geometry.SignedPermutation

@[expose] public section

/-!
# Actions on scalar potential fields

These are the translation, scale, sign, and signed-coordinate-permutation
actions appearing.
-/



namespace SubdiffusiveProcess.Model.PotentialField

open Homogenization Topology

noncomputable section

variable {d : ℕ}

public def valueScaleMap (c : ℝ) : C(ℝ, ℝ) :=
  ⟨fun y ↦ c * y, continuous_const.mul continuous_id⟩

public def derivScaleCLM (c : ℝ) :
    (Vec d →L[ℝ] ℝ) →L[ℝ] (Vec d →L[ℝ] ℝ) :=
  c • ContinuousLinearMap.id ℝ (Vec d →L[ℝ] ℝ)

public def derivScaleMap (c : ℝ) :
    C(Vec d →L[ℝ] ℝ, Vec d →L[ℝ] ℝ) :=
  ⟨derivScaleCLM c, (derivScaleCLM c).continuous⟩

public def scaleAmbient (c : ℝ) :
    (C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ)) →
      C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ) := fun p ↦
  ((valueScaleMap c).comp p.1, (derivScaleMap c).comp p.2)

private theorem continuous_scaleAmbient (c : ℝ) :
    Continuous (scaleAmbient (d := d) c) :=
  ((ContinuousMap.continuous_postcomp (valueScaleMap c)).comp continuous_fst).prodMk
    ((ContinuousMap.continuous_postcomp (derivScaleMap c)).comp continuous_snd)

/-- Multiply a potential and its derivative by a scalar. -/
def scale (c : ℝ) (g : PotentialField d) : PotentialField d :=
  ⟨scaleAmbient c g.1, by
    constructor
    · intro x
      simpa only [scaleAmbient, valueScaleMap, derivScaleMap, derivScaleCLM,
        ContinuousMap.comp_apply] using! (g.hasFDerivAt x).const_smul c
    · intro K hK
      obtain ⟨C, hC⟩ := g.2.2 K hK
      refine ⟨‖derivScaleCLM (d := d) c‖₊ * C, ?_⟩
      simpa only [scaleAmbient, derivScaleMap, ContinuousMap.comp_apply,
        Function.comp_def] using!
        (derivScaleCLM (d := d) c).lipschitzWith.comp_lipschitzOnWith hC⟩

@[simp]
theorem scale_apply (c : ℝ) (g : PotentialField d) (x : Vec d) :
    scale c g x = c * g x :=
  rfl

theorem continuous_scale (c : ℝ) : Continuous (scale (d := d) c) :=
  Continuous.subtype_mk
    ((continuous_scaleAmbient c).comp continuous_subtype_val)
    (fun g ↦ (scale c g).2)

public def translateMap (z : Vec d) : C(Vec d, Vec d) :=
  ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩

public def translateAmbient (z : Vec d) :
    (C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ)) →
      C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ) := fun p ↦
  (p.1.comp (translateMap z), p.2.comp (translateMap z))

private theorem continuous_translateAmbient (z : Vec d) :
    Continuous (translateAmbient (d := d) z) :=
  ((ContinuousMap.continuous_precomp (translateMap z)).comp continuous_fst).prodMk
    ((ContinuousMap.continuous_precomp (translateMap z)).comp continuous_snd)

/-- Translation in the convention `g(x + z)`. -/
def translate (z : Vec d) (g : PotentialField d) : PotentialField d :=
  ⟨translateAmbient z g.1, by
    constructor
    · intro x
      simpa only [translateAmbient, translateMap, ContinuousMap.comp_apply,
        Function.comp_def] using!
        (g.hasFDerivAt (x + z)).comp x ((hasFDerivAt_id x).add_const z)
    · intro K hK
      let T : Vec d → Vec d := fun x ↦ x + z
      obtain ⟨C, hC⟩ := g.2.2 (T '' K)
        (hK.image (isometry_add_right z).continuous)
      refine ⟨C, ?_⟩
      simpa only [translateAmbient, translateMap, ContinuousMap.comp_apply,
        Function.comp_def, T, mul_one] using!
        hC.comp (isometry_add_right z).lipschitzWith.lipschitzOnWith
          (Set.mapsTo_image T K)⟩

@[simp]
theorem translate_apply (z : Vec d) (g : PotentialField d) (x : Vec d) :
    translate z g x = g (x + z) :=
  rfl

theorem continuous_translate (z : Vec d) :
    Continuous (translate (d := d) z) :=
  Continuous.subtype_mk
    ((continuous_translateAmbient z).comp continuous_subtype_val)
    (fun g ↦ (translate z g).2)

theorem measurable_translate (z : Vec d) : Measurable (translate (d := d) z) :=
  (continuous_translate z).measurable

public def spatialCLM (r : ℝ) : Vec d →L[ℝ] Vec d :=
  r • ContinuousLinearMap.id ℝ (Vec d)

public def spatialMap (r : ℝ) : C(Vec d, Vec d) :=
  ⟨spatialCLM r, (spatialCLM r).continuous⟩

public def spatialScaleAmbient (r : ℝ) :
    (C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ)) →
      C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ) := fun p ↦
  (p.1.comp (spatialMap r),
    (derivScaleMap r).comp (p.2.comp (spatialMap r)))

private theorem continuous_spatialScaleAmbient (r : ℝ) :
    Continuous (spatialScaleAmbient (d := d) r) :=
  ((ContinuousMap.continuous_precomp (spatialMap r)).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_postcomp (derivScaleMap r)).comp
      (ContinuousMap.continuous_precomp (spatialMap r))).comp continuous_snd)

/-- Precompose by `x ↦ r x`, retaining the exact chain-rule factor. -/
def spatialScale (r : ℝ) (g : PotentialField d) : PotentialField d :=
  ⟨spatialScaleAmbient r g.1, by
    constructor
    · intro x
      simpa only [spatialScaleAmbient, spatialMap, spatialCLM, derivScaleMap,
        derivScaleCLM, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        ContinuousMap.coe_comp, ContinuousLinearMap.comp_smul,
        ContinuousLinearMap.comp_id, Function.comp_def] using!
        (g.hasFDerivAt (r • x)).comp x ((hasFDerivAt_id x).const_smul r)
    · intro K hK
      let S : Vec d → Vec d := spatialCLM (d := d) r
      obtain ⟨C, hC⟩ := g.2.2 (S '' K)
        (hK.image (spatialCLM (d := d) r).continuous)
      have hinner := hC.comp
        (spatialCLM (d := d) r).lipschitzWith.lipschitzOnWith
        (Set.mapsTo_image S K)
      refine ⟨‖derivScaleCLM (d := d) r‖₊ *
          (C * ‖spatialCLM (d := d) r‖₊), ?_⟩
      simpa only [spatialScaleAmbient, spatialMap, derivScaleMap,
        ContinuousMap.comp_apply, Function.comp_def, S] using!
        (derivScaleCLM (d := d) r).lipschitzWith.comp_lipschitzOnWith hinner⟩

@[simp]
theorem spatialScale_apply (r : ℝ) (g : PotentialField d) (x : Vec d) :
    spatialScale r g x = g (r • x) :=
  rfl

theorem continuous_spatialScale (r : ℝ) :
    Continuous (spatialScale (d := d) r) :=
  Continuous.subtype_mk
    ((continuous_spatialScaleAmbient r).comp continuous_subtype_val)
    (fun g ↦ (spatialScale r g).2)

/-- The source scaling action `g(x) ↦ g(3⁻ᵏ x)`. -/
def triadicScale (k : ℕ) (g : PotentialField d) : PotentialField d :=
  spatialScale (((3 : ℝ) ^ k)⁻¹) g

@[simp]
theorem triadicScale_apply (k : ℕ) (g : PotentialField d) (x : Vec d) :
    triadicScale k g x = g ((((3 : ℝ) ^ k)⁻¹) • x) :=
  rfl

theorem continuous_triadicScale (k : ℕ) :
    Continuous (triadicScale (d := d) k) :=
  continuous_spatialScale _

theorem measurable_triadicScale (k : ℕ) :
    Measurable (triadicScale (d := d) k) :=
  (continuous_triadicScale k).measurable

/-- Negation of a potential and its derivative. -/
def negate (g : PotentialField d) : PotentialField d :=
  scale (-1) g

@[simp]
theorem negate_apply (g : PotentialField d) (x : Vec d) :
    negate g x = -g x := by
  rw [negate, scale_apply]
  ring

theorem measurable_negate : Measurable (negate (d := d)) :=
  (continuous_scale (-1)).measurable

public def matVecContinuousLinearMap (R : Mat d) : Vec d →L[ℝ] Vec d :=
  ⟨Matrix.toLin' R, (Matrix.toLin' R).continuous_of_finiteDimensional⟩

public def rotateDerivativeMap (R : Mat d) :
    (Vec d →L[ℝ] ℝ) →L[ℝ] (Vec d →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (Vec d) (Vec d) ℝ).flip
    (matVecContinuousLinearMap R)

public def rotateDomainMap (R : Mat d) : C(Vec d, Vec d) :=
  ⟨matVecContinuousLinearMap R, (matVecContinuousLinearMap R).continuous⟩

public def rotateDerivativeContinuousMap (R : Mat d) :
    C(Vec d →L[ℝ] ℝ, Vec d →L[ℝ] ℝ) :=
  ⟨rotateDerivativeMap R, (rotateDerivativeMap R).continuous⟩

public def rotateAmbient (R : Mat d) :
    (C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ)) →
      C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ) := fun p ↦
  (p.1.comp (rotateDomainMap R),
    (rotateDerivativeContinuousMap R).comp (p.2.comp (rotateDomainMap R)))

private theorem continuous_rotateAmbient (R : Mat d) :
    Continuous (rotateAmbient (d := d) R) :=
  ((ContinuousMap.continuous_precomp (rotateDomainMap R)).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_postcomp (rotateDerivativeContinuousMap R)).comp
      (ContinuousMap.continuous_precomp (rotateDomainMap R))).comp continuous_snd)

/-- Precomposition by a signed coordinate permutation. -/
def rotate (R : Mat d) (_hR : IsSignedPermutationMatrix R)
    (g : PotentialField d) : PotentialField d :=
  ⟨rotateAmbient R g.1, by
    constructor
    · intro x
      simpa only [rotateAmbient, rotateDomainMap,
        rotateDerivativeContinuousMap, ContinuousMap.comp_apply,
        rotateDerivativeMap] using!
        (g.hasFDerivAt (matVecMul R x)).comp x
          (matVecContinuousLinearMap R).hasFDerivAt
    · intro K hK
      let S : Vec d → Vec d := matVecContinuousLinearMap R
      obtain ⟨C, hC⟩ := g.2.2 (S '' K)
        (hK.image (matVecContinuousLinearMap R).continuous)
      have hinner := hC.comp
        (matVecContinuousLinearMap R).lipschitzWith.lipschitzOnWith
        (Set.mapsTo_image S K)
      refine ⟨‖rotateDerivativeMap R‖₊ *
          (C * ‖matVecContinuousLinearMap R‖₊), ?_⟩
      simpa only [rotateAmbient, rotateDomainMap,
        rotateDerivativeContinuousMap, ContinuousMap.comp_apply,
        Function.comp_def, S] using!
        (rotateDerivativeMap R).lipschitzWith.comp_lipschitzOnWith hinner⟩

@[simp]
theorem rotate_apply (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (g : PotentialField d) (x : Vec d) :
    rotate R hR g x = g (matVecMul R x) :=
  rfl

theorem continuous_rotate (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Continuous (rotate (d := d) R hR) :=
  Continuous.subtype_mk
    ((continuous_rotateAmbient R).comp continuous_subtype_val)
    (fun g ↦ (rotate R hR g).2)

theorem measurable_rotate (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Measurable (rotate (d := d) R hR) :=
  (continuous_rotate R hR).measurable

end


end SubdiffusiveProcess.Model.PotentialField
