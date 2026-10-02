import Mathlib
/-! Theorem C: anomalous Hölder regularity and Liouville rigidity.
The vocabulary below reproduces the mathematical definitions needed by the statement.
The induced sample measure is written as its defining pullback measure. -/
set_option warn.classDefReducibility false
set_option autoImplicit false
noncomputable section
namespace SubdiffusiveProcessAudit.AnomalousHolderRegularity
open scoped BigOperators
namespace Homogenization
abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
def vecDot {d : ℕ} (x y : Homogenization.Vec d) : ℝ :=
  ∑ i, x i * y i
def vecNormSq {d : ℕ} (x : Homogenization.Vec d) : ℝ :=
  vecDot x x
def matVecMul {d : ℕ} (A : Mat d) (x : Homogenization.Vec d) : Homogenization.Vec d := fun i => ∑ j, A i j * x j
end Homogenization
namespace Homogenization
noncomputable def euclideanNorm {d : ℕ} (x : Homogenization.Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)
end Homogenization
open Homogenization Topology
def SubdiffusiveProcess.Frozen.Assumptions.PotentialField (d : ℕ) :=
  {p : C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) //
    (∀ x, HasFDerivAt p.1 (p.2 x) x) ∧
      ∀ K : Set (Homogenization.Vec d), IsCompact K →
        ∃ C : NNReal, LipschitzOnWith C p.2 K}
namespace Homogenization
abbrev scalarMatrix {d : ℕ} (sigma : ℝ) : Mat d :=
  sigma • (1 : Mat d)
end Homogenization
namespace Homogenization
open MeasureTheory
noncomputable section
structure RegCoeffField (d : ℕ) where
  toFun : Homogenization.Vec d → Mat d
  entry_measurable : ∀ i j, Measurable (fun x : Homogenization.Vec d => toFun x i j)
  entry_locInt : ∀ i j, LocallyIntegrable (fun x : Homogenization.Vec d => toFun x i j) volume
namespace RegCoeffField
variable {d : ℕ}
instance : CoeFun (RegCoeffField d) (fun _ => Homogenization.Vec d → Mat d) := ⟨toFun⟩
end RegCoeffField
end
end Homogenization
namespace Homogenization
open MeasureTheory
noncomputable section
variable {d : ℕ}
structure IsProbeR (φ : Homogenization.Vec d → ℝ) : Prop where
  measurable : Measurable φ
  bounded : ∃ C : ℝ, ∀ x, |φ x| ≤ C
  hasCompactSupport : HasCompactSupport φ
def entryTestR (i j : Fin d) (φ : Homogenization.Vec d → ℝ) (a : RegCoeffField d) : ℝ :=
  ∫ x, a x i j * φ x ∂volume
def LocalSigmaR (U : Set (Homogenization.Vec d)) : MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (i j : Fin d) (φ : Homogenization.Vec d → ℝ), IsProbeR φ ∧ Function.support φ ⊆ U ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTestR i j φ ⁻¹' t}
end
end Homogenization
namespace SubdiffusiveProcess.Frozen.Assumptions
open Homogenization MeasureTheory Topology
noncomputable section
noncomputable instance potentialFieldTopologicalSpace (d : ℕ) :
    TopologicalSpace (PotentialField d) :=
  TopologicalSpace.induced Subtype.val inferInstance
noncomputable instance potentialFieldMeasurableSpace (d : ℕ) :
    MeasurableSpace (PotentialField d) :=
  borel (PotentialField d)
instance potentialFieldBorelSpace (d : ℕ) : BorelSpace (PotentialField d) :=
  ⟨rfl⟩
namespace PotentialField
variable {d : ℕ}
instance : CoeFun (PotentialField d) (fun _ ↦ Homogenization.Vec d → ℝ) :=
  ⟨fun g ↦ g.1.1⟩
def deriv (g : PotentialField d) : C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) :=
  g.1.2
theorem hasFDerivAt (g : PotentialField d) (x : Homogenization.Vec d) :
    HasFDerivAt g (deriv g x) x :=
  g.2.1 x
theorem deriv_locallyLipschitz (g : PotentialField d) :
    LocallyLipschitz (deriv g) := by
  intro x
  obtain ⟨C, hC⟩ := g.2.2 (Metric.closedBall x 1) (isCompact_closedBall x 1)
  exact ⟨C, Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one,
    hC.mono Metric.ball_subset_closedBall⟩
theorem contDiff_one (g : PotentialField d) : ContDiff ℝ 1 g :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨deriv g, g.deriv_locallyLipschitz.continuous, g.hasFDerivAt⟩
theorem ext {g h : PotentialField d} (heq : ∀ x, g x = h x) : g = h := by
  have hval : g.1.1 = h.1.1 := ContinuousMap.ext heq
  have hderiv : g.1.2 = h.1.2 := by
    apply ContinuousMap.ext
    intro x
    exact (g.hasFDerivAt x).unique (by simpa only [hval] using! h.hasFDerivAt x)
  apply Subtype.ext
  exact Prod.ext hval hderiv
theorem continuous_eval (x : Homogenization.Vec d) :
    Continuous (fun g : PotentialField d ↦ g x) :=
  (continuous_eval_const x).comp continuous_subtype_val.fst
theorem measurable_eval (x : Homogenization.Vec d) :
    Measurable (fun g : PotentialField d ↦ g x) :=
  (continuous_eval x).measurable
theorem continuous_eval_deriv (x : Homogenization.Vec d) :
    Continuous (fun g : PotentialField d ↦ deriv g x) :=
  (continuous_eval_const x).comp continuous_subtype_val.snd
def forgetPotential (g : PotentialField d) : RegCoeffField d where
  toFun x := scalarMatrix (d := d) (g x)
  entry_measurable := fun i k ↦ by
    have hmat : Continuous (fun x : Homogenization.Vec d ↦ scalarMatrix (d := d) (g x)) :=
      g.1.1.continuous.smul continuous_const
    exact ((continuous_apply k).comp ((continuous_apply i).comp hmat)).measurable
  entry_locInt := fun i k ↦ by
    have hmat : Continuous (fun x : Homogenization.Vec d ↦ scalarMatrix (d := d) (g x)) :=
      g.1.1.continuous.smul continuous_const
    exact ((continuous_apply k).comp ((continuous_apply i).comp hmat)).locallyIntegrable
theorem forgetPotential_apply (g : PotentialField d) (x : Homogenization.Vec d) :
    forgetPotential g x = scalarMatrix (d := d) (g x) :=
  rfl
end PotentialField
end
end SubdiffusiveProcess.Frozen.Assumptions
namespace Homogenization
def IsSignedPermutationMatrix {d : ℕ} (R : Mat d) : Prop :=
  ∃ σ : Equiv.Perm (Fin d), ∃ s : Fin d → ℝ,
    (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ i j, R i j = if i = σ j then s j else 0
end Homogenization
namespace SubdiffusiveProcess.Frozen.Assumptions.PotentialField
open Homogenization Topology
noncomputable section
variable {d : ℕ}
def valueScaleMap (c : ℝ) : C(ℝ, ℝ) :=
  ⟨fun y ↦ c * y, continuous_const.mul continuous_id⟩
def derivScaleCLM (c : ℝ) :
    (Homogenization.Vec d →L[ℝ] ℝ) →L[ℝ] (Homogenization.Vec d →L[ℝ] ℝ) :=
  c • ContinuousLinearMap.id ℝ (Homogenization.Vec d →L[ℝ] ℝ)
def derivScaleMap (c : ℝ) :
    C(Homogenization.Vec d →L[ℝ] ℝ, Homogenization.Vec d →L[ℝ] ℝ) :=
  ⟨derivScaleCLM c, (derivScaleCLM c).continuous⟩
def scaleAmbient (c : ℝ) :
    (C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ)) →
      C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) := fun p ↦
  ((valueScaleMap c).comp p.1, (derivScaleMap c).comp p.2)
theorem continuous_scaleAmbient (c : ℝ) :
    Continuous (scaleAmbient (d := d) c) :=
  ((ContinuousMap.continuous_postcomp (valueScaleMap c)).comp continuous_fst).prodMk
    ((ContinuousMap.continuous_postcomp (derivScaleMap c)).comp continuous_snd)
def scale (c : ℝ) (g : PotentialField d) : PotentialField d :=
  ⟨scaleAmbient c g.1, by
    constructor
    · intro x
      simpa only [scaleAmbient, valueScaleMap, derivScaleMap, derivScaleCLM,
        ContinuousMap.comp_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv, ContinuousLinearMap.comp_id, id_eq, smul_apply, ContinuousLinearMap.id_apply] using! (g.hasFDerivAt x).const_smul c
    · intro K hK
      obtain ⟨C, hC⟩ := g.2.2 K hK
      refine ⟨‖derivScaleCLM (d := d) c‖₊ * C, ?_⟩
      simpa only [scaleAmbient, derivScaleMap, ContinuousMap.comp_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv, ContinuousLinearMap.comp_id, id_eq, smul_apply, ContinuousLinearMap.id_apply,
        Function.comp_def] using!
        (derivScaleCLM (d := d) c).lipschitzWith.comp_lipschitzOnWith hC⟩
theorem scale_apply (c : ℝ) (g : PotentialField d) (x : Homogenization.Vec d) :
    scale c g x = c * g x :=
  rfl
theorem continuous_scale (c : ℝ) : Continuous (scale (d := d) c) :=
  Continuous.subtype_mk
    ((continuous_scaleAmbient c).comp continuous_subtype_val)
    (fun g ↦ (scale c g).2)
def translateMap (z : Homogenization.Vec d) : C(Homogenization.Vec d, Homogenization.Vec d) :=
  ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩
def translateAmbient (z : Homogenization.Vec d) :
    (C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ)) →
      C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) := fun p ↦
  (p.1.comp (translateMap z), p.2.comp (translateMap z))
theorem continuous_translateAmbient (z : Homogenization.Vec d) :
    Continuous (translateAmbient (d := d) z) :=
  ((ContinuousMap.continuous_precomp (translateMap z)).comp continuous_fst).prodMk
    ((ContinuousMap.continuous_precomp (translateMap z)).comp continuous_snd)
def translate (z : Homogenization.Vec d) (g : PotentialField d) : PotentialField d :=
  ⟨translateAmbient z g.1, by
    constructor
    · intro x
      simpa only [translateAmbient, translateMap, ContinuousMap.comp_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv, ContinuousLinearMap.comp_id, id_eq, smul_apply, ContinuousLinearMap.id_apply,
        Function.comp_def] using!
        (g.hasFDerivAt (x + z)).comp x ((hasFDerivAt_id x).add_const z)
    · intro K hK
      let T : Homogenization.Vec d → Homogenization.Vec d := fun x ↦ x + z
      obtain ⟨C, hC⟩ := g.2.2 (T '' K)
        (hK.image (isometry_add_right z).continuous)
      refine ⟨C, ?_⟩
      simpa only [translateAmbient, translateMap, ContinuousMap.comp_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv, ContinuousLinearMap.comp_id, id_eq, smul_apply, ContinuousLinearMap.id_apply,
        Function.comp_def, T, mul_one] using!
        hC.comp (isometry_add_right z).lipschitzWith.lipschitzOnWith
          (Set.mapsTo_image T K)⟩
theorem translate_apply (z : Homogenization.Vec d) (g : PotentialField d) (x : Homogenization.Vec d) :
    translate z g x = g (x + z) :=
  rfl
theorem continuous_translate (z : Homogenization.Vec d) :
    Continuous (translate (d := d) z) :=
  Continuous.subtype_mk
    ((continuous_translateAmbient z).comp continuous_subtype_val)
    (fun g ↦ (translate z g).2)
theorem measurable_translate (z : Homogenization.Vec d) : Measurable (translate (d := d) z) :=
  (continuous_translate z).measurable
def spatialCLM (r : ℝ) : Homogenization.Vec d →L[ℝ] Homogenization.Vec d :=
  r • ContinuousLinearMap.id ℝ (Homogenization.Vec d)
def spatialMap (r : ℝ) : C(Homogenization.Vec d, Homogenization.Vec d) :=
  ⟨spatialCLM r, (spatialCLM r).continuous⟩
def spatialScaleAmbient (r : ℝ) :
    (C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ)) →
      C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) := fun p ↦
  (p.1.comp (spatialMap r),
    (derivScaleMap r).comp (p.2.comp (spatialMap r)))
theorem continuous_spatialScaleAmbient (r : ℝ) :
    Continuous (spatialScaleAmbient (d := d) r) :=
  ((ContinuousMap.continuous_precomp (spatialMap r)).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_postcomp (derivScaleMap r)).comp
      (ContinuousMap.continuous_precomp (spatialMap r))).comp continuous_snd)
def spatialScale (r : ℝ) (g : PotentialField d) : PotentialField d :=
  ⟨spatialScaleAmbient r g.1, by
    constructor
    · intro x
      simpa only [spatialScaleAmbient, spatialMap, spatialCLM, derivScaleMap,
        derivScaleCLM, ContinuousMap.comp_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv, ContinuousLinearMap.comp_id, id_eq, smul_apply, ContinuousLinearMap.id_apply, ContinuousMap.coe_mk,
        ContinuousMap.coe_comp, ContinuousLinearMap.comp_smul,
        ContinuousLinearMap.comp_id, Function.comp_def] using!
        (g.hasFDerivAt (r • x)).comp x ((hasFDerivAt_id x).const_smul r)
    · intro K hK
      let S : Homogenization.Vec d → Homogenization.Vec d := spatialCLM (d := d) r
      obtain ⟨C, hC⟩ := g.2.2 (S '' K)
        (hK.image (spatialCLM (d := d) r).continuous)
      have hinner := hC.comp
        (spatialCLM (d := d) r).lipschitzWith.lipschitzOnWith
        (Set.mapsTo_image S K)
      refine ⟨‖derivScaleCLM (d := d) r‖₊ *
          (C * ‖spatialCLM (d := d) r‖₊), ?_⟩
      simpa only [spatialScaleAmbient, spatialMap, derivScaleMap,
        ContinuousMap.comp_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv, ContinuousLinearMap.comp_id, id_eq, smul_apply, ContinuousLinearMap.id_apply, Function.comp_def, S] using!
        (derivScaleCLM (d := d) r).lipschitzWith.comp_lipschitzOnWith hinner⟩
theorem spatialScale_apply (r : ℝ) (g : PotentialField d) (x : Homogenization.Vec d) :
    spatialScale r g x = g (r • x) :=
  rfl
theorem continuous_spatialScale (r : ℝ) :
    Continuous (spatialScale (d := d) r) :=
  Continuous.subtype_mk
    ((continuous_spatialScaleAmbient r).comp continuous_subtype_val)
    (fun g ↦ (spatialScale r g).2)
def triadicScale (k : ℕ) (g : PotentialField d) : PotentialField d :=
  spatialScale (((3 : ℝ) ^ k)⁻¹) g
theorem triadicScale_apply (k : ℕ) (g : PotentialField d) (x : Homogenization.Vec d) :
    triadicScale k g x = g ((((3 : ℝ) ^ k)⁻¹) • x) :=
  rfl
theorem continuous_triadicScale (k : ℕ) :
    Continuous (triadicScale (d := d) k) :=
  continuous_spatialScale _
theorem measurable_triadicScale (k : ℕ) :
    Measurable (triadicScale (d := d) k) :=
  (continuous_triadicScale k).measurable
def negate (g : PotentialField d) : PotentialField d :=
  scale (-1) g
theorem negate_apply (g : PotentialField d) (x : Homogenization.Vec d) :
    negate g x = -g x := by
  rw [negate, scale_apply]
  ring
theorem measurable_negate : Measurable (negate (d := d)) :=
  (continuous_scale (-1)).measurable
def matVecContinuousLinearMap (R : Mat d) : Homogenization.Vec d →L[ℝ] Homogenization.Vec d :=
  ⟨Matrix.toLin' R, (Matrix.toLin' R).continuous_of_finiteDimensional⟩
def rotateDerivativeMap (R : Mat d) :
    (Homogenization.Vec d →L[ℝ] ℝ) →L[ℝ] (Homogenization.Vec d →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (Homogenization.Vec d) (Homogenization.Vec d) ℝ).flip
    (matVecContinuousLinearMap R)
def rotateDomainMap (R : Mat d) : C(Homogenization.Vec d, Homogenization.Vec d) :=
  ⟨matVecContinuousLinearMap R, (matVecContinuousLinearMap R).continuous⟩
def rotateDerivativeContinuousMap (R : Mat d) :
    C(Homogenization.Vec d →L[ℝ] ℝ, Homogenization.Vec d →L[ℝ] ℝ) :=
  ⟨rotateDerivativeMap R, (rotateDerivativeMap R).continuous⟩
def rotateAmbient (R : Mat d) :
    (C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ)) →
      C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) := fun p ↦
  (p.1.comp (rotateDomainMap R),
    (rotateDerivativeContinuousMap R).comp (p.2.comp (rotateDomainMap R)))
theorem continuous_rotateAmbient (R : Mat d) :
    Continuous (rotateAmbient (d := d) R) :=
  ((ContinuousMap.continuous_precomp (rotateDomainMap R)).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_postcomp (rotateDerivativeContinuousMap R)).comp
      (ContinuousMap.continuous_precomp (rotateDomainMap R))).comp continuous_snd)
def rotate (R : Mat d) (_hR : IsSignedPermutationMatrix R)
    (g : PotentialField d) : PotentialField d :=
  ⟨rotateAmbient R g.1, by
    constructor
    · intro x
      simpa only [rotateAmbient, rotateDomainMap,
        rotateDerivativeContinuousMap, ContinuousMap.comp_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv, ContinuousLinearMap.comp_id, id_eq, smul_apply, ContinuousLinearMap.id_apply,
        rotateDerivativeMap] using!
        (g.hasFDerivAt (matVecMul R x)).comp x
          (matVecContinuousLinearMap R).hasFDerivAt
    · intro K hK
      let S : Homogenization.Vec d → Homogenization.Vec d := matVecContinuousLinearMap R
      obtain ⟨C, hC⟩ := g.2.2 (S '' K)
        (hK.image (matVecContinuousLinearMap R).continuous)
      have hinner := hC.comp
        (matVecContinuousLinearMap R).lipschitzWith.lipschitzOnWith
        (Set.mapsTo_image S K)
      refine ⟨‖rotateDerivativeMap R‖₊ *
          (C * ‖matVecContinuousLinearMap R‖₊), ?_⟩
      simpa only [rotateAmbient, rotateDomainMap,
        rotateDerivativeContinuousMap, ContinuousMap.comp_apply, ContinuousMap.coe_comp, ContinuousMap.coe_mk, deriv, ContinuousLinearMap.comp_id, id_eq, smul_apply, ContinuousLinearMap.id_apply,
        Function.comp_def, S] using!
        (rotateDerivativeMap R).lipschitzWith.comp_lipschitzOnWith hinner⟩
theorem rotate_apply (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (g : PotentialField d) (x : Homogenization.Vec d) :
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
end SubdiffusiveProcess.Frozen.Assumptions.PotentialField
abbrev SubdiffusiveProcess.Frozen.Assumptions.PotentialSample (d : ℕ) :=
  ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d
namespace SubdiffusiveProcess.Frozen.Assumptions
open Filter Homogenization Topology
open scoped BigOperators
noncomputable section
namespace PotentialField
variable {d : ℕ}
def add (g h : PotentialField d) : PotentialField d :=
  ⟨(g.1.1 + h.1.1, deriv g + deriv h), by
    constructor
    · intro x
      exact (g.hasFDerivAt x).add (h.hasFDerivAt x)
    · intro K hK
      obtain ⟨Cg, hg⟩ := g.2.2 K hK
      obtain ⟨Ch, hh⟩ := h.2.2 K hK
      exact ⟨Cg + Ch, hg.add hh⟩⟩
theorem add_apply (g h : PotentialField d) (x : Homogenization.Vec d) :
    add g h x = g x + h x :=
  rfl
theorem add_deriv (g h : PotentialField d) (x : Homogenization.Vec d) :
    deriv (add g h) x = deriv g x + deriv h x :=
  rfl
def anchor (g : PotentialField d) : PotentialField d :=
  ⟨(⟨fun x ↦ g x - g 0, g.1.1.continuous.sub continuous_const⟩, deriv g), by
    constructor
    · intro x
      exact (g.hasFDerivAt x).sub_const (g 0)
    · exact g.2.2⟩
theorem anchor_apply (g : PotentialField d) (x : Homogenization.Vec d) :
    anchor g x = g x - g 0 :=
  rfl
theorem anchor_deriv (g : PotentialField d) (x : Homogenization.Vec d) :
    deriv (anchor g) x = deriv g x :=
  rfl
theorem anchor_origin (g : PotentialField d) : anchor g 0 = 0 := by
  rw [anchor_apply, sub_self]
end PotentialField
variable {d : ℕ}
def anchoredPartialSum (omega : PotentialSample d) (L : ℕ) (x : Homogenization.Vec d) : ℝ :=
  ∑ k ∈ Finset.range (L + 1), (omega k x - omega k 0)
def anchoredPartialSumField (omega : PotentialSample d) : ℕ → PotentialField d
  | 0 => PotentialField.anchor (omega 0)
  | L + 1 => PotentialField.add (anchoredPartialSumField omega L)
      (PotentialField.anchor (omega (L + 1)))
theorem anchoredPartialSumField_apply (omega : PotentialSample d) (L : ℕ)
    (x : Homogenization.Vec d) :
    anchoredPartialSumField omega L x = anchoredPartialSum omega L x := by
  induction L with
  | zero =>
      simp only [anchoredPartialSumField, PotentialField.anchor_apply,
        anchoredPartialSum, Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add]
  | succ L ih =>
      rw [anchoredPartialSumField, PotentialField.add_apply, ih,
        PotentialField.anchor_apply]
      change
        (∑ k ∈ Finset.range (L + 1), (omega k x - omega k 0)) +
            (omega (L + 1) x - omega (L + 1) 0) =
          ∑ k ∈ Finset.range ((L + 1) + 1), (omega k x - omega k 0)
      exact (Finset.sum_range_succ _ _).symm
def LipschitzSeminormCauchyOn
    (F : ℕ → Homogenization.Vec d → (Homogenization.Vec d →L[ℝ] ℝ)) (K : Set (Homogenization.Vec d)) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    LipschitzOnWith (Real.toNNReal epsilon) (fun x ↦ F m x - F n x) K
end
end SubdiffusiveProcess.Frozen.Assumptions
open MeasureTheory ProbabilityTheory
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw {d : ℕ}
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (k : ℕ) :
    ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
  P.map (fun omega => omega k)
open MeasureTheory ProbabilityTheory
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw {d : ℕ}
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) :
    ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
  SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw P 0
open Homogenization MeasureTheory ProbabilityTheory
structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawPrefix (d : ℕ) (delta : ℝ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  dimension : 2 ≤ d
  delta_pos : 0 < delta
  delta_le_half : delta ≤ (1 : ℝ) / 2
  independent :
    iIndepFun (fun k : ℕ ↦ fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦ ω k)
      P.toMeasure
  marginal_scaling : ∀ k : ℕ,
    SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw P k =
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
open Homogenization
def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma {d : ℕ}
    (U : Set (Homogenization.Vec d)) :
    MeasurableSpace (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
  MeasurableSpace.comap
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.forgetPotential
    (LocalSigmaR U)
open Homogenization MeasureTheory ProbabilityTheory
structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  integrable : ∀ x : Homogenization.Vec d,
    Integrable (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦ ω 0 x) P.toMeasure
  mean_zero : ∀ x : Homogenization.Vec d,
    ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, ω 0 x ∂P.toMeasure = 0
  stationary : ∀ z : Homogenization.Vec d,
    Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure =
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure
  range_dependence : ∀ (U V : Set (Homogenization.Vec d)),
    MeasurableSet U → MeasurableSet V →
      (∀ ⦃x y : Homogenization.Vec d⦄, x ∈ U → y ∈ V →
        Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y)) →
      Indep (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U)
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma V)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure
namespace Homogenization
structure TriadicCube (d : ℕ) where
  scale : ℤ
  index : Fin d → ℤ
deriving DecidableEq, Repr
noncomputable def cubeScaleFactor {d : ℕ} (Q : TriadicCube d) : ℝ :=
  (3 : ℝ) ^ Q.scale
def openCubeSet {d : ℕ} (Q : TriadicCube d) : Set (Homogenization.Vec d) :=
  { x | ∀ i,
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q < x i) ∧
      (x i < (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)) }
def originCube (d : ℕ) (m : ℤ) : TriadicCube d :=
  { scale := m
    index := 0 }
end Homogenization
open Homogenization
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeValueNorm
    {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  sSup (Set.range fun o : Option
      {x : Homogenization.Vec d // x ∈ openCubeSet (originCube d 0)} ↦
    match o with
    | none => 0
    | some x => |g x.1|)
open Homogenization
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivNorm
    {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  sSup (Set.range fun o : Option
      {x : Homogenization.Vec d // x ∈ openCubeSet (originCube d 0)} ↦
    match o with
    | none => 0
    | some x => ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x.1‖)
open Homogenization
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivLipschitzSeminorm
    {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  sSup (Set.range fun o : Option
      {p : ({x : Homogenization.Vec d // x ∈ openCubeSet (originCube d 0)} ×
          {x : Homogenization.Vec d // x ∈ openCubeSet (originCube d 0)}) // p.1 ≠ p.2} ↦
    match o with
    | none => 0
    | some p =>
        dist (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g p.1.1.1)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g p.1.2.1) /
          dist p.1.1.1 p.1.2.1)
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable {d : ℕ}
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeValueNorm g +
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivNorm g +
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivLipschitzSeminorm g
open MeasureTheory
def SubdiffusiveProcess.OGammaLE {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (σ A : ℝ) (X : Ω → ℝ) : Prop :=
  Integrable
      (fun ω ↦ Real.exp ((A⁻¹ * max (X ω) 0) ^ σ)) μ ∧
    ∫ ω, Real.exp ((A⁻¹ * max (X ω) 0) ^ σ) ∂μ ≤ 2
open MeasureTheory ProbabilityTheory
structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 (d : ℕ) (delta : ℝ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  regularity_expectation :
    SubdiffusiveProcess.OGammaLE (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure 2 delta
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
open Homogenization MeasureTheory ProbabilityTheory
structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG3 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  signed_coordinate_permutations : ∀ (R : Mat d)
      (hR : IsSignedPermutationMatrix R),
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR) =
      SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P
  negation :
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).map SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate =
      SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P
open MeasureTheory ProbabilityTheory
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.tauSq {d : ℕ}
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : ℝ :=
  Real.log
    (∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (g 0)
      ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure)
open MeasureTheory ProbabilityTheory
structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG4 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  exponential_integrable :
    Integrable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d ↦ Real.exp (g 0))
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure
  tauSq_pos : 0 < SubdiffusiveProcess.Frozen.Assumptions.tauSq P
open MeasureTheory
structure SubdiffusiveProcess.Frozen.Assumptions.GMCModel (d : ℕ) where
  delta : ℝ
  P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
  shellPrefix : SubdiffusiveProcess.Frozen.Assumptions.ShellLawPrefix d delta P
  G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d P
  G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta P
  G3 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG3 d P
  G4 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG4 d P
open Homogenization
open scoped BigOperators
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.aCutoff {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Homogenization.Vec d) : ℝ :=
  Real.exp
    (∑ k ∈ Finset.range (L + 1),
      (ω k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
namespace Homogenization
def basisVec {d : ℕ} (i : Fin d) : Homogenization.Vec d :=
  Pi.single i (1 : ℝ)
def HasWeakPartialDerivOn {d : ℕ} (U : Set (Homogenization.Vec d)) (i : Fin d)
    (u gi : Homogenization.Vec d → ℝ) : Prop :=
  ∀ φ : Homogenization.Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
      -∫ x in U, gi x * φ x ∂MeasureTheory.volume
def HasWeakGradientOn {d : ℕ} (U : Set (Homogenization.Vec d)) (u : Homogenization.Vec d → ℝ) (Du : Homogenization.Vec d → Homogenization.Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)
namespace HasWeakPartialDerivOn
end HasWeakPartialDerivOn
end Homogenization
namespace Homogenization
abbrev MemL2On {d : ℕ} (U : Set (Homogenization.Vec d)) (u : Homogenization.Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict U)
def GradMemL2On {d : ℕ} (U : Set (Homogenization.Vec d)) (Du : Homogenization.Vec d → Homogenization.Vec d) : Prop :=
  ∀ i : Fin d, MemL2On U (fun x => Du x i)
structure H1Function {d : ℕ} (U : Set (Homogenization.Vec d)) where
  toFun : Homogenization.Vec d → ℝ
  grad : Homogenization.Vec d → Homogenization.Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad
instance {d : ℕ} {U : Set (Homogenization.Vec d)} : CoeFun (H1Function U) (fun _ => Homogenization.Vec d → ℝ) where
  coe u := u.toFun
structure H10Function {d : ℕ} (U : Set (Homogenization.Vec d)) extends H1Function U where
  approx : ℕ → Homogenization.Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun x => approx n x - toH1Function.toFun x) 2
        (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm
          (fun x => (fderiv ℝ (approx n) x) (basisVec i) - toH1Function.grad x i) 2
          (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0)
instance {d : ℕ} {U : Set (Homogenization.Vec d)} : CoeFun (H10Function U) (fun _ => Homogenization.Vec d → ℝ) where
  coe u := u.toH1Function.toFun
end Homogenization
namespace Homogenization
noncomputable def volumeAverage {d : ℕ} (U : Set (Homogenization.Vec d)) (f : Homogenization.Vec d → ℝ) : ℝ :=
  (MeasureTheory.volume U).toReal⁻¹ * ∫ x in U, f x ∂MeasureTheory.volume
end Homogenization
namespace SubdiffusiveProcess.CoarseGrainingVocab
open Filter MeasureTheory
noncomputable section
abbrev Vec (d : ℕ) := Homogenization.Vec d
end
end SubdiffusiveProcess.CoarseGrainingVocab
namespace SubdiffusiveProcess.CoarseGrainingVocab
open Filter MeasureTheory Homogenization
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
def cube (d : ℕ) (m : ℤ) : Set (Homogenization.Vec d) :=
  openCubeSet (originCube d m)
def translatedCube (d : ℕ) (m : ℤ) (z : Homogenization.Vec d) : Set (Homogenization.Vec d) :=
  (fun x ↦ z + x) '' cube d m
def IsWeaklyHarmonicOn {d : ℕ} (a : Homogenization.Vec d → ℝ) (W : Set (Homogenization.Vec d))
    (u : H1Function W) : Prop :=
  ∀ φ : H10Function W,
    ∫ x in W, vecDot (a x • u.grad x) (φ.toH1Function.grad x) ∂volume = 0
def normalizedL2On {d : ℕ} (W : Set (Homogenization.Vec d)) (f : Homogenization.Vec d → ℝ) : ℝ :=
  Real.sqrt (volumeAverage W (fun x ↦ f x ^ 2))
def vectorNormalizedL2On {d : ℕ} (W : Set (Homogenization.Vec d))
    (f : Homogenization.Vec d → Homogenization.Vec d) : ℝ :=
  normalizedL2On W (fun x ↦ Homogenization.euclideanNorm (f x))
def averageOn {d : ℕ} (W : Set (Homogenization.Vec d)) (f : Homogenization.Vec d → ℝ) : ℝ :=
  volumeAverage W f
def OnTriadicGrid {d : ℕ} (n : ℕ) (z : Homogenization.Vec d) : Prop :=
  ∀ i : Fin d, ∃ k : ℤ, z i = (3 : ℝ) ^ n * k
end
end SubdiffusiveProcess.CoarseGrainingVocab
open Filter Homogenization Topology
structure SubdiffusiveProcess.Frozen.Assumptions.IsAnchoredC11Limit {d : ℕ}
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : Prop where
  value_tendsto : ∀ K : Set (Homogenization.Vec d), IsCompact K →
    TendstoUniformlyOn
      (fun L x ↦ SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSum omega L x)
      g atTop K
  deriv_tendsto : ∀ K : Set (Homogenization.Vec d), IsCompact K →
    TendstoUniformlyOn
      (fun L x ↦ SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
        (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField omega L) x)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g) atTop K
  deriv_lipschitz_cauchy : ∀ K : Set (Homogenization.Vec d), IsCompact K →
    SubdiffusiveProcess.Frozen.Assumptions.LipschitzSeminormCauchyOn
      (fun L x ↦ SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv
        (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField omega L) x) K
  anchored : g 0 = 0
def SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet (d : ℕ) :
    Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
  {omega | ∃! g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
    SubdiffusiveProcess.Frozen.Assumptions.IsAnchoredC11Limit omega g}
abbrev SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample (d : ℕ) :=
  {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d //
    omega ∈ SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet d}
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.anchoredLog {d : ℕ}
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
  Classical.choose omega.property.exists
open Homogenization
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.aAnchored {d : ℕ}
    (_M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    (x : Homogenization.Vec d) : ℝ :=
  Real.exp (SubdiffusiveProcess.Frozen.Assumptions.anchoredLog omega x)
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.coefficientAt {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) :
    SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ :=
  match L with
  | ⊤ => SubdiffusiveProcess.Frozen.Assumptions.aAnchored M ω
  | (n : ℕ) => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n ω.1
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.gammaReg (C0 delta : ℝ) : ℝ :=
  1 - C0 * delta * |Real.log delta| ^ (1 / 2 : ℝ)
open Filter SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions MeasureTheory ProbabilityTheory
open Homogenization
open Set
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology
theorem theoremC (d : ℕ) (hd : 2 ≤ d) :
    ∃ delta0 C0 C : ℝ, 0 < delta0 ∧ 0 < C0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
        let mu := Measure.comap (Subtype.val : AnchoredC11Sample d → PotentialSample d) M.P.toMeasure
        gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
        ∀ gamma ∈ Set.Icc (1 / 2 : ℝ) (gammaReg C0 M.delta),
          ∃ Lscale : WithTop ℕ → ℕ → AnchoredC11Sample d → ℕ,
            (∀ (L : WithTop ℕ) (m : ℕ), Measurable (Lscale L m)) ∧
            (∀ (L : WithTop ℕ) (m k : ℕ), 0 < k →
              mu {omega | k < Lscale L m omega} ≤
                ENNReal.ofReal (C * Real.exp (
                  -((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                    (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ᵐ omega ∂mu,
              (∀ (L : WithTop ℕ) (m : ℕ), 0 < m →
                ∀ u : H1Function (openCubeSet (originCube d m)),
                  IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) u →
                  ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (Lscale L m omega : ℤ) →
                    ∀ z : Homogenization.Vec d, OnTriadicGrid n z →
                    translatedCube d n z ⊆ cube d (m - 1) →
                      normalizedL2On (translatedCube d n z)
                          (fun x => u.toFun x - averageOn (translatedCube d n z) u.toFun) ≤
                        C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) *
                          normalizedL2On (cube d m)
                            (fun x => u.toFun x - averageOn (cube d m) u.toFun) ∧
                      vectorNormalizedL2On (translatedCube d n z)
                          (fun x => Real.sqrt (coefficientAt M L omega x) • u.grad x) ≤
                        C * (3 : ℝ) ^ ((1 - gamma) * ((m : ℝ) - (n : ℝ))) *
                          vectorNormalizedL2On (cube d m)
                            (fun x => Real.sqrt (coefficientAt M L omega x) • u.grad x)) ∧
              (∀ (L : WithTop ℕ) (u : Homogenization.Vec d → ℝ),
                (∀ m : ℤ, ∃ um : H1Function (openCubeSet (originCube d m)),
                  (∀ x, um.toFun x = u x) ∧
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um) →
                (∀ eps > 0, ∃ᶠ R : ℝ in atTop, R ^ (-gammaReg C0 M.delta) *
                    sInf {r : ℝ | ∃ c : ℝ,
                      r = normalizedL2On (Metric.ball (0 : Homogenization.Vec d) R) (fun x => u x - c)} < eps) →
                ∃ uRep : Homogenization.Vec d → ℝ,
                  Continuous uRep ∧ uRep =ᵐ[volume] u ∧
                  (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
                    (∀ x, um.toFun x = u x) →
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um →
                    uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
                  ∃ c : ℝ, ∀ x, uRep x = c)  := by
  sorry
end SubdiffusiveProcessAudit.AnomalousHolderRegularity
