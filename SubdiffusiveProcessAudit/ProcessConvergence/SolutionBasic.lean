module
public import Mathlib
@[expose] public section
open scoped Distributions
set_option autoImplicit false
noncomputable section
namespace SubdiffusiveProcessAudit.ProcessConvergence open scoped BigOperators namespace Homogenization
abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
def vecDot {d : ℕ} (x y : Homogenization.Vec d) : ℝ := ∑ i, x i * y i
def vecNormSq {d : ℕ} (x : Homogenization.Vec d) : ℝ := vecDot x x
theorem vecNormSq_nonneg {d : ℕ} (x : Homogenization.Vec d) : 0 ≤ vecNormSq x := by
  unfold vecNormSq vecDot
  refine Finset.sum_nonneg ?_
  intro i hi
  nlinarith [sq_nonneg (x i)]
def matVecMul {d : ℕ} (A : Mat d) (x : Homogenization.Vec d) : Homogenization.Vec d := fun i => ∑ j, A i j * x j
def matTranspose {d : ℕ} (A : Mat d) : Mat d := Matrix.transpose A
noncomputable def symmPart {d : ℕ} (A : Mat d) : Mat d := fun i j => (A i j + A j i) / 2
end Homogenization namespace Homogenization
noncomputable def euclideanNorm {d : ℕ} (x : Homogenization.Vec d) : ℝ := Real.sqrt (vecNormSq x)
end Homogenization open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization Topology
def SubdiffusiveProcess.Frozen.Assumptions.PotentialField (d : ℕ) :=
  {p : C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) //
    (∀ x, HasFDerivAt p.1 (p.2 x) x) ∧
      ∀ K : Set (Homogenization.Vec d), IsCompact K →
        ∃ C : NNReal, LipschitzOnWith C p.2 K}
namespace Homogenization
noncomputable abbrev volumeMeasureOn {d : ℕ} (U : Set (Homogenization.Vec d)) := MeasureTheory.volume.restrict U
noncomputable abbrev MemScalarL2 {d : ℕ} (U : Set (Homogenization.Vec d)) (u : Homogenization.Vec d → ℝ) : Prop := MeasureTheory.MemLp u 2 (volumeMeasureOn U)
section CarrierTransport
variable {d : ℕ} {U : Set (Homogenization.Vec d)}
end CarrierTransport
section ConstantFields
variable {d : ℕ} {U : Set (Homogenization.Vec d)}
variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
end ConstantFields
section Operators
variable {d : ℕ} {U : Set (Homogenization.Vec d)}
variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
end Operators end Homogenization namespace Homogenization
abbrev CoeffField (d : ℕ) := Homogenization.Vec d → Mat d
def IsEllipticMatrix {d : ℕ} (lam Lam : ℝ) (A : Mat d) : Prop := 0 < lam ∧ lam ≤ Lam ∧ (∀ ξ : Homogenization.Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ)) ∧ (∀ ξ : Homogenization.Vec d, Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ))
namespace IsEllipticMatrix
theorem mono {d : ℕ} {lam Lam lam' Lam' : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (hlam'_pos : 0 < lam') (hlam'_le : lam' ≤ lam) (hLam_le : Lam ≤ Lam') : IsEllipticMatrix lam' Lam' A := by
  rcases hA with ⟨hlam_pos, hlam_le_Lam, hlower, hinv⟩
  have hLam_pos : 0 < Lam := lt_of_lt_of_le hlam_pos hlam_le_Lam
  have hLam'_pos : 0 < Lam' := lt_of_lt_of_le hLam_pos hLam_le
  refine ⟨hlam'_pos, hlam'_le.trans (hlam_le_Lam.trans hLam_le), ?_, ?_⟩
  · intro ξ
    calc
      lam' * vecNormSq ξ ≤ lam * vecNormSq ξ :=
        mul_le_mul_of_nonneg_right hlam'_le (vecNormSq_nonneg ξ)
      _ ≤ vecDot ξ (matVecMul A ξ) := hlower ξ
  · intro ξ
    have hInv_le : Lam'⁻¹ ≤ Lam⁻¹ := (inv_le_inv₀ hLam'_pos hLam_pos).2 hLam_le
    calc
      Lam'⁻¹ * vecNormSq ξ ≤ Lam⁻¹ * vecNormSq ξ :=
        mul_le_mul_of_nonneg_right hInv_le (vecNormSq_nonneg ξ)
      _ ≤ vecDot ξ (matVecMul A⁻¹ ξ) := hinv ξ
end IsEllipticMatrix namespace IsEllipticFieldOn end IsEllipticFieldOn
noncomputable def restrictCoeffField {d : ℕ} (U : Set (Homogenization.Vec d)) (a : CoeffField d) : CoeffField d := by
  classical
  exact fun x => if x ∈ U then a x else 0
end Homogenization namespace Homogenization
abbrev scalarMatrix {d : ℕ} (sigma : ℝ) : Mat d := sigma • (1 : Mat d)
theorem matVecMul_scalarMatrix {d : ℕ} (sigma : ℝ) (x : Homogenization.Vec d) : matVecMul (scalarMatrix (d := d) sigma) x = sigma • x := by
  funext i
  rw [scalarMatrix, matVecMul, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hij : i ≠ j := Ne.symm hji
    simp [hij]
  · simp
theorem vecDot_smul_right {d : ℕ} (x y : Vec d) (c : ℝ) : vecDot x (c • y) = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  ext i
  ring
theorem isEllipticMatrix_scalarMatrix {d : ℕ} {sigma : ℝ} (hsigma : 0 < sigma) : IsEllipticMatrix sigma sigma (scalarMatrix (d := d) sigma) := by
  refine ⟨hsigma, le_rfl, ?_, ?_⟩
  · intro ξ
    rw [matVecMul_scalarMatrix, vecDot_smul_right, vecNormSq]
  · intro ξ
    have hInv :
        ((scalarMatrix (d := d) sigma)⁻¹ : Mat d) = sigma⁻¹ • (1 : Mat d) := by
      letI := invertibleOfNonzero (ne_of_gt hsigma)
      rw [scalarMatrix, Matrix.inv_smul (1 : Mat d) sigma (by simp)]
      simp
    rw [hInv, matVecMul_scalarMatrix, vecDot_smul_right, vecNormSq]
end Homogenization namespace Homogenization open MeasureTheory
structure RegCoeffField (d : ℕ) where
  toFun : Homogenization.Vec d → Mat d
  entry_measurable : ∀ i j, Measurable (fun x : Homogenization.Vec d => toFun x i j)
  entry_locInt : ∀ i j, LocallyIntegrable (fun x : Homogenization.Vec d => toFun x i j) volume
namespace RegCoeffField
variable {d : ℕ}
instance : CoeFun (RegCoeffField d) (fun _ => Homogenization.Vec d → Mat d) := ⟨toFun⟩
end RegCoeffField end Homogenization namespace Homogenization open MeasureTheory
variable {d : ℕ}
structure IsProbeR (φ : Homogenization.Vec d → ℝ) : Prop where
  measurable : Measurable φ
  bounded : ∃ C : ℝ, ∀ x, |φ x| ≤ C
  hasCompactSupport : HasCompactSupport φ
def entryTestR (i j : Fin d) (φ : Homogenization.Vec d → ℝ) (a : RegCoeffField d) : ℝ := ∫ x, a x i j * φ x ∂volume
def LocalSigmaR (U : Set (Homogenization.Vec d)) : MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (i j : Fin d) (φ : Homogenization.Vec d → ℝ), IsProbeR φ ∧ Function.support φ ⊆ U ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTestR i j φ ⁻¹' t}
end Homogenization namespace SubdiffusiveProcess.Frozen.Assumptions open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization MeasureTheory Topology
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
def deriv (g : PotentialField d) : C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) := g.1.2
theorem hasFDerivAt (g : PotentialField d) (x : Homogenization.Vec d) : HasFDerivAt g (deriv g x) x :=
  g.2.1 x
theorem deriv_locallyLipschitz (g : PotentialField d) : LocallyLipschitz (deriv g) := by
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
theorem continuous_eval (x : Homogenization.Vec d) : Continuous (fun g : PotentialField d ↦ g x) :=
  (continuous_eval_const x).comp continuous_subtype_val.fst
theorem measurable_eval (x : Homogenization.Vec d) : Measurable (fun g : PotentialField d ↦ g x) :=
  (continuous_eval x).measurable
theorem continuous_eval_deriv (x : Homogenization.Vec d) : Continuous (fun g : PotentialField d ↦ deriv g x) :=
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
theorem forgetPotential_apply (g : PotentialField d) (x : Homogenization.Vec d) : forgetPotential g x = scalarMatrix (d := d) (g x) :=
  rfl
end PotentialField end SubdiffusiveProcess.Frozen.Assumptions namespace Homogenization
def IsSignedPermutationMatrix {d : ℕ} (R : Mat d) : Prop :=
  ∃ σ : Equiv.Perm (Fin d), ∃ s : Fin d → ℝ,
    (∀ i, s i = 1 ∨ s i = -1) ∧
      ∀ i j, R i j = if i = σ j then s j else 0
end Homogenization namespace SubdiffusiveProcess.Frozen.Assumptions.PotentialField open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization Topology
variable {d : ℕ}
def valueScaleMap (c : ℝ) : C(ℝ, ℝ) := ⟨fun y ↦ c * y, continuous_const.mul continuous_id⟩
def derivScaleCLM (c : ℝ) : (Homogenization.Vec d →L[ℝ] ℝ) →L[ℝ] (Homogenization.Vec d →L[ℝ] ℝ) := c • ContinuousLinearMap.id ℝ (Homogenization.Vec d →L[ℝ] ℝ)
def derivScaleMap (c : ℝ) : C(Homogenization.Vec d →L[ℝ] ℝ, Homogenization.Vec d →L[ℝ] ℝ) := ⟨derivScaleCLM c, (derivScaleCLM c).continuous⟩
def scaleAmbient (c : ℝ) : (C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ)) → C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) := fun p ↦ ((valueScaleMap c).comp p.1, (derivScaleMap c).comp p.2)
theorem continuous_scaleAmbient (c : ℝ) : Continuous (scaleAmbient (d := d) c) :=
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
theorem scale_apply (c : ℝ) (g : PotentialField d) (x : Homogenization.Vec d) : scale c g x = c * g x :=
  rfl
theorem continuous_scale (c : ℝ) : Continuous (scale (d := d) c) :=
  Continuous.subtype_mk
    ((continuous_scaleAmbient c).comp continuous_subtype_val)
    (fun g ↦ (scale c g).2)
def translateMap (z : Homogenization.Vec d) : C(Homogenization.Vec d, Homogenization.Vec d) := ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩
def translateAmbient (z : Homogenization.Vec d) : (C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ)) → C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) := fun p ↦ (p.1.comp (translateMap z), p.2.comp (translateMap z))
theorem continuous_translateAmbient (z : Homogenization.Vec d) : Continuous (translateAmbient (d := d) z) :=
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
theorem translate_apply (z : Homogenization.Vec d) (g : PotentialField d) (x : Homogenization.Vec d) : translate z g x = g (x + z) :=
  rfl
theorem continuous_translate (z : Homogenization.Vec d) : Continuous (translate (d := d) z) :=
  Continuous.subtype_mk
    ((continuous_translateAmbient z).comp continuous_subtype_val)
    (fun g ↦ (translate z g).2)
theorem measurable_translate (z : Homogenization.Vec d) : Measurable (translate (d := d) z) :=
  (continuous_translate z).measurable
def spatialCLM (r : ℝ) : Homogenization.Vec d →L[ℝ] Homogenization.Vec d := r • ContinuousLinearMap.id ℝ (Homogenization.Vec d)
def spatialMap (r : ℝ) : C(Homogenization.Vec d, Homogenization.Vec d) := ⟨spatialCLM r, (spatialCLM r).continuous⟩
def spatialScaleAmbient (r : ℝ) : (C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ)) → C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) := fun p ↦ (p.1.comp (spatialMap r), (derivScaleMap r).comp (p.2.comp (spatialMap r)))
theorem continuous_spatialScaleAmbient (r : ℝ) : Continuous (spatialScaleAmbient (d := d) r) :=
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
theorem spatialScale_apply (r : ℝ) (g : PotentialField d) (x : Homogenization.Vec d) : spatialScale r g x = g (r • x) :=
  rfl
theorem continuous_spatialScale (r : ℝ) : Continuous (spatialScale (d := d) r) :=
  Continuous.subtype_mk
    ((continuous_spatialScaleAmbient r).comp continuous_subtype_val)
    (fun g ↦ (spatialScale r g).2)
def triadicScale (k : ℕ) (g : PotentialField d) : PotentialField d := spatialScale (((3 : ℝ) ^ k)⁻¹) g
theorem triadicScale_apply (k : ℕ) (g : PotentialField d) (x : Homogenization.Vec d) : triadicScale k g x = g ((((3 : ℝ) ^ k)⁻¹) • x) :=
  rfl
theorem continuous_triadicScale (k : ℕ) : Continuous (triadicScale (d := d) k) :=
  continuous_spatialScale _
theorem measurable_triadicScale (k : ℕ) : Measurable (triadicScale (d := d) k) :=
  (continuous_triadicScale k).measurable
def negate (g : PotentialField d) : PotentialField d := scale (-1) g
theorem negate_apply (g : PotentialField d) (x : Homogenization.Vec d) : negate g x = -g x := by
  rw [negate, scale_apply]
  ring
theorem measurable_negate : Measurable (negate (d := d)) :=
  (continuous_scale (-1)).measurable
def matVecContinuousLinearMap (R : Mat d) : Homogenization.Vec d →L[ℝ] Homogenization.Vec d := ⟨Matrix.toLin' R, (Matrix.toLin' R).continuous_of_finiteDimensional⟩
def rotateDerivativeMap (R : Mat d) : (Homogenization.Vec d →L[ℝ] ℝ) →L[ℝ] (Homogenization.Vec d →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ (Homogenization.Vec d) (Homogenization.Vec d) ℝ).flip (matVecContinuousLinearMap R)
def rotateDomainMap (R : Mat d) : C(Homogenization.Vec d, Homogenization.Vec d) := ⟨matVecContinuousLinearMap R, (matVecContinuousLinearMap R).continuous⟩
def rotateDerivativeContinuousMap (R : Mat d) : C(Homogenization.Vec d →L[ℝ] ℝ, Homogenization.Vec d →L[ℝ] ℝ) := ⟨rotateDerivativeMap R, (rotateDerivativeMap R).continuous⟩
def rotateAmbient (R : Mat d) : (C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ)) → C(Homogenization.Vec d, ℝ) × C(Homogenization.Vec d, Homogenization.Vec d →L[ℝ] ℝ) := fun p ↦ (p.1.comp (rotateDomainMap R), (rotateDerivativeContinuousMap R).comp (p.2.comp (rotateDomainMap R)))
theorem continuous_rotateAmbient (R : Mat d) : Continuous (rotateAmbient (d := d) R) :=
  ((ContinuousMap.continuous_precomp (rotateDomainMap R)).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_postcomp (rotateDerivativeContinuousMap R)).comp
      (ContinuousMap.continuous_precomp (rotateDomainMap R))).comp continuous_snd)
def rotate (R : Mat d) (_hR : IsSignedPermutationMatrix R) (g : PotentialField d) : PotentialField d :=
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
theorem rotate_apply (R : Mat d) (hR : IsSignedPermutationMatrix R) (g : PotentialField d) (x : Homogenization.Vec d) : rotate R hR g x = g (matVecMul R x) :=
  rfl
theorem continuous_rotate (R : Mat d) (hR : IsSignedPermutationMatrix R) : Continuous (rotate (d := d) R hR) :=
  Continuous.subtype_mk
    ((continuous_rotateAmbient R).comp continuous_subtype_val)
    (fun g ↦ (rotate R hR g).2)
theorem measurable_rotate (R : Mat d) (hR : IsSignedPermutationMatrix R) : Measurable (rotate (d := d) R hR) :=
  (continuous_rotate R hR).measurable
end SubdiffusiveProcess.Frozen.Assumptions.PotentialField
abbrev SubdiffusiveProcess.Frozen.Assumptions.PotentialSample (d : ℕ) := ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d
open MeasureTheory ProbabilityTheory
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw {d : ℕ} (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) (k : ℕ) : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) := P.map (fun omega => omega k)
open MeasureTheory ProbabilityTheory
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw {d : ℕ} (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) := SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw P 0
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization MeasureTheory ProbabilityTheory
structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawPrefix (d : ℕ) (delta : ℝ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  dimension : 2 ≤ d
  delta_pos : 0 < delta
  delta_le_half : delta ≤ (1 : ℝ) / 2
  independent : iIndepFun (fun k : ℕ ↦ fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦ ω k) P.toMeasure
  marginal_scaling : ∀ k : ℕ, SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw P k = (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization
def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma {d : ℕ} (U : Set (Homogenization.Vec d)) : MeasurableSpace (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) := MeasurableSpace.comap SubdiffusiveProcess.Frozen.Assumptions.PotentialField.forgetPotential (LocalSigmaR U)
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization MeasureTheory ProbabilityTheory
structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  integrable : ∀ x : Homogenization.Vec d, Integrable (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦ ω 0 x) P.toMeasure
  mean_zero : ∀ x : Homogenization.Vec d, ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, ω 0 x ∂P.toMeasure = 0
  stationary : ∀ z : Homogenization.Vec d, Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z) (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure = (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure
  range_dependence : ∀ (U V : Set (Homogenization.Vec d)), MeasurableSet U → MeasurableSet V → (∀ ⦃x y : Homogenization.Vec d⦄, x ∈ U → y ∈ V → Real.sqrt (d : ℝ) ≤ euclideanNorm (x - y)) → Indep (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U) (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma V) (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure
namespace Homogenization
def IsBoundedDomain {d : ℕ} (U : Set (Homogenization.Vec d)) : Prop := ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, |x i| ≤ R
namespace IsSobolevRegularDomain end IsSobolevRegularDomain end Homogenization namespace Homogenization
structure TriadicCube (d : ℕ) where
  scale : ℤ
  index : Fin d → ℤ
deriving DecidableEq, Repr
noncomputable def cubeScaleFactor {d : ℕ} (Q : TriadicCube d) : ℝ := (3 : ℝ) ^ Q.scale
def openCubeSet {d : ℕ} (Q : TriadicCube d) : Set (Homogenization.Vec d) :=
  { x | ∀ i,
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q < x i) ∧
      (x i < (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)) }
def originCube (d : ℕ) (m : ℤ) : TriadicCube d :=
  { scale := m
    index := 0 }
end Homogenization namespace Homogenization
theorem openCubeSet_eq_pi_Ioo {d : ℕ} (Q : TriadicCube d) : openCubeSet Q = Set.pi Set.univ (fun i : Fin d => Set.Ioo ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)) ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))) := by
  ext x
  simp [openCubeSet]
end Homogenization open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeValueNorm {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  sSup (Set.range fun o : Option
      {x : Homogenization.Vec d // x ∈ openCubeSet (originCube d 0)} ↦
    match o with
    | none => 0
    | some x => |g x.1|)
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivNorm {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  sSup (Set.range fun o : Option
      {x : Homogenization.Vec d // x ∈ openCubeSet (originCube d 0)} ↦
    match o with
    | none => 0
    | some x => ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g x.1‖)
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivLipschitzSeminorm {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ :=
  sSup (Set.range fun o : Option
      {p : ({x : Homogenization.Vec d // x ∈ openCubeSet (originCube d 0)} ×
          {x : Homogenization.Vec d // x ∈ openCubeSet (originCube d 0)}) // p.1 ≠ p.2} ↦
    match o with
    | none => 0
    | some p =>
        dist (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g p.1.1.1)
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g p.1.2.1) /
          dist p.1.1.1 p.1.2.1)
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable {d : ℕ} (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) : ℝ := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeValueNorm g + SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivNorm g + SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivLipschitzSeminorm g
open MeasureTheory
def SubdiffusiveProcess.OGammaLE {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (σ A : ℝ) (X : Ω → ℝ) : Prop := Integrable (fun ω ↦ Real.exp ((A⁻¹ * max (X ω) 0) ^ σ)) μ ∧ ∫ ω, Real.exp ((A⁻¹ * max (X ω) 0) ^ σ) ∂μ ≤ 2
open MeasureTheory ProbabilityTheory
structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 (d : ℕ) (delta : ℝ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  regularity_expectation : SubdiffusiveProcess.OGammaLE (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure 2 delta SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization MeasureTheory ProbabilityTheory
structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG3 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  signed_coordinate_permutations : ∀ (R : Mat d) (hR : IsSignedPermutationMatrix R), (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR) = SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P
  negation : (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).map SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate = SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P
open MeasureTheory ProbabilityTheory
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.tauSq {d : ℕ} (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : ℝ := Real.log (∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (g 0) ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure)
open MeasureTheory ProbabilityTheory
structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG4 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  exponential_integrable : Integrable (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d ↦ Real.exp (g 0)) (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).toMeasure
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
open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization open scoped BigOperators
noncomputable def SubdiffusiveProcess.Frozen.Assumptions.aCutoff {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Homogenization.Vec d) : ℝ := Real.exp (∑ k ∈ Finset.range (L + 1), (ω k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
namespace Homogenization
theorem isOpen_openCubeSet {d : ℕ} (Q : TriadicCube d) : IsOpen (openCubeSet Q) := by
  rw [openCubeSet_eq_pi_Ioo]
  exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
end Homogenization namespace Homogenization
theorem Bornology.IsBounded.isBoundedDomain {d : ℕ} {U : Set (Homogenization.Vec d)} (hU : Bornology.IsBounded U) : IsBoundedDomain U := by
  classical
  by_cases hd : d = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    subst hd
    intro x hx i
    exact Fin.elim0 i
  · haveI : NeZero d := ⟨hd⟩
    have hcoord :
        ∀ i : Fin d, Bornology.IsBounded (Function.eval i '' U) := fun i => hU.image_eval i
    have hcoord_bound :
        ∀ i : Fin d, ∃ R : ℝ, 0 < R ∧ ∀ y ∈ Function.eval i '' U, ‖y‖ ≤ R := by
      intro i
      rcases isBounded_iff_forall_norm_le.1 (hcoord i) with ⟨R, hR⟩
      refine ⟨max R 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
      intro y hy
      exact (hR y hy).trans (le_max_left _ _)
    choose R hRpos hR using hcoord_bound
    let Rmax : ℝ := Finset.univ.sup' Finset.univ_nonempty R
    have hRmax_pos : 0 < Rmax := by
      let i0 : Fin d := 0
      have hi0 : i0 ∈ (Finset.univ : Finset (Fin d)) := by simp
      have hle : R i0 ≤ Rmax := by
        exact Finset.le_sup' (s := Finset.univ) (f := R) hi0
      exact lt_of_lt_of_le (hRpos i0) hle
    refine ⟨Rmax, hRmax_pos, ?_⟩
    intro x hx i
    have hxi : ‖x i‖ ≤ R i := hR i (x i) ⟨x, hx, rfl⟩
    have hRi : R i ≤ Rmax := by
      exact Finset.le_sup' (s := Finset.univ) (f := R) (by simp : i ∈ Finset.univ)
    exact by simpa [Real.norm_eq_abs] using! hxi.trans hRi
theorem IsBoundedDomain.isBounded {d : ℕ} {U : Set (Homogenization.Vec d)} (hU : IsBoundedDomain U) : Bornology.IsBounded U := by
  rcases hU with ⟨R, hRpos, hR⟩
  refine isBounded_iff_forall_norm_le.2 ⟨R, ?_⟩
  intro x hx
  refine (pi_norm_le_iff_of_nonneg (le_of_lt hRpos)).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using! hR x hx i
def IsOpenBoundedConvexDomain {d : ℕ} (U : Set (Homogenization.Vec d)) : Prop := IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U
namespace IsOpenBoundedConvexDomain
theorem isOpen {d : ℕ} {U : Set (Homogenization.Vec d)} (hU : IsOpenBoundedConvexDomain U) : IsOpen U :=
  hU.1
theorem isBoundedDomain {d : ℕ} {U : Set (Homogenization.Vec d)} (hU : IsOpenBoundedConvexDomain U) : IsBoundedDomain U :=
  hU.2.1
end IsOpenBoundedConvexDomain namespace IsSobolevRegularDomain end IsSobolevRegularDomain
theorem isBoundedDomain_openCubeSet {d : ℕ} (Q : TriadicCube d) : IsBoundedDomain (openCubeSet Q) := by
  rw [openCubeSet_eq_pi_Ioo]
  exact Bornology.IsBounded.isBoundedDomain <|
    Bornology.IsBounded.pi fun i =>
      show Bornology.IsBounded
        (Set.Ioo
          ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
          ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q))) from
        Metric.isBounded_Ioo _ _
theorem convex_openCubeSet {d : ℕ} (Q : TriadicCube d) : Convex ℝ (openCubeSet Q) := by
  rw [openCubeSet_eq_pi_Ioo]
  refine convex_pi ?_
  intro i hi
  exact convex_Ioo _ _
theorem isOpenBoundedConvexDomain_openCubeSet {d : ℕ} (Q : TriadicCube d) : IsOpenBoundedConvexDomain (openCubeSet Q) := by
  exact ⟨isOpen_openCubeSet Q, isBoundedDomain_openCubeSet Q, convex_openCubeSet Q⟩
end Homogenization namespace Homogenization
def basisVec {d : ℕ} (i : Fin d) : Homogenization.Vec d := Pi.single i (1 : ℝ)
def HasWeakPartialDerivOn {d : ℕ} (U : Set (Homogenization.Vec d)) (i : Fin d) (u gi : Homogenization.Vec d → ℝ) : Prop := ∀ φ : Homogenization.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume = -∫ x in U, gi x * φ x ∂MeasureTheory.volume
def HasWeakGradientOn {d : ℕ} (U : Set (Homogenization.Vec d)) (u : Homogenization.Vec d → ℝ) (Du : Homogenization.Vec d → Homogenization.Vec d) : Prop := ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)
namespace HasWeakPartialDerivOn end HasWeakPartialDerivOn end Homogenization namespace Homogenization
abbrev MemL2On {d : ℕ} (U : Set (Homogenization.Vec d)) (u : Homogenization.Vec d → ℝ) : Prop := MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict U)
def GradMemL2On {d : ℕ} (U : Set (Homogenization.Vec d)) (Du : Homogenization.Vec d → Homogenization.Vec d) : Prop := ∀ i : Fin d, MemL2On U (fun x => Du x i)
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
  tendsto_approx : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun x => approx n x - toH1Function.toFun x) 2 (MeasureTheory.volume.restrict U)) Filter.atTop (nhds 0)
  tendsto_approx_grad : ∀ i : Fin d, Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun x => (fderiv ℝ (approx n) x) (basisVec i) - toH1Function.grad x i) 2 (MeasureTheory.volume.restrict U)) Filter.atTop (nhds 0)
instance {d : ℕ} {U : Set (Homogenization.Vec d)} : CoeFun (H10Function U) (fun _ => Homogenization.Vec d → ℝ) where
  coe u := u.toH1Function.toFun
end Homogenization namespace Homogenization
def IsPotentialOn {d : ℕ} (U : Set (Homogenization.Vec d)) (f : Homogenization.Vec d → Homogenization.Vec d) : Prop := ∃ u : H1Function U, u.grad = f
noncomputable def IsSolenoidalOn {d : ℕ} (U : Set (Homogenization.Vec d)) (g : Homogenization.Vec d → Homogenization.Vec d) : Prop := ∀ φ : H10Function U, ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume = 0
end Homogenization namespace Homogenization
def IsAHarmonicGradient {d : ℕ} (a : CoeffField d) (U : Set (Homogenization.Vec d)) (f : Homogenization.Vec d → Homogenization.Vec d) : Prop := IsPotentialOn U f ∧ IsSolenoidalOn U (fun x => matVecMul (a x) (f x))
structure AHarmonicFunction {d : ℕ} (a : CoeffField d) (U : Set (Homogenization.Vec d)) where
  toH1 : H1Function U
  isHarmonic : IsAHarmonicGradient a U toH1.grad
namespace AHarmonicFunctionMeanZero end AHarmonicFunctionMeanZero namespace AHarmonicPair end AHarmonicPair namespace AHarmonicFunction end AHarmonicFunction end Homogenization namespace Homogenization namespace Book namespace Ch02
structure Domain (d : ℕ) where
  carrier : Set (Homogenization.Vec d)
  isDomain : IsOpenBoundedConvexDomain carrier
  nonempty : carrier.Nonempty
namespace Domain
instance {d : ℕ} : Coe (Domain d) (Set (Homogenization.Vec d)) where
  coe U := U.carrier
theorem isOpen {d : ℕ} (U : Domain d) : IsOpen (U : Set (Homogenization.Vec d)) :=
  U.isDomain.isOpen
theorem isBoundedDomain {d : ℕ} (U : Domain d) : IsBoundedDomain (U : Set (Homogenization.Vec d)) :=
  U.isDomain.isBoundedDomain
theorem measurableSet {d : ℕ} (U : Domain d) : MeasurableSet (U : Set (Homogenization.Vec d)) :=
  U.isOpen.measurableSet
end Domain
structure CoeffOn {d : ℕ} (U : Domain d) where
  toCoeffField : CoeffField d
  lam : ℝ
  Lam : ℝ
  lam_pos : 0 < lam
  lam_le_Lam : lam ≤ Lam
  aeStronglyMeasurable : ∀ i j : Fin d, MeasureTheory.AEStronglyMeasurable (fun x : Homogenization.Vec d => restrictCoeffField (U : Set (Homogenization.Vec d)) toCoeffField x i j) (volumeMeasureOn (U : Set (Homogenization.Vec d)))
  aeElliptic : ∀ᵐ x ∂ volumeMeasureOn (U : Set (Homogenization.Vec d)), IsEllipticMatrix lam Lam (toCoeffField x)
namespace CoeffOn
instance {d : ℕ} {U : Domain d} : CoeFun (CoeffOn U) (fun _ => CoeffField d) where
  coe a := a.toCoeffField
namespace AEEq end AEEq end CoeffOn
abbrev Solution {d : ℕ} (U : Domain d) (a : CoeffOn U) := AHarmonicFunction a.toCoeffField (U : Set (Homogenization.Vec d))
namespace Solution namespace SameGradientAE end SameGradientAE end Solution end Ch02 end Book end Homogenization namespace Homogenization namespace Book namespace Ch02
noncomputable def average {d : ℕ} (U : Domain d) (f : Homogenization.Vec d → ℝ) : ℝ := (MeasureTheory.volume (U : Set (Homogenization.Vec d))).toReal⁻¹ * ∫ x in (U : Set (Homogenization.Vec d)), f x ∂MeasureTheory.volume
noncomputable def responseIntegrand {d : ℕ} (U : Domain d) (a : CoeffOn U) (p q : Homogenization.Vec d) (v : Solution U a) : Homogenization.Vec d → ℝ := fun x => -((1 / 2 : ℝ) * vecDot (v.toH1.grad x) (matVecMul (symmPart (a.toCoeffField x)) (v.toH1.grad x))) - vecDot p (matVecMul (a.toCoeffField x) (v.toH1.grad x)) + vecDot q (v.toH1.grad x)
noncomputable def responseValue {d : ℕ} (U : Domain d) (a : CoeffOn U) (p q : Homogenization.Vec d) (v : Solution U a) : ℝ := average U (responseIntegrand U a p q v)
noncomputable def responseValueSet {d : ℕ} (U : Domain d) (a : CoeffOn U) (p q : Homogenization.Vec d) : Set ℝ :=
  {m | ∃ v : Solution U a, m = responseValue U a p q v}
noncomputable def responseJ {d : ℕ} (U : Domain d) (a : CoeffOn U) (p q : Homogenization.Vec d) : ℝ := sSup (responseValueSet U a p q)
namespace IsResponseMaximizer end IsResponseMaximizer namespace CanonicalMaximizer end CanonicalMaximizer end Ch02 end Book end Homogenization namespace Homogenization namespace Book namespace Ch02
structure CoarseMatrices (d : ℕ) where
  sigma : Mat d
  sigmaStarInv : Mat d
  kappa : Mat d
namespace CoarseMatrices
def coeff {d : ℕ} (M : CoarseMatrices d) : Mat d := M.sigma - matTranspose M.kappa
end CoarseMatrices
noncomputable def mixedResponse {d : ℕ} (U : Domain d) (a : CoeffOn U) (p q : Homogenization.Vec d) : ℝ := responseJ U a p q - responseJ U a p 0 - responseJ U a 0 q + vecDot p q
noncomputable def sigmaStarInvEntry {d : ℕ} (U : Domain d) (a : CoeffOn U) (i j : Fin d) : ℝ :=
  if _h : i = j then
    2 * responseJ U a (0 : Homogenization.Vec d) (Pi.single i 1)
  else
    responseJ U a (0 : Homogenization.Vec d) (Pi.single i 1 + Pi.single j 1)
      - responseJ U a (0 : Homogenization.Vec d) (Pi.single i 1)
      - responseJ U a (0 : Homogenization.Vec d) (Pi.single j 1)
noncomputable def sigmaStarInvCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) : Mat d := fun i j => sigmaStarInvEntry U a i j
noncomputable def sigmaStarCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) : Mat d := (sigmaStarInvCoarse U a)⁻¹
noncomputable def sigmaStarInvKappaCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) : Mat d := fun i j => mixedResponse U a (Pi.single j 1) (Pi.single i 1)
noncomputable def kappaCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) : Mat d := sigmaStarCoarse U a * sigmaStarInvKappaCoarse U a
noncomputable def canonicalSigmaCorrectedResponse {d : ℕ} (U : Domain d) (a : CoeffOn U) (p : Homogenization.Vec d) : ℝ := responseJ U a p 0 - (1 / 2 : ℝ) * vecDot p (matVecMul (matTranspose (kappaCoarse U a)) (matVecMul (sigmaStarInvCoarse U a) (matVecMul (kappaCoarse U a) p)))
noncomputable def sigmaEntry {d : ℕ} (U : Domain d) (a : CoeffOn U) (i j : Fin d) : ℝ :=
  if _h : i = j then
    2 * canonicalSigmaCorrectedResponse U a (Pi.single i 1)
  else
    canonicalSigmaCorrectedResponse U a (Pi.single i 1 + Pi.single j 1)
      - canonicalSigmaCorrectedResponse U a (Pi.single i 1)
      - canonicalSigmaCorrectedResponse U a (Pi.single j 1)
noncomputable def sigmaCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) : Mat d := fun i j => sigmaEntry U a i j
noncomputable def coarseMatrices {d : ℕ} (U : Domain d) (a : CoeffOn U) : CoarseMatrices d where
  sigma := sigmaCoarse U a
  sigmaStarInv := sigmaStarInvCoarse U a
  kappa := kappaCoarse U a
noncomputable def aCoarse {d : ℕ} (U : Domain d) (a : CoeffOn U) : Mat d := (coarseMatrices U a).coeff
end Ch02 end Book end Homogenization open scoped BigOperators namespace Homogenization namespace Book namespace Ch02
theorem openCubeSet_nonempty {d : ℕ} (Q : TriadicCube d) : (openCubeSet Q).Nonempty := by
  refine ⟨fun i => (Q.index i : ℝ) * cubeScaleFactor Q, ?_⟩
  intro i
  have hp : 0 < cubeScaleFactor Q := zpow_pos (by norm_num) _
  constructor <;> dsimp <;> nlinarith
noncomputable def cubeDomain {d : ℕ} (Q : TriadicCube d) : Domain d where
  carrier := openCubeSet Q
  isDomain := isOpenBoundedConvexDomain_openCubeSet Q
  nonempty := openCubeSet_nonempty Q
namespace TriadicCoeffFamily namespace AEEq end AEEq end TriadicCoeffFamily namespace MultiscaleExponent end MultiscaleExponent end Ch02 end Book end Homogenization namespace Homogenization end Homogenization namespace SubdiffusiveProcess.CoarseGrainingVocab open Filter MeasureTheory Homogenization.Book
abbrev Vec (d : ℕ) := Homogenization.Vec d
def scalarCoeffField {d : ℕ} (a : Homogenization.Vec d → ℝ) : Homogenization.CoeffField d := fun x => Homogenization.scalarMatrix (a x)
structure ScalarCoeffOnData {d : ℕ} (U : Ch02.Domain d) (a : Homogenization.Vec d → ℝ) where
  lam : ℝ
  Lam : ℝ
  lam_pos : 0 < lam
  lam_le_Lam : lam ≤ Lam
  aeStronglyMeasurable : ∀ i j : Fin d, AEStronglyMeasurable (fun x : Homogenization.Vec d => Homogenization.restrictCoeffField (U : Set (Homogenization.Vec d)) (scalarCoeffField a) x i j) (Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d)))
  aeBounds : ∀ᵐ x ∂ Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d)), lam ≤ a x ∧ a x ≤ Lam
noncomputable def ScalarCoeffOnData.toCoeffOn {d : ℕ} {U : Ch02.Domain d} {a : Homogenization.Vec d → ℝ} (h : ScalarCoeffOnData U a) : Ch02.CoeffOn U where
  toCoeffField := scalarCoeffField a
  lam := h.lam
  Lam := h.Lam
  lam_pos := h.lam_pos
  lam_le_Lam := h.lam_le_Lam
  aeStronglyMeasurable := h.aeStronglyMeasurable
  aeElliptic := h.aeBounds.mono fun x hx => by
    have hax : 0 < a x := lt_of_lt_of_le h.lam_pos hx.1
    exact (Homogenization.isEllipticMatrix_scalarMatrix hax).mono
      h.lam_pos hx.1 hx.2
theorem exists_aCutoffCoeffOnData {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (U : Ch02.Domain d) : Nonempty (ScalarCoeffOnData U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) := by
  let a := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω
  have ha_cont : Continuous a :=
    by
      exact Real.continuous_exp.comp (continuous_finsetSum _ fun k _ => (ω k).1.1.continuous.sub continuous_const)
  have hU_compact : IsCompact (closure (U : Set (Homogenization.Vec d))) :=
    U.isDomain.isBoundedDomain.isBounded.isCompact_closure
  have hU_nonempty : (closure (U : Set (Homogenization.Vec d))).Nonempty :=
    U.nonempty.closure
  obtain ⟨x_min, hx_min, h_min⟩ :=
    hU_compact.exists_isMinOn hU_nonempty ha_cont.continuousOn
  obtain ⟨x_max, hx_max, h_max⟩ :=
    hU_compact.exists_isMaxOn hU_nonempty ha_cont.continuousOn
  refine ⟨{
    lam := a x_min
    Lam := a x_max
    lam_pos := ?_
    lam_le_Lam := h_min hx_max
    aeStronglyMeasurable := ?_
    aeBounds := ?_
  }⟩
  · exact Real.exp_pos _
  · intro i j
    have h_cont_matrix : Continuous (fun x : Homogenization.Vec d =>
        Homogenization.scalarMatrix (d := d) (a x)) :=
      ha_cont.smul continuous_const
    have h_cont_entry : Continuous (fun x : Homogenization.Vec d =>
        Homogenization.scalarMatrix (d := d) (a x) i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp h_cont_matrix)
    have h_meas_entry : AEStronglyMeasurable
        (fun x : Homogenization.Vec d => Homogenization.scalarMatrix (d := d) (a x) i j)
        (Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d))) :=
      h_cont_entry.aestronglyMeasurable
    have h_mem : ∀ᵐ x ∂ Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d)),
        x ∈ (U : Set (Homogenization.Vec d)) :=
      MeasureTheory.ae_restrict_mem U.measurableSet
    refine h_meas_entry.congr ?_
    filter_upwards [h_mem] with x hx
    simp only [scalarCoeffField,
      Homogenization.restrictCoeffField, hx]
    rfl
  · have h_mem : ∀ᵐ x ∂ Homogenization.volumeMeasureOn (U : Set (Homogenization.Vec d)),
        x ∈ (U : Set (Homogenization.Vec d)) :=
      MeasureTheory.ae_restrict_mem U.measurableSet
    filter_upwards [h_mem] with x hx
    exact ⟨h_min (subset_closure hx), h_max (subset_closure hx)⟩
noncomputable def aCutoffCoeffOnData {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (U : Ch02.Domain d) : ScalarCoeffOnData U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) := Classical.choice (exists_aCutoffCoeffOnData M L ω U)
end SubdiffusiveProcess.CoarseGrainingVocab namespace SubdiffusiveProcess.CoarseGrainingVocab open Filter Homogenization.Book
abbrev Mat (d : ℕ) := Homogenization.Mat d
abbrev TriadicCube (d : ℕ) := Homogenization.TriadicCube d
noncomputable abbrev aMatrix {d : ℕ} (U : Ch02.Domain d) (a : Ch02.CoeffOn U) : Mat d := Ch02.aCoarse U a
end SubdiffusiveProcess.CoarseGrainingVocab namespace SubdiffusiveProcess.CoarseGrainingVocab open MeasureTheory Homogenization.Book open scoped ENNReal Distributions
noncomputable def randomAMatrix {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (U : Ch02.Domain d) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : Mat d := aMatrix U (aCutoffCoeffOnData M m ω U).toCoeffOn
end SubdiffusiveProcess.CoarseGrainingVocab open MeasureTheory open scoped Matrix.Norms.Elementwise
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.abar {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (U : Homogenization.Book.Ch02.Domain d) : SubdiffusiveProcess.CoarseGrainingVocab.Mat d := ∫ ω, SubdiffusiveProcess.CoarseGrainingVocab.randomAMatrix M m U ω ∂M.P.toMeasure
namespace SubdiffusiveProcess.CoarseGrainingVocab open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization.Book
noncomputable def abarScalarReadout {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m n : ℕ) : ℝ := Matrix.trace (abar M m (Ch02.cubeDomain (Homogenization.originCube d (n : ℤ)))) / (d : ℝ)
end SubdiffusiveProcess.CoarseGrainingVocab
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.ahom {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) : ℝ := sInf (Set.range (SubdiffusiveProcess.CoarseGrainingVocab.abarScalarReadout M m))
namespace MarkovProcess
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
def IsSubMarkovKernel (κ : ProbabilityTheory.Kernel α β) : Prop := ∀ x, κ x Set.univ ≤ 1
namespace IsSubMarkovKernel open ProbabilityTheory
variable {κ : Kernel α β} {η : Kernel β γ}
end IsSubMarkovKernel end MarkovProcess open MeasureTheory open ProbabilityTheory namespace MarkovProcess
variable {α : Type*} [MeasurableSpace α]
noncomputable def kernelIntegral (κ : Kernel α α) (f : α → ℝ) (x : α) : ℝ := ∫ y, f y ∂κ x
end MarkovProcess open Set open scoped ENNReal ProbabilityTheory namespace MarkovProcess open MeasureTheory ProbabilityTheory
structure SubMarkovKernelSemigroup (α : Type*) [MeasurableSpace α] where
  kernel : NNReal → Kernel α α
  measurable_kernel : Measurable fun p : NNReal × α ↦ kernel p.1 p.2
  kernel_zero : kernel 0 = Kernel.id
  kernel_add : ∀ s t, kernel (s + t) = (kernel t).comp (kernel s)
  isSubMarkovKernel : ∀ t, IsSubMarkovKernel (kernel t)
namespace SubMarkovKernelSemigroup
variable {α : Type*} [MeasurableSpace α]
instance : CoeFun (SubMarkovKernelSemigroup α)
    (fun _ ↦ NNReal → Kernel α α) where
  coe P := P.kernel
variable (P : SubMarkovKernelSemigroup α)
def IsConservative : Prop := ∀ t x, P t x univ = 1
namespace IsConservative end IsConservative end SubMarkovKernelSemigroup end MarkovProcess namespace MarkovProcess.Semigroup open Filter Set Topology
abbrev PositiveShift := Set.Ioi (0 : ℝ)
end MarkovProcess.Semigroup namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent open Filter Topology open MarkovProcess MarkovProcess.Semigroup open scoped ZeroAtInfty
variable {E : Type*} [TopologicalSpace E]
structure C0ResolventDatum (E : Type*) [TopologicalSpace E] where
  solution : PositiveShift → C₀(E, ℝ) → C₀(E, ℝ)
  solution_add : ∀ (μ : PositiveShift) (f g : C₀(E, ℝ)), solution μ (f + g) = solution μ f + solution μ g
  solution_smul : ∀ (μ : PositiveShift) (r : ℝ) (f : C₀(E, ℝ)), solution μ (r • f) = r • solution μ f
  solution_nonneg : ∀ (μ : PositiveShift) (f : C₀(E, ℝ)), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ solution μ f x
  norm_solution_le : ∀ (μ : PositiveShift) (f : C₀(E, ℝ)), ‖solution μ f‖ ≤ ((μ : ℝ))⁻¹ * ‖f‖
  solution_sub_solution : ∀ (μ ν : PositiveShift) (f : C₀(E, ℝ)), solution μ f - solution ν f = ((ν : ℝ) - (μ : ℝ)) • solution μ (solution ν f)
namespace C0ResolventDatum
variable (D : C0ResolventDatum E)
def linearMap (μ : PositiveShift) : C₀(E, ℝ) →ₗ[ℝ] C₀(E, ℝ) where
  toFun := D.solution μ
  map_add' := D.solution_add μ
  map_smul' r f := D.solution_smul μ r f
def operator (μ : PositiveShift) : C₀(E, ℝ) →L[ℝ] C₀(E, ℝ) := LinearMap.mkContinuous (D.linearMap μ) ((μ : ℝ))⁻¹ (D.norm_solution_le μ)
end C0ResolventDatum end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent open MeasureTheory open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization open SubdiffusiveProcess.CoarseGrainingVocab
variable {d : ℕ}
def IsMassiveWeakSolutionOn (c rho : Homogenization.Vec d → ℝ) (mu : ℝ) (W : Set (Homogenization.Vec d)) (u : H1Function W) (f : Homogenization.Vec d → ℝ) : Prop := ∀ φ : H10Function W, mu * ∫ x in W, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume + ∫ x in W, vecDot (c x • u.grad x) (φ.toH1Function.grad x) ∂volume = ∫ x in W, rho x * f x * φ.toH1Function.toFun x ∂volume
end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent open MeasureTheory Set open _root_.SubdiffusiveProcessAudit.ProcessConvergence.Homogenization open SubdiffusiveProcess.CoarseGrainingVocab open MarkovProcess MarkovProcess.Semigroup open scoped ZeroAtInfty
variable {d : ℕ}
def IsWeakEllipticResolvent (c rho : Homogenization.Vec d → ℝ) (D : C0ResolventDatum (Homogenization.Vec d)) : Prop := ∀ (mu : PositiveShift) (f : C₀(Homogenization.Vec d, ℝ)) (W : Set (Homogenization.Vec d)), IsOpenBoundedConvexDomain W → ∃ u : H1Function W, (∀ x ∈ W, u.toFun x = D.solution mu f x) ∧ IsMassiveWeakSolutionOn c rho (mu : ℝ) W u (fun x ↦ f x)
end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent open MeasureTheory Filter Set TopologicalSpace open scoped ENNReal ContDiff Distributions namespace SubdiffusiveProcess
abbrev SpatialCoordinates (d : ℕ) := Fin d → ℝ
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
end SubdiffusiveProcess open MeasureTheory open scoped NNReal namespace SubdiffusiveProcess
def layerScaling (d : ℕ) (j : ℤ) : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
  ContinuousMap.compRightContinuousMap ℝ
    (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-j) • x,
      by fun_prop⟩ : C(SpatialCoordinates d, SpatialCoordinates d))
end SubdiffusiveProcess open MeasureTheory open scoped NNReal namespace SubdiffusiveProcess
def scaledLayerLaw (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) (j : ℤ) : ProbabilityMeasure C(SpatialCoordinates d, ℝ) := ν.map (layerScaling d j)
end SubdiffusiveProcess open MeasureTheory open scoped NNReal namespace SubdiffusiveProcess
def commonScaleLaw (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ)) : ProbabilityMeasure (ℤ → C(SpatialCoordinates d, ℝ)) := ⟨Measure.infinitePi (fun j : ℤ => (scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ))), inferInstance⟩
end SubdiffusiveProcess open MeasureTheory open scoped NNReal namespace SubdiffusiveProcess
abbrev DiffusionPath (d : ℕ) := C(ℝ≥0, SpatialCoordinates d)
end SubdiffusiveProcess open MeasureTheory namespace MarkovProcess
abbrev ContinuousPath (alpha : Type*) [TopologicalSpace alpha] := C(NNReal, alpha)
namespace ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
def coordinateProcess (t : NNReal) (omega : ContinuousPath alpha) : alpha := omega t
theorem measurable_coordinateProcess [MeasurableSpace alpha] [BorelSpace alpha] (t : NNReal) : Measurable[borel (ContinuousPath alpha)] (coordinateProcess (alpha := alpha) t) :=
  (continuous_eval_const t).borel_measurable.mono le_rfl
    (le_of_eq BorelSpace.measurable_eq)
def canonicalFiltration [MeasurableSpace alpha] [BorelSpace alpha] : Filtration NNReal (borel (ContinuousPath alpha)) where
  seq t := ⨆ s : Set.Iic t,
    MeasurableSpace.comap (coordinateProcess (alpha := alpha) s) ‹MeasurableSpace alpha›
  mono' t u htu := by
    refine iSup_le fun s => ?_
    exact le_iSup_of_le (⟨s.1, s.2.trans htu⟩ : Set.Iic u) le_rfl
  le' t := iSup_le fun s => (measurable_coordinateProcess s).comap_le
end ContinuousPath end MarkovProcess namespace MarkovProcess
abbrev FiniteOrderedTimes (n : ℕ) := Fin n ↪o NNReal
namespace FiniteOrderedTimes
def relativeTail {n : ℕ} (times : FiniteOrderedTimes (n + 1)) : FiniteOrderedTimes n := OrderEmbedding.ofStrictMono (fun i ↦ times i.succ - times 0) fun _ _ hij ↦ tsub_lt_tsub_right_of_le (times.monotone (Fin.zero_le _)) (times.strictMono (Fin.strictMono_succ hij))
def emptyPath (α : Type*) : Fin 0 → α := Fin.elim0
end FiniteOrderedTimes end MarkovProcess open MeasureTheory ProbabilityTheory open scoped ProbabilityTheory namespace MarkovProcess
theorem measurable_finCons {α : Type*} [MeasurableSpace α] {n : ℕ} : Measurable (fun z : α × (Fin n → α) ↦ @Fin.cons n (fun _ : Fin (n + 1) ↦ α) z.1 z.2) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.cons_zero] using! (measurable_fst : Measurable (Prod.fst : α × (Fin n → α) → α))
  · simpa only [Fin.cons_succ] using!
      (measurable_pi_apply j).comp (measurable_snd : Measurable (Prod.snd : α × (Fin n → α) → _))
namespace SubMarkovKernelSemigroup
variable {α : Type*} [MeasurableSpace α]
noncomputable def finiteTimeKernel (P : SubMarkovKernelSemigroup α) : {n : ℕ} → FiniteOrderedTimes n → Kernel α (Fin n → α)
  | 0, _ => Kernel.const α (Measure.dirac (FiniteOrderedTimes.emptyPath α))
  | n + 1, times =>
      Kernel.mapOfMeasurable
        (P (times 0) ⊗ₖ Kernel.prodMkLeft α (finiteTimeKernel P times.relativeTail))
        (fun z ↦ @Fin.cons n (fun _ : Fin (n + 1) ↦ α) z.1 z.2) measurable_finCons
end SubMarkovKernelSemigroup end MarkovProcess open MeasureTheory ProbabilityTheory namespace MarkovProcess namespace SubMarkovKernelSemigroup
variable {α : Type*} [MeasurableSpace α]
noncomputable def finiteSetTimes (I : Finset NNReal) : FiniteOrderedTimes I.card := I.orderEmbOfFin rfl
noncomputable def orderedPathToFiniteSet (I : Finset NNReal) (path : Fin I.card → α) : I → α := fun t ↦ path ((I.orderIsoOfFin rfl).symm t)
theorem measurable_orderedPathToFiniteSet (I : Finset NNReal) : Measurable (orderedPathToFiniteSet (α := α) I) :=
  measurable_pi_iff.mpr fun t ↦ measurable_pi_apply ((I.orderIsoOfFin rfl).symm t)
noncomputable def finiteSetKernel (P : SubMarkovKernelSemigroup α) (I : Finset NNReal) : Kernel α (I → α) := Kernel.mapOfMeasurable (finiteTimeKernel P (finiteSetTimes I)) (orderedPathToFiniteSet I) (measurable_orderedPathToFiniteSet I)
namespace IsConservative end IsConservative end SubMarkovKernelSemigroup end MarkovProcess open MeasureTheory namespace MarkovProcess namespace ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
def timeTranslation (S : NNReal) : C(NNReal, NNReal) where
  toFun t := S + t
  continuous_toFun := continuous_const.add continuous_id
def shift (S : NNReal) (omega : ContinuousPath alpha) : ContinuousPath alpha := omega.comp (timeTranslation S)
end ContinuousPath end MarkovProcess open Filter MeasureTheory ProbabilityTheory Topology open scoped NNReal namespace MarkovProcess namespace ContinuousPath
def finiteEvaluation {ι α : Type*} [TopologicalSpace α] (τ : ι → NNReal) : ContinuousPath α → (ι → α) := fun path i ↦ path (τ i)
end ContinuousPath
section KernelLimits
variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [LocallyCompactSpace α]
namespace SubMarkovKernelSemigroup namespace IsConservative
variable [CompleteSpace α] [StandardBorelSpace α] [Nonempty α]
end IsConservative end SubMarkovKernelSemigroup end KernelLimits end MarkovProcess open MeasureTheory ProbabilityTheory open scoped NNReal namespace MarkovProcess
section FinsetEvaluation
namespace ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
abbrev finsetEvaluation (I : Finset NNReal) : ContinuousPath alpha → (I → alpha) := finiteEvaluation (fun t : I ↦ (t : NNReal))
end ContinuousPath end FinsetEvaluation namespace Kernel
noncomputable section DenseFiniteEvaluation
variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [MeasurableSpace beta]
end DenseFiniteEvaluation end Kernel namespace SubMarkovKernelSemigroup open IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable [LocallyCompactSpace alpha]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
end SubMarkovKernelSemigroup end MarkovProcess open Set open scoped ENNReal namespace MarkovProcess namespace LifetimePath
variable {alpha : Type*} [TopologicalSpace alpha]
end LifetimePath namespace ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
def exitTime (U : Set alpha) (omega : ContinuousPath alpha) : ENNReal :=
  sInf {s : ENNReal | ∃ t : NNReal, s = (t : ENNReal) ∧ omega t ∉ U}
end ContinuousPath namespace LifetimePath
variable {alpha : Type*} [TopologicalSpace alpha]
end LifetimePath end MarkovProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
abbrev BilateralField (d : ℕ) := ℤ → C(SpatialCoordinates d, ℝ)
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open scoped CompactlySupported ENNReal NNReal namespace SubdiffusiveProcess
def finePotential {d : ℕ} (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d) : ℝ := ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j)) x
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open scoped CompactlySupported ENNReal NNReal namespace SubdiffusiveProcess
def fineDensity {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d) : ℝ := Real.exp (finePotential N omega x - (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open scoped CompactlySupported ENNReal NNReal namespace SubdiffusiveProcess
def chaosCutoff {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (omega : BilateralField d) : Measure (SpatialCoordinates d) := volume.withDensity (ENNReal.ofReal ∘ fineDensity M N omega)
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def cutoffPotential {d : ℕ} (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) : ℝ := H omega x + ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j)) x
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def cutoffCoefficient {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) : ℝ := (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * Real.exp (cutoffPotential H omega N x - (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def cutoffSpeedDensity {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) : ℝ := Real.exp (cutoffPotential H omega N x - (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def cutoffSpeedMeasure {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) : Measure (SpatialCoordinates d) := volume.withDensity (ENNReal.ofReal ∘ cutoffSpeedDensity M H omega N)
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def HasFiniteMeanExits {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)) (omega : BilateralField d) : Prop := ∀ U : Set (SpatialCoordinates d), IsOpen U → Bornology.IsBounded U → ∃ C : ℝ≥0∞, C < (⊤ : ℝ≥0∞) ∧ ∀ x ∈ U, ∫⁻ path, ContinuousPath.exitTime U path ∂(K (omega, x)) ≤ C
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def usualNaturalAt {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (mu : Measure (DiffusionPath d)) (t : NNReal) : MeasurableSpace (DiffusionPath d) :=
  ⨅ s : {s : NNReal // t < s},
    ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d) s.val ⊔
      MeasurableSpace.generateFrom {A : Set (DiffusionPath d) | mu A = 0}
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def IsUsualStoppingTime {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (mu : Measure (DiffusionPath d)) (tau : DiffusionPath d → WithTop NNReal) : Prop :=
  ∀ t : NNReal, MeasurableSet[usualNaturalAt mu t] {path | tau path ≤ t}
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def MeasurableAtUsualStoppingTime {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (mu : Measure (DiffusionPath d)) (tau : DiffusionPath d → WithTop NNReal) (A : Set (DiffusionPath d)) : Prop :=
  NullMeasurableSet A mu ∧
    ∀ t : NNReal, MeasurableSet[usualNaturalAt mu t] (A ∩ {path | tau path ≤ t})
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def HasStrongMarkovRestart {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)) (omega : BilateralField d) : Prop :=
  ∀ (x : SpatialCoordinates d) (tau : DiffusionPath d → WithTop NNReal),
    IsUsualStoppingTime (K (omega, x)) tau →
    ∀ (A : Set (DiffusionPath d)),
      MeasurableAtUsualStoppingTime (K (omega, x)) tau A →
      ∀ F : DiffusionPath d → ℝ≥0∞, Measurable F →
        ∫⁻ path in A ∩ {path | tau path < ⊤},
            F (ContinuousPath.shift ((tau path).untopD 0) path) ∂(K (omega, x)) =
          ∫⁻ path in A ∩ {path | tau path < ⊤},
            ∫⁻ future, F future
              ∂(K (omega, path ((tau path).untopD 0))) ∂(K (omega, x))
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def infraredPartialSum {d : ℕ} (omega : BilateralField d) (L : ℕ) : C(SpatialCoordinates d, ℝ) := Finset.sum (Finset.range L) (fun n ↦ omega (Int.ofNat (n + 1)) - ContinuousMap.const _ (omega (Int.ofNat (n + 1)) 0))
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def jointPathProbabilityMeasure {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)) (hK : IsMarkovKernel K) (omega : BilateralField d) (x : SpatialCoordinates d) : ProbabilityMeasure (DiffusionPath d) := by
  letI : IsProbabilityMeasure (K (omega, x)) := hK.isProbabilityMeasure (omega, x)
  exact ⟨K (omega, x), inferInstance⟩
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def MeasuresConvergeLocally {d : ℕ} (muN : ℕ → Measure (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d)) : Prop := ∀ f : C_c(SpatialCoordinates d, ℝ), Tendsto (fun N ↦ ∫ x, f x ∂muN N) atTop (nhds (∫ x, f x ∂mu))
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def pathLevyProkhorovDist {d : ℕ} (mu nu : ProbabilityMeasure (DiffusionPath d)) : ℝ :=
  letI : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  levyProkhorovDist (mu : Measure (DiffusionPath d)) (nu : Measure (DiffusionPath d))
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def physicalTimeFactor {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) : ℝ≥0 := Real.toNNReal (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * (3 : ℝ) ^ (2 * N) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def physicalRescaledPath {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) : DiffusionPath d → DiffusionPath d := fun path ↦ ((3 : ℝ)⁻¹ ^ N) • path.comp ⟨fun t ↦ physicalTimeFactor M N * t, continuous_const.mul continuous_id⟩
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov namespace SubdiffusiveProcess
def SemigroupSymmetric {d : ℕ} (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (mu : Measure (SpatialCoordinates d)) : Prop := ∀ (t : ℝ≥0) (f g : SpatialCoordinates d → ℝ≥0∞), Measurable f → Measurable g → ∫⁻ x, f x * (∫⁻ y, g y ∂P t x) ∂mu = ∫⁻ x, g x * (∫⁻ y, f y ∂P t x) ∂mu
end SubdiffusiveProcess open Filter MeasureTheory ProbabilityTheory Topology Asymptotics open MarkovProcess open scoped CompactlySupported ENNReal NNReal LevyProkhorov open SubdiffusiveProcess
namespace Paper
def lim_brownian_law {d : ℕ} (Q : Measure (DiffusionPath d)) : Prop := IsProbabilityMeasure Q ∧ ∃ (x0 : SpatialCoordinates d) (S : Matrix (Fin d) (Fin d) ℝ), S.PosSemidef ∧ (∀ᵐ w ∂Q, w 0 = x0) ∧ ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t → ∀ xi : Fin n → SpatialCoordinates d, ∫ w, Complex.exp (Complex.I * ∑ j : Fin n, ∑ a : Fin d, ((xi j a * (w (t j.succ) a - w (t j.castSucc) a) : ℝ) : ℂ)) ∂Q = Complex.exp (-(1 / 2 : ℂ) * ∑ j : Fin n, ((((t j.succ : ℝ) - (t j.castSucc : ℝ)) * dotProduct (xi j) (S.mulVec (xi j)) : ℝ) : ℂ))
end Paper
open Paper
end SubdiffusiveProcessAudit.ProcessConvergence
