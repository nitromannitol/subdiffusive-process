module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution
public import Homogenization.Ambient.CoefficientFieldHilbert
public import Homogenization.CoarseGraining.HilbertMinimization
public import Homogenization.Sobolev.Foundations.H10Graph

@[expose] public section

/-!
# Existence for the local massive Dirichlet problem

This module constructs the weak solution of the weighted massive equation from
`s.fixed.coefficient` and `mfd:sec-speed`.  The zeroth-order term makes the form coercive
for the full `H¹` graph norm, with constant `min (μ ρ_min) λ`; no Poincare
inequality enters the Lax--Milgram step.

The library's `H1CoerciveHilbertSpace` is the mean-zero graph used for Neumann
problems.  Dirichlet data require the full closed `H¹` graph instead.  We use
the same `WithLp 2` Hilbert realization, take the closed `H¹₀` graph as the
variation subspace, and apply `Homogenization.affineMinimizerMap` after shifting
the scalar forcing by its Lax--Milgram representative.

## Main declaration

* `exists_isMassiveDirichletSolutionOn` -- existence with prescribed `H¹`
  boundary datum on a bounded open convex domain.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped RealInnerProductSpace

noncomputable section

variable {d : ℕ}

namespace MassiveScalarMultiplier

variable {W : Set (Vec d)} {rho : Vec d → ℝ} {rhoMax : ℝ}

public def applyFn (F : ScalarL2 W) : Vec d → ℝ :=
  fun x ↦ rho x * F x

private theorem aestronglyMeasurable_applyFn
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (F : ScalarL2 W) :
    AEStronglyMeasurable (applyFn (rho := rho) F) (volumeMeasureOn W) :=
  hrhoMeas.mul (MeasureTheory.Lp.aestronglyMeasurable F)

private theorem memL2_applyFn
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (F : ScalarL2 W) :
    MemScalarL2 W (applyFn (rho := rho) F) := by
  have hbound : ∀ᵐ x ∂(volumeMeasureOn W),
      ‖applyFn (rho := rho) F x‖ ≤ max rhoMax 0 * ‖F x‖ := by
    filter_upwards [hrhoBdd] with x hx
    calc
      ‖applyFn (rho := rho) F x‖ = |rho x| * ‖F x‖ := by
        rw [applyFn, norm_mul, Real.norm_eq_abs]
      _ ≤ rhoMax * ‖F x‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      _ ≤ max rhoMax 0 * ‖F x‖ := by
        gcongr
        exact le_max_left _ _
  exact MemLp.of_le_mul (MeasureTheory.Lp.memLp F)
    (aestronglyMeasurable_applyFn hrhoMeas F) hbound

public noncomputable def apply
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (F : ScalarL2 W) : ScalarL2 W :=
  Homogenization.toScalarL2 (show MemScalarL2 W (applyFn (rho := rho) F) from by
    exact memL2_applyFn hrhoMeas hrhoBdd F)

private theorem coeFn_apply
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (F : ScalarL2 W) :
    apply hrhoMeas hrhoBdd F =ᵐ[volumeMeasureOn W] applyFn (rho := rho) F :=
  Homogenization.coeFn_toScalarL2 (memL2_applyFn hrhoMeas hrhoBdd F)

private theorem apply_add
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (F G : ScalarL2 W) :
    apply hrhoMeas hrhoBdd (F + G) =
      apply hrhoMeas hrhoBdd F + apply hrhoMeas hrhoBdd G := by
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_apply hrhoMeas hrhoBdd (F + G),
      coeFn_apply hrhoMeas hrhoBdd F, coeFn_apply hrhoMeas hrhoBdd G,
      MeasureTheory.Lp.coeFn_add F G,
      MeasureTheory.Lp.coeFn_add (apply hrhoMeas hrhoBdd F) (apply hrhoMeas hrhoBdd G)]
    with x hFG hF hG hdom hcod
  simp only [applyFn] at hFG hF hG
  rw [hFG, hdom]
  calc
    rho x * ((F : Vec d → ℝ) + (G : Vec d → ℝ)) x =
        rho x * F x + rho x * G x := by
      simp only [Pi.add_apply]
      ring
    _ = apply hrhoMeas hrhoBdd F x + apply hrhoMeas hrhoBdd G x := by
      rw [hF, hG]
    _ = (apply hrhoMeas hrhoBdd F + apply hrhoMeas hrhoBdd G) x := by
      simpa only [Pi.add_apply] using hcod.symm

private theorem apply_smul
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (r : ℝ) (F : ScalarL2 W) :
    apply hrhoMeas hrhoBdd (r • F) = r • apply hrhoMeas hrhoBdd F := by
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_apply hrhoMeas hrhoBdd (r • F),
      coeFn_apply hrhoMeas hrhoBdd F, MeasureTheory.Lp.coeFn_smul r F,
      MeasureTheory.Lp.coeFn_smul r (apply hrhoMeas hrhoBdd F)]
    with x hrF hF hdom hcod
  simp only [applyFn] at hrF hF
  rw [hrF, hdom]
  calc
    rho x * (r • (F : Vec d → ℝ)) x = r * (rho x * F x) := by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = r * apply hrhoMeas hrhoBdd F x := by rw [hF]
    _ = (r • apply hrhoMeas hrhoBdd F) x := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hcod.symm

private theorem norm_apply_le
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (F : ScalarL2 W) :
    ‖apply hrhoMeas hrhoBdd F‖ ≤ max rhoMax 0 * ‖F‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_apply hrhoMeas hrhoBdd F, hrhoBdd] with x hF hx
  rw [hF]
  simp only [applyFn, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hx.trans (le_max_left _ _)) (abs_nonneg _)

/-- Multiplication by a bounded measurable scalar weight on `L²(W)`. -/
noncomputable def clm
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax) :
    ScalarL2 W →L[ℝ] ScalarL2 W := by
  let L : ScalarL2 W →ₗ[ℝ] ScalarL2 W :=
    { toFun := apply hrhoMeas hrhoBdd
      map_add' := by exact apply_add hrhoMeas hrhoBdd
      map_smul' := by exact apply_smul hrhoMeas hrhoBdd }
  exact L.mkContinuous (max rhoMax 0) (by exact norm_apply_le hrhoMeas hrhoBdd)

theorem coeFn_clm
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (F : ScalarL2 W) :
    clm hrhoMeas hrhoBdd F =ᵐ[volumeMeasureOn W] fun x ↦ rho x * F x := by
  exact coeFn_apply hrhoMeas hrhoBdd F

theorem rhoMin_mul_norm_sq_le_inner_clm
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    {rhoMin : ℝ} (hrhoLow : ∀ᵐ x ∂(volumeMeasureOn W), rhoMin ≤ rho x)
    (F : ScalarL2 W) :
    rhoMin * ‖F‖ ^ 2 ≤ inner ℝ (clm hrhoMeas hrhoBdd F) F := by
  have hFF : Integrable (fun x ↦ F x * F x) (volumeMeasureOn W) :=
    (MeasureTheory.Lp.memLp F).integrable_mul (MeasureTheory.Lp.memLp F)
  have hρF : MemScalarL2 W (fun x ↦ rho x * F x) :=
    memL2_applyFn hrhoMeas hrhoBdd F
  have hρFF : Integrable (fun x ↦ (rho x * F x) * F x) (volumeMeasureOn W) :=
    hρF.integrable_mul (MeasureTheory.Lp.memLp F)
  have hpoint : ∀ᵐ x ∂(volumeMeasureOn W),
      rhoMin * (F x * F x) ≤ (rho x * F x) * F x := by
    filter_upwards [hrhoLow] with x hx
    nlinarith [sq_nonneg (F x)]
  calc
    rhoMin * ‖F‖ ^ 2 = ∫ x in W, rhoMin * (F x * F x) ∂volume := by
      rw [← real_inner_self_eq_norm_sq F, scalarInner_eq_integral,
        integral_const_mul]
    _ ≤ ∫ x in W, (rho x * F x) * F x ∂volume :=
      integral_mono_ae (hFF.const_mul rhoMin) hρFF hpoint
    _ = inner ℝ (clm hrhoMeas hrhoBdd F) F := by
      rw [scalarInner_eq_integral]
      refine (integral_congr_ae ?_).symm
      filter_upwards [coeFn_clm hrhoMeas hrhoBdd F] with x hx
      rw [hx]

end MassiveScalarMultiplier

/-! ### The full closed `H¹` graph as a Hilbert carrier -/

namespace MassiveH1Hilbert

variable {W : Set (Vec d)}

noncomputable abbrev Ambient := WithLp 2 (ScalarL2 W × HilbertVectorL2 W)

noncomputable abbrev ambientEquiv :
    Ambient (W := W) ≃L[ℝ] ScalarL2 W × HilbertVectorL2 W :=
  WithLp.prodContinuousLinearEquiv 2 ℝ (ScalarL2 W) (HilbertVectorL2 W)

noncomputable abbrev closedSubmodule : ClosedSubmodule ℝ (Ambient (W := W)) :=
  (h1GraphClosedSubmodule (U := W)).comap
    (ambientEquiv (W := W)).toContinuousLinearMap

noncomputable abbrev Space := ↥(closedSubmodule (W := W)).toSubmodule

noncomputable instance : SeminormedAddCommGroup (Space (W := W)) := by
  exact inferInstanceAs (SeminormedAddCommGroup (closedSubmodule (W := W)).toSubmodule)

noncomputable instance : NormedAddCommGroup (Space (W := W)) := by
  exact inferInstanceAs (NormedAddCommGroup (closedSubmodule (W := W)).toSubmodule)

noncomputable instance : NormedSpace ℝ (Space (W := W)) := by
  exact inferInstanceAs (NormedSpace ℝ (closedSubmodule (W := W)).toSubmodule)

noncomputable instance : InnerProductSpace ℝ (Space (W := W)) := by
  exact inferInstanceAs (InnerProductSpace ℝ (closedSubmodule (W := W)).toSubmodule)

noncomputable instance : CompleteSpace (Space (W := W)) := by
  simpa [Space, closedSubmodule] using!
    (closedSubmodule (W := W)).isClosed.completeSpace_coe

abbrev value (z : Space (W := W)) : ScalarL2 W := z.1.fst

abbrev gradient (z : Space (W := W)) : HilbertVectorL2 W := z.1.snd

noncomputable def valueCLM : Space (W := W) →L[ℝ] ScalarL2 W :=
  (WithLp.fstL (p := 2) (𝕜 := ℝ) (α := ScalarL2 W) (β := HilbertVectorL2 W)).comp
    (closedSubmodule (W := W)).toSubmodule.subtypeL

noncomputable def gradientCLM : Space (W := W) →L[ℝ] HilbertVectorL2 W :=
  (WithLp.sndL (p := 2) (𝕜 := ℝ) (α := ScalarL2 W) (β := HilbertVectorL2 W)).comp
    (closedSubmodule (W := W)).toSubmodule.subtypeL

@[simp] theorem valueCLM_apply (z : Space (W := W)) : valueCLM z = value z := rfl

@[simp] theorem gradientCLM_apply (z : Space (W := W)) : gradientCLM z = gradient z := rfl

/-- The full graph point carried by an `H¹` function. -/
noncomputable def ofH1Function (u : H1Function W) : Space (W := W) := by
  refine ⟨(ambientEquiv (W := W)).symm (u.toScalarL2, u.gradToHilbertVectorL2), ?_⟩
  change (ambientEquiv (W := W))
      ((ambientEquiv (W := W)).symm (u.toScalarL2, u.gradToHilbertVectorL2)) ∈
    h1GraphClosedSubmodule (U := W)
  rw [(ambientEquiv (W := W)).apply_symm_apply]
  exact h1_pair_mem_h1GraphClosedSubmodule u

@[simp] theorem value_ofH1Function (u : H1Function W) :
    value (ofH1Function u) = u.toScalarL2 := by
  simp [ofH1Function, value]

@[simp] theorem gradient_ofH1Function (u : H1Function W) :
    gradient (ofH1Function u) = u.gradToHilbertVectorL2 := by
  simp [ofH1Function, gradient]

/-- Recover the `H¹` function represented by a full graph point. -/
noncomputable def toH1Function (z : Space (W := W)) : H1Function W := by
  let p : ScalarL2 W × HilbertVectorL2 W := (ambientEquiv (W := W)) z.1
  have hp : p ∈ h1GraphClosedSubmodule (U := W) :=
    (ClosedSubmodule.mem_comap).1 z.2
  exact toH1FunctionOfMemH1Graph (U := W) p hp

@[simp] theorem toH1Function_toScalarL2 (z : Space (W := W)) :
    (toH1Function z).toScalarL2 = value z := by
  simpa only [value, ambientEquiv] using!
    toH1FunctionOfMemH1Graph_toScalarL2 (U := W)
      ((ambientEquiv (W := W)) z.1) ((ClosedSubmodule.mem_comap).1 z.2)

@[simp] theorem toH1Function_gradToHilbertVectorL2 (z : Space (W := W)) :
    (toH1Function z).gradToHilbertVectorL2 = gradient z := by
  simpa only [gradient, ambientEquiv] using!
    toH1FunctionOfMemH1Graph_gradToHilbertVectorL2 (U := W)
      ((ambientEquiv (W := W)) z.1) ((ClosedSubmodule.mem_comap).1 z.2)

@[simp] theorem ofH1Function_toH1Function (z : Space (W := W)) :
    ofH1Function (toH1Function z) = z := by
  apply Subtype.ext
  apply (ambientEquiv (W := W)).injective
  apply Prod.ext
  · simp
  · simp

/-- The closed `H¹₀` variation graph inside the full `H¹` Hilbert graph. -/
noncomputable def zeroTraceSubmodule : ClosedSubmodule ℝ (Space (W := W)) :=
  (h10GraphClosedSubmodule W).comap
    ((ambientEquiv (W := W)).toContinuousLinearMap.comp
      (closedSubmodule (W := W)).toSubmodule.subtypeL)

theorem sub_ofH1Function_mem_zeroTraceSubmodule_iff
    (z : Space (W := W)) (hD : H1Function W) :
    z - ofH1Function hD ∈ zeroTraceSubmodule (W := W) ↔
      ((value z - hD.toScalarL2, gradient z - hD.gradToHilbertVectorL2) ∈
        h10GraphClosedSubmodule W) := by
  rfl

theorem ofH10Function_mem_zeroTraceSubmodule (phi : H10Function W) :
    ofH1Function phi.toH1Function ∈ zeroTraceSubmodule (W := W) := by
  change
    (phi.toH1Function.toScalarL2, phi.toH1Function.gradToHilbertVectorL2) ∈
      h10GraphClosedSubmodule W
  exact Submodule.le_topologicalClosure (h10GraphSubmodule W)
    (h10_pair_mem_h10GraphSubmodule phi)

/-! ### The massive form on the full graph -/

variable {c rho : Vec d → ℝ} {mu lam Lam rhoMin rhoMax : ℝ}

noncomputable def weightedValueCLM
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax) :
    Space (W := W) →L[ℝ] ScalarL2 W :=
  (MassiveScalarMultiplier.clm hrhoMeas hrhoBdd).comp (valueCLM (W := W))

noncomputable def massBilin
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax) :
    Space (W := W) →L[ℝ] Space (W := W) →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp
    (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (weightedValueCLM hrhoMeas hrhoBdd) (valueCLM (W := W))

noncomputable def coeffGradientCLM
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c)) :
    Space (W := W) →L[ℝ] HilbertVectorL2 W :=
  (hilbertCoeffOperator hEll).comp (gradientCLM (W := W))

noncomputable def coeffGradientBilin
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c)) :
    Space (W := W) →L[ℝ] Space (W := W) →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp
    (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (coeffGradientCLM hEll) (gradientCLM (W := W))

noncomputable def massiveBilin
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax) :
    Space (W := W) →L[ℝ] Space (W := W) →L[ℝ] ℝ :=
  mu • massBilin hrhoMeas hrhoBdd + coeffGradientBilin hEll

@[simp] theorem massBilin_apply
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (z w : Space (W := W)) :
    massBilin hrhoMeas hrhoBdd z w =
      inner ℝ (MassiveScalarMultiplier.clm hrhoMeas hrhoBdd (value z)) (value w) := by
  unfold massBilin
  rw [ContinuousLinearMap.bilinearComp_apply]
  rfl

@[simp] theorem coeffGradientBilin_apply
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (z w : Space (W := W)) :
    coeffGradientBilin hEll z w =
      inner ℝ (hilbertCoeffOperator hEll (gradient z)) (gradient w) := by
  unfold coeffGradientBilin
  rw [ContinuousLinearMap.bilinearComp_apply]
  rfl

@[simp] theorem massiveBilin_apply
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (z w : Space (W := W)) :
    massiveBilin (mu := mu) hEll hrhoMeas hrhoBdd z w =
      mu * massBilin hrhoMeas hrhoBdd z w + coeffGradientBilin hEll z w := by
  simp [massiveBilin]

theorem massBilin_apply_ofH1Function
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (u v : H1Function W) :
    massBilin hrhoMeas hrhoBdd (ofH1Function u) (ofH1Function v) =
      ∫ x in W, rho x * u.toFun x * v.toFun x ∂volume := by
  rw [massBilin_apply, value_ofH1Function, value_ofH1Function,
    scalarInner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [MassiveScalarMultiplier.coeFn_clm hrhoMeas hrhoBdd u.toScalarL2,
      u.coeFn_toScalarL2, v.coeFn_toScalarL2] with x hρ hu hv
  rw [hρ, hu, hv]

theorem coeffGradientBilin_apply_ofH1Function
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (u v : H1Function W) :
    coeffGradientBilin hEll (ofH1Function u) (ofH1Function v) =
      ∫ x in W, vecDot (c x • u.grad x) (v.grad x) ∂volume := by
  rw [coeffGradientBilin_apply, gradient_ofH1Function, gradient_ofH1Function]
  have hAu := hilbertCoeffOperator_toHilbertVectorL2OfVecField hEll u.grad_memVectorL2
  rw [show u.gradToHilbertVectorL2 =
      toHilbertVectorL2OfVecField u.grad_memVectorL2 from rfl, hAu]
  rw [show v.gradToHilbertVectorL2 =
      toHilbertVectorL2OfVecField v.grad_memVectorL2 from rfl]
  rw [inner_toHilbertVectorL2OfVecField_eq_integral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp [scalarCoeffField, matVecMul_scalarMatrix]

theorem massiveBilin_apply_ofH1Function
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (u v : H1Function W) :
    massiveBilin (mu := mu) hEll hrhoMeas hrhoBdd
        (ofH1Function u) (ofH1Function v) =
      mu * ∫ x in W, rho x * u.toFun x * v.toFun x ∂volume +
        ∫ x in W, vecDot (c x • u.grad x) (v.grad x) ∂volume := by
  rw [massiveBilin_apply, massBilin_apply_ofH1Function,
    coeffGradientBilin_apply_ofH1Function]

/-! ### Coercivity -/

theorem coeffGradientBilin_self_ge
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (z : Space (W := W)) :
    lam * ‖gradient z‖ ^ 2 ≤ coeffGradientBilin hEll z z := by
  let u : H1Function W := toH1Function z
  have hsqInt : IntegrableOn (fun x ↦ vecNormSq (u.grad x)) W :=
    integrableOn_vecNormSq_h1Grad u
  have hflux : MemVectorL2 W (fun x ↦ c x • u.grad x) := by
    simpa [scalarCoeffField, matVecMul_scalarMatrix] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have henergyInt : IntegrableOn
      (fun x ↦ vecDot (c x • u.grad x) (u.grad x)) W :=
    integrableOn_vecDot_of_memVectorL2 hflux u.grad_memVectorL2
  have hmem : ∀ᵐ x ∂(volumeMeasureOn W), x ∈ W := by
    exact (ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
      (Filter.Eventually.of_forall fun _ hx ↦ hx)
  have hpoint : ∀ᵐ x ∂(volumeMeasureOn W),
      lam * vecNormSq (u.grad x) ≤ vecDot (c x • u.grad x) (u.grad x) := by
    filter_upwards [hmem] with x hx
    simpa [scalarCoeffField, matVecMul_scalarMatrix, vecDot_comm] using
      (hEll.2 x hx).2.2.1 (u.grad x)
  have hgradNorm : ‖gradient z‖ ^ 2 = ∫ x in W, vecNormSq (u.grad x) ∂volume := by
    calc
      ‖gradient z‖ ^ 2 = inner ℝ (gradient z) (gradient z) :=
        (real_inner_self_eq_norm_sq (gradient z)).symm
      _ = inner ℝ u.gradToHilbertVectorL2 u.gradToHilbertVectorL2 := by
        rw [toH1Function_gradToHilbertVectorL2]
      _ = ∫ x in W, vecNormSq (u.grad x) ∂volume := by
        simpa only [H1Function.gradToHilbertVectorL2, vecNormSq] using!
          inner_toHilbertVectorL2OfVecField_eq_integral
            u.grad_memVectorL2 u.grad_memVectorL2
  have hform : coeffGradientBilin hEll z z =
      ∫ x in W, vecDot (c x • u.grad x) (u.grad x) ∂volume := by
    simpa [u] using coeffGradientBilin_apply_ofH1Function hEll u u
  rw [hgradNorm, hform]
  calc
    lam * ∫ x in W, vecNormSq (u.grad x) ∂volume =
        ∫ x in W, lam * vecNormSq (u.grad x) ∂volume := by
      rw [integral_const_mul]
    _ ≤ ∫ x in W, vecDot (c x • u.grad x) (u.grad x) ∂volume :=
      integral_mono_ae (hsqInt.const_mul lam) henergyInt hpoint

theorem norm_sq_eq_value_add_gradient_sq (z : Space (W := W)) :
    ‖z‖ ^ 2 = ‖value z‖ ^ 2 + ‖gradient z‖ ^ 2 := by
  have hnorm : ‖z‖ = Real.sqrt (‖value z‖ ^ 2 + ‖gradient z‖ ^ 2) := by
    calc
      ‖z‖ = ‖(z : Ambient (W := W))‖ := rfl
      _ = Real.sqrt (‖z.1.fst‖ ^ 2 + ‖z.1.snd‖ ^ 2) := by
        exact WithLp.prod_norm_eq_of_L2 (x := z.1)
      _ = Real.sqrt (‖value z‖ ^ 2 + ‖gradient z‖ ^ 2) := rfl
  rw [hnorm, Real.sq_sqrt]
  positivity

/-- The massive form controls the full `H¹` graph norm with the sharp
constant supplied by the two zeroth/first-order ellipticity bounds. -/
theorem isCoercive_massiveBilin
    (hmu : 0 < mu) (hrhoMin : 0 < rhoMin) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (hrhoLow : ∀ᵐ x ∂(volumeMeasureOn W), rhoMin ≤ rho x) :
    IsCoercive (massiveBilin (mu := mu) hEll hrhoMeas hrhoBdd) := by
  refine ⟨min (mu * rhoMin) lam, ?_, ?_⟩
  · exact lt_min (mul_pos hmu hrhoMin) hlam
  intro z
  have hmass := MassiveScalarMultiplier.rhoMin_mul_norm_sq_le_inner_clm
    hrhoMeas hrhoBdd hrhoLow (value z)
  have hmass' : rhoMin * ‖value z‖ ^ 2 ≤ massBilin hrhoMeas hrhoBdd z z := by
    simpa using hmass
  have hgrad := coeffGradientBilin_self_ge hEll z
  have hmu0 : 0 ≤ mu := hmu.le
  have hval0 : 0 ≤ ‖value z‖ ^ 2 := sq_nonneg _
  have hgrad0 : 0 ≤ ‖gradient z‖ ^ 2 := sq_nonneg _
  have hCmass : min (mu * rhoMin) lam ≤ mu * rhoMin := min_le_left _ _
  have hCgrad : min (mu * rhoMin) lam ≤ lam := min_le_right _ _
  have hnormprod : ‖z‖ * ‖z‖ = ‖value z‖ ^ 2 + ‖gradient z‖ ^ 2 := by
    rw [← pow_two, norm_sq_eq_value_add_gradient_sq]
  rw [massiveBilin_apply]
  rw [mul_assoc, hnormprod]
  nlinarith [mul_le_mul_of_nonneg_left hmass' hmu0]

/-! ### The weighted scalar forcing -/

noncomputable def forcingFunctional
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    {f : Vec d → ℝ} (hf : MemL2On W f) :
    Space (W := W) →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (ScalarL2 W)
      (Homogenization.toScalarL2
        (memL2On_mul_of_bounded hrhoMeas hrhoBdd hf))).comp
    (valueCLM (W := W))

theorem forcingFunctional_apply_ofH1Function
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    {f : Vec d → ℝ} (hf : MemL2On W f) (u : H1Function W) :
    forcingFunctional hrhoMeas hrhoBdd hf (ofH1Function u) =
      ∫ x in W, rho x * f x * u.toFun x ∂volume := by
  rw [forcingFunctional, ContinuousLinearMap.comp_apply,
    InnerProductSpace.toDual_apply_apply, valueCLM_apply, value_ofH1Function,
    scalarInner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards
      [Homogenization.coeFn_toScalarL2
        (memL2On_mul_of_bounded hrhoMeas hrhoBdd hf),
       u.coeFn_toScalarL2] with x hF hu
  rw [hF, hu]

end MassiveH1Hilbert

/-! ### Existence on bounded open convex windows -/

/-- **Massive Lax--Milgram solver.**  The weighted massive resolvent equation
has a weak solution with any prescribed `H¹` boundary datum on a bounded open
convex window.  Coercivity comes from the mass and ellipticity lower bounds;
no Poincare estimate is used. -/
theorem exists_isMassiveDirichletSolutionOn [NeZero d]
    {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {c rho : Vec d → ℝ} {mu lam Lam rhoMin rhoMax : ℝ}
    (hmu : 0 < mu) (hrhoMin : 0 < rhoMin) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x)
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (hD : H1Function W) {f : Vec d → ℝ} (hf : MemL2On W f) :
    ∃ u : H1Function W,
      IsMassiveDirichletSolutionOn c rho mu W u hD f := by
  classical
  let : IsFiniteMeasure (volumeMeasureOn W) := hW.isFiniteMeasure_restrict_volume
  have hmemW : ∀ᵐ x ∂(volumeMeasureOn W), x ∈ W := by
    exact (ae_restrict_iff' hW.isOpen.measurableSet).2
      (Filter.Eventually.of_forall fun _ hx ↦ hx)
  have hrhoLowAE : ∀ᵐ x ∂(volumeMeasureOn W), rhoMin ≤ rho x := by
    filter_upwards [hmemW] with x hx
    exact hrhoLow x hx
  let B := MassiveH1Hilbert.massiveBilin (mu := mu) hEll hrhoMeas hrhoBdd
  let K := MassiveH1Hilbert.zeroTraceSubmodule (W := W)
  let ell := MassiveH1Hilbert.forcingFunctional hrhoMeas hrhoBdd hf
  have hB : IsCoercive B := by
    exact MassiveH1Hilbert.isCoercive_massiveBilin
      hmu hrhoMin hlam hEll hrhoMeas hrhoBdd hrhoLowAE
  let q := linearQuadraticResponseMaximizer B hB ell
  let x := MassiveH1Hilbert.ofH1Function hD - q
  let m := affineMinimizerMap K B hB x
  let z := m + q
  have hzFirst (phi : H10Function W) :
      B z (MassiveH1Hilbert.ofH1Function phi.toH1Function) =
        ell (MassiveH1Hilbert.ofH1Function phi.toH1Function) := by
    let wp : K.toSubmodule :=
      ⟨MassiveH1Hilbert.ofH1Function phi.toH1Function,
        MassiveH1Hilbert.ofH10Function_mem_zeroTraceSubmodule phi⟩
    change B z (wp : MassiveH1Hilbert.Space (W := W)) =
      ell (wp : MassiveH1Hilbert.Space (W := W))
    calc
      B z (wp : MassiveH1Hilbert.Space (W := W)) = B m wp + B q wp := by
        rw [show z = m + q from rfl, B.map_add₂]
      _ = 0 + ell wp := by
        rw [show m = affineMinimizerMap K B hB x from rfl,
          affineMinimizerMap_firstVariation K B hB x wp,
          show q = linearQuadraticResponseMaximizer B hB ell from rfl,
          linearQuadraticResponseMaximizer_firstVariation]
      _ = ell wp := zero_add _
  have hzMem :
      z - MassiveH1Hilbert.ofH1Function hD ∈ K := by
    have hm := sub_affineMinimizerMap_apply_mem K B hB x
    convert hm using 1
    all_goals
      dsimp [z, m, x]
      abel
  have hzPair :
      (MassiveH1Hilbert.value z - hD.toScalarL2,
          MassiveH1Hilbert.gradient z - hD.gradToHilbertVectorL2) ∈
        h10GraphClosedSubmodule W :=
    (MassiveH1Hilbert.sub_ofH1Function_mem_zeroTraceSubmodule_iff z hD).1 hzMem
  obtain ⟨w, hwVal, hwGrad⟩ :=
    exists_h10Function_of_mem_h10GraphClosedSubmodule (U := W) hW hzPair
  let u : H1Function W := hD + w.toH1Function
  have huGraph : MassiveH1Hilbert.ofH1Function u = z := by
    apply Subtype.ext
    apply (MassiveH1Hilbert.ambientEquiv (W := W)).injective
    change (u.toScalarL2, u.gradToHilbertVectorL2) =
      (MassiveH1Hilbert.value z, MassiveH1Hilbert.gradient z)
    apply Prod.ext
    · rw [show u = hD + w.toH1Function from rfl,
        H1Function.toScalarL2_add, hwVal]
      simp only
      abel
    · rw [show u = hD + w.toH1Function from rfl,
        H1Function.gradToHilbertVectorL2_add, hwGrad]
      simp only
      abel
  refine ⟨u, ?_, ?_⟩
  · exact ⟨w, fun _ ↦ rfl, fun _ ↦ rfl⟩
  · intro phi
    have hfirst :
        B (MassiveH1Hilbert.ofH1Function u)
            (MassiveH1Hilbert.ofH1Function phi.toH1Function) =
          ell (MassiveH1Hilbert.ofH1Function phi.toH1Function) := by
      calc
        B (MassiveH1Hilbert.ofH1Function u)
            (MassiveH1Hilbert.ofH1Function phi.toH1Function) =
            B z (MassiveH1Hilbert.ofH1Function phi.toH1Function) := by
          exact congrArg
            (fun y ↦ B y (MassiveH1Hilbert.ofH1Function phi.toH1Function))
            huGraph
        _ = ell (MassiveH1Hilbert.ofH1Function phi.toH1Function) := hzFirst phi
    calc
      mu * ∫ x in W, rho x * u.toFun x * phi.toH1Function.toFun x ∂volume +
          ∫ x in W, vecDot (c x • u.grad x) (phi.toH1Function.grad x) ∂volume =
          MassiveH1Hilbert.massiveBilin (mu := mu) hEll hrhoMeas hrhoBdd
            (MassiveH1Hilbert.ofH1Function u)
            (MassiveH1Hilbert.ofH1Function phi.toH1Function) :=
        (MassiveH1Hilbert.massiveBilin_apply_ofH1Function
          hEll hrhoMeas hrhoBdd u phi.toH1Function).symm
      _ = B (MassiveH1Hilbert.ofH1Function u)
            (MassiveH1Hilbert.ofH1Function phi.toH1Function) := rfl
      _ = ell (MassiveH1Hilbert.ofH1Function phi.toH1Function) := hfirst
      _ = MassiveH1Hilbert.forcingFunctional hrhoMeas hrhoBdd hf
            (MassiveH1Hilbert.ofH1Function phi.toH1Function) := rfl
      _ = ∫ x in W, rho x * f x * phi.toH1Function.toFun x ∂volume :=
        MassiveH1Hilbert.forcingFunctional_apply_ofH1Function
          hrhoMeas hrhoBdd hf phi.toH1Function

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
