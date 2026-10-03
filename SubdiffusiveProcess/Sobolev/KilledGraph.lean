module

public import SubdiffusiveProcess.Sobolev.WeakGradient
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

@[expose] public section

/-!
# The killed Sobolev graph

The zero-boundary space is the closure of the classical function/gradient
pairs of smooth functions compactly supported in the domain. Integration by
parts proves that this closure consists of genuine weak gradients. No trace
or density theorem about a proposed abstract space is assumed.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Classical function and coordinate derivatives of a compactly supported smooth function. -/
def smoothSobolevData (φ : 𝓓(Ω, ℝ)) : SobolevData Ω :=
  (testL2 φ, testPartialL2 φ)

/-- The actual smooth-gradient graph is linear. -/
def smoothSobolevDataLinear : 𝓓(Ω, ℝ) →ₗ[ℝ] SobolevData Ω where
  toFun := smoothSobolevData
  map_add' φ ψ := by
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [testL2_coeFn (φ + ψ), testL2_coeFn φ, testL2_coeFn ψ,
        Lp.coeFn_add (testL2 φ) (testL2 ψ)] with x ha hb hc hd
      change (testL2 (φ + ψ)) x = (testL2 φ + testL2 ψ) x
      rw [ha, hd]
      change φ x + ψ x = (testL2 φ) x + (testL2 ψ) x
      rw [hb, hc]
    · funext i
      apply Lp.ext
      filter_upwards [testPartialL2_coeFn (φ + ψ) i, testPartialL2_coeFn φ i,
        testPartialL2_coeFn ψ i, Lp.coeFn_add (testPartialL2 φ i) (testPartialL2 ψ i)]
        with x ha hb hc hd
      change (testPartialL2 (φ + ψ) i) x = (testPartialL2 φ i + testPartialL2 ψ i) x
      rw [ha, hd]
      simp only [Pi.add_apply, hb, hc]
      change fderiv ℝ ((φ : SpatialCoordinates d → ℝ) + (ψ : SpatialCoordinates d → ℝ)) x (Pi.single i 1) = _
      rw [fderiv_add (φ.contDiff.differentiable (by simp) x)
        (ψ.contDiff.differentiable (by simp) x)]
      rfl
  map_smul' c φ := by
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [testL2_coeFn (c • φ), testL2_coeFn φ,
        Lp.coeFn_smul c (testL2 φ)] with x ha hb hc
      change (testL2 (c • φ)) x = (c • testL2 φ) x
      simp [ha, hb, hc]
    · funext i
      apply Lp.ext
      filter_upwards [testPartialL2_coeFn (c • φ) i, testPartialL2_coeFn φ i,
        Lp.coeFn_smul c (testPartialL2 φ i)] with x ha hb hc
      change (testPartialL2 (c • φ) i) x = (c • testPartialL2 φ i) x
      rw [ha, hc]
      simp only [Pi.smul_apply, hb]
      change fderiv ℝ (c • (φ : SpatialCoordinates d → ℝ)) x (Pi.single i 1) = _
      rw [fderiv_const_smul (φ.contDiff.differentiable (by simp) x)]
      rfl

/-- Classical derivatives satisfy the weak derivative identities on the actual domain. -/
theorem smoothSobolevData_mem (ψ : 𝓓(Ω, ℝ)) :
    smoothSobolevData ψ ∈ weakSobolevGraph Ω := by
  rw [mem_weakSobolevGraph_iff]
  intro φ i
  let v : SpatialCoordinates d := Pi.single i 1
  have hφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (φ.contDiff.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have hψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (ψ.contDiff.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (SpatialCoordinates d))) (v := v)
    ((hφ.mul ψ.contDiff.continuous).integrable_of_hasCompactSupport
      (φ.hasCompactSupport.fderiv_apply ℝ v).mul_right)
    ((φ.contDiff.continuous.mul hψ).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right)
    ((φ.contDiff.continuous.mul ψ.contDiff.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right)
    (fun x _ => φ.contDiff.differentiable (by simp) x)
    (fun x _ => ψ.contDiff.differentiable (by simp) x)
  have hleft : (∫ x in (Ω : Set (SpatialCoordinates d)),
      φ x * (testPartialL2 ψ i) x) = ∫ x, φ x * fderiv ℝ ψ x v := by
    calc
      _ = ∫ x in (Ω : Set (SpatialCoordinates d)), φ x * fderiv ℝ ψ x v := by
        apply integral_congr_ae
        filter_upwards [testPartialL2_coeFn ψ i] with x hx
        rw [hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hx (φ.tsupport_subset h))
        simp only [hz, zero_mul]
  have hright : (∫ x in (Ω : Set (SpatialCoordinates d)),
      fderiv ℝ φ x v * (testL2 ψ) x) = ∫ x, fderiv ℝ φ x v * ψ x := by
    calc
      _ = ∫ x in (Ω : Set (SpatialCoordinates d)), fderiv ℝ φ x v * ψ x := by
        apply integral_congr_ae
        filter_upwards [testL2_coeFn ψ] with x hx
        rw [hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hz : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ
          (fun h => hx (φ.tsupport_subset h))
        simp only [hz, ContinuousLinearMap.zero_apply, zero_mul]
  change (∫ x in (Ω : Set (SpatialCoordinates d)), φ x * (testPartialL2 ψ i) x) +
    (∫ x in (Ω : Set (SpatialCoordinates d)), fderiv ℝ φ x v * (testL2 ψ) x) = 0
  rw [hleft, hright, hibp, neg_add_cancel]

/-- The zero-boundary Sobolev graph is the closure of actual compactly supported smooth data. -/
def killedSobolevGraph (Ω : Opens (SpatialCoordinates d)) : Submodule ℝ (SobolevData Ω) :=
  (LinearMap.range (smoothSobolevDataLinear (Ω := Ω))).topologicalClosure

/-- The killed space is closed, hence complete in its graph norm. -/
theorem isClosed_killedSobolevGraph :
    IsClosed (killedSobolevGraph Ω : Set (SobolevData Ω)) :=
  Submodule.isClosed_topologicalClosure _

/-- Every element of the killed completion has genuine weak first derivatives. -/
theorem killedSobolevGraph_le_weakSobolevGraph : killedSobolevGraph Ω ≤ weakSobolevGraph Ω := by
  apply Submodule.topologicalClosure_minimal
  · rintro z ⟨φ, rfl⟩
    exact smoothSobolevData_mem φ
  · exact isClosed_weakSobolevGraph

/-- Smooth compactly supported data belong to the killed space. -/
theorem smoothSobolevData_mem_killed (φ : 𝓓(Ω, ℝ)) :
    smoothSobolevData φ ∈ killedSobolevGraph Ω :=
  Submodule.le_topologicalClosure _ ⟨φ, rfl⟩

end SubdiffusiveProcess
