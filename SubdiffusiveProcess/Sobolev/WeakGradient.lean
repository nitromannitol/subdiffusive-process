import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# The actual weak-gradient graph

Spatial coordinates use the usual finite product, with its sup norm. Gradient
energy will use the sum of squared coordinate L2 norms, not that sup norm.
The graph below imposes the distributional derivative identity against every
smooth function compactly supported in the open domain. It does not assume
an abstract space has the properties of a Sobolev space.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
namespace SubdiffusiveProcess
noncomputable section

abbrev SpatialCoordinates (d : ℕ) := Fin d → ℝ
abbrev DomainL2 {d : ℕ} (Ω : Opens (SpatialCoordinates d)) :=
  Lp ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))
abbrev SobolevData {d : ℕ} (Ω : Opens (SpatialCoordinates d)) :=
  DomainL2 Ω × (Fin d → DomainL2 Ω)

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- A smooth compactly supported test, as an actual scalar L2 equivalence class. -/
noncomputable def testL2 (φ : 𝓓(Ω, ℝ)) : DomainL2 Ω :=
  (φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ

/-- The coordinate derivative of a test is also an actual L2 function. -/
noncomputable def testPartialL2 (φ : 𝓓(Ω, ℝ)) (i : Fin d) : DomainL2 Ω :=
  ((φ.contDiff.continuous_fderiv_apply (by simp)).comp
    (continuous_id.prodMk continuous_const) |>.memLp_of_hasCompactSupport
      (φ.hasCompactSupport.fderiv_apply ℝ (Pi.single i 1))).toLp
    (fun x => fderiv ℝ φ x (Pi.single i 1))

/-- No pointwise representative is selected outside its almost-everywhere identity. -/
theorem testL2_coeFn (φ : 𝓓(Ω, ℝ)) :
    (testL2 φ : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] φ :=
  MemLp.coeFn_toLp _

/-- The L2 derivative is the classical coordinate derivative almost everywhere. -/
theorem testPartialL2_coeFn (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    (testPartialL2 φ i : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
      (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
  MemLp.coeFn_toLp _

/-- One distributional integration-by-parts constraint, as a bounded linear functional. -/
noncomputable def weakGradientTest (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    SobolevData Ω →L[ℝ] ℝ :=
  ((innerSL ℝ (testL2 φ)).comp
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _))) +
  ((innerSL ℝ (testPartialL2 φ i)).comp (ContinuousLinearMap.fst ℝ _ _))

/-- The graph of weak first derivatives on the open domain. -/
noncomputable def weakSobolevGraph (Ω : Opens (SpatialCoordinates d)) :
    Submodule ℝ (SobolevData Ω) :=
  ⨅ (φ : 𝓓(Ω, ℝ)) (i : Fin d), LinearMap.ker (weakGradientTest φ i)

/-- Membership is the actual distributional derivative identity. -/
theorem mem_weakSobolevGraph_iff (z : SobolevData Ω) :
    z ∈ weakSobolevGraph Ω ↔ ∀ (φ : 𝓓(Ω, ℝ)) (i : Fin d),
      (∫ x in (Ω : Set (SpatialCoordinates d)), φ x * z.2 i x) +
        (∫ x in (Ω : Set (SpatialCoordinates d)), fderiv ℝ φ x (Pi.single i 1) * z.1 x) = 0 := by
  simp only [weakSobolevGraph, Submodule.mem_iInf, LinearMap.mem_ker]
  have htest : ∀ (φ : 𝓓(Ω, ℝ)) (i : Fin d),
      weakGradientTest φ i z =
        (∫ x in (Ω : Set (SpatialCoordinates d)), φ x * z.2 i x) +
          (∫ x in (Ω : Set (SpatialCoordinates d)), fderiv ℝ φ x (Pi.single i 1) * z.1 x) := by
    intro φ i
    change inner ℝ (testL2 φ) (z.2 i) + inner ℝ (testPartialL2 φ i) z.1 = _
    rw [L2.inner_def, L2.inner_def]
    congr 1
    · apply integral_congr_ae
      filter_upwards [testL2_coeFn φ] with x hx
      simp [hx, mul_comm]
    · apply integral_congr_ae
      filter_upwards [testPartialL2_coeFn φ i] with x hx
      simp [hx, mul_comm]
  simp only [htest]

/-- The weak-gradient graph is closed in the product of scalar L2 spaces. -/
theorem isClosed_weakSobolevGraph :
    IsClosed (weakSobolevGraph Ω : Set (SobolevData Ω)) := by
  simp only [weakSobolevGraph, Submodule.coe_iInf]
  change IsClosed (⋂ (φ : 𝓓(Ω, ℝ)) (i : Fin d),
    {z : SobolevData Ω | weakGradientTest φ i z = 0})
  exact isClosed_iInter fun φ => isClosed_iInter fun i =>
    isClosed_eq (weakGradientTest φ i).continuous continuous_const

/-- The weak derivative of the zero function vanishes: no extra derivative
coordinate can be hidden in the graph. -/
theorem weakSobolevGraph_gradient_eq_zero {g : Fin d → DomainL2 Ω}
    (hg : (0, g) ∈ weakSobolevGraph Ω) : g = 0 := by
  have htest := (mem_weakSobolevGraph_iff (0, g)).mp hg
  funext i
  apply Lp.ext
  have hi := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (((Lp.memLp (g i)).locallyIntegrable (by norm_num)).locallyIntegrableOn (Ω : Set (SpatialCoordinates d)))
    (fun φ hφ hc hΩ => ?_)
  · filter_upwards [hi, ae_restrict_mem Ω.isOpen.measurableSet,
      (Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d))))] with x hx hΩ hz
    change (g i : SpatialCoordinates d → ℝ) x = (0 : DomainL2 Ω) x
    exact (hx hΩ).trans hz.symm
  · let φb : 𝓓(Ω, ℝ) := ⟨φ, hφ, hc, hΩ⟩
    have he := htest φb i
    have hz : (∫ x in (Ω : Set (SpatialCoordinates d)),
        fderiv ℝ φb x (Pi.single i 1) * (0 : DomainL2 Ω) x) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))] with x hx
      simp only [hx, Pi.zero_apply, mul_zero]
    rw [hz, add_zero] at he
    simpa only [smul_eq_mul] using he

/-- A function has at most one L2 weak gradient. -/
theorem weakSobolevGraph_gradient_unique {u : DomainL2 Ω} {g h : Fin d → DomainL2 Ω}
    (hg : (u, g) ∈ weakSobolevGraph Ω) (hh : (u, h) ∈ weakSobolevGraph Ω) : g = h := by
  have hz : (0, g - h) ∈ weakSobolevGraph Ω := by
    simpa only [Prod.mk_sub_mk, sub_self] using (weakSobolevGraph Ω).sub_mem hg hh
  exact sub_eq_zero.mp (weakSobolevGraph_gradient_eq_zero hz)

end
end SubdiffusiveProcess
