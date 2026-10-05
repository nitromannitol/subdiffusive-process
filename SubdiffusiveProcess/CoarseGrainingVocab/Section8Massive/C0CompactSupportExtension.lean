module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventPackage
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.ContinuousMap.CompactlySupported

@[expose] public section

/-!
# Extending sup-norm contractions from compactly supported data

This file isolates the functional-analytic completion step in the whole-space
massive-resolvent construction.  Compactly supported continuous real functions
embed isometrically and densely in `C₀(E, ℝ)`.  Consequently every bounded
linear solution operator constructed first on compactly supported data extends
uniquely to `C₀(E, ℝ)`, without any further PDE input.

The density proof uses value truncation rather than a spatial cutoff.  For
`f : C₀(E, ℝ)`, deleting the values whose absolute value is at most `δ` gives a
continuous compactly supported function at uniform distance at most `δ` from
`f`.  This works on every locally compact domain and is particularly convenient
for `E = Vec d`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter Set Topology
open scoped CompactlySupported ZeroAtInfty

noncomputable section

variable {E : Type*} [TopologicalSpace E] [T2Space E]

/-- The canonical linear inclusion `C_c(E, ℝ) → C₀(E, ℝ)`. -/
noncomputable def compactSupportToC0 : C_c(E, ℝ) →ₗ[ℝ] C₀(E, ℝ) where
  toFun f := (f : C₀(E, ℝ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [T2Space E] in
@[simp]
theorem compactSupportToC0_apply (f : C_c(E, ℝ)) (x : E) :
    compactSupportToC0 f x = f x := rfl

/-- Soft value truncation: it agrees with `t` up to an error `δ` and vanishes
when `|t| ≤ δ`. -/
def softValueCutoff (δ t : ℝ) : ℝ :=
  max (t - δ) 0 + min (t + δ) 0

theorem continuous_softValueCutoff (δ : ℝ) : Continuous (softValueCutoff δ) := by
  exact ((continuous_id.sub continuous_const).max continuous_const).add
    ((continuous_id.add continuous_const).min continuous_const)

theorem softValueCutoff_eq_zero {δ t : ℝ} (ht : |t| ≤ δ) :
    softValueCutoff δ t = 0 := by
  rw [abs_le] at ht
  have h₁ : t - δ ≤ 0 := by linarith
  have h₂ : 0 ≤ t + δ := by linarith
  rw [softValueCutoff, max_eq_right h₁, min_eq_right h₂, add_zero]

theorem abs_softValueCutoff_sub_le {δ t : ℝ} (hδ : 0 ≤ δ) :
    |softValueCutoff δ t - t| ≤ δ := by
  rcases le_total t (-δ) with ht | ht
  · have h₁ : t - δ ≤ 0 := by linarith
    have h₂ : t + δ ≤ 0 := by linarith
    simp [softValueCutoff, max_eq_right h₁, min_eq_left h₂, abs_of_nonneg hδ]
  · rcases le_total t δ with ht' | ht'
    · have habs : |t| ≤ δ := abs_le.2 ⟨by linarith, ht'⟩
      rw [softValueCutoff_eq_zero habs]
      simpa [abs_neg] using habs
    · have h₁ : 0 ≤ t - δ := by linarith
      have h₂ : 0 ≤ t + δ := by linarith
      simp [softValueCutoff, max_eq_left h₁, min_eq_right h₂, abs_of_nonneg hδ]

/-- A compactly supported approximation obtained by deleting small values of a
function vanishing at infinity. -/
noncomputable def compactSupportApprox (f : C₀(E, ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    C_c(E, ℝ) where
  toFun := softValueCutoff δ ∘ f
  continuous_toFun := (continuous_softValueCutoff δ).comp f.continuous
  hasCompactSupport' := by
    have hnear : {t : ℝ | |t| < δ} ∈ 𝓝 (0 : ℝ) := by
      simpa only [abs_lt, Set.Ioo_def] using Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ
    obtain ⟨K, hKcompact, hK⟩ := mem_cocompact.mp
      (tendsto_def.mp (zero_at_infty f) _ hnear)
    refine HasCompactSupport.of_support_subset_isCompact hKcompact ?_
    intro x hx
    by_contra hxK
    have hsmall : |f x| < δ := hK hxK
    have hz := softValueCutoff_eq_zero (le_of_lt hsmall)
    exact hx (by simp [Function.comp_apply, hz])

@[simp]
theorem compactSupportApprox_apply (f : C₀(E, ℝ)) (δ : ℝ) (hδ : 0 < δ) (x : E) :
    compactSupportApprox f δ hδ x = softValueCutoff δ (f x) := rfl

theorem norm_compactSupportApprox_sub_le (f : C₀(E, ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    ‖compactSupportToC0 (compactSupportApprox f δ hδ) - f‖ ≤ δ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le hδ.le).2 fun x ↦ ?_
  simp only [ZeroAtInftyContinuousMap.toBCF_apply,
    ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, compactSupportToC0_apply,
    compactSupportApprox_apply, Real.norm_eq_abs]
  exact abs_softValueCutoff_sub_le hδ.le

/-- Compactly supported continuous functions have dense range in `C₀(E, ℝ)`.
The statement is phrased for the canonical continuous linear inclusion so it
can be fed directly to `ContinuousLinearMap.extend`. -/
theorem denseRange_compactSupportToC0 :
    DenseRange (compactSupportToC0 : C_c(E, ℝ) → C₀(E, ℝ)) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  refine ⟨compactSupportApprox f (ε / 2) (half_pos hε), ?_⟩
  rw [dist_eq_norm]
  rw [norm_sub_rev]
  exact (norm_compactSupportApprox_sub_le f (ε / 2) (half_pos hε)).trans_lt
    (half_lt_self hε)

/-- The sup-norm extension of a bounded linear operator initially constructed
on compactly supported continuous data. -/
noncomputable def extendCompactSupportOperator
    (T : C_c(E, ℝ) →ₗ[ℝ] C₀(E, ℝ)) : C₀(E, ℝ) →L[ℝ] C₀(E, ℝ) :=
  LinearMap.extendOfNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
    (E := C_c(E, ℝ)) (Eₗ := C₀(E, ℝ)) (F := C₀(E, ℝ))
    T compactSupportToC0

@[simp]
theorem extendCompactSupportOperator_compactSupport
    (T : C_c(E, ℝ) →ₗ[ℝ] C₀(E, ℝ)) {C : ℝ}
    (hT : ∀ g, ‖T g‖ ≤ C * ‖compactSupportToC0 g‖)
    (f : C_c(E, ℝ)) :
    extendCompactSupportOperator T (compactSupportToC0 f) = T f := by
  have hnorm : ∃ C : ℝ, ∀ g : C_c(E, ℝ),
      ‖T g‖ ≤ C * ‖compactSupportToC0 g‖ := ⟨C, hT⟩
  change (LinearMap.extendOfNorm T compactSupportToC0)
    (compactSupportToC0 f) = T f
  exact LinearMap.extendOfNorm_eq (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
    (E := C_c(E, ℝ)) (Eₗ := C₀(E, ℝ)) (F := C₀(E, ℝ)) (f := T)
    (e := compactSupportToC0) denseRange_compactSupportToC0 hnorm f

theorem norm_extendCompactSupportOperator_apply_le
    (T : C_c(E, ℝ) →ₗ[ℝ] C₀(E, ℝ)) {C : ℝ}
    (hT : ∀ g, ‖T g‖ ≤ C * ‖compactSupportToC0 g‖) (f : C₀(E, ℝ)) :
    ‖extendCompactSupportOperator T f‖ ≤ C * ‖f‖ := by
  change ‖(LinearMap.extendOfNorm T compactSupportToC0) f‖ ≤ C * ‖f‖
  exact LinearMap.norm_extendOfNorm_apply_le (𝕜 := ℝ) (𝕜₂ := ℝ)
    (σ₁₂ := RingHom.id ℝ) (E := C_c(E, ℝ))
    (Eₗ := C₀(E, ℝ)) (F := C₀(E, ℝ)) (f := T)
    (e := compactSupportToC0) denseRange_compactSupportToC0 C hT f

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
