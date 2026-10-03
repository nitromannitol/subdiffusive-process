module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452ForwardMaximal

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology

open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-! ## The path measure -/

/-- The σ-finite path measure `∫ₓ P_x dx`. -/
def pathMeasure (d : ℕ) : Measure (ContinuousPath (Vec d)) :=
  Measure.bind volume (laplacianContinuousLaw d)

theorem lintegral_pathMeasure {F : ContinuousPath (Vec d) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, F ω ∂(pathMeasure d))
      = ∫⁻ x, (∫⁻ ω, F ω ∂(laplacianContinuousLaw d x)) ∂volume :=
  Measure.lintegral_bind (laplacianContinuousLaw d).measurable.aemeasurable hF.aemeasurable

/-! ## The reversal map -/

/-- The time reflection `u ↦ T − u` of `ℝ≥0`, as a continuous map. -/
def timeReflect (T : ℝ≥0) : C(ℝ≥0, ℝ≥0) :=
  ⟨fun u => T - u, continuous_real_toNNReal.comp (continuous_const.sub NNReal.continuous_coe)⟩

theorem reversePath_eq_comp (T : ℝ≥0) (ω : ContinuousPath (Vec d)) :
    reversePath T ω = ω.comp (timeReflect T) := rfl

theorem continuous_reversePath (T : ℝ≥0) :
    Continuous (reversePath T : ContinuousPath (Vec d) → ContinuousPath (Vec d)) := by
  have h : (reversePath T : ContinuousPath (Vec d) → ContinuousPath (Vec d))
      = fun ω => ω.comp (timeReflect T) := rfl
  rw [h]
  exact ContinuousMap.continuous_precomp (timeReflect T)

theorem measurable_reversePath (T : ℝ≥0) :
    Measurable (reversePath T : ContinuousPath (Vec d) → ContinuousPath (Vec d)) :=
  (continuous_reversePath T).measurable

/-- **The invariance of the path measure under time reversal**, as a named predicate.

The restriction to functionals measurable for the canonical filtration at `T` is **not** a
convenience: the unrestricted statement `(pathMeasure d).map (reversePath T) = pathMeasure d` is
**false**.  `reversePath T ω` is frozen at `ω 0` on `[T, ∞)` -- truncated subtraction sends every
`u > T` to `0` -- so the reversed measure is carried by eventually-constant paths, which are
`pathMeasure`-null.  Only the restriction of the two measures to `𝓕_T` agree, and that is all the
consumer needs: the maximal functional over `[0, T]` is `𝓕_T`-measurable. -/
def PathReversalInvariance (d : ℕ) : Prop :=
  ∀ (T : ℝ≥0) (G : ContinuousPath (Vec d) → ℝ≥0∞),
    Measurable[ContinuousPath.canonicalFiltration (alpha := Vec d) T] G →
    (∫⁻ ω, G (reversePath T ω) ∂(pathMeasure d)) = ∫⁻ ω, G ω ∂(pathMeasure d)

theorem lintegral_reversePath (hinv : PathReversalInvariance d) (T : ℝ≥0)
    {F : ContinuousPath (Vec d) → ℝ≥0∞}
    (hF : Measurable[ContinuousPath.canonicalFiltration (alpha := Vec d) T] F) :
    (∫⁻ ω, F (reversePath T ω) ∂(pathMeasure d)) = ∫⁻ ω, F ω ∂(pathMeasure d) :=
  hinv T F hF

/-! ## Measurability of the continuous supremum -/

theorem dyadicGridSup_le_iSup {T : ℝ≥0} {F : ℝ≥0 → ℝ≥0∞} (n : ℕ) :
    dyadicGridSup F T n ≤ ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), F t := by
  refine Finset.sup'_le _ _ fun k _ => ?_
  exact le_iSup_of_le (dyadicTime T n k) (le_iSup_of_le (dyadicTime_le T n k) le_rfl)

theorem iSup_eq_iSup_dyadicGridSup {T : ℝ≥0} {F : ℝ≥0 → ℝ≥0∞} (hF : Continuous F) :
    (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), F t) = ⨆ n : ℕ, dyadicGridSup F T n :=
  le_antisymm (iSup_le_dyadicGridSup hF) (iSup_le fun n => dyadicGridSup_le_iSup n)

/-- Measurability of the continuous supremum, **for any σ-algebra** for which the integrand is
measurable at every time `≤ T`.  Instantiated at the ambient Borel structure and at the canonical
filtration at `T`; the latter is what the reversal invariance consumes. -/
theorem measurable_iSup_le_of_continuous' {m : MeasurableSpace (ContinuousPath (Vec d))}
    {F : ContinuousPath (Vec d) → ℝ≥0 → ℝ≥0∞} (T : ℝ≥0)
    (hcont : ∀ ω, Continuous (F ω))
    (hmeas : ∀ t : ℝ≥0, t ≤ T → Measurable[m] fun ω => F ω t) :
    Measurable[m] fun ω : ContinuousPath (Vec d) => ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), F ω t := by
  have h : (fun ω : ContinuousPath (Vec d) => ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), F ω t)
      = fun ω => ⨆ n : ℕ, dyadicGridSup (F ω) T n :=
    funext fun ω => iSup_eq_iSup_dyadicGridSup (hcont ω)
  rw [h]
  exact Measurable.iSup fun n =>
    Finset.measurable_range_sup'' (f := fun k ω => F ω (dyadicTime T n k))
      (fun k _ => hmeas (dyadicTime T n k) (dyadicTime_le T n k))

theorem measurable_iSup_le_of_continuous {F : ContinuousPath (Vec d) → ℝ≥0 → ℝ≥0∞}
    (hcont : ∀ ω, Continuous (F ω))
    (hmeas : ∀ t : ℝ≥0, Measurable fun ω => F ω t) (T : ℝ≥0) :
    Measurable fun ω : ContinuousPath (Vec d) => ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), F ω t :=
  measurable_iSup_le_of_continuous' T hcont fun t _ => hmeas t

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
