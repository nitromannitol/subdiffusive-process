module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.EnergyStability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.EstimateLimits
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.S6Assembly
public import Homogenization.Sobolev.Foundations.PoincareZeroTrace
public import Homogenization.Sobolev.MatchedPair.ScaledPoincare

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### The zero-trace Poincaré inequality in set-integral form -/

/-- **Zero-trace Poincaré, integral form.**  On a bounded open convex domain
there is a constant controlling the `L²` size of every `H¹₀` function by the
Dirichlet energy of its gradient. -/
theorem exists_poincare_integral_const [NeZero d] {W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) (hWm : MeasurableSet W) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ w : H10Function W,
      ∫ x in W, w.toH1Function.toFun x ^ 2 ∂volume ≤
        Cp * ∫ x in W, vecNormSq (w.toH1Function.grad x) ∂volume := by
  classical
  obtain ⟨C, hC0, hC⟩ :=
    H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hW
  refine ⟨C ^ 2 * (d : ℝ), by positivity, fun w ↦ ?_⟩
  set u : H1Function W := w.toH1Function with hu
  set N : ℝ := (eLpNorm u.toFun 2 (volumeMeasureOn W)).toReal with hN
  set G : Fin d → ℝ := fun i ↦
    (eLpNorm (fun x ↦ u.grad x i) 2 (volumeMeasureOn W)).toReal with hG
  have hmain : N ≤ C * ∑ i, G i := by
    have h1 := hC w
    rw [norm_toScalarL2_eq u, gradientCoordL2NormSum_eq_sum_eLpNorm u] at h1
    exact h1
  have hNnn : 0 ≤ N := ENNReal.toReal_nonneg
  have hGnn : ∀ i, 0 ≤ G i := fun _ ↦ ENNReal.toReal_nonneg
  have hSnn : 0 ≤ ∑ i, G i := Finset.sum_nonneg fun i _ ↦ hGnn i
  have hsq : N ^ 2 ≤ C ^ 2 * (∑ i, G i) ^ 2 := by nlinarith [hmain, hNnn, hC0]
  have hcs : (∑ i, G i) ^ 2 ≤ (d : ℝ) * ∑ i, G i ^ 2 := by
    simpa using
      sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := G)
  have hstep : N ^ 2 ≤ C ^ 2 * ((d : ℝ) * ∑ i, G i ^ 2) :=
    hsq.trans (mul_le_mul_of_nonneg_left hcs (by positivity))
  have hNsq : N ^ 2 = ∫ x in W, u.toFun x ^ 2 ∂volume :=
    toReal_eLpNorm_two_sq_eq_integral_sq u.memL2
  have hGsq : ∀ i, G i ^ 2 = ∫ x in W, u.grad x i ^ 2 ∂volume := fun i ↦
    toReal_eLpNorm_two_sq_eq_integral_sq (u.gradMemL2 i)
  have hgradInt : ∀ i : Fin d, IntegrableOn (fun x ↦ u.grad x i ^ 2) W :=
    fun i ↦ (u.gradMemL2 i).integrable_sq
  have hsum : ∑ i, ∫ x in W, u.grad x i ^ 2 ∂volume
      = ∫ x in W, vecNormSq (u.grad x) ∂volume := by
    rw [← integral_finsetSum _ (fun i _ ↦ hgradInt i)]
    refine setIntegral_congr_fun hWm ?_
    intro x _
    simp only [vecNormSq, vecDot]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hNsq] at hstep
  refine hstep.trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦ hGsq i), ← hsum]
  ring

/-! ### Transfer of vanishing integrals -/

/-- A vanishing nonnegative set integral on a window vanishes on every
measurable subwindow. -/
theorem tendsto_setIntegral_zero_of_subset {V W : Set (Vec d)}
    {f : ℕ → Vec d → ℝ} (hVW : V ⊆ W) (hVm : MeasurableSet V)
    (hnn : ∀ j x, 0 ≤ f j x)
    (hint : ∀ j, IntegrableOn (f j) W)
    (h : Tendsto (fun j ↦ ∫ x in W, f j x ∂volume) atTop (nhds 0)) :
    Tendsto (fun j ↦ ∫ x in V, f j x ∂volume) atTop (nhds 0) := by
  refine squeeze_zero (fun j ↦ ?_) (fun j ↦ ?_) h
  · exact setIntegral_nonneg hVm fun x _ ↦ hnn j x
  · exact setIntegral_mono_set (hint j)
      (Filter.Eventually.of_forall fun x ↦ hnn j x)
      (LE.le.eventuallySubset hVW)

/-- A vanishing set integral of squares gives a vanishing normalized `L²`
seminorm. -/
theorem tendsto_normalizedL2On_of_tendsto_integral_sq {W : Set (Vec d)}
    {f : ℕ → Vec d → ℝ}
    (h : Tendsto (fun j ↦ ∫ x in W, f j x ^ 2 ∂volume) atTop (nhds 0)) :
    Tendsto (fun j ↦ normalizedL2On W (f j)) atTop (nhds 0) := by
  have hscaled : Tendsto
      (fun j ↦ (volume W).toReal⁻¹ * ∫ x in W, f j x ^ 2 ∂volume)
      atTop (nhds 0) := by
    simpa using h.const_mul ((volume W).toReal⁻¹)
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hscaled
  rw [Real.sqrt_zero] at hsqrt
  exact hsqrt

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut
