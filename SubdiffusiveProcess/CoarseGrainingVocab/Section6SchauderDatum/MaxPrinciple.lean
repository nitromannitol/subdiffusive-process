module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.WindowDomain
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Carrier
public import Homogenization.Sobolev.Foundations.PoincareZeroTrace

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryLaneMaxPrinciple.lean
-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/AffineSplitHarmonic.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryLaneMaxPrinciple.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/AffineSplitHarmonic.lean

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

open MeasureTheory
open Homogenization (Vec H1Function H10Function vecDot vecNormSq volumeMeasureOn
  IsOpenBoundedConvexDomain)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-! ### Integrability of the tested integrand -/

/-- The tested integrand of the weak Laplacian is integrable: it is a finite sum
of products of `L²` gradient coordinates. -/
theorem integrableOn_vecDot_grad {V : Set (Vec d)} (u φ : H1Function V) :
    IntegrableOn (fun y => vecDot (u.grad y) (φ.grad y)) V volume := by
  have hsum : (fun y => vecDot (u.grad y) (φ.grad y)) =
      fun y => ∑ i : Fin d, (u.grad y i * φ.grad y i) := by
    funext y
    rw [vecDot]
  rw [IntegrableOn, hsum]
  refine integrable_finset_sum _ fun i _ => ?_
  exact (u.gradMemL2 i).integrable_mul (φ.gradMemL2 i)

/-! ### The weak boundary bound -/

/-- **`u ≤ M` on `∂V`, weakly.**  The positive part `(u - M)₊` lies in `H¹₀(V)`,
carrying CoarseGraining's Stampacchia gradient `1_{u>M} ∇u`.

The `H¹` membership and the gradient formula are unconditional
(`Homogenization.exists_h1_max_sub_const`); the content of this predicate is the
zero trace.  Given the first component the second is forced almost everywhere by
uniqueness of weak gradients on an open window; it is bundled so that no consumer
has to rerun that argument, not to strengthen the hypothesis. -/
def HasBoundaryUpperBoundOn (V : Set (Vec d)) (u : H1Function V) (M : ℝ) : Prop :=
  ∃ ψ : H10Function V,
    ψ.toH1Function.toFun = (fun y => max (u.toFun y - M) 0) ∧
      (∀ᵐ y ∂(volumeMeasureOn V),
        ψ.toH1Function.grad y = {p | M < u.toFun p}.indicator u.grad y)

/-! ### The maximum principle -/

/-- **The weak maximum principle for the Laplacian.**

A weakly harmonic `H¹` function on an open bounded convex window which is `≤ M`
on the boundary (in the zero-trace sense of `HasBoundaryUpperBoundOn`) is `≤ M`
almost everywhere in the window. -/
theorem ae_le_of_isUnitWeaklyHarmonicOn [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {u : H1Function V} {M : ℝ}
    (hu : IsUnitWeaklyHarmonicOn V u) (hM : HasBoundaryUpperBoundOn V u M) :
    ∀ᵐ y ∂(volumeMeasureOn V), u.toFun y ≤ M := by
  obtain ⟨ψ, hψval, hψgrad⟩ := hM
  have hae : ∀ᵐ y ∂(volumeMeasureOn V),
      vecDot (u.grad y) (ψ.toH1Function.grad y) =
        vecNormSq (ψ.toH1Function.grad y) := by
    filter_upwards [hψgrad] with y hy
    by_cases hmem : y ∈ {p | M < u.toFun p}
    · rw [hy, Set.indicator_of_mem hmem, vecNormSq]
    · rw [hy, Set.indicator_of_notMem hmem]
      simp [vecDot, vecNormSq]
  have hzero : ∫ y in V, vecNormSq (ψ.toH1Function.grad y) ∂volume = 0 := by
    rw [← integral_congr_ae hae]
    exact hu ψ
  have hint : Integrable (fun y => vecNormSq (ψ.toH1Function.grad y))
      (volumeMeasureOn V) := by
    have h := integrableOn_vecDot_grad ψ.toH1Function ψ.toH1Function
    simpa [IntegrableOn, volumeMeasureOn, vecNormSq] using h
  have hgz : (fun y => vecNormSq (ψ.toH1Function.grad y)) =ᵐ[volumeMeasureOn V] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun y => Homogenization.vecNormSq_nonneg _) hint).1 hzero
  have hgradzero : ψ.toH1Function.grad =ᵐ[volumeMeasureOn V] 0 := by
    filter_upwards [hgz] with y hy
    refine Homogenization.vecNormSq_eq_zero ?_
    simpa using hy
  have hVL2 : ψ.toH1Function.gradToVectorL2 = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [ψ.toH1Function.coeFn_gradToVectorL2, hgradzero] with y h1 h2
    rw [h1, h2]
  have hS :=
    Homogenization.H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
      (Homogenization.H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hV)
      ψ hVL2
  have hval : ψ.toH1Function.toFun =ᵐ[volumeMeasureOn V] 0 := by
    have hc := ψ.toH1Function.coeFn_toScalarL2
    rw [hS] at hc
    filter_upwards [hc, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volumeMeasureOn V)]
      with y h1 h2
    rw [← h1, h2]
  filter_upwards [hval] with y hy
  have hmax : max (u.toFun y - M) 0 = 0 := by
    rw [← congrFun hψval y]
    simpa using hy
  have hle : u.toFun y - M ≤ 0 := max_eq_right_iff.1 hmax
  linarith only [hle]

/-! ### The two-sided form -/

theorem isUnitWeaklyHarmonicOn_neg {V : Set (Vec d)} {u : H1Function V}
    (hu : IsUnitWeaklyHarmonicOn V u) : IsUnitWeaklyHarmonicOn V (-u) := by
  intro φ
  have hrw : ∀ y, vecDot ((-u).grad y) (φ.toH1Function.grad y) =
      -vecDot (u.grad y) (φ.toH1Function.grad y) := by
    intro y
    simp only [Homogenization.H1Function.neg_grad, vecDot, Pi.neg_apply, neg_mul,
      Finset.sum_neg_distrib]
  calc
    ∫ y in V, vecDot ((-u).grad y) (φ.toH1Function.grad y) ∂volume
        = ∫ y in V, -vecDot (u.grad y) (φ.toH1Function.grad y) ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => hrw y)
    _ = -∫ y in V, vecDot (u.grad y) (φ.toH1Function.grad y) ∂volume := integral_neg _
    _ = 0 := by rw [hu φ, neg_zero]

/-- **The two-sided weak maximum principle**: `‖u‖_{L^∞(V)} ≤ M` for a weakly
harmonic `u` whose boundary datum is two-sidedly bounded by `M`. -/
theorem ae_abs_le_of_isUnitWeaklyHarmonicOn [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) {u : H1Function V} {M : ℝ}
    (hu : IsUnitWeaklyHarmonicOn V u) (hupper : HasBoundaryUpperBoundOn V u M)
    (hlower : HasBoundaryUpperBoundOn V (-u) M) :
    ∀ᵐ y ∂(volumeMeasureOn V), |u.toFun y| ≤ M := by
  have h1 := ae_le_of_isUnitWeaklyHarmonicOn hV hu hupper
  have h2 := ae_le_of_isUnitWeaklyHarmonicOn hV (isUnitWeaklyHarmonicOn_neg hu) hlower
  filter_upwards [h1, h2] with y hy1 hy2
  have hy2' : -u.toFun y ≤ M := by
    simpa using hy2
  exact abs_le.2 ⟨by linarith only [hy2'], hy1⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
