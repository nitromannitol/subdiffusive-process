import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FixedCutoffConditionalReadout

/-!
# Moments from a fixed-cutoff response envelope

The algebraic response theorem controls the raw `ENNReal` errors.  This file
converts that pointwise control into the raw moment premise consumed by the
Dirichlet energy theorem, retaining the extended-real finiteness information.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

theorem paperENNRealLpNorm_le_eLpNorm_of_ae_le_ofReal
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞} {W : Omega → ℝ}
    (hW : ∀ᵐ omega ∂mu, 0 ≤ W omega)
    (hXW : ∀ᵐ omega ∂mu, X omega ≤ ENNReal.ofReal (W omega)) :
    paperENNRealLpNorm mu p X ≤ eLpNorm W (ENNReal.ofReal p) mu := by
  rw [paperENNRealLpNorm_eq_eLpNorm mu hp X]
  calc
    eLpNorm X (ENNReal.ofReal p) mu ≤
        eLpNorm (ENNReal.ofReal ∘ W) (ENNReal.ofReal p) mu := by
      apply eLpNorm_mono_ae'
      filter_upwards [hXW] with omega homega
      simpa only [Function.comp_apply, enorm_eq_self] using homega
    _ = eLpNorm W (ENNReal.ofReal p) mu :=
      eLpNorm_ofReal W hW

/-- A decaying response envelope is no larger in `L^p` than its common
prefactor. -/
theorem paperENNRealLpNorm_le_responsePrefactor
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p theta : ℝ} (hp : 0 < p) (htheta : 0 ≤ theta) (N : ℕ)
    {X : Omega → ℝ≥0∞} {W : Omega → ℝ}
    (hW : ∀ omega, 0 ≤ W omega)
    (hXW : ∀ᵐ omega ∂mu,
      X omega ≤ ENNReal.ofReal
        (W omega * fixedCutoffDirichletResponseWeight theta N)) :
    paperENNRealLpNorm mu p X ≤ eLpNorm W (ENNReal.ofReal p) mu := by
  apply paperENNRealLpNorm_le_eLpNorm_of_ae_le_ofReal hp
    (Filter.Eventually.of_forall hW)
  filter_upwards [hXW] with omega homega
  refine homega.trans (ENNReal.ofReal_le_ofReal ?_)
  have hR := fixedCutoffDirichletResponseWeight_le_one N htheta
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hR (hW omega)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
