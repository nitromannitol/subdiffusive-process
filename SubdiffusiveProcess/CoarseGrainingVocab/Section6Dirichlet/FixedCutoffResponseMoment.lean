module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FixedCutoffConditionalReadout

@[expose] public section

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
  calc
    paperENNRealLpNorm mu p X ≤
        SubdiffusiveProcess.RawLp.eLpNorm (ENNReal.ofReal ∘ W) (ENNReal.ofReal p) mu := by
      rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (ENNReal.ofReal_pos.mpr hp).ne'
        ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
      unfold paperENNRealLpNorm
      simp only [one_div, Function.comp_apply, enorm_eq_self]
      apply ENNReal.rpow_le_rpow _ (inv_nonneg.mpr hp.le)
      apply lintegral_mono_ae
      filter_upwards [hXW] with omega homega
      exact ENNReal.rpow_le_rpow homega hp.le
    _ ≤ eLpNorm (ENNReal.ofReal ∘ W) (ENNReal.ofReal p) mu :=
      SubdiffusiveProcess.RawLp.eLpNorm_le_guarded _ _ _
    _ = eLpNorm W (ENNReal.ofReal p) mu := eLpNorm_ofReal W hW

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
