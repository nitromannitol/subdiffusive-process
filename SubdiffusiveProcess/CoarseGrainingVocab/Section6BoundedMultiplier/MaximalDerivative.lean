module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.LocalRatioTail

@[expose] public section

/-!
# Maximal derivative of the fixed cutoff

The logarithm of the finite cutoff is a finite shell sum.  Its Fréchet
derivative is therefore the finite sum of the stored shell derivatives.  The
same translated `g2` envelopes used by the coefficient-ratio event control
this derivative on every unit covering cube, with the same unshifted Gaussian
union-bound probability.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open Homogenization IndependentSums
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := PotentialSample d
private abbrev Field (d : ℕ) := PotentialField d

/-- The actual Fréchet derivative of `log a_L`, written as a finite shell
sum. -/
def fixedCutoffLogFDeriv {d : ℕ} (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (x : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ k ∈ Finset.range (L + 1), _root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega k) x

/-- The finite sum above is indeed the derivative of the logarithm of the
cutoff. -/
theorem hasFDerivAt_log_aCutoff {d : ℕ} (M : GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    HasFDerivAt (fun y ↦ Real.log (aCutoff M L omega y))
      (fixedCutoffLogFDeriv L omega x) x := by
  have hfun : (fun y ↦ Real.log (aCutoff M L omega y)) =
      fun y ↦ ∑ k ∈ Finset.range (L + 1),
        (omega k y - tauSq M.P) := by
    funext y
    simp only [aCutoff, Real.log_exp]
  rw [hfun]
  unfold fixedCutoffLogFDeriv
  exact HasFDerivAt.fun_sum fun k _hk ↦
    (omega k).hasFDerivAt x |>.sub_const (tauSq M.P)

/-- The translated own-scale `g2` observable controls one shell derivative
throughout a translated unit cube. -/
theorem norm_shellDeriv_le_translatedSmallShellEnvelope_unit {d : ℕ}
    (j : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ translatedCube d 0 z) :
    ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega j) x‖ ≤
      translatedSmallShellEnvelope j (0 : ℤ) z omega := by
  let z' : Vec d := (((3 : ℝ) ^ j)⁻¹) • z
  let u : Vec d := (((3 : ℝ) ^ j)⁻¹) • (x - z)
  let g : _root_.SubdiffusiveProcess.Model.PotentialField d := _root_.SubdiffusiveProcess.Model.PotentialField.translate z'
    (unscalePotential j (omega j))
  have hx' : x - z ∈ openCubeSet (originCube d 0) := by
    rcases hx with ⟨w, hw, rfl⟩
    simpa [cube] using hw
  have hu : u ∈ openCubeSet (originCube d 0) := by
    rw [mem_openCubeSet_originCube_iff] at hx' ⊢
    intro i
    have hj : (1 : ℝ) ≤ (3 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hp : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    have hi := hx' i
    simp only [u, Pi.smul_apply, smul_eq_mul, zpow_zero, mul_one]
    constructor
    · rw [← div_eq_inv_mul, lt_div_iff₀ hp]
      calc
        -(1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ -(1 / 2 : ℝ) := by
          nlinarith
        _ < (x - z) i := by simpa only [zpow_zero, mul_one] using hi.1
    · rw [← div_eq_inv_mul, div_lt_iff₀ hp]
      calc
        (x - z) i < (1 / 2 : ℝ) := by
          simpa only [zpow_zero, mul_one] using hi.2
        _ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
          nlinarith
  have hderiv : _root_.SubdiffusiveProcess.Model.PotentialField.deriv g u =
      (3 : ℝ) ^ j • _root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega j) x := by
    change (3 : ℝ) ^ j • _root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega j)
        ((3 : ℝ) ^ j • (u + z')) =
      (3 : ℝ) ^ j • _root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega j) x
    congr 1
    congr 1
    dsimp [u, z']
    rw [← smul_add, sub_add_cancel, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ j ≠ 0), one_smul]
  have hG := _root_.SubdiffusiveProcess.Model.PotentialField.norm_deriv_le_g2Observable g hu
  rw [hderiv, norm_smul,
    Real.norm_of_nonneg (by positivity : 0 ≤ (3 : ℝ) ^ j)] at hG
  have hjpos : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  rw [translatedSmallShellEnvelope, show (0 : ℤ) - (j : ℤ) = -(j : ℤ) by omega,
    zpow_neg, zpow_natCast]
  rw [le_inv_mul_iff₀ hjpos]
  simpa only [g, z', translatedShellG2] using hG

/-- A cutoff-uniform envelope for the norm of `grad log a_L` on one
translated unit cube. -/
def fixedCutoffLogDerivativeEnvelope {d : ℕ} (L : ℕ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  ∑ k ∈ Finset.range (L + 1),
    translatedSmallShellEnvelope k (0 : ℤ) z omega

theorem fixedCutoffOscillationEnvelope_eq_two_mul_logDerivativeEnvelope
    {d : ℕ} (L : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    fixedCutoffOscillationEnvelope L z omega =
      2 * fixedCutoffLogDerivativeEnvelope L z omega := by
  rfl

/-- Pointwise maximal derivative bound on one translated unit cube. -/
theorem norm_fixedCutoffLogFDeriv_le_envelope {d : ℕ}
    (L : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ translatedCube d 0 z) :
    ‖fixedCutoffLogFDeriv L omega x‖ ≤
      fixedCutoffLogDerivativeEnvelope L z omega := by
  unfold fixedCutoffLogFDeriv fixedCutoffLogDerivativeEnvelope
  calc
    ‖∑ k ∈ Finset.range (L + 1), _root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega k) x‖ ≤
        ∑ k ∈ Finset.range (L + 1),
          ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega k) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (L + 1),
        translatedSmallShellEnvelope k (0 : ℤ) z omega := by
      exact Finset.sum_le_sum fun k _hk ↦
        norm_shellDeriv_le_translatedSmallShellEnvelope_unit k z omega hx

/-- On the common finite-cover envelope event, every covering unit cube has
the advertised maximal derivative bound. -/
theorem norm_fixedCutoffLogFDeriv_le_on_coveringGood {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d} (hgood : omega ∈ coveringFixedCutoffEnvelopeGood M L m z)
    (p : Fin d → ℤ) (hp : p ∈ shellCoverShifts d m) {x : Vec d}
    (hx : x ∈ translatedCube d 0 (z + physicalShellCoverCenter 0 p)) :
    ‖fixedCutoffLogFDeriv L omega x‖ ≤
      boundedMultiplierCoverOscillationThreshold M m / 2 := by
  have hderiv := norm_fixedCutoffLogFDeriv_le_envelope L
    (z + physicalShellCoverCenter 0 p) omega hx
  have henv := mem_coveringFixedCutoffEnvelopeGood_iff.1 hgood p hp
  rw [fixedCutoffOscillationEnvelope_eq_two_mul_logDerivativeEnvelope] at henv
  exact hderiv.trans (by linarith)

/-- The same statement read literally as the norm of the Fréchet derivative
of `log a_L`. -/
theorem norm_fderiv_log_aCutoff_le_on_coveringGood {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d} (hgood : omega ∈ coveringFixedCutoffEnvelopeGood M L m z)
    (p : Fin d → ℤ) (hp : p ∈ shellCoverShifts d m) {x : Vec d}
    (hx : x ∈ translatedCube d 0 (z + physicalShellCoverCenter 0 p)) :
    ‖fderiv ℝ (fun y ↦ Real.log (aCutoff M L omega y)) x‖ ≤
      boundedMultiplierCoverOscillationThreshold M m / 2 := by
  rw [(hasFDerivAt_log_aCutoff M L omega x).fderiv]
  exact norm_fixedCutoffLogFDeriv_le_on_coveringGood M L m z hgood p hp hx

/-- Event packaging for the maximal derivative input, with the printed
`exp(-1/(delta^2 |log delta|^2))` exceptional probability.  The parameter in
the proof is the unshifted Gaussian `q`. -/
theorem exists_maximalDerivativeGoodEvent {d : ℕ}
    (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d) :
    ∃ good : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d), MeasurableSet good ∧
      M.P.toMeasure goodᶜ ≤ ENNReal.ofReal
        (Real.exp (-1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
      ∀ omega ∈ good, ∀ p ∈ shellCoverShifts d m, ∀ x,
        x ∈ translatedCube d 0 (z + physicalShellCoverCenter 0 p) →
        ‖fderiv ℝ (fun y ↦ Real.log (aCutoff M L omega y)) x‖ ≤
          boundedMultiplierCoverOscillationThreshold M m / 2 := by
  refine ⟨coveringFixedCutoffEnvelopeGood M L m z,
    measurableSet_coveringFixedCutoffEnvelopeGood M L m z,
    measure_compl_coveringFixedCutoffEnvelopeGood_le M L m z, ?_⟩
  intro omega hgood p hp x hx
  exact norm_fderiv_log_aCutoff_le_on_coveringGood M L m z hgood p hp hx

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
