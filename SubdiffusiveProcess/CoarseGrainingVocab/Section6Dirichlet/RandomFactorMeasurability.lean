module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ResponseCoefficientMeasurability

@[expose] public section

/-!
# Coefficient measurability of the Dirichlet random factor

This is the literal algebraic random factor introduced after
`e.Dirichlet.prebalance`.  Its measurability is separated from its moment and
parameter-balance estimates: once the universal energy factor is known to be
coefficient-measurable, the two response-error inputs are discharged by
`ResponseCoefficientMeasurability.lean` in one application.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

variable {d : ℕ} {Ω : Type*}

/-- The common random factor from the proof of
the cutoff Dirichlet homogenization proposition, before its moment estimate. -/
noncomputable def dirichletRandomFactor
    (C delta vartheta s1 s2 : ℝ) (k : ℕ)
    (E1 E2 Y : Ω → ℝ) (omega : Ω) : ℝ :=
  1 + C * Real.rpow delta (-vartheta) *
      (Real.rpow 3 (s1 * k) * E1 omega * Y omega +
        Real.rpow 3 (-s2 * k) *
          (1 + Real.rpow 3 (s1 * k) * (E2 omega) ^ 2)) +
    C * Real.rpow delta (-1) * E1 omega * Y omega

/-- Measurability of the manuscript random factor is closed under the three
coefficient-measurable random inputs. -/
theorem coefficientMeasurable_dirichletRandomFactor
    (A : Ω → Vec d → ℝ) (C delta vartheta s1 s2 : ℝ) (k : ℕ)
    (E1 E2 Y : Ω → ℝ)
    (hE1 : CoefficientMeasurable A E1)
    (hE2 : CoefficientMeasurable A E2)
    (hY : CoefficientMeasurable A Y) :
    CoefficientMeasurable A
      (dirichletRandomFactor C delta vartheta s1 s2 k E1 E2 Y) := by
  let : MeasurableSpace Ω := coefficientSigma A
  change Measurable E1 at hE1
  change Measurable E2 at hE2
  change Measurable Y at hY
  change Measurable (dirichletRandomFactor C delta vartheta s1 s2 k E1 E2 Y)
  unfold dirichletRandomFactor
  have hFirst : Measurable fun omega =>
      Real.rpow 3 (s1 * k) * E1 omega * Y omega :=
    (measurable_const.mul hE1).mul hY
  have hSecond : Measurable fun omega =>
      Real.rpow 3 (-s2 * k) *
        (1 + Real.rpow 3 (s1 * k) * (E2 omega) ^ 2) :=
    measurable_const.mul
      (measurable_const.add (measurable_const.mul (hE2.pow_const 2)))
  have hBalanced : Measurable fun omega =>
      C * Real.rpow delta (-vartheta) *
        (Real.rpow 3 (s1 * k) * E1 omega * Y omega +
          Real.rpow 3 (-s2 * k) *
            (1 + Real.rpow 3 (s1 * k) * (E2 omega) ^ 2)) :=
    (measurable_const.mul measurable_const).mul (hFirst.add hSecond)
  have hZeroForce : Measurable fun omega =>
      C * Real.rpow delta (-1) * E1 omega * Y omega :=
    ((measurable_const.mul measurable_const).mul hE1).mul hY
  exact (measurable_const.add hBalanced).add hZeroForce

/-- Specialized one-term discharge: the two full response errors are already
measurable in the literal rescaled-coefficient sigma-field, so only the
universal energy factor remains as input. -/
theorem coefficientMeasurable_dirichletRandomFactor_of_energyFactor
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
    (C delta vartheta s1 s2 : ℝ) (k : ℕ) (Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ)
    (hY : CoefficientMeasurable
      (fun omega => rescaledCutoffCoefficient M L N omega) Y) :
    CoefficientMeasurable
      (fun omega => rescaledCutoffCoefficient M L N omega)
      (dirichletRandomFactor C delta vartheta s1 s2 k
        (dirichletFullResponseOne M L N s1)
        (dirichletFullResponseTwo M L N s1)
        Y) := by
  exact coefficientMeasurable_dirichletRandomFactor
    (fun omega => rescaledCutoffCoefficient M L N omega)
    C delta vartheta s1 s2 k _ _ Y
    (coefficientMeasurable_dirichletFullResponseOne M L N s1)
    (coefficientMeasurable_dirichletFullResponseTwo M L N s1) hY

/-- Coefficient-only envelope for the two square-root ellipticity factors in
`e.Dirichlet.energy.factor`.  The later energy module proves the analytic
domination; this file records the universal random carrier. -/
noncomputable def dirichletEllipticityEnvelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ) (s : ℝ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  1 + 2 * dirichletFullResponseTwo M L N s omega

/-- The coefficient-only ellipticity envelope is at least one. -/
theorem one_le_dirichletEllipticityEnvelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ) (s : ℝ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    1 ≤ dirichletEllipticityEnvelope M L N s omega := by
  unfold dirichletEllipticityEnvelope
  exact le_add_of_nonneg_right
    (mul_nonneg (by norm_num) (dirichletFullResponseTwo_nonneg M L N s omega))

/-- The explicit ellipticity envelope is measurable for the literal rescaled
coefficient sigma-field. -/
theorem coefficientMeasurable_dirichletEllipticityEnvelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ) (s : ℝ) :
    CoefficientMeasurable
      (fun omega => rescaledCutoffCoefficient M L N omega)
      (dirichletEllipticityEnvelope M L N s) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    coefficientSigma (fun omega => rescaledCutoffCoefficient M L N omega)
  change Measurable (dirichletEllipticityEnvelope M L N s)
  unfold dirichletEllipticityEnvelope
  exact measurable_const.add
    (measurable_const.mul
      (coefficientMeasurable_dirichletFullResponseTwo M L N s))

/-- The concrete common random factor of the Dirichlet proof.  It depends only
on the coefficient, not on the forcing or boundary datum. -/
noncomputable def dirichletUniversalRandomFactor
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
    (C delta vartheta s1 s2 : ℝ) (k : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  dirichletRandomFactor C delta vartheta s1 s2 k
    (dirichletFullResponseOne M L N s1)
    (dirichletFullResponseTwo M L N s1)
    (dirichletEllipticityEnvelope M L N s1) omega

/-- The concrete universal random factor is measurable in the literal
coefficient sigma-field. -/
theorem coefficientMeasurable_dirichletUniversalRandomFactor
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
    (C delta vartheta s1 s2 : ℝ) (k : ℕ) :
    CoefficientMeasurable
      (fun omega => rescaledCutoffCoefficient M L N omega)
      (dirichletUniversalRandomFactor M L N C delta vartheta s1 s2 k) := by
  unfold dirichletUniversalRandomFactor
  exact coefficientMeasurable_dirichletRandomFactor_of_energyFactor
    M L N C delta vartheta s1 s2 k
    (dirichletEllipticityEnvelope M L N s1)
    (coefficientMeasurable_dirichletEllipticityEnvelope M L N s1)

/-- Under the manuscript sign assumptions, the concrete universal factor is
at least one. -/
theorem one_le_dirichletUniversalRandomFactor
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
    {C delta : ℝ} (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (vartheta s1 s2 : ℝ) (k : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    1 ≤ dirichletUniversalRandomFactor M L N C delta vartheta s1 s2 k omega := by
  have hE1 : 0 ≤ dirichletFullResponseOne M L N s1 omega :=
    dirichletFullResponseOne_nonneg M L N s1 omega
  have hE2 : 0 ≤ dirichletFullResponseTwo M L N s1 omega :=
    dirichletFullResponseTwo_nonneg M L N s1 omega
  have hY : 0 ≤ dirichletEllipticityEnvelope M L N s1 omega :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans
      (one_le_dirichletEllipticityEnvelope M L N s1 omega)
  have hFirst : 0 ≤ Real.rpow 3 (s1 * k) *
      dirichletFullResponseOne M L N s1 omega *
        dirichletEllipticityEnvelope M L N s1 omega :=
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hE1) hY
  have hSecond : 0 ≤ Real.rpow 3 (-s2 * k) *
      (1 + Real.rpow 3 (s1 * k) *
        (dirichletFullResponseTwo M L N s1 omega) ^ 2) := by
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (add_nonneg (by norm_num)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)))
  have hBalanced : 0 ≤ C * Real.rpow delta (-vartheta) *
      (Real.rpow 3 (s1 * k) * dirichletFullResponseOne M L N s1 omega *
          dirichletEllipticityEnvelope M L N s1 omega +
        Real.rpow 3 (-s2 * k) *
          (1 + Real.rpow 3 (s1 * k) *
            (dirichletFullResponseTwo M L N s1 omega) ^ 2)) :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hdelta _))
      (add_nonneg hFirst hSecond)
  have hZeroForce : 0 ≤ C * Real.rpow delta (-1) *
      dirichletFullResponseOne M L N s1 omega *
        dirichletEllipticityEnvelope M L N s1 omega :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg hdelta _)) hE1) hY
  unfold dirichletUniversalRandomFactor dirichletRandomFactor
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab
