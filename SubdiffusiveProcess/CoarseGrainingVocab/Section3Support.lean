module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section2Support
public import Homogenization.Besov.Negative.ExactFiniteBridge
public import Homogenization.Geometry.CubeMetric

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization.Book
open scoped BigOperators ENNReal Matrix.Norms.Elementwise MatrixOrder

noncomputable section

/-- Pointwise two-term `ℓ^p` aggregate. -/
noncomputable def paperTwoTermLpObservable {Ω : Type*}
    (p : ℝ) (X Y : Ω → ℝ) (ω : Ω) : ℝ :=
  Real.rpow (Real.rpow (max (X ω) 0) p + Real.rpow (max (Y ω) 0) p) p⁻¹

/-- Extend the cutoff by the convention `a_{-1}=1`. -/
noncomputable def aCutoffAtInt {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℤ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) : ℝ :=
  if n < 0 then 1 else _root_.SubdiffusiveProcess.Model.aCutoff M n.toNat ω x

theorem aCutoffAtInt_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℤ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    0 < aCutoffAtInt M n ω x := by
  by_cases hn : n < 0
  · simp [aCutoffAtInt, hn]
  · simp only [aCutoffAtInt, hn, ↓reduceIte]
    exact _root_.SubdiffusiveProcess.Model.aCutoff_pos M n.toNat ω x

theorem continuous_aCutoffAtInt {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℤ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Continuous (aCutoffAtInt M n ω) := by
  by_cases hn : n < 0
  · have heq : aCutoffAtInt M n ω = fun _ : Vec d => (1 : ℝ) := by
      funext x
      simp [aCutoffAtInt, hn]
    rw [heq]
    exact continuous_const
  · have heq : aCutoffAtInt M n ω = _root_.SubdiffusiveProcess.Model.aCutoff M n.toNat ω := by
      funext x
      simp [aCutoffAtInt, hn]
    rw [heq]
    exact _root_.SubdiffusiveProcess.Model.continuous_aCutoff M n.toNat ω

/-- Direct diagonal exact-circ negative Besov norm. -/
noncomputable def paperNegativeBesovCircDiagonal {d : ℕ}
    (Q : TriadicCube d) (s p : ℝ) (f : Vec d → ℝ)
    (hf : Homogenization.ExactCircIntegrable Q f) : ℝ≥0∞ :=
  (ENNReal.ofReal s) ^ p⁻¹ *
    (∑' j : ℕ, (Homogenization.exactCircDepthTerm Q s p f hf j) ^ p) ^ p⁻¹

/-- First scalar ratio field. -/
noncomputable def cutoffRatioMinusOne {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) : ℝ :=
  _root_.SubdiffusiveProcess.Model.aCutoff M m ω x / aCutoffAtInt M n ω x - 1

/-- Exponentially normalized inverse ratio field. -/
noncomputable def normalizedInverseCutoffRatioMinusOne {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) : ℝ :=
  Real.exp (-2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℤ) - n : ℤ)) *
      (aCutoffAtInt M n ω x / _root_.SubdiffusiveProcess.Model.aCutoff M m ω x) - 1

/-- Continuous fields are integrable on every exact-circ descendant block. -/
theorem exactCircIntegrable_of_continuous {d : ℕ} (Q : TriadicCube d)
    {f : Vec d → ℝ} (hf : Continuous f) : Homogenization.ExactCircIntegrable Q f where
  block := by
    intro j R hR
    have hi : IntegrableOn f
        (Metric.closedBall (Homogenization.cubeCenter R) (Homogenization.cubeRadius R)) :=
      hf.continuousOn.integrableOn_compact
        (ProperSpace.isCompact_closedBall
          (Homogenization.cubeCenter R) (Homogenization.cubeRadius R))
    have hc : Integrable f (Homogenization.cubeMeasure R) := by
      exact hi.mono_set (Homogenization.cubeSet_subset_closedBall R)
    exact hc.smul_measure ENNReal.ofReal_ne_top

/-- Exact-circ certificate for the forward cutoff ratio. -/
theorem cutoffRatioExactCircIntegrable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Homogenization.ExactCircIntegrable (Homogenization.originCube d (m : ℤ))
      (cutoffRatioMinusOne M m n ω) := by
  apply exactCircIntegrable_of_continuous
  exact ((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M m ω).div
    (continuous_aCutoffAtInt M n ω)
    (fun x => (aCutoffAtInt_pos M n ω x).ne')).sub continuous_const

/-- Exact-circ certificate for the inverse cutoff ratio. -/
theorem inverseCutoffRatioExactCircIntegrable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Homogenization.ExactCircIntegrable (Homogenization.originCube d (m : ℤ))
      (normalizedInverseCutoffRatioMinusOne M m n ω) := by
  apply exactCircIntegrable_of_continuous
  exact (continuous_const.mul ((continuous_aCutoffAtInt M n ω).div
    (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M m ω)
    (fun x => (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m ω x).ne'))).sub continuous_const

/-- First random negative-Besov norm in the Section 3 estimate. -/
noncomputable def cutoffRatioNegativeBesov {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ) (s p : ℝ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  paperNegativeBesovCircDiagonal (Homogenization.originCube d (m : ℤ)) s p
    (cutoffRatioMinusOne M m n ω) (cutoffRatioExactCircIntegrable M m n ω)

/-- Inverse-ratio random negative-Besov norm. -/
noncomputable def inverseCutoffRatioNegativeBesov {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (n : ℤ) (s p : ℝ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  paperNegativeBesovCircDiagonal (Homogenization.originCube d (m : ℤ)) s p
    (normalizedInverseCutoffRatioMinusOne M m n ω)
    (inverseCutoffRatioExactCircIntegrable M m n ω)

/-- Random finite-volume dual coarse matrix. -/
noncomputable def randomAStarMatrix {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Mat d :=
  aStarMatrix U (aCutoffCoeffOnData M L ω U).toCoeffOn

/-- Symmetric inverse-square-root convention. -/
noncomputable def matrixInvSqrt {d : ℕ} (A : Mat d) : Mat d :=
  (CFC.sqrt A)⁻¹

/-- Operator-norm normalized matrix deviation. -/
noncomputable def normalizedMatrixDeviation {d : ℕ} (A B : Mat d) (c : ℝ) : ℝ :=
  Ch02.matrixOperatorNorm (c⁻¹ • (matrixInvSqrt A * B * matrixInvSqrt A) - (1 : Mat d))

/-- Forward cutoff sensitivity at `L`. -/
noncomputable def cutoffSensitivityForwardAt {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (U : Ch02.Domain d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  let c := _root_.SubdiffusiveProcess.Model.aCutoff M n ω 0 /
    _root_.SubdiffusiveProcess.Model.aCutoff M L ω 0
  normalizedMatrixDeviation (randomAStarMatrix M L U ω) (randomAStarMatrix M n U ω) c +
    normalizedMatrixDeviation (randomAMatrix M L U ω) (randomAMatrix M n U ω) c

/-- Reverse cutoff sensitivity at `L`. -/
noncomputable def cutoffSensitivityReverseAt {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ) (U : Ch02.Domain d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  let c := _root_.SubdiffusiveProcess.Model.aCutoff M L ω 0 /
    _root_.SubdiffusiveProcess.Model.aCutoff M n ω 0
  normalizedMatrixDeviation (randomAStarMatrix M n U ω) (randomAStarMatrix M L U ω) c +
    normalizedMatrixDeviation (randomAMatrix M n U ω) (randomAMatrix M L U ω) c

/-- Forward pointwise supremum, in the faithful `ENNReal` setting. -/
noncomputable def cutoffSensitivityForwardSup {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (U : Ch02.Domain d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ⨆ L : {L : ℕ // n ≤ L}, ENNReal.ofReal (cutoffSensitivityForwardAt M L.1 n U ω)

/-- Reverse pointwise supremum, in the faithful `ENNReal` setting. -/
noncomputable def cutoffSensitivityReverseSup {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (U : Ch02.Domain d)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ⨆ L : {L : ℕ // n ≤ L}, ENNReal.ofReal (cutoffSensitivityReverseAt M L.1 n U ω)

/-- Pointwise spatial supremum of a positive cutoff ratio. -/
noncomputable def cutoffRatioSup {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (numerator denominator : ℕ)
    (U : Ch02.Domain d) (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  sSup {r : ℝ | ∃ x : Vec d, x ∈ (U : Set (Vec d)) ∧
    r = _root_.SubdiffusiveProcess.Model.aCutoff M numerator ω x /
      _root_.SubdiffusiveProcess.Model.aCutoff M denominator ω x}

/-- Annealed inverse dual coarse matrix. -/
noncomputable def abarStarInv {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (U : Ch02.Domain d) : Mat d :=
  ∫ ω, (randomAStarMatrix M m U ω)⁻¹ ∂M.P.toMeasure

end

end SubdiffusiveProcess.CoarseGrainingVocab
