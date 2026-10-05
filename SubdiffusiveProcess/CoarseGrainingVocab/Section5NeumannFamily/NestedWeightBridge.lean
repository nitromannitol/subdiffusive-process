module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.TwoRadiusHessianFamily

@[expose] public section

/-!
# Nested-weight form of the two-radius harmonic cell bounds

`exists_twoRadiusNeumannHessianFamily` delivers the two harmonic cell bounds
in the raw geometric shape

```
  cubeScaleFactor R * d^2 * ratio^(1/16d) * (C * L⁻¹ * parentCoordinateSum).
```

The thermodynamic readout layer
(`OneStepNestedSourceParentReadout.lean`) consumes them in the normalized
shape `A * oneStepNestedHarmonicWeight d hd depth N * parentCoordinateSum`,
where `N` is the number of triadic scales between the cell and its parent.
The two shapes are *equal*, not merely comparable: only the physical side
quotient collapses to `3⁻ᴺ`, and the normalized restriction ratio is carried
along unchanged.  This module records that identity and restates the family
accordingly.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Exact conversion of the geometric harmonic prefactor into the nested
harmonic weight.  Only the scale gap `N = Q.scale - R.scale` is used; the two
cubes need not be concentric. -/
theorem twoRadiusHarmonicCellFactor_mul_eq_nestedWeight
    (d : ℕ) (hd : 3 ≤ d) (depth N : ℕ) (Q R : TriadicCube d)
    (hscale : Q.scale = R.scale + (N : ℤ)) (C S : ℝ) :
    twoRadiusHarmonicCellFactor d hd depth Q R *
        (C * (cubeScaleFactor Q)⁻¹ * S) =
      ((d : ℝ) ^ 2 * C) *
        oneStepNestedHarmonicWeight d hd depth N * S := by
  have hQ : cubeScaleFactor Q =
      cubeScaleFactor (originCube d (R.scale + (N : ℤ))) := by
    simp only [cubeScaleFactor, originCube, hscale]
  have hratio := triadicAxisNormalizedMeasureRatio_nested_eq
    (d := d) (source := R.scale) N depth R rfl
  unfold twoRadiusHarmonicCellFactor oneStepNestedHarmonicWeight
  rw [hQ, hratio]
  rw [oneStepNested_harmonic_prefactor_eq (source := R.scale) N R rfl
    (((ENNReal.ofReal
      (((3 : ℝ) ^ ((N : ℤ) - ((depth + 1 : ℕ) : ℤ))) ^ d)) ^
        (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal) C S]
  ring

/-! ## Readout identities for the induced scalar family -/

theorem toCellFamily_neumann_eq
    {ι Omega : Type*} [MeasurableSpace Omega]
    {s : Finset ι} {cell : ι → TriadicCube d}
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell)
    (i : ι) (omega : Omega) :
    F.toCellFamily.neumann i omega =
      oneStepCellB (cell i)
        (oneStepTwoRadiusNeumannCombinedHessian F i omega) := rfl

theorem toCellFamily_dirichlet_eq
    {ι Omega : Type*} [MeasurableSpace Omega]
    {s : Finset ι} {cell : ι → TriadicCube d}
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell)
    (i : ι) (omega : Omega) :
    F.toCellFamily.dirichlet i omega =
      oneStepCellB (cell i) (F.dirichletHessian i omega) := rfl

theorem toCellFamily_localHarmonic_eq
    {ι Omega : Type*} [MeasurableSpace Omega]
    {s : Finset ι} {cell : ι → TriadicCube d}
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell)
    (i : ι) (omega : Omega) :
    F.toCellFamily.localHarmonic i omega =
      oneStepCellB (cell i) (F.localHarmonicHessian i omega) := rfl

theorem toCellFamily_outerHarmonic_eq
    {ι Omega : Type*} [MeasurableSpace Omega]
    {s : Finset ι} {cell : ι → TriadicCube d}
    (F : OneStepTwoRadiusNeumannHessianFamily d ι Omega s cell)
    (i : ι) (omega : Omega) :
    F.toCellFamily.outerHarmonic i omega =
      oneStepCellB (cell i) (F.outerHarmonicHessian i omega) := rfl

/-! ## The family with both harmonic bounds in nested-weight form -/

/-- The two-radius Neumann Hessian family, with the two harmonic cell bounds
delivered in exactly the shape consumed by
`lintegral_average_nestedHarmonic_four_le`, hence by
`twoRadiusNeumannHessian_nested_thermodynamic_readout_le`.

The nonnegativity of the two scalar members is recorded as well, since the
sweep lemma asks for it. -/
theorem exists_twoRadiusNeumannHessianFamily_nestedWeight
    [NeZero d] (hd : 3 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d) (K : ℤ)
    (hh : 0 < h) (N : ℕ)
    {ι : Type*} (s : Finset ι) (parent cell : ι → TriadicCube d)
    (hparentK : ∀ i, openCubeSet (parent i) ⊆ openCubeSet (originCube d K))
    (hcellInner : ∀ i, openCubeSet (cell i) ⊆
      twoRadiusConcentric (parent i) (twoRadiusHarmonicDepth d hd))
    (hgap : ∀ i, (parent i).scale = (cell i).scale + (N : ℤ)) :
    ∃ F : OneStepTwoRadiusNeumannHessianFamily d ι (NFSample d) s cell,
      (∀ i omega, (F.neumann i omega).grad =
        (oneStepOriginNeumannSolution M n h p K omega hh).toH1Function.grad) ∧
      (∀ i omega, (F.dirichlet i omega).grad =
        (twoRadiusLocalDirichletPiece M n h p (parent i) omega hh).grad) ∧
      (∀ i omega,
        F.toCellFamily.localHarmonic i omega ≤
          ((d : ℝ) ^ 2 * twoRadiusHarmonicConst d hd) *
            oneStepNestedHarmonicWeight d hd
              (twoRadiusHarmonicDepth d hd) N *
            twoRadiusParentCoordinateSum (parent i)
              (twoRadiusLocalHarmonicPiece M n h p (parent i) omega hh)) ∧
      (∀ i omega,
        F.toCellFamily.outerHarmonic i omega ≤
          ((d : ℝ) ^ 2 * twoRadiusHarmonicConst d hd) *
            oneStepNestedHarmonicWeight d hd
              (twoRadiusHarmonicDepth d hd) N *
            twoRadiusParentCoordinateSum (parent i)
              (twoRadiusOuterHarmonicPiece M n h p K (parent i)
                (hparentK i) omega hh)) := by
  obtain ⟨F, hneu, hdir, _hloc, _hout, hlocB, houtB⟩ :=
    exists_twoRadiusNeumannHessianFamily hd M n h p K hh s parent cell
      hparentK hcellInner
  refine ⟨F, hneu, hdir, ?_, ?_⟩
  · intro i omega
    rw [toCellFamily_localHarmonic_eq]
    refine (hlocB i omega).trans_eq ?_
    exact twoRadiusHarmonicCellFactor_mul_eq_nestedWeight d hd
      (twoRadiusHarmonicDepth d hd) N (parent i) (cell i) (hgap i)
      (twoRadiusHarmonicConst d hd)
      (twoRadiusParentCoordinateSum (parent i)
        (twoRadiusLocalHarmonicPiece M n h p (parent i) omega hh))
  · intro i omega
    rw [toCellFamily_outerHarmonic_eq]
    refine (houtB i omega).trans_eq ?_
    exact twoRadiusHarmonicCellFactor_mul_eq_nestedWeight d hd
      (twoRadiusHarmonicDepth d hd) N (parent i) (cell i) (hgap i)
      (twoRadiusHarmonicConst d hd)
      (twoRadiusParentCoordinateSum (parent i)
        (twoRadiusOuterHarmonicPiece M n h p K (parent i)
          (hparentK i) omega hh))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
