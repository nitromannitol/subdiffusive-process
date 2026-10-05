module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.EnergyFactor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FullResponseMoments

@[expose] public section

/-!
# Almost-sure reconstruction of the raw Dirichlet response errors

The prebalance theorem consumes the extended-real response errors, while the
random-factor and moment rows use their real `toReal` readouts.  A finite
positive moment makes both raw errors finite almost surely and hence restores
them exactly from those real readouts.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

private theorem coefficientSigma_rescaledCutoffCoefficient_le_ambient
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ) :
    coefficientSigma (fun omega ↦ rescaledCutoffCoefficient M L N omega) ≤
      (inferInstance : MeasurableSpace (Sample d)) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.aux_dedup_d153_coefficientSigma_rescaledCutoffCoefficient_le_ambient (d := d) (M := M) (L := L) (N := N)

/-- Ambient measurability of the raw first response error. -/
theorem measurable_dirichletFullResponseOneENNReal
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ) (s : ℝ) :
    Measurable (fun omega ↦
      paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
        s .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L)) := by
  exact
    (measurable_paperHomogenizationError_infinity_finite_rescaledCoefficientSigma
      M L N (originCube d (N : ℤ)) (N : ℤ) s 1).mono
        (coefficientSigma_rescaledCutoffCoefficient_le_ambient M L N) le_rfl

private theorem ae_ne_top_of_paperENNRealLpNorm_le_ofReal
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p B : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞} (hX : Measurable X)
    (hbound : paperENNRealLpNorm mu p X ≤ ENNReal.ofReal B) :
    ∀ᵐ omega ∂mu, X omega ≠ ⊤ := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.aux_dedup_d128_ae_ne_top_of_paperENNRealLpNorm_le_ofReal (Omega := Omega) (mu := mu) (p := p) (B := B) (hp := hp) (X := X) (hX := hX) (hbound := hbound)

/-- Two finite response moments simultaneously identify the raw errors with
the `ofReal` images of the real readouts used by the random factor. -/
theorem ae_rawDirichletResponses_eq_ofReal_readouts_of_moments
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
    {s p B1 B2 : ℝ} (hp : 0 < p)
    (hOne : paperENNRealLpNorm M.P.toMeasure p
      (fun omega ↦ paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
        s .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L)) ≤
      ENNReal.ofReal B1)
    (hTwo : paperENNRealLpNorm M.P.toMeasure p
      (fun omega ↦ paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
        (s / 2) .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)) ≤
      ENNReal.ofReal B2) :
    ∀ᵐ omega ∂M.P.toMeasure,
      paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
          s .infinity (.finite 1) (aCutoffFamily M L omega) (ahom M L) =
        ENNReal.ofReal (dirichletFullResponseOne M L N s omega) ∧
      paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
          (s / 2) .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L) =
        ENNReal.ofReal (dirichletFullResponseTwo M L N s omega) := by
  have hOneFinite := ae_ne_top_of_paperENNRealLpNorm_le_ofReal
    M.P.toMeasure hp (measurable_dirichletFullResponseOneENNReal M L N s) hOne
  have hTwoFinite := ae_ne_top_of_paperENNRealLpNorm_le_ofReal
    M.P.toMeasure hp (measurable_dirichletFullResponseTwoENNReal M L N s) hTwo
  filter_upwards [hOneFinite, hTwoFinite] with omega hOneTop hTwoTop
  constructor
  · exact (ENNReal.ofReal_toReal hOneTop).symm
  · exact (ENNReal.ofReal_toReal hTwoTop).symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
