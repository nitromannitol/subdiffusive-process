module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.MomentFactorization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.TranslatedDefect
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitResponse

@[expose] public section

/-!
# Positive-scale conditional response moment

This module packages the probability step immediately after
the localization of `J` from cutoff `L` to scale `m`.  It factors the suffix error from the prefix
response at the original induction exponent, and exposes the exact remaining
input as a suffix-measurable majorant of the squared localization error.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section


-- Argument: mirrors the prefix/suffix response-leg composition in the
-- Superdiffusion file above, using GMC's established relative-measurability API.
theorem paperScalarProbeMaxOn_cutoff_lpnorm_le_of_suffix_majorant {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m0 k L m : ℕ}
    {xi delta1 : ℝ} (hS : inductionHypothesis M m0 xi delta1)
    (hk : k ≤ m0) (Q : TriadicCube d) (hQ : Q.scale = (k : ℤ))
    (X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞)
    (hX : @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Ioi k))
      inferInstance X)
    (hdom : ∀ᵐ omega ∂M.P.toMeasure,
      ENNReal.ofReal
          (responseLocalizationError M L k (Ch02.cubeDomain Q)
            (tailCoefficientCubeAverage M L m omega) omega ^ 2) ≤ X omega) :
    paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
        paperScalarProbeMaxOn (Ch02.cubeDomain Q)
          (aCutoffCoeffOnData M L omega (Ch02.cubeDomain Q)).toCoeffOn
          (tailCoefficientCubeAverage M L m omega)) ≤
      2 * ENNReal.ofReal delta1 +
        3 * paperENNRealLpNorm M.P.toMeasure xi X *
          (ENNReal.ofReal delta1 + 1) := by
  let D := normalizedDefect M k (Ch02.cubeDomain Q)
  let F := fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
    paperScalarProbeMaxOn (Ch02.cubeDomain Q)
      (aCutoffCoeffOnData M L omega (Ch02.cubeDomain Q)).toCoeffOn
      (tailCoefficientCubeAverage M L m omega)
  have hD : @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Iic k))
      inferInstance D :=
    measurable_normalizedDefect_potentialShellIndexSigma_Iic M k
      (Ch02.cubeDomain Q)
  have hpoint : ∀ᵐ omega ∂M.P.toMeasure,
      F omega ≤ 2 * D omega + 3 * X omega * (D omega + 1) := by
    filter_upwards [hdom] with omega herror
    have hloc := paperScalarProbeMaxOn_cutoff_le_localized M L k
      (Ch02.cubeDomain Q) (tailCoefficientCubeAverage M L m omega)
      (tailCoefficientCubeAverage_pos M L m omega) omega
    calc
      F omega ≤ 2 * D omega +
          3 * ENNReal.ofReal
              (responseLocalizationError M L k (Ch02.cubeDomain Q)
                (tailCoefficientCubeAverage M L m omega) omega ^ 2) *
            (D omega + 1) := hloc
      _ ≤ 2 * D omega + 3 * X omega * (D omega + 1) := by gcongr
  have hraw := paperENNRealLpNorm_localized_prefix_suffix M k hS.1 hD hX hpoint
  have hDbound : paperENNRealLpNorm M.P.toMeasure xi D ≤ ENNReal.ofReal delta1 :=
    inductionHypothesis_normalizedDefect_cube M hS hk Q hQ
  exact hraw.trans (by gcongr)

end

end SubdiffusiveProcess.CoarseGrainingVocab
