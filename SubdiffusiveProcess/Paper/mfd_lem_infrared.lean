import SubdiffusiveProcess.Infrared.CompactGradientConvergence
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Main.NativeInfraredLimit

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper




theorem mfd_lem_infrared
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
  ∃ C : Compacts (SpatialCoordinates d) → ℝ,
    (∀ K, 0 ≤ C K) ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (μ : Measure (NativeBilateralPotentialSample d)),
      μ = Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) →
      ∃ H : NativeBilateralPotentialSample d →
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        Measurable H ∧
        (∀ K : Compacts (SpatialCoordinates d),
          Measurable (fun omega => compactPotentialC1Norm K (H omega)) ∧
          Measurable (fun omega => compactGradientLipschitzObservable K (H omega))) ∧
        (∀ᵐ omega ∂μ,
          (∀ x : SpatialCoordinates d,
            H omega x = ∑' n : ℕ,
              (positiveScaledNativeLayer omega n x -
                positiveScaledNativeLayer omega n 0)) ∧
          (∀ K : Compacts (SpatialCoordinates d),
            Tendsto
              (fun L => compactPotentialC1Norm K
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
                  (positiveAnchoredInfraredTruncation omega L)
                  (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega))))
              atTop (nhds 0)) ∧
          (∀ K : Compacts (SpatialCoordinates d),
            Tendsto
              (fun L => compactGradientLipschitzObservable K
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
                  (positiveAnchoredInfraredTruncation omega L)
                  (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (H omega))))
              atTop (nhds 0)) ∧
          (∀ K : Compacts (SpatialCoordinates d),
            LipschitzOnWith
              (Real.toNNReal (compactGradientLipschitzObservable K (H omega)))
              (fun x => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (H omega) x)
              (K : Set (SpatialCoordinates d)))) ∧
        (∀ K : Compacts (SpatialCoordinates d), ∀ p : ℝ≥0∞,
          2 ≤ p → p ≠ ∞ → ∀ n : ℕ,
            eLpNorm (fun omega => compactPotentialC1Norm K
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.anchor
                (positiveScaledNativeLayer omega n))) p μ ≤
              ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal *
                (3 : ℝ) ^ (-(n + 1 : ℤ)))) ∧
        (∀ K : Compacts (SpatialCoordinates d), ∀ p : ℝ≥0∞,
          2 ≤ p → p ≠ ∞ →
          eLpNorm (fun omega => compactPotentialC1Norm K (H omega)) p μ ≤
            ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal) ∧
          eLpNorm (fun omega => compactGradientLipschitzObservable K (H omega)) p μ ≤
            ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal) ∧
          ∀ L : ℕ,
            eLpNorm (fun omega => compactPotentialC1Norm K
                (positiveAnchoredInfraredTruncation omega L)) p μ ≤
              ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal) ∧
            eLpNorm (fun omega => compactGradientLipschitzObservable K
                (positiveAnchoredInfraredTruncation omega L)) p μ ≤
              ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal)) ∧
        (∀ K : Compacts (SpatialCoordinates d), ∀ lambda : ℝ, 0 ≤ lambda →
          Integrable (fun omega => Real.exp
            (lambda * compactPotentialC1Norm K (H omega))) μ ∧
          (∫ omega, Real.exp (lambda * compactPotentialC1Norm K (H omega)) ∂μ) ≤
            2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2) ∧
          Integrable (fun omega => Real.exp
            (lambda * compactGradientLipschitzObservable K (H omega))) μ ∧
          (∫ omega, Real.exp
              (lambda * compactGradientLipschitzObservable K (H omega)) ∂μ) ≤
            2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2) ∧
          ∀ L : ℕ,
            Integrable (fun omega => Real.exp (lambda * compactPotentialC1Norm K
              (positiveAnchoredInfraredTruncation omega L))) μ ∧
            (∫ omega, Real.exp (lambda * compactPotentialC1Norm K
                (positiveAnchoredInfraredTruncation omega L)) ∂μ) ≤
              2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2) ∧
            Integrable (fun omega => Real.exp
              (lambda * compactGradientLipschitzObservable K
                (positiveAnchoredInfraredTruncation omega L))) μ ∧
            (∫ omega, Real.exp (lambda * compactGradientLipschitzObservable K
                (positiveAnchoredInfraredTruncation omega L)) ∂μ) ≤
              2 * Real.exp (C K * lambda ^ 2 * M.delta ^ 2)) := by
  obtain ⟨C, hC, hmain⟩ := lem_infrared hd
  refine ⟨C, hC, ?_⟩
  rintro M mu rfl
  obtain ⟨H, hHm, hobs, hae, hlayers, hmom, hexp⟩ := hmain M _ rfl
  refine ⟨H, hHm, hobs, ?_, hlayers, hmom, hexp⟩
  filter_upwards [hae, ae_positiveScaledNativeLayer_shellC11Summable M] with omega hom hs
  refine ⟨hom.1, hom.2.1, ?_, hom.2.2⟩
  have hEq : H omega = SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.anchoredLimitField hs := by
    apply SubdiffusiveProcess.Frozen.Assumptions.PotentialField.ext
    intro x
    rw [hom.1 x]
    rfl
  have hLim : SubdiffusiveProcess.Frozen.Assumptions.IsAnchoredC11Limit
      (positiveScaledNativeLayer omega) (H omega) := by
    rw [hEq]
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.isAnchoredC11Limit_anchoredLimitField hs
  exact fun K => SubdiffusiveProcess.Infrared.tendsto_native_compactGradientLipschitzObservable omega _ hLim K

end Paper
