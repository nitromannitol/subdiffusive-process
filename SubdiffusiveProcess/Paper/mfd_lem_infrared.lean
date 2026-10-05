module

public import SubdiffusiveProcess.Infrared.CompactGradientConvergence
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Main.NativeInfraredLimit

@[expose] public section

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper




theorem mfd_lem_infrared
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
  ∃ C : Compacts (SpatialCoordinates d) → ℝ,
    (∀ K, 0 ≤ C K) ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (μ : Measure (NativeBilateralPotentialSample d)),
      μ = Measure.infinitePi (fun _ : ℤ =>
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) →
      ∃ H : NativeBilateralPotentialSample d →
          _root_.SubdiffusiveProcess.Model.PotentialField d,
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
                (_root_.SubdiffusiveProcess.Model.PotentialField.add
                  (positiveAnchoredInfraredTruncation omega L)
                  (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H omega))))
              atTop (nhds 0)) ∧
          (∀ K : Compacts (SpatialCoordinates d),
            Tendsto
              (fun L => compactGradientLipschitzObservable K
                (_root_.SubdiffusiveProcess.Model.PotentialField.add
                  (positiveAnchoredInfraredTruncation omega L)
                  (_root_.SubdiffusiveProcess.Model.PotentialField.scale (-1) (H omega))))
              atTop (nhds 0)) ∧
          (∀ K : Compacts (SpatialCoordinates d),
            LipschitzOnWith
              (Real.toNNReal (compactGradientLipschitzObservable K (H omega)))
              (fun x => _root_.SubdiffusiveProcess.Model.PotentialField.deriv (H omega) x)
              (K : Set (SpatialCoordinates d)))) ∧
        (∀ K : Compacts (SpatialCoordinates d), ∀ p : ℝ≥0∞,
          2 ≤ p → p ≠ ∞ → ∀ n : ℕ,
            eLpNorm (fun omega => compactPotentialC1Norm K
              (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
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
    apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
    intro x
    rw [hom.1 x]
    rfl
  have hLim : _root_.SubdiffusiveProcess.Model.IsAnchoredC11Limit
      (positiveScaledNativeLayer omega) (H omega) := by
    rw [hEq]
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.isAnchoredC11Limit_anchoredLimitField hs
  exact fun K => SubdiffusiveProcess.Infrared.tendsto_native_compactGradientLipschitzObservable omega _ hLim K

end SubdiffusiveProcess.Paper
