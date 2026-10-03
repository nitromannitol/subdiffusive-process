module

public import SubdiffusiveProcess.Probability.SeparatedLayerFactorization
public import SubdiffusiveProcess.Probability.FineDensityMultipointMoment
public import SubdiffusiveProcess.Main.ScaledLayerLaw
public import SubdiffusiveProcess.Main.LayerScaling
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.ChaosRootFieldLaw
public import SubdiffusiveProcess.Main.BilateralField

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section
namespace SubdiffusiveProcess

theorem chaosSampleLaw_prod_exp_sub_tauSq_eq_one_of_fineLayer_separated
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (p j : ℕ)
    (x : Fin p → SpatialCoordinates d)
    (hsep : Pairwise (fun i k : Fin p =>
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) <
        Homogenization.euclideanNorm (x i - x k))) :
    (∫ omega : BilateralField d,
        ∏ i : Fin p, Real.exp
          ((omega (-(Int.ofNat j))) (x i) -
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
        ∂(chaosSampleLaw M).toMeasure) = 1 := by
  classical
  have hsep' : Pairwise (fun i k : Fin p =>
      Real.sqrt (d : ℝ) <
        Homogenization.euclideanNorm ((3 : ℝ) ^ j • x i - (3 : ℝ) ^ j • x k)) := by
    intro i k hik
    have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    have hpow : (3 : ℝ) ^ j * (3 : ℝ) ^ (-(j : ℤ)) = 1 := by
      rw [← zpow_natCast (3 : ℝ) j,
        ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    have hmul : (3 : ℝ) ^ j *
        (Real.sqrt (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))) <
        (3 : ℝ) ^ j * Homogenization.euclideanNorm (x i - x k) :=
      mul_lt_mul_of_pos_left (hsep hik) h3
    have hmul' : Real.sqrt (d : ℝ) <
        (3 : ℝ) ^ j * Homogenization.euclideanNorm (x i - x k) := by
      calc
        Real.sqrt (d : ℝ) = (3 : ℝ) ^ j *
            ((3 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (d : ℝ)) := by
              rw [← mul_assoc, hpow, one_mul]
        _ < (3 : ℝ) ^ j * Homogenization.euclideanNorm (x i - x k) := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using! hmul
    calc
      Real.sqrt (d : ℝ) <
          (3 : ℝ) ^ j * Homogenization.euclideanNorm (x i - x k) := hmul'
      _ = Homogenization.euclideanNorm ((3 : ℝ) ^ j • (x i - x k)) := by
        rw [Homogenization.euclideanNorm_smul, abs_of_pos h3]
      _ = Homogenization.euclideanNorm
          ((3 : ℝ) ^ j • x i - (3 : ℝ) ^ j • x k) := by
        rw [smul_sub]
  have hg := integral_prod_exp_sub_tauSq_eq_one_of_separated M p
    (fun i : Fin p => (3 : ℝ) ^ j • x i) hsep'
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let Hs : C(SpatialCoordinates d, ℝ) → ℝ := fun f =>
    ∏ i : Fin p, Real.exp (f ((3 : ℝ) ^ j • x i) -
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  have hHsmeas : Measurable Hs := by
    dsimp [Hs]
    apply Finset.measurable_prod
    intro i hi
    exact ((continuous_eval_const ((3 : ℝ) ^ j • x i)).measurable.sub
      measurable_const).exp
  have hg' : (∫ f : C(SpatialCoordinates d, ℝ), Hs f
      ∂(chaosRootFieldLaw M).toMeasure) = 1 := by
    change (∫ f : C(SpatialCoordinates d, ℝ), Hs f ∂
      Measure.map forget (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) = 1
    rw [integral_map forget.continuous.measurable.aemeasurable]
    · simpa only [Hs, forget, ContinuousMap.coe_mk] using! hg
    · exact hHsmeas.aestronglyMeasurable
  let H : C(SpatialCoordinates d, ℝ) → ℝ := fun f =>
    ∏ i : Fin p, Real.exp (f (x i) -
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  have hHmeas : Measurable H := by
    dsimp [H]
    apply Finset.measurable_prod
    intro i hi
    exact ((continuous_eval_const (x i)).measurable.sub measurable_const).exp
  have hscale_eq (f : C(SpatialCoordinates d, ℝ)) :
      H (layerScaling d (-(Int.ofNat j)) f) = Hs f := by
    dsimp [H, Hs, layerScaling]
    congr 1
    funext i
    simp only [neg_neg, zpow_natCast]
    rfl
  have hscale :
      (∫ f : C(SpatialCoordinates d, ℝ), H f ∂
        (scaledLayerLaw d (chaosRootFieldLaw M) (-(Int.ofNat j))).toMeasure) = 1 := by
    change (∫ f : C(SpatialCoordinates d, ℝ), H f ∂
      Measure.map (layerScaling d (-(Int.ofNat j)))
        (chaosRootFieldLaw M).toMeasure) = 1
    rw [integral_map (layerScaling d (-(Int.ofNat j))).continuous.measurable.aemeasurable]
    · calc
        (∫ f : C(SpatialCoordinates d, ℝ),
            H (layerScaling d (-(Int.ofNat j)) f) ∂
              (chaosRootFieldLaw M).toMeasure) =
            ∫ f : C(SpatialCoordinates d, ℝ), Hs f ∂
              (chaosRootFieldLaw M).toMeasure := by
                apply integral_congr_ae
                filter_upwards with f
                exact hscale_eq f
        _ = 1 := hg'
    · exact hHmeas.aestronglyMeasurable
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun j' =>
    (scaledLayerLaw d (chaosRootFieldLaw M) j').toMeasure
  have heval := measurePreserving_eval_infinitePi laws (-(Int.ofNat j))
  calc
    (∫ omega : BilateralField d,
        ∏ i : Fin p, Real.exp
          ((omega (-(Int.ofNat j))) (x i) -
            SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
        ∂(chaosSampleLaw M).toMeasure) =
        ∫ omega : BilateralField d,
          H (omega (-(Int.ofNat j))) ∂
            Measure.infinitePi laws := by
              rfl
    _ = ∫ f : C(SpatialCoordinates d, ℝ), H f ∂
        Measure.map (fun omega : BilateralField d =>
          omega (-(Int.ofNat j))) (Measure.infinitePi laws) := by
            rw [integral_map heval.measurable.aemeasurable]
            exact hHmeas.aestronglyMeasurable
    _ = ∫ f : C(SpatialCoordinates d, ℝ), H f ∂laws (-(Int.ofNat j)) := by
          rw [heval.map_eq]
    _ = 1 := hscale

end SubdiffusiveProcess
