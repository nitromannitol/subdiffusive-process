import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCorrectorEnergyBridge

/-! # A law-preserving shift of the triadic potential tower

Removing the first layer and undoing one spatial scaling preserves the full
sequence law. This lets the shell API, indexed from layer one, cover layer zero.
-/

open MeasureTheory ProbabilityTheory Homogenization
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.LaplacianCorrector

abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d
abbrev Field (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialField d
abbrev Model (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.GMCModel d

/-- Remove the first layer and undo one triadic spatial scaling. -/
def shiftSample {d : ℕ} (omega : Sample d) : Sample d :=
  fun k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale 3 (omega (k + 1))

theorem measurable_shiftSample {d : ℕ} : Measurable (shiftSample (d := d)) := by
  apply measurable_pi_lambda
  intro k
  exact (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.continuous_spatialScale 3).measurable.comp
    (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate (k + 1))

theorem spatialScale_three_triadicScale_succ {d : ℕ} (k : ℕ) (g : Field d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale 3
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale (k + 1) g) =
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k g := by
  apply SubdiffusiveProcess.Frozen.Assumptions.PotentialField.ext
  intro x
  simp only [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply,
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale_apply, smul_smul]
  congr 1
  congr 1
  rw [pow_succ, mul_inv_rev]
  ring

theorem map_shiftSample_coordinate {d : ℕ} (M : Model d) (k : ℕ) :
    Measure.map (fun omega : Sample d => shiftSample omega k) M.P.toMeasure =
      Measure.map (fun omega : Sample d => omega k) M.P.toMeasure := by
  have hs := (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.continuous_spatialScale
    (d := d) 3).measurable
  have hc := SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate (d := d) (k + 1)
  change Measure.map
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale 3 ∘ fun omega : Sample d =>
      omega (k + 1)) M.P.toMeasure = _
  rw [← Measure.map_map hs hc]
  change Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale 3)
    (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P (k + 1)).toMeasure =
    (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure
  rw [M.shellPrefix.marginal_scaling (k + 1), M.shellPrefix.marginal_scaling k,
    ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    Measure.map_map hs (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale (k + 1))]
  congr 1
  funext g
  exact spatialScale_three_triadicScale_succ k g

theorem measurePreserving_shiftSample {d : ℕ} (M : Model d) :
    MeasurePreserving (shiftSample (d := d)) M.P.toMeasure M.P.toMeasure := by
  refine ⟨measurable_shiftSample, ?_⟩
  have hprod := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k)).mp
    M.shellPrefix.independent
  have hshift := (M.shellPrefix.independent.precomp
    (show Function.Injective (fun k : ℕ => k + 1) by
      intro i j hij
      exact Nat.add_right_cancel hij)).comp
      (fun _ => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale 3)
      (fun _ => (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.continuous_spatialScale 3).measurable)
  have hshiftProd := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => (measurable_pi_apply k).comp measurable_shiftSample)).mp hshift
  calc
    Measure.map shiftSample M.P.toMeasure =
        Measure.infinitePi (fun k => Measure.map
          (fun omega : Sample d => shiftSample omega k) M.P.toMeasure) := hshiftProd
    _ = Measure.infinitePi (fun k => Measure.map
          (fun omega : Sample d => omega k) M.P.toMeasure) := by
      congr 1
      funext k
      exact map_shiftSample_coordinate M k
    _ = Measure.map (fun omega : Sample d => omega) M.P.toMeasure := hprod.symm
    _ = M.P.toMeasure := Measure.map_id

/-- Literal multiplier of any finite window, including a window starting at zero. -/
def windowMultiplier {d : ℕ} (M : Model d) (a h : ℕ)
    (omega : Sample d) (x : Vec d) : ℝ :=
  Real.exp (∑ k ∈ Finset.Ico a (a + h),
    (omega k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) - 1

theorem windowMultiplier_shiftSample {d : ℕ} (M : Model d) (a h : ℕ)
    (hh : 0 < h) (omega : Sample d) (x : Vec d) :
    windowMultiplier M a h (shiftSample omega) x =
      SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.oneStepMultiplierAt M a h ((3 : ℝ) • x) omega := by
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.oneStepMultiplierAt,
    SubdiffusiveProcess.CoarseGrainingVocab.cutoffRatioMinusOne_eq_exp_shell M (a + h) (a : ℤ)
      omega ((3 : ℝ) • x) (by omega) (by omega)]
  unfold windowMultiplier SubdiffusiveProcess.CoarseGrainingVocab.cutoffShellSum
  have hsum :
      (∑ k ∈ Finset.Ico a (a + h),
        (shiftSample omega k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) =
      (∑ k ∈ Finset.Ico (a + 1) (a + h + 1), omega k ((3 : ℝ) • x)) -
        (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
    simp only [shiftSample, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico]
    simp only [Nat.add_sub_cancel_left, nsmul_eq_mul]
    congr 1
    exact (Finset.sum_Ico_add' (fun k => omega k ((3 : ℝ) • x)) a (a + h) 1)
  rw [hsum]
  have hind : SubdiffusiveProcess.CoarseGrainingVocab.cutoffShellIndices (a + h) (a : ℤ) =
      Finset.Ico (a + 1) (a + h + 1) := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.cutoffShellIndices
    have hacast : (a : ℤ) + 1 = ((a + 1 : ℕ) : ℤ) := by omega
    rw [hacast, Int.toNat_natCast]
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hind]
  congr 2
  congr 1
  push_cast
  ring

end SubdiffusiveProcess.LaplacianCorrector
