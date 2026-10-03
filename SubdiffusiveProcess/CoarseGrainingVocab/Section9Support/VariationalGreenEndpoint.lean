module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalLevelBound
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalLevelEnergy

@[expose] public section

/-!
# The critical forcing-to-infinity gain of the variational Green inverse

The zero-boundary Green solution gains from L^(2 gamma) to L infinity,
where gamma=(1-2/p0)^(-1). The estimate uses only the frozen Sobolev and
Poincaré constants and has the exact mass normalization. No diffusion law,
prior high integrability, or bounded representative of the solution is used.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The critical `L^(2 gamma) → L infinity` variational Green estimate. -/
theorem variational_green_critical_gain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) {c rho : Vec d → ℝ}
    (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {p A F : ℝ} (hp : 2 < p) (hA : 0 < A) (hF : 0 < F)
    (hSob : SobolevAssumption c rho U p A F)
    (hPoi : PoincareAssumption c rho U A F)
    {f : Vec d → ℝ} (hf : MemLp f (ENNReal.ofReal (2 / (1 - 2 / p))) ((weightedMeasure rho).restrict U))
    (u : H10Function U) (hu : IsMassiveWeakSolutionOn c rho 0 U u.toH1Function f) :
    eLpNorm u.toH1Function.toFun ⊤ ((weightedMeasure rho).restrict U) ≤
      ENNReal.ofReal (stampacchiaConstant p * A * (A + 1) * F) *
        weightedMeasure rho U ^ (-(1 - 2 / p) / 2) *
          eLpNorm f (ENNReal.ofReal (2 / (1 - 2 / p))) ((weightedMeasure rho).restrict U) := by
  let mu := (weightedMeasure rho).restrict U
  letI : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  obtain ⟨lo, hi, hlo, hrb⟩ := hr.2
  have hmeasure := weightedMeasure_restrict_le_smul_volume_restrict hU.isOpen.measurableSet hi
    (hrb.mono fun _ hx => hx.2)
  letI : IsFiniteMeasure mu := ⟨by
    apply (Measure.le_iff.mp hmeasure univ MeasurableSet.univ).trans_lt
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top (volume.restrict U) univ)⟩
  have hmass : mu univ = weightedMeasure rho U := by simp only [mu, Measure.restrict_apply_univ]
  have hmu0 : 0 < mu univ := weightedMeasure_restrict_open_pos hU.isOpen hr univ isOpen_univ
    (by simpa only [univ_inter] using! hne)
  have hM : 0 < (weightedMeasure rho U).toReal := by
    rw [← hmass]
    exact ENNReal.toReal_pos hmu0.ne' (measure_ne_top mu univ)
  have hMtop : weightedMeasure rho U ≠ ⊤ := by rw [← hmass]; exact measure_ne_top mu univ
  let B : ℝ := A * (A + 1) * F * (weightedMeasure rho U).toReal ^ (-(1 - 2 / p))
  have hB : 0 < B := by dsimp only [B]; positivity
  have hu2 : MemLp u.toH1Function.toFun 2 mu :=
    memLp_weighted_of_volume_restrict hU.isOpen.measurableSet hr u.toH1Function.memL2
  have hupper := variational_ae_le_of_level_estimates mu hp hB (by rwa [hmass]) hu2 hf
    (variational_green_positive_level_bound hU hc hr hA.le hF.le hSob hPoi u hu)
  have huneg : IsMassiveWeakSolutionOn c rho 0 U (-u).toH1Function (fun x => -f x) :=
    isMassiveWeakSolutionOn_neg hu
  have huneg2 : MemLp (-u).toH1Function.toFun 2 mu :=
    memLp_weighted_of_volume_restrict hU.isOpen.measurableSet hr (-u).toH1Function.memL2
  have hfneg : MemLp (fun x => -f x) (ENNReal.ofReal (2 / (1 - 2 / p))) mu := hf.neg
  have hnegative := variational_ae_le_of_level_estimates mu hp hB (by rwa [hmass]) huneg2 hfneg
    (variational_green_positive_level_bound hU hc hr hA.le hF.le hSob hPoi (-u) huneg)
  have hnegNorm : eLpNorm (fun x => -f x) (ENNReal.ofReal (2 / (1 - 2 / p))) mu =
      eLpNorm f (ENNReal.ofReal (2 / (1 - 2 / p))) mu := eLpNorm_neg f _ _
  have hpair : ∀ᵐ x ∂mu, |u.toH1Function.toFun x| ≤ stampacchiaConstant p * B *
      (mu univ).toReal ^ (1 / (2 / (1 - 2 / p))) *
        (eLpNorm f (ENNReal.ofReal (2 / (1 - 2 / p))) mu).toReal := by
    filter_upwards [hupper, hnegative] with x hx hxneg
    rw [hnegNorm] at hxneg
    change (-1 : ℝ) * u.toH1Function.toFun x ≤ _ at hxneg
    rw [neg_one_mul] at hxneg
    exact abs_le.mpr ⟨by linarith, hx⟩
  have hq : 1 / (2 / (1 - 2 / p)) = (1 - 2 / p) / 2 := by field_simp
  have hconstant : stampacchiaConstant p * B * (mu univ).toReal ^ (1 / (2 / (1 - 2 / p))) =
      (stampacchiaConstant p * A * (A + 1) * F) * (weightedMeasure rho U).toReal ^ (-(1 - 2 / p) / 2) := by
    rw [hmass, hq]
    dsimp only [B]
    calc
      _ = (stampacchiaConstant p * A * (A + 1) * F) *
          ((weightedMeasure rho U).toReal ^ (-(1 - 2 / p)) *
            (weightedMeasure rho U).toReal ^ ((1 - 2 / p) / 2)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hM]
        congr 2
        ring
  simp only [hconstant] at hpair
  have hnorm : eLpNorm u.toH1Function.toFun ⊤ mu ≤ ENNReal.ofReal
      ((stampacchiaConstant p * A * (A + 1) * F) * (weightedMeasure rho U).toReal ^ (-(1 - 2 / p) / 2) *
        (eLpNorm f (ENNReal.ofReal (2 / (1 - 2 / p))) mu).toReal) := by
    rw [eLpNorm_exponent_top
      (memLp_weighted_of_volume_restrict hU.isOpen.measurableSet hr
        u.toH1Function.memL2).aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound
      (hpair.mono fun _ hx => by simpa only [Real.norm_eq_abs] using! hx)
  have hcoef : 0 ≤ stampacchiaConstant p * A * (A + 1) * F := by
    have hpos := stampacchiaConstant_pos p
    positivity
  rw [ENNReal.ofReal_mul (mul_nonneg hcoef (Real.rpow_nonneg hM.le _)),
    ENNReal.ofReal_toReal hf.eLpNorm_ne_top, ENNReal.ofReal_mul hcoef,
    ← ENNReal.ofReal_rpow_of_pos hM, ENNReal.ofReal_toReal hMtop] at hnorm
  exact hnorm

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
