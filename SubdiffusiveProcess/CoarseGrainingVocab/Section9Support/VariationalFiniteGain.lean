module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalPowerEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalPowerNorms

@[expose] public section

/-!
# Finite-exponent gain of the variational Green inverse

The power test, Sobolev, and Hölder yield every finite gain in the Sobolev
range. A qualitative bound justifies the test and cancellation; its size
does not occur in the estimate. The critical forcing estimate supplies
that bound for bounded forcing in the subsequent assembly.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The positive part of a bounded Green solution has the exact finite-exponent gain. -/
theorem variational_green_positive_finite_gain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) {c rho : Vec d → ℝ}
    (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {p0 p s A F : ℝ} (hp0 : 2 < p0) (hp : 1 < p) (hs : 1 ≤ s)
    (hbalance : 1 / p + (2 * s - 1) / (p0 * s) ≤ 1)
    (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hSob : SobolevAssumption c rho U p0 A F)
    (hPoi : PoincareAssumption c rho U A F)
    {f : Vec d → ℝ} (hf : AEStronglyMeasurable f ((weightedMeasure rho).restrict U))
    (u : H10Function U) (hu : IsMassiveWeakSolutionOn c rho 0 U u.toH1Function f)
    {M : ℝ} (hM : 0 ≤ M)
    (hub : ∀ᵐ x ∂volume.restrict U, |u.toH1Function.toFun x| ≤ M) :
    eLpNorm (fun x => max (u.toH1Function.toFun x) 0) (ENNReal.ofReal (p0 * s))
        ((weightedMeasure rho).restrict U) ≤
      ENNReal.ofReal (A * (A + 1) * F * (s ^ 2 / (2 * s - 1))) *
        weightedMeasure rho U ^ (1 / (p0 * s) - 1 / p) *
          eLpNorm f (ENNReal.ofReal p) ((weightedMeasure rho).restrict U) := by
  let mu := (weightedMeasure rho).restrict U
  let v : Vec d → ℝ := fun x => max (u.toH1Function.toFun x) 0
  have hs0 : 0 < s := by linarith
  have hp00 : 0 < p0 := by linarith
  have ht : 0 < 2 * s - 1 := by linarith
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
  have hMass0 : weightedMeasure rho U ≠ 0 := by rw [← hmass]; exact hmu0.ne'
  have hMasstop : weightedMeasure rho U ≠ ⊤ := by rw [← hmass]; exact measure_ne_top mu univ
  have hMassReal : 0 < (weightedMeasure rho U).toReal := ENNReal.toReal_pos hMass0 hMasstop
  have hv0 (x : Vec d) : 0 ≤ v x := le_max_right _ _
  have hvmeas : AEStronglyMeasurable v (volume.restrict U) := by
    simpa only [v] using! continuous_max.comp_aestronglyMeasurable
      (u.toH1Function.memL2.aestronglyMeasurable.prodMk aestronglyMeasurable_const)
  have hvb : ∀ᵐ x ∂volume.restrict U, ‖v x‖ ≤ M := by
    filter_upwards [hub] with x hx
    rw [Real.norm_of_nonneg (hv0 x)]
    exact max_le ((le_abs_self _).trans hx) hM
  have hvvol : MemLp v (ENNReal.ofReal (p0 * s)) (volume.restrict U) := MemLp.of_bound hvmeas M hvb
  have hvmem : MemLp v (ENNReal.ofReal (p0 * s)) mu :=
    memLp_weighted_of_volume_restrict hU.isOpen.measurableSet hr hvvol
  have hpower := variational_power_sobolev hU hc hr hA hF hSob hPoi u hu hM hub hs
  change eLpNorm (fun x => v x ^ s) (ENNReal.ofReal p0) mu ^ 2 ≤ _ at hpower
  have hnormeq : eLpNorm (fun x => v x ^ s) (ENNReal.ofReal p0) mu =
      eLpNorm v (ENNReal.ofReal (p0 * s)) mu ^ s := by
    rw [ENNReal.ofReal_mul hp00.le, ← eLpNorm_norm_rpow v hvmem.aestronglyMeasurable hs0]
    congr 1
    funext x
    rw [Real.norm_of_nonneg (hv0 x)]
  rw [hnormeq, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hpower
  norm_num only [Nat.cast_ofNat] at hpower
  have hholder := variational_power_holder hf hvmem.aestronglyMeasurable hp
    (mul_pos hp00 hs0) ht hbalance
  simp only [Real.norm_of_nonneg (hv0 _)] at hholder
  have hbound := hpower.trans (mul_le_mul' le_rfl hholder)
  let B : ℝ := A * (A + 1) * F * (s ^ 2 / (2 * s - 1))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hcoef : ENNReal.ofReal
      (A * (A + 1) * F * (weightedMeasure rho U).toReal ^ (-(1 - 2 / p0)) *
        (s ^ 2 / (2 * s - 1))) = ENNReal.ofReal B * weightedMeasure rho U ^ (-(1 - 2 / p0)) := by
    rw [show A * (A + 1) * F * (weightedMeasure rho U).toReal ^ (-(1 - 2 / p0)) *
        (s ^ 2 / (2 * s - 1)) = B * (weightedMeasure rho U).toReal ^ (-(1 - 2 / p0)) by
          dsimp only [B]; ring,
      ENNReal.ofReal_mul hB, ← ENNReal.ofReal_rpow_of_pos hMassReal,
      ENNReal.ofReal_toReal hMasstop]
  have hexp : -(1 - 2 / p0) + (1 - 1 / p - (2 * s - 1) / (p0 * s)) =
      1 / (p0 * s) - 1 / p := by field_simp; ring
  rw [hcoef, hmass] at hbound
  apply variational_cancel_power hvmem.eLpNorm_ne_top hs
  calc
    _ = eLpNorm v (ENNReal.ofReal (p0 * s)) mu ^ (s * 2) := by congr 1; ring
    _ ≤ _ := hbound
    _ = _ := by
      rw [← hexp, ENNReal.rpow_add _ _ hMass0 hMasstop]
      dsimp only [B]
      ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
