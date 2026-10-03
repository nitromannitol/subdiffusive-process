module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.EnergyReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyIntegrability
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions

@[expose] public section

/-! # Raw local cutoff energy from the native Hölder energy row -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open scoped ENNReal NNReal

noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Static

/-- The normalized vector energy readout controls its literal lower integral. -/
theorem lintegral_energy_le_volume_mul_sq {d : ℕ} (W : Set (Homogenization.Vec d))
    (a : Homogenization.Vec d → ℝ) (G : Homogenization.Vec d → Homogenization.Vec d)
    (ha : ∀ x, 0 ≤ a x) (hvol : 0 < (volume W).toReal)
    (hint : IntegrableOn (fun x => a x * vecNormSq (G x)) W) {B : ℝ}
    (hB : 0 ≤ B)
    (hbound : vectorNormalizedL2On W (fun x => Real.sqrt (a x) • G x) ≤ B) :
    ∫⁻ x in W, ENNReal.ofReal (a x * vecDot (G x) (G x)) ≤
      ENNReal.ofReal ((volume W).toReal * B ^ 2) := by
  have hnn : ∀ x, 0 ≤ a x * vecNormSq (G x) := fun x =>
    mul_nonneg (ha x) (by unfold vecNormSq; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have hintnn : 0 ≤ ∫ x in W, a x * vecNormSq (G x) := integral_nonneg hnn
  have havgnn : 0 ≤ volumeAverage W (fun x => a x * vecNormSq (G x)) := by
    unfold volumeAverage
    positivity
  rw [Section6Holder.vectorNormalizedL2On_sqrt_smul_eq_sqrt_volumeAverage W a G ha] at hbound
  have havg : volumeAverage W (fun x => a x * vecNormSq (G x)) ≤ B ^ 2 := by
    nlinarith [Real.sq_sqrt havgnn, Real.sqrt_nonneg (volumeAverage W
      (fun x => a x * vecNormSq (G x)))]
  have hraw : (∫ x in W, a x * vecNormSq (G x)) ≤ (volume W).toReal * B ^ 2 := by
    unfold volumeAverage at havg
    rw [mul_comm, ← div_eq_mul_inv] at havg
    simpa only [mul_comm] using (div_le_iff₀ hvol).mp havg
  change (∫⁻ x in W, ENNReal.ofReal (a x * vecNormSq (G x))) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith)

/-- Any supplied native cutoff Hölder conclusion controls the energy on every
truncated window below its stopping scale. This includes boundary windows. -/
theorem cutoff_window_energy_le_of_holder_conclusions {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C : ℝ) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (alpha : ℝ) (m X : ℕ)
    (u h : H1Function (openCubeSet (originCube d (m : ℤ)))) (g : Homogenization.Vec d → Homogenization.Vec d)
    (hC : 0 ≤ C)
    (hconcl : HolderRegularityConclusions M C L omega alpha m X u h g)
    (n : ℕ) (hn : (n : ℤ) ≤ (m : ℤ) - (X : ℤ)) (x : Homogenization.Vec d)
    (hx : x ∈ cube d (m : ℤ)) :
    ∫⁻ z in truncatedCube d (m : ℤ) (n : ℤ) x,
        ENNReal.ofReal (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega z *
          vecDot (u.grad z) (u.grad z)) ≤
      ENNReal.ofReal (((3 : ℝ) ^ n) ^ d *
        (C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
          (vectorNormalizedL2On (cube d (m : ℤ))
              (fun z => Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega z) • u.grad z) +
            (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
              (3 : ℝ) ^ ((m : ℝ) / 2) * holderSeminormOn (cube d (m : ℤ)) (1 / 2) g +
            (if x ∈ cube d ((m : ℤ) - 1) then 0 else
              (tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
                (3 : ℝ) ^ ((m : ℝ) / 2) *
                fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ m)
                  (1 / 2) h.grad))) ^ 2) := by
  have hnm : (n : ℤ) - 1 ≤ (m : ℤ) := by omega
  let W := truncatedCube d (m : ℤ) (n : ℤ) x
  have hint : IntegrableOn (fun z => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega z *
      vecNormSq (u.grad z)) W :=
    (Section6HarmonicApproximation.integrableOn_aCutoff_energy M L omega
      (originCube d (m : ℤ)) u).mono_set
        (Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) (n : ℤ) x)
  have hb := hconcl.2.1 n hn x hx
  have hB := (show 0 ≤ vectorNormalizedL2On W
      (fun z => Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega z) • u.grad z) from
        Real.sqrt_nonneg _).trans hb
  have hraw := lintegral_energy_le_volume_mul_sq W
    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) u.grad
    (fun z => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega z).le)
    (Section6ExcessDecay.volume_toReal_truncatedCube_pos x hx hnm) hint hB hb
  refine hraw.trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [Int.cast_natCast, zpow_natCast] using
    (Section6ExcessDecay.volume_toReal_truncatedCube_bounds x hx hnm).2

end SubdiffusiveProcess.Static
