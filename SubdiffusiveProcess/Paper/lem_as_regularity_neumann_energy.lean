module

public import SubdiffusiveProcess.Paper.lem_as_regularity_neumann_resolved
public import SubdiffusiveProcess.Probability.SubgeometricEnvelope
public import SubdiffusiveProcess.Analysis.SubwavelengthAbsorption

@[expose] public section

/-! A uniform first-moment envelope closes the microscopic radii of the Neumann energy estimate. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Metric SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- One pathwise constant controls all cutoff Neumann energies at every radius in the unit cube. -/
theorem lem_as_regularity_neumann_energy (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
        ∀ (N : ℕ) (f : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
          AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x) = 0 →
        ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos) f u →
        ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
          localGradientEnergy (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos)
            (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
            (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
            (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤ K * Kf ^ 2 * rad ^ t := by
  let t0 := ((d : ℝ) + t) / 2
  have ht01 : (d : ℝ) - 1 < t0 := by dsimp only [t0]; linarith only [ht1, ht2]
  have ht02 : t0 < (d : ℝ) := by dsimp only [t0]; linarith only [ht2]
  have htt0 : t < t0 := by dsimp only [t0]; linarith only [ht2]
  obtain ⟨dr, hdr, hresolved⟩ := lem_as_regularity_neumann_resolved d hd E Pc Xc W Cp Sf
    D Step Dbase Interp t ht1 ht2
  obtain ⟨dm, hdm, hmoment⟩ := cor_neumann_source d hd E Pc Xc W D Cp t0 (1 / 2)
    1 (fun _ => 1) ht01 ht02 (by norm_num) (by norm_num) (fun _ => le_rfl)
  refine ⟨min dr dm, lt_min hdr hdm, ?_⟩
  intro M Rm Sreg It H hIR hdelta
  obtain ⟨Kcut, Ccut, hmem, hnorm, hest⟩ := hmoment M Rm Sreg It H hIR
    (hdelta.trans (min_le_right _ _))
  have henv := ae_subgeometric_envelope_of_memLp_one (chaosSampleLaw M).toMeasure Kcut (Ccut 0)
    (by simpa only [ENNReal.ofReal_one] using hmem 0)
    (by simpa only [ENNReal.ofReal_one] using hnorm 0)
    (t0 - t) (sub_pos.mpr htt0)
  filter_upwards [henv, hest, hresolved M Rm Sreg It H hIR
    (hdelta.trans (min_le_left _ _))] with omega hb he hr
  obtain ⟨B, hB, hb⟩ := hb
  obtain ⟨Kr, hKr, hr⟩ := hr
  refine ⟨B + Kr, add_pos hB hKr, ?_⟩
  intro N f Kf hKf hf hfb hf0 u hu x hx rad hrad hrad1
  have hmult : 0 ≤ Kf ^ 2 * rad ^ t := by positivity
  by_cases hcut : (3 : ℝ) ^ (-(N : ℤ)) ≤ rad
  · exact (hr N f Kf hKf hf hfb hf0 u hu x hx rad hcut).trans
      (by nlinarith only [mul_nonneg hB.le hmult])
  · have hsmall := (he N f Kf hKf hf hfb hf0 u hu).2 x rad hx hrad hrad1
    have hbound := subwavelength_energy_absorb _ (Kcut N omega) B Kf t t0 rad N
      hB.le htt0.le hrad (le_of_not_ge hcut) (hb N) hsmall
    exact hbound.trans (by nlinarith only [mul_nonneg hKr.le hmult])

end SubdiffusiveProcess.Paper
