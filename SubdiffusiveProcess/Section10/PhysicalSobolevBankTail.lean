module

public import SubdiffusiveProcess.Section10.PhysicalLocalTransportTail
public import SubdiffusiveProcess.Section10.KilledSobolevMoment
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

open MeasureTheory Homogenization SubdiffusiveProcess TopologicalSpace
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- A measurable version of the literal finite/full infrared oscillation price.
Its twice-Q moment uses the two existing exponential suppliers at order 4Q.
Both compact constants are fixed before the model, cutoff and requested order. -/
theorem physical_infrared_multiplier_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (S : Compacts (SpatialCoordinates d)) :
    ∃ Ct Cf : ℝ, 0 ≤ Ct ∧ 0 ≤ Cf ∧ ∀ (M : GMCModel d) (n : ℕ) (Q : ℝ), 1 ≤ Q →
      ∃ R : NativeEnvironment d → ℝ, Measurable R ∧ (∀ η, 1 ≤ R η) ∧
        (∫⁻ η, ENNReal.ofReal (R η ^ (2 * Q)) ∂nativeLaw M) ≤
          ENNReal.ofReal (2 * Real.exp (Ct * (4 * Q) ^ 2 * M.delta ^ 2) +
            2 * Real.exp (Cf * (4 * Q) ^ 2 * M.delta ^ 2)) ∧
        ∀ᵐ η ∂nativeLaw M, R η = Real.exp
          (compactPotentialC1Norm S (positiveAnchoredInfraredTruncation η n) +
            ‖(infraredField M (bilateralEnvironment η)).restrict (S : Set (SpatialCoordinates d))‖) := by
  obtain ⟨Ct, hCt, htrunc⟩ := native_truncation_moments hd
  obtain ⟨Cf, hCf, hfull⟩ := full_infrared_moments hd
  refine ⟨Ct S, Cf S, hCt S, hCf S, ?_⟩
  intro M n Q hQ
  let u : NativeEnvironment d → ℝ := fun η =>
    compactPotentialC1Norm S (positiveAnchoredInfraredTruncation η n)
  let v : NativeEnvironment d → ℝ := fun η =>
    ‖(infraredField M (bilateralEnvironment η)).restrict (S : Set (SpatialCoordinates d))‖
  let R0 : NativeEnvironment d → ℝ := fun η => Real.exp (u η + v η)
  have hu0 (η : NativeEnvironment d) : 0 ≤ u η := by unfold u compactPotentialC1Norm; positivity
  have hv0 (η : NativeEnvironment d) : 0 ≤ v η := norm_nonneg _
  obtain ⟨hu1, _⟩ := htrunc M S 1 (by norm_num) n
  obtain ⟨hv1, _⟩ := hfull M S 1 (by norm_num)
  have hvm1 := (bilateralEnvironment_preserving M).integrable_comp_of_integrable hv1
  have hR0 : AEStronglyMeasurable R0 (nativeLaw M) := by
    have hprod := hu1.aestronglyMeasurable.mul hvm1.aestronglyMeasurable
    simp only [one_mul] at hprod
    have hprod' : AEStronglyMeasurable
        (fun η => Real.exp (u η) * Real.exp (v η)) (nativeLaw M) := hprod
    simpa only [R0, Real.exp_add] using hprod'
  let R : NativeEnvironment d → ℝ := fun η => max 1 (hR0.mk R0 η)
  have hR : Measurable R := measurable_const.max hR0.stronglyMeasurable_mk.measurable
  have hReq : ∀ᵐ η ∂nativeLaw M, R η = R0 η := by
    filter_upwards [hR0.ae_eq_mk] with η hη
    change max 1 (hR0.mk R0 η) = R0 η
    rw [← hη, max_eq_right]
    exact Real.one_le_exp (add_nonneg (hu0 η) (hv0 η))
  have horder : 0 ≤ 4 * Q := by linarith
  obtain ⟨huOrder, huOrderBound⟩ := htrunc M S (4 * Q) horder n
  obtain ⟨hvOrder, hvOrderBound⟩ := hfull M S (4 * Q) horder
  have hvmOrder := (bilateralEnvironment_preserving M).integrable_comp_of_integrable hvOrder
  have hum : (∫⁻ η, ENNReal.ofReal (Real.exp (4 * Q * u η)) ∂nativeLaw M) ≤
      ENNReal.ofReal (2 * Real.exp (Ct S * (4 * Q) ^ 2 * M.delta ^ 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal huOrder (by filter_upwards with η using (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal huOrderBound
  have hvm : (∫⁻ η, ENNReal.ofReal (Real.exp (4 * Q * v η)) ∂nativeLaw M) ≤
      ENNReal.ofReal (2 * Real.exp (Cf S * (4 * Q) ^ 2 * M.delta ^ 2)) := by
    have hvmAE := hvOrder.aestronglyMeasurable
    rw [← (bilateralEnvironment_preserving M).map_eq] at hvmAE
    have hi := integral_map (bilateralEnvironment_preserving M).measurable.aemeasurable hvmAE
    rw [(bilateralEnvironment_preserving M).map_eq] at hi
    calc
      _ = ENNReal.ofReal (∫ η, Real.exp (4 * Q * v η) ∂nativeLaw M) :=
        (ofReal_integral_eq_lintegral_ofReal hvmOrder
          (by filter_upwards with η using (Real.exp_pos _).le)).symm
      _ = ENNReal.ofReal (∫ ξ, Real.exp (4 * Q *
          ‖(infraredField M ξ).restrict (S : Set (SpatialCoordinates d))‖)
          ∂(chaosSampleLaw M).toMeasure) := congrArg ENNReal.ofReal hi.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hvOrderBound
  refine ⟨R, hR, fun η => le_max_left _ _, ?_, hReq⟩
  calc
    _ ≤ ∫⁻ η, ENNReal.ofReal (Real.exp (4 * Q * u η)) +
        ENNReal.ofReal (Real.exp (4 * Q * v η)) ∂nativeLaw M := by
      apply lintegral_mono_ae
      filter_upwards [hReq] with η hη
      rw [hη]
      change ENNReal.ofReal (Real.exp (u η + v η) ^ (2 * Q)) ≤
        ENNReal.ofReal (Real.exp (4 * Q * u η)) + ENNReal.ofReal (Real.exp (4 * Q * v η))
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have he : Real.exp (u η + v η) ^ (2 * Q) =
          Real.exp (2 * Q * u η) * Real.exp (2 * Q * v η) := by
        rw [← Real.exp_mul, ← Real.exp_add]
        congr 1
        ring
      have hu2 : Real.exp (4 * Q * u η) = Real.exp (2 * Q * u η) ^ 2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      have hv2 : Real.exp (4 * Q * v η) = Real.exp (2 * Q * v η) ^ 2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [he, hu2, hv2]
      nlinarith [sq_nonneg (Real.exp (2 * Q * u η) - Real.exp (2 * Q * v η))]
    _ = (∫⁻ η, ENNReal.ofReal (Real.exp (4 * Q * u η)) ∂nativeLaw M) +
        (∫⁻ η, ENNReal.ofReal (Real.exp (4 * Q * v η)) ∂nativeLaw M) :=
      lintegral_add_left' huOrder.aestronglyMeasurable.aemeasurable.ennreal_ofReal _
    _ ≤ _ := (add_le_add hum hvm).trans_eq
      (ENNReal.ofReal_add (by positivity) (by positivity)).symm

end SubdiffusiveProcess.Section10
