module

public import SubdiffusiveProcess.Section10.MeanExitPhysicalData
public import SubdiffusiveProcess.Section10.MeanExitPowerMoments
public import SubdiffusiveProcess.Section10.PhysicalTightnessActualExitBank
public import MarkovProcess.Killed.Nested

@[expose] public section



open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Filter Topology Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.Section10.PhysicalAttachment SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10
open PhysicalTightness

/-- The proved deterministic certificate's moment-bank interface. This internal
adapter premise is discharged from the exact static source input below. -/
def PhysicalLocalExitMomentBank (d : ℕ) : Prop :=
  ∀ Q : ℝ, 1 ≤ Q → ∃ δ : ℝ, 0 < δ ∧
    ∀ M : GMCModel d, M.delta ≤ δ → ∃ C : ℝ, 0 < C ∧
      ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
        ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
          (∫⁻ omega, ENNReal.ofReal (K omega ^ Q)
            ∂(physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
          ∀ᵐ omega ∂(physicalLaw M).toMeasure,
            LocalExitCertificate (localCoefficient M L m z omega)
              (localSpeed M L m z omega) (K omega)

/-- Exact direct physical clock; the common coefficient factor cancels. -/
theorem meanExit_physical_affine_clock {d : ℕ} (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ((3 : ℝ) ^ m) ^ 2 * c / (c * ahom M (activeScale L m)) =
      (rawClock M L m : ℝ) := by
  change _ = (3 : ℝ) ^ (2 * m) / ahom M (activeScale L m)
  rw [← pow_mul, Nat.mul_comm m 2]
  field_simp [hc.ne', (ahom_pos M _).ne']



theorem physicalMeanExitEarlyExitSupplier_of_localBank {d : ℕ} (hd : 2 ≤ d)
    (hDensity : SmoothReversibleKilledDensitySupplier)
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess)
    (hbank : PhysicalLocalExitMomentBank d) : PhysicalMeanExitEarlyExitSupplier d := by
  intro Q hQ
  obtain ⟨δ, hδ, hmodels⟩ := hbank (2 * Q) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨C, hC, hlocal⟩ := hmodels M hM
  refine ⟨(4 : ℝ) ^ Q * C, mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hC, ?_⟩
  intro X hX hphysical L m z
  obtain ⟨K, hK, hKone, hKmoment, hKlocal⟩ := hlocal L m z
  let F : AnchoredC11Sample d → ℝ := fun omega => 4 * K omega ^ (2 : ℕ)
  have hF : Measurable F := measurable_const.mul (hK.pow_const 2)
  have hFone : ∀ omega, 1 ≤ F omega := by
    intro omega
    have hk := hKone omega
    have hs := mul_le_mul hk hk zero_le_one (zero_le_one.trans hk)
    dsimp only [F]
    nlinarith only [hs]
  have hm := lintegral_factor_power_moment (physicalLaw M).toMeasure hK
    (fun omega => zero_le_one.trans (hKone omega)) (by norm_num : (0 : ℝ) ≤ 4)
    hKmoment
  have hFmoment : (∫⁻ omega, ENNReal.ofReal (F omega ^ Q)
      ∂(physicalLaw M).toMeasure) ≤ ENNReal.ofReal ((4 : ℝ) ^ Q * C) := by
    simpa only [F, Real.rpow_two] using hm
  refine ⟨F, hF, hFone, hFmoment, ?_⟩
  have hdata := physicalMeanExitFamily_localDiffusionData hd hDensity hFOT M X hX hphysical
  filter_upwards [hKlocal, hdata] with omega hloc hD
  obtain ⟨chi, hchi01, hchi1, henergy, hmoser⟩ := hloc
  let r : ℝ := (3 : ℝ) ^ m
  let c : ℝ := localFactor M L m z omega
  have hr : 0 < r := pow_pos (by norm_num) _
  have hc : 0 < c := localFactor_pos M L m z omega
  have hcoefficient : ∀ x, coefficientAt M L omega (r • x + z) =
      (c * ahom M (activeScale L m)) * localCoefficient M L m z omega x := by
    intro x
    dsimp only [localCoefficient, localSpeed, r, c]
    rw [add_comm]
    field_simp [(localFactor_pos M L m z omega).ne', (ahom_pos M _).ne']
  have hspeed : ∀ x, coefficientAt M L omega (r • x + z) =
      c * localSpeed M L m z omega x := by
    intro x
    dsimp only [localSpeed, r, c]
    rw [add_comm]
    field_simp [(localFactor_pos M L m z omega).ne']
  have hfast := exit_probability_le_of_affine_cutoff_moser (hD L)
    (continuous_coefficientAt M L omega) (coefficientAt_pos M L omega)
    hr hc (mul_pos hc (ahom_pos M _)) z hcoefficient hspeed
    (1 / 2) (1 / 6) (1 / 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    chi hchi01 hchi1 (K omega) (K omega) (zero_le_one.trans (hKone omega))
    (zero_le_one.trans (hKone omega)) henergy hmoser
  rw [meanExit_physical_affine_clock M L m hc] at hfast
  have hinner : (3 : ℝ) ^ ((m : ℤ) - 2) / 2 = r * (1 / 18) := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    norm_num
    dsimp only [r]
    ring
  have houter : (3 : ℝ) ^ (m : ℤ) / 2 = r * (1 / 2) := by
    rw [zpow_natCast]
    dsimp only [r]
    ring
  intro t ht x hx
  rw [hinner] at hx
  have htclock : 0 < t * (rawClock M L m : ℝ) := mul_pos ht (rawClock_pos M L m)
  have hbound := hfast (t * (rawClock M L m : ℝ)) htclock x hx
  have hmap : ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath) x
      {w | LifetimePath.exitTime (Metric.ball z (r * (1 / 2))) w ≤
        ENNReal.ofReal (t * (rawClock M L m : ℝ))} =
      X L (omega, x) {w | ContinuousPath.exitTime (Metric.ball z (r * (1 / 2))) w ≤
        ENNReal.ofReal (t * (rawClock M L m : ℝ))} := by
    rw [Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath,
      Measure.map_apply LifetimePath.measurable_ofContinuousPath
        (measurableSet_le (LifetimePath.measurable_exitTime _ Metric.isOpen_ball) measurable_const)]
    simp only [physicalSlice, Kernel.comap_apply, Set.preimage_setOf_eq,
      LifetimePath.exitTime_ofContinuousPath]
  rw [hmap, mul_div_cancel_right₀ t (show (rawClock M L m : ℝ) ≠ 0 from
    (NNReal.coe_pos.mpr (rawClock_pos M L m)).ne')] at hbound
  rw [houter]
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have hk0 := zero_le_one.trans (hKone omega)
  have hsqrt : Real.sqrt (K omega) ≤ K omega := Real.sqrt_le_iff.mpr
    ⟨hk0, by simpa only [mul_one, pow_two] using
      mul_le_mul_of_nonneg_left (hKone omega) hk0⟩
  rw [Real.sqrt_mul ht.le]
  calc
    4 * (K omega * (Real.sqrt t * Real.sqrt (K omega))) ≤
        4 * (K omega * (Real.sqrt t * K omega)) := by gcongr
    _ = F omega * Real.sqrt t := by dsimp only [F]; ring


end SubdiffusiveProcess.Section10
