import SubdiffusiveProcess.Section10.PhysicalTightnessAffineExit
import SubdiffusiveProcess.Section10.PhysicalTightnessCoupling
import SubdiffusiveProcess.Section10.PhysicalSobolevBankDescent
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel

/-! Model-specific attachment of the local analytic certificate to the literal
common-scale lifetime kernels. The analytic bank remains the incoming static
and subharmonic obligation. All environment maps, coefficient identities,
spatial carriers, clock cancellation and measurable marginal descent are
constructed here, rather than being supplied as caller equality premises. -/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section11
open SubdiffusiveProcess
open scoped ENNReal NNReal Pointwise
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness
open PhysicalLocalTransport

/-- The fixed local analytic input used in Step 1, on the literal coefficient
and speed. This is a proposition describing a cutoff and estimates, not a
model or diffusion construction. -/
def LocalExitCertificate {d : ℕ} (a b : Vec d → ℝ) (K : ℝ) : Prop :=
  ∃ chi : H10Function (Metric.ball (0 : Vec d) (1 / 2)),
    (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
    (∀ x ∈ Metric.ball (0 : Vec d) (1 / 6), chi.toFun x = 1) ∧
    energy a (Metric.ball (0 : Vec d) (1 / 2)) chi.toH1Function ≤ K ∧
    ∀ w : H1Function (Metric.ball (0 : Vec d) (1 / 6)),
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Vec d) (1 / 6)), 0 ≤ w.toFun x) →
      (∃ Mw : ℝ, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Vec d) (1 / 6)), w.toFun x ≤ Mw) →
      IsWeakSubSolutionOn a (Metric.ball (0 : Vec d) (1 / 6)) w →
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Vec d) (1 / 18)),
        ENNReal.ofReal (w.toFun x) ≤ ENNReal.ofReal K *
          (∫⁻ y in Metric.ball (0 : Vec d) (1 / 6), ENNReal.ofReal (w.toFun y ^ 2 * b y)) ^
            (1 / 2 : ℝ)

/-- Exact clock after cancellation of the actual common positive scalar. -/
theorem common_affine_clock {d : ℕ} (M : GMCModel d) (L : WithTop ℕ) (N m : ℕ)
    (hactive : activeScale L N = N) {c : ℝ} (hc : 0 < c) :
    (((3 : ℝ) ^ ((m : ℤ) - N)) ^ 2 * c /
      (c * ahom M (activeScale L m) / ahom M N)) = relativeClock M L N m := by
  rw [relativeClock_eq M L N m hactive]
  have hpow : ((3 : ℝ) ^ ((m : ℤ) - N)) ^ 2 =
      (3 : ℝ) ^ (2 * ((m : ℤ) - N)) := by
    simpa only [zpow_ofNat, mul_comm] using
      (zpow_mul (3 : ℝ) ((m : ℤ) - N) (2 : ℤ)).symm
  rw [hpow]
  field_simp [hc.ne', (ahom_pos M N).ne', (ahom_pos M (activeScale L m)).ne']

/-- Construct the measurable early-exit bank on the actual chaos law from the
local physical analytic bank. The input moment is `2Q`, chosen before the
static disorder threshold. The output has cost `1+2*4^Q*C` and works at every
start and every positive time, for finite and top and for all `m`, including
`m>N`. No caller coefficient, pushforward or path-law equality is accepted. -/
theorem actual_common_exit_moment_bank_of_local_analytic_bank {d : ℕ}
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (M : GMCModel d) (H : BilateralField d → C(Vec d, ℝ))
    (hH : InfraredCharacterization M H)
    (Hf : BilateralField d → C(Vec d, ℝ)) (hHf : Hf = H ∨ Hf = fun _ => 0)
    (LN : ℕ → Kernel (BilateralField d × Vec d) (Path d))
    (hdata : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      LocalDiffusionData (cutoffCoefficient M Hf xi N) (cutoffSpeedDensity M Hf xi N)
        (Kernel.comap (LN N) (fun x => (xi, x)) measurable_prodMk_left))
    (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (hlocal : ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
      ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
        (∫⁻ omega, ENNReal.ofReal (K omega ^ (2 * Q))
          ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
        ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
          LocalExitCertificate (localCoefficient M L m z omega) (localSpeed M L m z omega) (K omega)) :
    ∀ N m : ℕ, ∀ y : Vec d,
      ∃ L : WithTop ℕ,
        ((L = ⊤ ∧ Hf = H) ∨ (L = (N : WithTop ℕ) ∧ Hf = fun _ => 0)) ∧
        ∃ F : BilateralField d → ℝ, Measurable F ∧ (∀ xi, 1 ≤ F xi) ∧
          (∫⁻ xi, ENNReal.ofReal (F xi ^ Q) ∂(chaosSampleLaw M).toMeasure) ≤
            ENNReal.ofReal (1 + 2 * ((4 : ℝ) ^ Q * C)) ∧
          ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ t : ℝ, 0 < t →
            ∀ x ∈ Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - N) / 18),
              LN N (xi, x) {w | LifetimePath.exitTime
                (Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - N) / 2)) w ≤ ENNReal.ofReal t} ≤
                  ENNReal.ofReal (F xi * Real.sqrt (t / relativeClock M L N m)) := by
  intro N m y
  letI : Nonempty (NativeEnvironment d) := Measure.nonempty_of_neZero (nativeLaw M)
  obtain ⟨L, hbranch, hphysical, hbilateral, -, hcoeff⟩ :=
    actual_common_local_coupling M H hH Hf hHf N
  obtain ⟨K, hK, hKone, hKmoment, hKlocal⟩ := hlocal L m ((3 : ℝ) ^ N • y)
  have hactive : activeScale L N = N := by
    rcases hbranch with ⟨hL, -⟩ | ⟨hL, -⟩ <;> subst L
    · simp only [activeScale, WithTop.untopD_top, min_self]
    · rw [activeScale_coe, min_self]
  let r : ℝ := (3 : ℝ) ^ ((m : ℤ) - N)
  have hr : 0 < r := zpow_pos (by norm_num) _
  let Fsource : NativeEnvironment d → ℝ := fun eta =>
    4 * K (physicalEnvironment M N 0 eta) ^ (2 : ℕ)
  have hFs : Measurable Fsource := by
    simpa only [Fsource, pow_two] using measurable_const.mul
      ((hK.comp hphysical.measurable).mul (hK.comp hphysical.measurable))
  have hFsone : ∀ eta, 1 ≤ Fsource eta := by
    intro eta
    have hk := hKone (physicalEnvironment M N 0 eta)
    have hk0 : 0 ≤ K (physicalEnvironment M N 0 eta) := zero_le_one.trans hk
    have hs := mul_le_mul hk hk zero_le_one hk0
    change 1 ≤ 4 * K (physicalEnvironment M N 0 eta) ^ (2 : ℕ)
    nlinarith only [hs]
  have hpower : ∀ eta, Fsource eta ^ Q =
      (4 : ℝ) ^ Q * K (physicalEnvironment M N 0 eta) ^ (2 * Q) := by
    intro eta
    dsimp only [Fsource]
    rw [Real.mul_rpow (by norm_num) (sq_nonneg _), ← Real.rpow_natCast,
      ← Real.rpow_mul (zero_le_one.trans (hKone _))]
    norm_num only [Nat.cast_ofNat]
  have hm : (∫⁻ eta, ENNReal.ofReal (Fsource eta ^ Q) ∂nativeLaw M) ≤
      ENNReal.ofReal ((4 : ℝ) ^ Q * C) := by
    simp_rw [hpower, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) Q)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      hphysical.lintegral_comp (f := fun omega => ENNReal.ofReal (K omega ^ (2 * Q)))
        (ENNReal.measurable_ofReal.comp (hK.pow measurable_const))]
    exact mul_le_mul_right hKmoment _
  let P : BilateralField d → ℝ → Prop := fun xi f =>
    ∀ t : ℝ, 0 < t → ∀ x ∈ Metric.ball y (r / 18),
      LN N (xi, x) {w | LifetimePath.exitTime (Metric.ball y (r / 2)) w ≤ ENNReal.ofReal t} ≤
        ENNReal.ofReal (f * Real.sqrt (t / relativeClock M L N m))
  have hPmono : ∀ xi f f', f ≤ f' → P xi f → P xi f' := by
    intro xi f f' hff hp t ht x hx
    exact (hp t ht x hx).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hff (Real.sqrt_nonneg _)))
  have hP : ∀ᵐ eta ∂nativeLaw M, P (bilateralEnvironment eta) (Fsource eta) := by
    filter_upwards [hcoeff, hphysical.quasiMeasurePreserving.ae hKlocal,
      hbilateral.quasiMeasurePreserving.ae hdata] with eta heq hloc hD
    obtain ⟨chi, hchi01, hchi1, henergy, hmoser⟩ := hloc
    let c := commonLocalFactor M L N m y (physicalEnvironment M N 0 eta)
    have hc : 0 < c := commonLocalFactor_pos M L N m y _
    have hspeed : ∀ x, cutoffSpeedDensity M Hf (bilateralEnvironment eta) N (r • x + y) =
        c * localSpeed M L m ((3 : ℝ) ^ N • y) (physicalEnvironment M N 0 eta) x := by
      intro x
      simpa only [add_comm] using (heq m y x).2.1
    have hcoefficient : ∀ x, cutoffCoefficient M Hf (bilateralEnvironment eta) N (r • x + y) =
        (c * ahom M (activeScale L m) / ahom M N) *
          localCoefficient M L m ((3 : ℝ) ^ N • y) (physicalEnvironment M N 0 eta) x := by
      intro x
      simpa only [add_comm] using (heq m y x).2.2
    have hfast := exit_probability_le_of_affine_cutoff_moser (hD N)
      (Lane4.cutoffCoefficient_continuous M Hf (bilateralEnvironment eta) N)
      (fun x => Lane4.cutoffCoefficient_pos M Hf (bilateralEnvironment eta) N x)
      hr hc (div_pos (mul_pos hc (ahom_pos M _)) (ahom_pos M N)) y hcoefficient hspeed
      (1 / 2) (1 / 6) (1 / 18) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      chi hchi01 hchi1 (K (physicalEnvironment M N 0 eta)) (K (physicalEnvironment M N 0 eta))
      (zero_le_one.trans (hKone _)) (zero_le_one.trans (hKone _)) henergy hmoser
    rw [common_affine_clock M L N m hactive hc] at hfast
    have hhalf : r * (1 / 2) = r / 2 := by ring
    have hinner : r * (1 / 18) = r / 18 := by ring
    simp only [hhalf, hinner, Kernel.comap_apply] at hfast
    intro t ht x hx
    have hbound := hfast t ht x hx
    refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    have hk := hKone (physicalEnvironment M N 0 eta)
    have hk0 := zero_le_one.trans hk
    have hsqrt : Real.sqrt (K (physicalEnvironment M N 0 eta)) ≤ K (physicalEnvironment M N 0 eta) :=
      Real.sqrt_le_iff.mpr ⟨hk0, by
        simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hk hk0⟩
    rw [Real.sqrt_mul (div_nonneg ht.le (relativeClock_pos M L N m).le)]
    change 4 * (K (physicalEnvironment M N 0 eta) *
      (Real.sqrt (t / relativeClock M L N m) * Real.sqrt (K (physicalEnvironment M N 0 eta)))) ≤
        (4 * K (physicalEnvironment M N 0 eta) ^ 2) * Real.sqrt (t / relativeClock M L N m)
    calc
      _ ≤ 4 * (K (physicalEnvironment M N 0 eta) *
          (Real.sqrt (t / relativeClock M L N m) * K (physicalEnvironment M N 0 eta))) := by
        gcongr
      _ = _ := by ring
  obtain ⟨F, hF, hFone, hFmoment, hFbound⟩ :=
    SubdiffusiveProcess.Section10.physicalBank_measurable_descent (nativeLaw M) (chaosSampleLaw M).toMeasure
      hbilateral hFs hFsone hQ (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) Q) hC)
      hm P hPmono hP
  exact ⟨L, hbranch, F, hF, hFone, hFmoment, hFbound⟩

end SubdiffusiveProcess.Section10.PhysicalTightness
