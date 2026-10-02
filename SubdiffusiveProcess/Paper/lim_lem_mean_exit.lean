import SubdiffusiveProcess.Paper.tight_lem_static
import SubdiffusiveProcess.Section10.PhysicalAttachment
import SubdiffusiveProcess.Paper.tight_lem_subharmonic
import SubdiffusiveProcess.Section10.PhysicalTightnessActualExitBank
import SubdiffusiveProcess.Section10.KilledSobolevEnergy
import SubdiffusiveProcess.Section10.MeanExitPhysicalEarlyExit
import SubdiffusiveProcess.Section10.PhysicalSobolevBankBounds
import SubdiffusiveProcess.Paper.tight_static
import SubdiffusiveProcess.Paper.lfsgs_response_bank
import SubdiffusiveProcess.Paper.inputs_J_witness
import SubdiffusiveProcess.Paper.inputs_poincare_witness
import SubdiffusiveProcess.Paper.inputs_Sf_witness
import SubdiffusiveProcess.Section10.PhysicalSobolevBankDescent
import SubdiffusiveProcess.Section10.PhysicalLocalTransportInfrared
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.Section10.PhysicalSobolevBankTail
import SubdiffusiveProcess.Paper.tight_static_coer
import SubdiffusiveProcess.Section10.PhysicalSobolevBankLargeDomain
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowMomentTranslatedEllipticity
import SubdiffusiveProcess.Analysis.ContinuousCubeCoefficient
import Homogenization.Book.Ch04.Theorems.DilationLaw
import SubdiffusiveProcess.Section10.PhysicalSobolevBankLargeEllipticity
import SubdiffusiveProcess.Section10.PhysicalSobolevBankLargeCoercivity
import SubdiffusiveProcess.Section10.PhysicalLargeMassMoment
import SubdiffusiveProcess.Section10.KilledSobolev
import SubdiffusiveProcess.Paper.tight_subharmonic
import SubdiffusiveProcess.Section10.KilledSobolevMomentEnergy
import SubdiffusiveProcess.Section10.KilledSobolevConstants
import SubdiffusiveProcess.Section10.TorsionExitPhysical
import SubdiffusiveProcess.Section10.PhysicalLocalTransportResolvent
import SubdiffusiveProcess.Section10.PhysicalLocalTransportUniqueness
import SubdiffusiveProcess.Paper.physical_rescaling
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellTransport
import SubdiffusiveProcess.Processes.E7.FellerFromResolvent
import SubdiffusiveProcess.Section10.TorsionExitDensityPhysical
import SubdiffusiveProcess.Section10.TorsionExitDensityTransport
import SubdiffusiveProcess.Paper.inputs_classical_fot_part_process
import SubdiffusiveProcess.Section10.MeanExitBankConstants
import Mathlib
import SubdiffusiveProcess.Main.DiffusionPath
import MarkovProcess.Path.ExitTime
import MarkovProcess.Main
import MarkovProcess.FiniteTime.ProjectiveFamily
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierGrowth
import SubdiffusiveProcess.Frozen.Section6.Defs.CoefficientAt
import SubdiffusiveProcess.Section10.ExitMomentPassageAffine
import SubdiffusiveProcess.Section10.ExitTailMomentsPhysical
import SubdiffusiveProcess.Section10.PhysicalAttachmentUniqueness
import SubdiffusiveProcess.Section10.MeanExitLower
import SubdiffusiveProcess.Section10.MeanExitEarlyExitInterface
import SubdiffusiveProcess.Paper.lim_killed_density_continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- Inlined proved source application: SubdiffusiveProcess.Section10.MeanExitStaticInput. -/
noncomputable section aux_lim_lem_mean_exit_inline_0

/-! Source application interface: exactly the committed Section 8 static
statement. The unproved anchor is imported for its vocabulary, never applied
as a provider. Reusable library modules do not import this application. -/

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10
open Paper



def aux_lim_lem_mean_exit_TightStaticEstimateInput : Prop :=
  ∀ (d : ℕ) (y0 : Vec d) (ρ0 : ℝ) (_hρ0 : 0 < ρ0) (p : ℕ)
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    (_hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i)
    (_hin : ∀ i, Metric.ball (c i) (s1 i / 2) ⊆ Metric.ball y0 (ρ0 / 2)),
    ∃ B : ℝ, 0 < B ∧ ∀ q : ℝ, 1 ≤ q →
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ delta0 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
            ∃ K : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d → ℝ, Measurable K ∧
              (∀ ω, 1 ≤ K ω) ∧
              (∫⁻ ω, ENNReal.ofReal (K ω ^ q)
                ∂(SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M
                  (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
                  (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure) ≤
                ENNReal.ofReal C ∧
              ∀ᵐ ω ∂(SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M
                  (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
                  (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure,
                let j : ℕ := match L with
                  | ⊤ => m
                  | (n : ℕ) => min m n
                let cz : ℝ := coefficientAt M L ω z /
                  SubdiffusiveProcess.Frozen.Assumptions.aCutoff M j ω.1 z
                let b : Vec d → ℝ := fun x => cz⁻¹ * coefficientAt M L ω (z + (3 : ℝ) ^ m • x)
                aux_tight_lem_static_estimates b (fun x => (ahom M j)⁻¹ * b x) y0 ρ0 c s0 s1 (K ω) B

end SubdiffusiveProcess.Section10
end aux_lim_lem_mean_exit_inline_0

/- Inlined proved source application: SubdiffusiveProcess.Section10.MeanExitStaticCertificate. -/
noncomputable section aux_lim_lem_mean_exit_inline_1



open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section11
open scoped ENNReal
namespace SubdiffusiveProcess.Section10
open Paper PhysicalTightness

/-- The three pairs supply the outer adapted cutoff, inner killed coercivity,
and all dyadic cutoffs for Moser on radius 1/6 with target radius 1/18. -/
def aux_lim_lem_mean_exit_meanExitPairSides0 (i : Fin 3) : ℝ :=
  if i = 0 then 1 / 3 else if i = 1 then 1 / 6 else 1 / 9

def aux_lim_lem_mean_exit_meanExitPairSides1 (i : Fin 3) : ℝ :=
  if i = 0 then 1 else if i = 1 then 1 / 3 else 2 / 9

theorem aux_lim_lem_mean_exit_meanExitPairSides_pos :
    ∀ i, 0 < aux_lim_lem_mean_exit_meanExitPairSides0 i ∧ aux_lim_lem_mean_exit_meanExitPairSides0 i < aux_lim_lem_mean_exit_meanExitPairSides1 i := by
  intro i
  fin_cases i <;> norm_num [aux_lim_lem_mean_exit_meanExitPairSides0, aux_lim_lem_mean_exit_meanExitPairSides1]

theorem aux_lim_lem_mean_exit_meanExitPairSides_subset {d : ℕ} :
    ∀ i, Metric.ball (0 : Vec d) (aux_lim_lem_mean_exit_meanExitPairSides1 i / 2) ⊆
      Metric.ball (0 : Vec d) ((2 : ℝ) / 2) := by
  intro i
  apply Metric.ball_subset_ball
  fin_cases i <;> norm_num [aux_lim_lem_mean_exit_meanExitPairSides1]

/-- A bounded deterministic export of the actual combined local certificate.
D and e are fixed by dimension/geometry/B, before every requested moment. -/
theorem aux_lim_lem_mean_exit_localExitCertificate_of_static (d : ℕ) (hd : 1 ≤ d) (B : ℝ) (hB : 0 < B) :
    ∃ D e : ℝ, 1 ≤ D ∧ 1 ≤ e ∧
      ∀ (b A : Vec d → ℝ) (K : ℝ), Continuous b → Continuous A →
        (∀ x, 0 < b x) → (∀ x, 0 < A x) → 1 ≤ K →
        aux_tight_lem_static_estimates b A 0 2 (fun _ : Fin 3 => 0)
          aux_lim_lem_mean_exit_meanExitPairSides0 aux_lim_lem_mean_exit_meanExitPairSides1 K B →
        LocalExitCertificate A b (D * K ^ e) := by
  obtain ⟨C, Bm, hC, _hBm, hdet⟩ :=
    aux_tight_lem_subharmonic_det hd B (1 / 9) hB (by norm_num)
  let D := max 1 (max C ((1 / 3 : ℝ) ^ (-B)))
  let e := max 1 Bm
  have hD : 1 ≤ D := le_max_left _ _
  have hCD : C ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hgapD : (1 / 3 : ℝ) ^ (-B) ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have he : 1 ≤ e := le_max_left _ _
  refine ⟨D, e, hD, he, ?_⟩
  intro b A K hb hA hbpos hApos hK hest
  have hk0 : 0 ≤ K := zero_le_one.trans hK
  have hke : K ≤ K ^ e := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hK he
  have hcm : C * K ^ Bm ≤ D * K ^ e := mul_le_mul hCD
    (Real.rpow_le_rpow_of_exponent_le hK (le_max_right _ _))
    (Real.rpow_nonneg hk0 _) (zero_le_one.trans hD)
  have hchi := hest.2.2 (0 : Fin 3) 0 0 (by norm_num)
  have hR0 : ((1 - ((0 : ℕ) : ℝ) / 2 ^ (0 : ℕ)) * aux_lim_lem_mean_exit_meanExitPairSides0 0 +
      ((0 : ℕ) : ℝ) / 2 ^ (0 : ℕ) * aux_lim_lem_mean_exit_meanExitPairSides1 0) / 2 = (1 / 6 : ℝ) := by
    norm_num [aux_lim_lem_mean_exit_meanExitPairSides0, aux_lim_lem_mean_exit_meanExitPairSides1, Fin.ext_iff]
  have hR1 : ((1 - ((0 + 1 : ℕ) : ℝ) / 2 ^ (0 : ℕ)) * aux_lim_lem_mean_exit_meanExitPairSides0 0 +
      ((0 + 1 : ℕ) : ℝ) / 2 ^ (0 : ℕ) * aux_lim_lem_mean_exit_meanExitPairSides1 0) / 2 = (1 / 2 : ℝ) := by
    norm_num [aux_lim_lem_mean_exit_meanExitPairSides0, aux_lim_lem_mean_exit_meanExitPairSides1, Fin.ext_iff]
  rw [hR1, hR0] at hchi
  rw [show (aux_lim_lem_mean_exit_meanExitPairSides1 0 - aux_lim_lem_mean_exit_meanExitPairSides0 0) / 2 ^ (0 : ℕ) / 2 =
    (1 / 3 : ℝ) by norm_num [aux_lim_lem_mean_exit_meanExitPairSides0, aux_lim_lem_mean_exit_meanExitPairSides1, Fin.ext_iff]] at hchi
  obtain ⟨chi, hchi01, hchi1, _hsupport, hcutoff⟩ := hchi
  refine ⟨chi, hchi01, hchi1, ?_, ?_⟩
  · have hcut := hcutoff (0 : Vec d) 1 (by norm_num) le_rfl
    have hinter : Metric.ball (0 : Vec d) 1 ∩ Metric.ball (0 : Vec d) (1 / 2) =
        Metric.ball 0 (1 / 2) :=
      inter_eq_right.mpr (Metric.ball_subset_ball (by norm_num))
    rw [hinter, Real.one_rpow, mul_one] at hcut
    have hAb := SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
      hA hApos (Metric.isBounded_ball (x := (0 : Vec d)) (r := (1 / 2 : ℝ)))
    have hE := killedCoefficientEnergy_eq_ofReal_energy hAb chi.toH1Function
    change (∫⁻ y in Metric.ball (0 : Vec d) (1 / 2),
      ENNReal.ofReal (A y * vecDot (chi.grad y) (chi.grad y))) =
        ENNReal.ofReal (energy A (Metric.ball 0 (1 / 2)) chi.toH1Function) at hE
    rw [hE] at hcut
    have henergy : energy A (Metric.ball 0 (1 / 2)) chi.toH1Function ≤
        K * (1 / 3 : ℝ) ^ (-B) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcut
    refine henergy.trans ?_
    calc
      K * (1 / 3 : ℝ) ^ (-B) ≤ K * D := mul_le_mul_of_nonneg_left hgapD hk0
      _ ≤ K ^ e * D := mul_le_mul_of_nonneg_right hke (zero_le_one.trans hD)
      _ = _ := mul_comm _ _
  · intro w hw0 hwM hsub
    obtain ⟨Mw, hwM⟩ := hwM
    obtain ⟨w', hgrad, hae, hw'0, hw'M⟩ :=
      aux_tight_lem_subharmonic_regularize w hw0 hwM
    have hsub' : IsWeakSubSolutionOn A (Metric.ball (0 : Vec d) (1 / 6)) w' := by
      intro psi hpsi
      simpa only [hgrad] using hsub psi hpsi
    have hcoer := aux_tight_lem_subharmonic_coer_of_est hest (1 : Fin 3)
    rw [show aux_lim_lem_mean_exit_meanExitPairSides1 (1 : Fin 3) / 2 = (1 / 6 : ℝ) by
      norm_num [aux_lim_lem_mean_exit_meanExitPairSides1, Fin.ext_iff]] at hcoer
    have hcut := aux_tight_lem_subharmonic_cut_of_est hest (2 : Fin 3)
      (δ := 1 / 9) (z := 0) rfl
      (by norm_num [aux_lim_lem_mean_exit_meanExitPairSides0, Fin.ext_iff]) (by norm_num [aux_lim_lem_mean_exit_meanExitPairSides1, Fin.ext_iff])
    have hmass : ∀ (x : Vec d) (r : ℝ), 0 < r → r ≤ 1 →
        Metric.ball x r ⊆ Metric.ball (0 : Vec d) (1 / 6) →
        ENNReal.ofReal (K⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
          volume.withDensity (fun y => ENNReal.ofReal (b y)) (Metric.ball x r) ∧
        volume.withDensity (fun y => ENNReal.ofReal (b y)) (Metric.ball x r) ≤
          ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2)) := by
      intro x r hr hr1 hball
      exact hest.1 x r hr hr1 (hball.trans (Metric.ball_subset_ball (by norm_num)))
    have hmoser := hdet b A K 0 (1 / 6) 0 hb hA hbpos hApos hK
      (by norm_num) (Metric.ball_subset_ball (by norm_num)) hmass hcoer hcut
      w' hw'0 ⟨_, hw'M⟩ hsub'
    norm_num only at hmoser
    have hI : (∫⁻ y in Metric.ball (0 : Vec d) (1 / 6),
        ENNReal.ofReal (w'.toFun y ^ 2 * b y)) =
        ∫⁻ y in Metric.ball (0 : Vec d) (1 / 6), ENNReal.ofReal (w.toFun y ^ 2 * b y) :=
      lintegral_congr_ae (hae.mono fun y hy => by simp only [hy])
    rw [hI] at hmoser
    have haew := ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_ball (by norm_num : (1 / 18 : ℝ) ≤ 1 / 6)) hae
    filter_upwards [hmoser, haew] with x hx hxw
    rw [hxw] at hx
    exact hx.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hcm) _)

end SubdiffusiveProcess.Section10
end aux_lim_lem_mean_exit_inline_1

/- Inlined proved source application: SubdiffusiveProcess.Section10.MeanExitStaticMomentBank. -/
noncomputable section aux_lim_lem_mean_exit_inline_2

/-! The exact Section 8 static statement supplies the actual local moment bank
on every finite/top physical sample, including m>L. This source application
never applies the unproved static or subharmonic source constant. -/
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Filter
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.Section10.PhysicalAttachment SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10
open Paper PhysicalTightness



theorem aux_lim_lem_mean_exit_meanExit_static_local_definitions {d : ℕ} (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) (z : Vec d) (omega : AnchoredC11Sample d) (K B : ℝ) :
    (let j : ℕ := match L with | ⊤ => m | (n : ℕ) => min m n
     let cz : ℝ := coefficientAt M L omega z / aCutoff M j omega.1 z
     let b : Vec d → ℝ := fun x => cz⁻¹ * coefficientAt M L omega (z + (3 : ℝ) ^ m • x)
     aux_tight_lem_static_estimates b (fun x => (ahom M j)⁻¹ * b x) 0 2
       (fun _ : Fin 3 => 0) aux_lim_lem_mean_exit_meanExitPairSides0 aux_lim_lem_mean_exit_meanExitPairSides1 K B) ↔
    aux_tight_lem_static_estimates (localSpeed M L m z omega) (localCoefficient M L m z omega)
      0 2 (fun _ : Fin 3 => 0) aux_lim_lem_mean_exit_meanExitPairSides0 aux_lim_lem_mean_exit_meanExitPairSides1 K B := by
  cases L using WithTop.recTopCoe with
  | top =>
    unfold PhysicalLocalTransport.localCoefficient PhysicalLocalTransport.localSpeed
      PhysicalLocalTransport.localFactor
    simp only [PhysicalLocalTransport.activeScale, WithTop.untopD_top, min_self]
  | coe l => rfl

/-- B and the deterministic power e precede Q; the input static order e*Q
precedes delta. C precedes every L,m,z on the actual anchored law. -/
theorem aux_lim_lem_mean_exit_physicalLocalExitMomentBank_of_tightStatic {d : ℕ} (hd : 1 ≤ d)
    (hStatic : aux_lim_lem_mean_exit_TightStaticEstimateInput) : PhysicalLocalExitMomentBank d := by
  obtain ⟨B, hB, hstatic⟩ := hStatic d 0 2 (by norm_num) 3 (fun _ => 0)
    aux_lim_lem_mean_exit_meanExitPairSides0 aux_lim_lem_mean_exit_meanExitPairSides1 aux_lim_lem_mean_exit_meanExitPairSides_pos aux_lim_lem_mean_exit_meanExitPairSides_subset
  obtain ⟨D, e, hD, he, hdet⟩ := aux_lim_lem_mean_exit_localExitCertificate_of_static d hd B hB
  intro Q hQ
  obtain ⟨δ, hδ, hmodels⟩ := hstatic (e * Q) (one_le_mul_of_one_le_of_one_le he hQ)
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨C, hC, hlocal⟩ := hmodels M hM
  refine ⟨D ^ Q * C, mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hD) _) hC, ?_⟩
  intro L m z
  obtain ⟨K, hK, hKone, hKmoment, hKstatic⟩ := hlocal L m z
  let F : AnchoredC11Sample d → ℝ := fun omega => D * K omega ^ e
  have hFm : Measurable F := measurable_const.mul (hK.pow measurable_const)
  have hFone : ∀ omega, 1 ≤ F omega := fun omega =>
    one_le_mul_of_one_le_of_one_le hD (Real.one_le_rpow (hKone omega) (zero_le_one.trans he))
  have hm := lintegral_factor_power_moment (physicalLaw M).toMeasure hK
    (fun omega => zero_le_one.trans (hKone omega)) (zero_le_one.trans hD) hKmoment
  refine ⟨F, hFm, hFone, hm, ?_⟩
  filter_upwards [hKstatic] with omega hest
  have hest' := (aux_lim_lem_mean_exit_meanExit_static_local_definitions M L m z omega (K omega) B).mp hest
  exact hdet _ _ _ (continuous_localSpeed M L m z omega)
    (continuous_const.mul (continuous_localSpeed M L m z omega))
    (localSpeed_pos M L m z omega)
    (fun x => mul_pos (inv_pos.mpr (ahom_pos M _)) (localSpeed_pos M L m z omega x))
    (hKone omega) hest'

end SubdiffusiveProcess.Section10
end aux_lim_lem_mean_exit_inline_2



noncomputable section aux_lim_lem_mean_exit_inline_3

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace Paper

/-- The actual two-projection static bank; its standing analytic packages and
response input are supplied by proved constructors, before any model application. -/
theorem aux_lim_lem_mean_exit_inlined_physical_sobolev_bilateral_static_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ B : ℝ, 0 < B ∧ ∀ Q : ℝ, 1 ≤ Q →
      ∃ δ : ℝ, 0 < δ ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ δ →
        ∃ C : ℝ, 0 < C ∧
          ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
            ∀ N : ℕ, ∃ K : BilateralField d → ℝ,
              Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
              (∫⁻ ω, ENNReal.ofReal (K ω ^ Q) ∂(chaosSampleLaw M).toMeasure) ≤
                ENNReal.ofReal C ∧
              ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure,
                PhysicalStaticBounds (cutoffSpeedDensity M H ω N)
                  (cutoffCoefficient M H ω N) B (K ω) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  let Jc := Classical.choice (inputs_J_witness d hd)
  let Pc := Classical.choice (inputs_poincare_witness d hd Jc)
  let Sf := Classical.choice (inputs_Sf_witness d hd)
  obtain ⟨Cresp, hCresp, hresponses⟩ := lfsgs_response_bank hd
  refine ⟨5, by norm_num, ?_⟩
  intro Q hQ
  obtain ⟨δup, hδup, hupper⟩ := aux_tight_static_upper hd Q hQ
  obtain ⟨δcoer, hδcoer, hcoercivity⟩ := tight_static_coer hd Jc Pc Sf Q hQ
  refine ⟨min δup δcoer, lt_min hδup hδcoer, ?_⟩
  intro M hM
  obtain ⟨Rm, _⟩ := hresponses M
  obtain ⟨Cup, hCup, hupperM⟩ := hupper M (hM.trans (min_le_left _ _)) 4 (by norm_num)
  obtain ⟨Cc, hCc, hcoerM⟩ := hcoercivity M Rm
    (hM.trans (min_le_right _ _)) 4 (by norm_num)
  refine ⟨Cup + Cc, by positivity, ?_⟩
  intro H hH N
  obtain ⟨Kup, hKup, hKupone, hKupm, hmass⟩ := hupperM H hH
  obtain ⟨Kc, hKc, hKcone, hKcm, hcoer⟩ := hcoerM H hH N
  let K : BilateralField d → ℝ := fun ω => max (Kup ω) (Kc ω)
  refine ⟨K, hKup.max hKc, fun ω => (hKupone ω).trans (le_max_left _ _), ?_, ?_⟩
  · exact lintegral_max_rpow_le (chaosSampleLaw M).toMeasure hKup
      (fun ω => zero_le_one.trans (hKupone ω)) (fun ω => zero_le_one.trans (hKcone ω))
      (zero_le_one.trans hQ) hCup.le hCc.le hKupm hKcm
  · filter_upwards [hmass, hcoer] with ω hm hc
    constructor
    · intro x hx r hr hr1
      have hx' : x ∈ Metric.ball (0 : SpatialCoordinates d) ((4 : ℝ) / 2) := by
        simpa only [show (4 : ℝ) / 2 = 2 by norm_num] using hx
      exact (hm N x r hr hr1 hx').trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _)))
    · intro w
      have hh := (hc (1 / 2) (by norm_num) (by norm_num)).2
      have hrad : (4 : ℝ) * ((1 / 2 : ℚ) : ℝ) / 2 = 1 := by norm_num
      have hden : ((1 / 2 : ℚ).den : ℝ) = 2 := by norm_num
      rw [hrad, hden] at hh
      exact (hh w).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (by norm_num) (5 : ℝ)))) _)

end Paper
end aux_lim_lem_mean_exit_inline_3



noncomputable section aux_lim_lem_mean_exit_inline_4

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
namespace Paper



theorem aux_lim_lem_mean_exit_inlined_physical_sobolev_top_static_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ B : ℝ, 0 < B ∧ ∀ Q : ℝ, 1 ≤ Q →
      ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
        ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (z : SpatialCoordinates d),
          ∃ Kphys : AnchoredC11Sample d → ℝ, Measurable Kphys ∧
            (∀ ω, 1 ≤ Kphys ω) ∧
            (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ Q) ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤
              ENNReal.ofReal C ∧
            ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
              PhysicalStaticBounds (localSpeed M ⊤ m z ω) (localCoefficient M ⊤ m z ω)
                B (Kphys ω) := by
  obtain ⟨B, hB, hbank⟩ := aux_lim_lem_mean_exit_inlined_physical_sobolev_bilateral_static_bank hd
  refine ⟨B, hB, ?_⟩
  intro Q hQ
  obtain ⟨δ, hδ, hmodels⟩ := hbank Q hQ
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨C, hC, hcutoffs⟩ := hmodels M hM
  refine ⟨1 + 2 * C, by positivity, ?_⟩
  intro m z
  obtain ⟨K, hK, hKone, hKm, hKs⟩ := hcutoffs (infraredField M) (infraredField_spec M) m
  let Kn : NativeEnvironment d → ℝ := K ∘ bilateralEnvironment
  have hKn : Measurable Kn := hK.comp (bilateralEnvironment_preserving M).measurable
  have hKnm : (∫⁻ η, ENNReal.ofReal (Kn η ^ Q) ∂nativeLaw M) ≤ ENNReal.ofReal C := by
    rw [← (bilateralEnvironment_preserving M).map_eq] at hKm
    simpa only [Kn, Function.comp_apply] using
      (lintegral_map (ENNReal.measurable_ofReal.comp (hK.pow measurable_const))
        (bilateralEnvironment_preserving M).measurable).symm.trans_le hKm
  have hKns : ∀ᵐ η ∂nativeLaw M,
      PhysicalStaticBounds (localSpeed M ⊤ m z (physicalEnvironment M m z η))
        (localCoefficient M ⊤ m z (physicalEnvironment M m z η)) B (Kn η) := by
    filter_upwards [(bilateralEnvironment_preserving M).quasiMeasurePreserving.ae hKs,
      top_local_identification M m z] with η hη heq
    have hb : localSpeed M ⊤ m z (physicalEnvironment M m z η) =
        cutoffSpeedDensity M (infraredField M) (bilateralEnvironment η) m :=
      funext fun x => (heq x).1
    have ha : localCoefficient M ⊤ m z (physicalEnvironment M m z η) =
        cutoffCoefficient M (infraredField M) (bilateralEnvironment η) m :=
      funext fun x => (heq x).2
    rw [hb, ha]
    exact hη
  haveI : StandardBorelSpace (AnchoredC11Sample d) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d).standardBorel
  haveI : MeasurableEq (AnchoredC11Sample d) := by
    let u := upgradeStandardBorel (AnchoredC11Sample d)
    letI : TopologicalSpace (AnchoredC11Sample d) := u.toTopologicalSpace
    letI : BorelSpace (AnchoredC11Sample d) := u.toBorelSpace
    letI : PolishSpace (AnchoredC11Sample d) := u.toPolishSpace
    infer_instance
  haveI : Nonempty (NativeEnvironment d) := ⟨fun _ => zeroNativePotentialField d⟩
  exact physicalBank_measurable_descent (nativeLaw M) (PhysicalAttachment.physicalLaw M).toMeasure
    (physicalEnvironment_preserving M m z) hKn (fun η => hKone _) (by linarith) hC.le hKnm
    (fun ω k => PhysicalStaticBounds (localSpeed M ⊤ m z ω) (localCoefficient M ⊤ m z ω) B k)
    (fun ω k k' hkk hs => hs.mono hkk) hKns

end Paper
end aux_lim_lem_mean_exit_inline_4



noncomputable section aux_lim_lem_mean_exit_inline_5

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10 TopologicalSpace
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open scoped ENNReal
namespace Paper

/-- Finite m<=l physical bank, with the literal truncated infrared correction,
true anchored law, saturated source normalization and measurable marginal descent.
The static order 2Q and infrared exponential order 4Q precede the threshold. -/
theorem aux_lim_lem_mean_exit_inlined_physical_sobolev_finite_static_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ B : ℝ, 0 < B ∧ ∀ Q : ℝ, 1 ≤ Q →
      ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
        ∃ C : ℝ, 0 < C ∧ ∀ (l m : ℕ), m ≤ l → ∀ z : SpatialCoordinates d,
          ∃ Kphys : AnchoredC11Sample d → ℝ, Measurable Kphys ∧
            (∀ ω, 1 ≤ Kphys ω) ∧
            (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ Q) ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤
              ENNReal.ofReal C ∧
            ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
              PhysicalStaticBounds (localSpeed M l m z ω) (localCoefficient M l m z ω)
                B (Kphys ω) := by
  let S : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall 0 4, isCompact_closedBall _ _⟩
  obtain ⟨Ct, Cf, hCt, hCf, htail⟩ := physical_infrared_multiplier_bank hd S
  obtain ⟨B, hB, hbank⟩ := aux_lim_lem_mean_exit_inlined_physical_sobolev_bilateral_static_bank hd
  refine ⟨B, hB, ?_⟩
  intro Q hQ
  obtain ⟨δ, hδ, hmodels⟩ := hbank (2 * Q) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨Cs, hCs, hcutoffs⟩ := hmodels M hM
  let Cr := 2 * Real.exp (Ct * (4 * Q) ^ 2 * M.delta ^ 2) +
    2 * Real.exp (Cf * (4 * Q) ^ 2 * M.delta ^ 2)
  have hCr : 0 < Cr := by dsimp [Cr]; positivity
  refine ⟨1 + 2 * (Cr + Cs), by positivity, ?_⟩
  intro l m hml z
  obtain ⟨K, hK, hKone, hKm, hKs⟩ := hcutoffs (infraredField M) (infraredField_spec M) m
  obtain ⟨R, hR, hRone, hRm, hReq⟩ := htail M (l - m) Q hQ
  let Kn : NativeEnvironment d → ℝ := K ∘ bilateralEnvironment
  have hKn : Measurable Kn := hK.comp (bilateralEnvironment_preserving M).measurable
  have hKnm : (∫⁻ η, ENNReal.ofReal (Kn η ^ (2 * Q)) ∂nativeLaw M) ≤ ENNReal.ofReal Cs := by
    rw [← (bilateralEnvironment_preserving M).map_eq] at hKm
    simpa only [Kn, Function.comp_apply] using
      (lintegral_map (ENNReal.measurable_ofReal.comp (hK.pow measurable_const))
        (bilateralEnvironment_preserving M).measurable).symm.trans_le hKm
  let Ktotal : NativeEnvironment d → ℝ := fun η => R η * Kn η
  have hKt : Measurable Ktotal := hR.mul hKn
  have hKtone : ∀ η, 1 ≤ Ktotal η := fun η =>
    one_le_mul_of_one_le_of_one_le (hRone η) (hKone _)
  have hKtm : (∫⁻ η, ENNReal.ofReal (Ktotal η ^ Q) ∂nativeLaw M) ≤
      ENNReal.ofReal (Cr + Cs) := physicalBank_product_moment (nativeLaw M) hR
        (fun η => zero_le_one.trans (hRone η)) (fun η => zero_le_one.trans (hKone _))
        hCr.le hCs.le hRm hKnm
  have hKts : ∀ᵐ η ∂nativeLaw M,
      PhysicalStaticBounds (localSpeed M l m z (physicalEnvironment M m z η))
        (localCoefficient M l m z (physicalEnvironment M m z η)) B (Ktotal η) := by
    filter_upwards [(bilateralEnvironment_preserving M).quasiMeasurePreserving.ae hKs,
      hReq, finite_local_identification M l m z] with η hs hRdef heq
    have hb : ∀ y ∈ Metric.ball (0 : SpatialCoordinates d) 4,
        finiteLocalSpeed M l m (bilateralEnvironment η) y ≤
          R η * cutoffSpeedDensity M (infraredField M) (bilateralEnvironment η) m y := by
      intro y hy
      rw [hRdef]
      exact (finite_multiplier_bounds M hml S η (Metric.ball_subset_closedBall hy)).2
    have ha : ∀ y ∈ Metric.ball (0 : SpatialCoordinates d) 1,
        cutoffCoefficient M (infraredField M) (bilateralEnvironment η) m y ≤
          R η * finiteLocalCoefficient M l m (bilateralEnvironment η) y := by
      intro y hy
      have hyS : y ∈ (S : Set (SpatialCoordinates d)) :=
        Metric.ball_subset_closedBall (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 4) hy)
      have hlower := (finite_multiplier_bounds M hml S η hyS).1
      let T := compactPotentialC1Norm S (positiveAnchoredInfraredTruncation η (l - m)) +
        ‖(infraredField M (bilateralEnvironment η)).restrict (S : Set (SpatialCoordinates d))‖
      have hh := mul_le_mul_of_nonneg_left hlower (Real.exp_pos T).le
      change Real.exp T * (Real.exp (-T) * _) ≤ _ at hh
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hh
      change (ahom M m)⁻¹ * cutoffSpeedDensity M (infraredField M) (bilateralEnvironment η) m y ≤
        R η * ((ahom M (min m l))⁻¹ * finiteLocalSpeed M l m (bilateralEnvironment η) y)
      rw [min_eq_left hml, hRdef]
      have hp := mul_le_mul_of_nonneg_left hh (inv_pos.mpr (ahom_pos M m)).le
      convert hp using 1; ring
    have hf := hs.multiplier (zero_le_one.trans (hRone η)) hb ha
    have hb' : localSpeed M l m z (physicalEnvironment M m z η) =
        finiteLocalSpeed M l m (bilateralEnvironment η) := funext fun x => (heq x).1
    have ha' : localCoefficient M l m z (physicalEnvironment M m z η) =
        finiteLocalCoefficient M l m (bilateralEnvironment η) := funext fun x => (heq x).2
    rw [hb', ha']
    exact hf
  haveI : StandardBorelSpace (AnchoredC11Sample d) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d).standardBorel
  haveI : MeasurableEq (AnchoredC11Sample d) := by
    let u := upgradeStandardBorel (AnchoredC11Sample d)
    letI : TopologicalSpace (AnchoredC11Sample d) := u.toTopologicalSpace
    letI : BorelSpace (AnchoredC11Sample d) := u.toBorelSpace
    letI : PolishSpace (AnchoredC11Sample d) := u.toPolishSpace
    infer_instance
  haveI : Nonempty (NativeEnvironment d) := ⟨fun _ => zeroNativePotentialField d⟩
  exact physicalBank_measurable_descent (nativeLaw M) (PhysicalAttachment.physicalLaw M).toMeasure
    (physicalEnvironment_preserving M m z) hKt hKtone (by linarith) (by positivity) hKtm
    (fun ω k => PhysicalStaticBounds (localSpeed M l m z ω) (localCoefficient M l m z ω) B k)
    (fun ω k k' hkk hs => hs.mono hkk) hKts

end Paper
end aux_lim_lem_mean_exit_inline_5



noncomputable section aux_lim_lem_mean_exit_inline_6

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
namespace Paper

/-- The two completed physical branches, with one exponent and one moment
constant before L,m,z. This bounded export explicitly excludes finite l<m. -/
theorem aux_lim_lem_mean_exit_inlined_physical_sobolev_static_bank_small_scale {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ B : ℝ, 0 < B ∧ ∀ Q : ℝ, 1 ≤ Q →
      ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
        ∃ C : ℝ, 0 < C ∧ ∀ (L : WithTop ℕ) (m : ℕ),
          (L = ⊤ ∨ ∃ l : ℕ, L = l ∧ m ≤ l) → ∀ z : SpatialCoordinates d,
          ∃ Kphys : AnchoredC11Sample d → ℝ, Measurable Kphys ∧
            (∀ ω, 1 ≤ Kphys ω) ∧
            (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ Q) ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤
              ENNReal.ofReal C ∧
            ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
              PhysicalStaticBounds (localSpeed M L m z ω) (localCoefficient M L m z ω)
                B (Kphys ω) := by
  obtain ⟨Bt, hBt, htop⟩ := aux_lim_lem_mean_exit_inlined_physical_sobolev_top_static_bank hd
  obtain ⟨Bf, hBf, hfinite⟩ := aux_lim_lem_mean_exit_inlined_physical_sobolev_finite_static_bank hd
  refine ⟨max Bt Bf, hBt.trans_le (le_max_left _ _), ?_⟩
  intro Q hQ
  obtain ⟨δt, hδt, htm⟩ := htop Q hQ
  obtain ⟨δf, hδf, hfm⟩ := hfinite Q hQ
  refine ⟨min δt δf, lt_min hδt hδf, ?_⟩
  intro M hM
  obtain ⟨Ct, hCt, ht⟩ := htm M (hM.trans (min_le_left _ _))
  obtain ⟨Cf, hCf, hf⟩ := hfm M (hM.trans (min_le_right _ _))
  refine ⟨max Ct Cf, hCt.trans_le (le_max_left _ _), ?_⟩
  intro L m hscope z
  rcases hscope with hL | ⟨l, hL, hml⟩
  · subst L
    obtain ⟨K, hK, hone, hmom, hs⟩ := ht m z
    refine ⟨K, hK, hone, hmom.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)), ?_⟩
    filter_upwards [hs] with ω hω
    exact hω.exponent_mono (zero_le_one.trans (hone ω)) (le_max_left _ _)
  · subst L
    obtain ⟨K, hK, hone, hmom, hs⟩ := hf l m hml z
    refine ⟨K, hK, hone, hmom.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)), ?_⟩
    filter_upwards [hs] with ω hω
    exact hω.exponent_mono (zero_le_one.trans (hone ω)) (le_max_right _ _)

end Paper
end aux_lim_lem_mean_exit_inline_6



noncomputable section aux_lim_lem_mean_exit_inline_7

/-! The literal native H10 coercivity projection from the lower ellipticity
factor on the scale-(m+1) padded physical cube. No microcube partition is used. -/
open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Section10
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open scoped ENNReal
namespace Paper

/-- Exact rescaling of the unit native chart to the unnormalized physical
cutoff field. Only descendants of the unit root are read by lambdaSq. -/
theorem aux_lim_lem_mean_exit_inlined_physical_large_chart_lambda {d : ℕ} [NeZero d]
    (J : in_J d) (M : GMCModel d) (l n : ℕ) (ω : PotentialSample d)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hb : (b.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))]
        fun x => aCutoff M l ω ((3 : ℝ) ^ n • x)) :
    J.lam 0 1 one_pos b 0 1 s 1 =
      Ch04.lambdaSqCoeffField (originCube d (n : ℤ)) s (.finite 1)
        (aCutoffRegCoeffField M l ω) := by
  let F := aCutoffRegCoeffField M l ω
  have hF := aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M l ω
  have hG := hF.of_rescaleCoeffField n
  let G := Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField (rescaleReg n F) hG
  rw [J.lam_eq 0 1 one_pos b 0 1 one_pos Set.Subset.rfl s hs 1 le_rfl]
  simp only [show (1 : ℝ≥0∞) ≠ ⊤ by simp, ↓reduceIte, ENNReal.toReal_one]
  have hb0 : (b.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (openCubeSet (originCube d 0))]
        fun x => aCutoff M l ω ((3 : ℝ) ^ n • x) := by
    simpa only [← centeredCube_zero_eq_openCubeSet_originCube (d := d) 0 one_pos,
      zpow_zero] using hb
  have heq : Ch02.lambdaSq (originCube d 0) s (.finite 1) (J.chart 0 1 one_pos b 0 1) =
      Ch02.lambdaSq (originCube d 0) s (.finite 1) G := by
    apply SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.lambdaSq_eq_of_descendantAEEq
    intro k R hR
    have hsub := openCubeSet_subset_of_mem_descendantsAtScale
      (descendant_scale_le_of_mem_descendantsAtScale hR) hR
    have hchart := J.chart_eq 0 1 one_pos b 0 1 one_pos Set.Subset.rfl R hsub
    have hbR := hb0.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))
    filter_upwards [hchart, hbR] with x hx hbx
    simp only [Pi.zero_apply, zero_add, one_mul] at hx
    simpa only [G, F, Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField,
      rescaleReg_apply, aCutoffRegCoeffField_apply, zero_add, one_mul] using hx.trans
        (congrArg scalarMatrix hbx)
  rw [heq]
  have hnorm : Ch02.lambdaSq (originCube d 0) s (.finite 1) G =
      Ch04.lambdaSqCoeffField (originCube d 0) s (.finite 1) (rescaleReg n F) := by
    unfold Ch04.lambdaSqCoeffField
    rw [dif_pos hG]
  rw [hnorm]
  simpa only [Nat.add_zero, Int.ofNat_zero] using
    Ch04.lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      hF n 0 s (.finite 1)

/-- Every native H10 test on the unit ball, with actual lower-integral energy.
The saturated normalization is ahom_l and the padding cost is deterministic. -/
theorem aux_lim_lem_mean_exit_inlined_physical_large_killed_of_lambda {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ D : ℝ, 0 < D ∧ ∀ M : GMCModel d, ∀ l m : ℕ, l ≤ m →
      ∀ z : SpatialCoordinates d, ∀ ω : AnchoredC11Sample d,
        ∀ w : H10Function (Metric.ball (0 : SpatialCoordinates d) 1),
          killedFractionalEnergy (Metric.ball (0 : SpatialCoordinates d) 1) w.toFun +
            ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) 1, ENNReal.ofReal (w.toFun x ^ 2) ≤
          ENNReal.ofReal (D * (ahom M l *
            (Ch04.lambdaSqCoeffField (originCube d ((m + 1 : ℕ) : ℤ))
              (1 / 16) (.finite 1) (aCutoffRegCoeffField M l
                (translatePotentialSample z ω.val)))⁻¹)) *
            killedCoefficientEnergy (localCoefficient M l m z ω) w.toH1Function := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  let J := Classical.choice (inputs_J_witness d hd)
  let P := Classical.choice (inputs_poincare_witness d hd J)
  let S := Classical.choice (inputs_Sf_witness d hd)
  obtain ⟨Cb, hCb, hbesov⟩ := lane4_besov_h34_coercivity d hd J P S (1 / 16) (by norm_num)
  obtain ⟨Cd, hCd, htransfer⟩ := aux_hcoer_transfer_killed hd S
  let D := Cd * Cb * ((3 : ℝ) ^ (1 / 2 : ℝ) + (3 : ℝ) ^ 2)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro M l m hlm z ω
  let ωz := translatePotentialSample z ω.val
  let f := fun x : SpatialCoordinates d => aCutoff M l ωz ((3 : ℝ) ^ (m + 1) • x)
  have hf : Continuous f := (continuous_aCutoff M l ωz).comp (continuous_const.smul continuous_id)
  have hfpos : ∀ x, 0 < f x := fun x => aCutoff_pos M l ωz _
  let b := continuousCubeCoefficient 0 1 one_pos f hf hfpos
  have hb := continuousCubeCoefficient_ae 0 1 one_pos f hf hfpos
  have hlam := aux_lim_lem_mean_exit_inlined_physical_large_chart_lambda J M l (m + 1) ωz (1 / 16) (by norm_num) b hb
  have hlampos := J.lam_pos 0 1 one_pos b 0 1 (1 / 16) 1
  let lamval := J.lam 0 1 one_pos b 0 1 (1 / 16) 1
  let A := localCoefficient M l m z ω
  have hAeq : A = fun y => (ahom M l)⁻¹ * aCutoff M l ω.val (z + (3 : ℝ) ^ m • y) := by
    unfold A localCoefficient localSpeed
    rw [activeScale_coe, min_eq_right hlm, localFactor_eq_one M hlm z ω]
    simp only [inv_one, one_mul]
    rfl
  have hAc : Continuous A := by
    rw [hAeq]
    exact continuous_const.mul ((continuous_aCutoff M l ω.val).comp
      (continuous_const.add (continuous_const.smul continuous_id)))
  have hAp : ∀ y, 0 < A y := by
    rw [hAeq]; intro y
    exact mul_pos (inv_pos.mpr (ahom_pos M l)) (aCutoff_pos M l ω.val _)
  have hcoef : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      (ahom M l)⁻¹ * b.val x ≤ A (0 + (3 : ℝ) • x) := by
    filter_upwards [hb] with x hx
    rw [hx, hAeq, zero_add]
    apply le_of_eq
    congr 1
    change aCutoff M l ωz ((3 : ℝ) ^ (m + 1) • x) = _
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.aCutoff_translatePotentialSample]
    congr 1
    simp only [pow_succ, mul_smul, add_comm]
  have ht := htransfer 0 3 (by norm_num) A hAc hAp b (ahom M l)⁻¹ (Cb * lamval⁻¹)
    (inv_pos.mpr (ahom_pos M l)) (mul_nonneg hCb.le (inv_nonneg.mpr hlampos.le))
    hcoef (fun v => (hbesov 0 one_pos b).1 v |>.2)
  have hc : Cd * (Cb * lamval⁻¹) * ((ahom M l)⁻¹)⁻¹ *
      ((3 : ℝ) ^ (1 / 2 : ℝ) + (3 : ℝ) ^ 2) =
      D * (ahom M l * (Ch04.lambdaSqCoeffField (originCube d ((m + 1 : ℕ) : ℤ))
        (1 / 16) (.finite 1) (aCutoffRegCoeffField M l ωz))⁻¹) := by
    rw [inv_inv, ← hlam]
    dsimp [D, lamval]; ring
  rw [hc] at ht
  intro w
  have hh := aux_hcoer_H10_omega A (s := 2) (R := 3) (by norm_num)
    (ENNReal.ofReal (D * (ahom M l * (Ch04.lambdaSqCoeffField
      (originCube d ((m + 1 : ℕ) : ℤ)) (1 / 16) (.finite 1)
        (aCutoffRegCoeffField M l ωz))⁻¹))) ht
  rw [show (2 : ℝ) / 2 = 1 by norm_num] at hh
  exact hh w

end Paper
end aux_lim_lem_mean_exit_inline_7



noncomputable section aux_lim_lem_mean_exit_inline_8

/-! The actual retained-window killed bank and actual physical-law consumer.
Mass is deliberately supplied by its separate worker projection. -/
open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open scoped ENNReal
namespace Paper

/-- The killed projection, uniform in the retained length and omitted depth.
No response or static estimate is an input to this actual-model theorem. -/
theorem aux_lim_lem_mean_exit_inlined_physical_retained_window_killed_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∀ Q : ℝ, 1 ≤ Q → ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ δ → ∀ l k : ℕ, 1 ≤ k →
        ∃ K : (Fin (l + 1) → C(SpatialCoordinates d, ℝ)) → ℝ,
          Measurable K ∧ (∀ ξ, 1 ≤ K ξ) ∧
          (∫⁻ ξ, ENNReal.ofReal (K ξ ^ Q) ∂windowLaw M l (l + k)) ≤ ENNReal.ofReal C ∧
          ∀ᵐ ξ ∂windowLaw M l (l + k),
            PhysicalKilledCoercivity (retainedWindowCoefficient M l ξ) (K ξ) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨D, hD, hdet⟩ := aux_lim_lem_mean_exit_inlined_physical_large_killed_of_lambda hd
  let D0 := max 1 D
  have hD0 : 1 ≤ D0 := le_max_left _ _
  have hDD0 : D ≤ D0 := le_max_right _ _
  intro Q hQ
  obtain ⟨δ, C0, hδ, hC0, hbank⟩ := physical_large_ellipticity_physical_bank hd Q hQ
  let C1 := D0 ^ Q * C0
  have hC1 : 0 < C1 := mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hD0) _) hC0
  refine ⟨δ, 1 + 2 * C1, hδ, by positivity, ?_⟩
  intro M hM l k _hk
  let m := l + k
  obtain ⟨K0, hK0, hone, hm0, hs0⟩ := hbank M hM l (m + 1) (by dsimp [m]; omega) 0
  let Kphys := fun ω : AnchoredC11Sample d => D0 * K0 ω
  have hKm : (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ Q)
      ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal C1 := by
    calc
      _ = ENNReal.ofReal (D0 ^ Q) * ∫⁻ ω, ENNReal.ofReal (K0 ω ^ Q)
            ∂(PhysicalAttachment.physicalLaw M).toMeasure := by
        simp only [Kphys, Real.mul_rpow (zero_le_one.trans hD0)
          (zero_le_one.trans (hone _)), ENNReal.ofReal_mul (Real.rpow_nonneg (zero_le_one.trans hD0) _)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (D0 ^ Q) * ENNReal.ofReal C0 := by gcongr
      _ = _ := (ENNReal.ofReal_mul (Real.rpow_nonneg (zero_le_one.trans hD0) _)).symm
  have hKs : ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
      PhysicalKilledCoercivity (retainedWindowCoefficient M l (physicalWindow l m 0 ω)) (Kphys ω) := by
    filter_upwards [hs0] with ω hω
    rw [retainedWindowCoefficient_physical M (by dsimp [m]; omega)]
    intro w
    have hh := hdet M l m (by dsimp [m]; omega) 0 ω w
    have hfactor : D * (ahom M l * (Ch04.lambdaSqCoeffField
        (originCube d ((m + 1 : ℕ) : ℤ)) (1 / 16) (.finite 1)
        (aCutoffRegCoeffField M l (translatePotentialSample 0 ω.val)))⁻¹) ≤ Kphys ω := by
      have hX0 : 0 ≤ ahom M l * (Ch04.lambdaSqCoeffField
        (originCube d ((m + 1 : ℕ) : ℤ)) (1 / 16) (.finite 1)
        (aCutoffRegCoeffField M l (translatePotentialSample 0 ω.val)))⁻¹ := by
        exact mul_nonneg (ahom_pos M l).le (inv_nonneg.mpr
          (Ch04.lambdaSqCoeffField_finite_nonneg _ _ (by norm_num) (by norm_num)))
      exact mul_le_mul hDD0 hω hX0 (zero_le_one.trans hD0)
    exact hh.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hfactor) _)
  haveI : StandardBorelSpace (AnchoredC11Sample d) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d).standardBorel
  haveI : Nonempty (AnchoredC11Sample d) := ⟨defaultAnchored M⟩
  exact physicalBank_measurable_descent (PhysicalAttachment.physicalLaw M).toMeasure
    (windowLaw M l m) (physicalWindow_preserving M l m 0)
    (hK0.const_mul D0) (fun ω => by nlinarith [hone ω])
    (zero_lt_one.trans_le hQ) hC1.le hKm
    (fun ξ K => PhysicalKilledCoercivity (retainedWindowCoefficient M l ξ) K)
    (fun ξ K K' hKK hs => hs.mono hKK) hKs

/-- Concrete actual physical-law consumer, obtained through the exact window
pushforward at every deterministic center. The constant C is unchanged. -/
theorem aux_lim_lem_mean_exit_inlined_physical_large_killed_moment_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∀ Q : ℝ, 1 ≤ Q → ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ δ → ∀ l k : ℕ, 1 ≤ k →
        ∀ z : SpatialCoordinates d, ∃ Kphys : AnchoredC11Sample d → ℝ,
          Measurable Kphys ∧ (∀ ω, 1 ≤ Kphys ω) ∧
          (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ Q) ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤
            ENNReal.ofReal C ∧
          ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
            PhysicalKilledCoercivity (localCoefficient M l (l + k) z ω) (Kphys ω) := by
  intro Q hQ
  obtain ⟨δ, C, hδ, hC, hwindow⟩ := aux_lim_lem_mean_exit_inlined_physical_retained_window_killed_bank hd Q hQ
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro M hM l k hk z
  obtain ⟨K, hK, hone, hm, hs⟩ := hwindow M hM l k hk
  exact physicalRetainedWindow_killed_pullback M (by omega) z hK hone hm hs

end Paper
end aux_lim_lem_mean_exit_inline_8



noncomputable section aux_lim_lem_mean_exit_inline_9

open MeasureTheory SubdiffusiveProcess Homogenization TopologicalSpace
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open scoped ENNReal BigOperators
namespace Paper

/-- Actual finite l<m mass bank. The cell input order 2dQ is fixed before δ;
C is chosen before l,k,z. Every test ball is controlled on one finite event. -/
theorem aux_lim_lem_mean_exit_inlined_physical_retained_mass_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
      ∃ C : ℝ, 0 < C ∧ ∀ l k : ℕ, 1 ≤ k → ∀ z : SpatialCoordinates d,
        ∃ Kphys : AnchoredC11Sample d → ℝ, Measurable Kphys ∧ (∀ ω, 1 ≤ Kphys ω) ∧
          (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ Q) ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤
            ENNReal.ofReal C ∧
          ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
            PhysicalMassBounds (localSpeed M l (l + k) z ω) (Kphys ω) := by
  classical
  obtain ⟨B, _, hbank⟩ := aux_lim_lem_mean_exit_inlined_physical_sobolev_finite_static_bank hd
  have hp : (1 : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * d)
  have horder : 1 ≤ ((2 * d : ℕ) : ℝ) * Q :=
    one_le_mul_of_one_le_of_one_le hp hQ
  obtain ⟨δ, hδ, hmodels⟩ := hbank (((2 * d : ℕ) : ℝ) * Q) horder
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨C0, hC0, hlocal⟩ := hmodels M hM
  let C := (((15 : ℝ) ^ d + 1) ^ Q * (2 : ℝ) ^ Q) *
    (1 + ((27 : ℝ) ^ d) ^ Q * C0)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro l k _hk z
  let s : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  have hs : 0 < s := zpow_neg_pos k
  have hs1 : s ≤ 1 := three_zpow_neg_le_one k
  choose K hKm hKone hKmom hKs using
    (fun j : Fin d → ℤ => hlocal l l le_rfl (z + (3 : ℝ) ^ (l + k) • massGridCenter (s / 3) j))
  let Kg : AnchoredC11Sample d → ℝ := fun ω => massGlobalConstant s (fun j => K j ω)
  obtain ⟨hgm, hgmoment⟩ := massGlobalConstant_moment
    (PhysicalAttachment.physicalLaw M).toMeasure hs hs1 hQ hC0.le K hKm
      (fun j ω => zero_le_one.trans (hKone j ω)) hKmom
  refine ⟨Kg, hgm, fun ω => massGlobalConstant_one hs.le
    (fun j => zero_le_one.trans (hKone j ω)), hgmoment, ?_⟩
  have hfinite : ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
      ∀ j ∈ massGlobalGrid d s,
        PhysicalStaticBounds
          (localSpeed M l l (z + (3 : ℝ) ^ (l + k) • massGridCenter (s / 3) j) ω)
          (localCoefficient M l l (z + (3 : ℝ) ^ (l + k) • massGridCenter (s / 3) j) ω)
          B (K j ω) := (Filter.eventually_all_finset _).mpr fun j _ => hKs j
  filter_upwards [hfinite] with ω hω
  apply mass_finite_spatial_aggregation (by omega : 0 < d) hs hs1
    (localSpeed M l (l + k) z ω) (fun j => K j ω)
    (fun j => zero_le_one.trans (hKone j ω))
  intro j hj
  have heq : (fun y => localSpeed M l (l + k) z ω (massGridCenter (s / 3) j + s • y)) =
      localSpeed M l l (z + (3 : ℝ) ^ (l + k) • massGridCenter (s / 3) j) ω :=
    funext fun y => mass_physical_micro_density M l k z _ ω y
  rw [heq]
  exact (hω j hj).1

/-- The exact retained-window law, obtained by marginal descent of the actual
physical construction, with the complete all-center/all-radius certificate. -/
theorem aux_lim_lem_mean_exit_inlined_actual_retained_window_mass_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
      ∃ C : ℝ, 0 < C ∧ ∀ l k : ℕ, 1 ≤ k →
        ∃ K : (Fin (l + 1) → C(SpatialCoordinates d, ℝ)) → ℝ,
          Measurable K ∧ (∀ ξ, 1 ≤ K ξ) ∧
          (∫⁻ ξ, ENNReal.ofReal (K ξ ^ Q) ∂windowLaw M l (l + k)) ≤ ENNReal.ofReal C ∧
          ∀ᵐ ξ ∂windowLaw M l (l + k), PhysicalMassBounds (retainedWindowSpeed M l ξ) (K ξ) := by
  obtain ⟨δ, hδ, hmodels⟩ := aux_lim_lem_mean_exit_inlined_physical_retained_mass_bank hd Q hQ
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨C0, hC0, hcutoffs⟩ := hmodels M hM
  refine ⟨1 + 2 * C0, by positivity, ?_⟩
  intro l k hk
  obtain ⟨Kp, hKp, hpone, hpmom, hpbound⟩ := hcutoffs l k hk 0
  haveI : StandardBorelSpace (AnchoredC11Sample d) :=
    (Section6Anchored.measurableSet_anchoredC11GoodSet d).standardBorel
  haveI : Nonempty (AnchoredC11Sample d) := ⟨defaultAnchored M⟩
  have hbound : ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
      PhysicalMassBounds (retainedWindowSpeed M l (physicalWindow l (l + k) 0 ω)) (Kp ω) := by
    filter_upwards [hpbound] with ω hω
    rw [retainedWindowSpeed_physical M (by omega)]
    exact hω
  exact physicalBank_measurable_descent (PhysicalAttachment.physicalLaw M).toMeasure
    (windowLaw M l (l + k)) (physicalWindow_preserving M l (l + k) 0)
    hKp hpone (by linarith) hC0.le hpmom
    (fun ξ c => PhysicalMassBounds (retainedWindowSpeed M l ξ) c)
    (fun ξ c c' hcc h => h.mono hcc) hbound

end Paper
end aux_lim_lem_mean_exit_inline_9



noncomputable section aux_lim_lem_mean_exit_inline_10

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
namespace Paper

/-- Actual finite retained-window mass and killed projections, joined on the
same window law and pulled back by the literal physicalWindow. -/
theorem aux_lim_lem_mean_exit_inlined_physical_sobolev_large_static_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
      ∃ C : ℝ, 0 < C ∧ ∀ l k : ℕ, 1 ≤ k → ∀ z : SpatialCoordinates d,
        ∃ Kphys : AnchoredC11Sample d → ℝ,
          Measurable Kphys ∧ (∀ ω, 1 ≤ Kphys ω) ∧
          (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ Q)
            ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
          ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
            PhysicalStaticBounds (localSpeed M l (l + k) z ω)
              (localCoefficient M l (l + k) z ω) 0 (Kphys ω) := by
  obtain ⟨δm, hδm, hmass⟩ := aux_lim_lem_mean_exit_inlined_actual_retained_window_mass_bank hd Q hQ
  obtain ⟨δc, Cc, hδc, hCc, hcoer⟩ := aux_lim_lem_mean_exit_inlined_physical_retained_window_killed_bank hd Q hQ
  refine ⟨min δm δc, lt_min hδm hδc, ?_⟩
  intro M hM
  obtain ⟨Cm, hCm, hm⟩ := hmass M (hM.trans (min_le_left _ _))
  refine ⟨Cm + Cc, add_pos hCm hCc, ?_⟩
  intro l k hk z
  obtain ⟨Km, hKm, hmone, hmoment, hmcert⟩ := hm l k hk
  obtain ⟨Kc, hKc, hcone, hcmoment, hccert⟩ :=
    hcoer M (hM.trans (min_le_right _ _)) l k hk
  exact physicalRetainedWindow_join_projection_banks M (by omega) z
    hKm hKc hmone hcone (zero_le_one.trans hQ) hCm.le hCc.le
    hmoment hcmoment hmcert hccert

/-- The actual static bank for every finite cutoff and top. B is fixed before
the moment order; the moment constant precedes L,m,z. -/
theorem aux_lim_lem_mean_exit_inlined_physical_sobolev_static_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ B : ℝ, 0 < B ∧ ∀ Q : ℝ, 1 ≤ Q →
      ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
        ∃ C : ℝ, 0 < C ∧ ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          ∃ Kphys : AnchoredC11Sample d → ℝ, Measurable Kphys ∧
            (∀ ω, 1 ≤ Kphys ω) ∧
            (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ Q)
              ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
            ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
              PhysicalStaticBounds (localSpeed M L m z ω) (localCoefficient M L m z ω)
                B (Kphys ω) := by
  classical
  obtain ⟨B, hB, hsmall⟩ := aux_lim_lem_mean_exit_inlined_physical_sobolev_static_bank_small_scale hd
  refine ⟨B, hB, ?_⟩
  intro Q hQ
  obtain ⟨δs, hδs, hs⟩ := hsmall Q hQ
  obtain ⟨δg, hδg, hg⟩ := aux_lim_lem_mean_exit_inlined_physical_sobolev_large_static_bank hd Q hQ
  refine ⟨min δs δg, lt_min hδs hδg, ?_⟩
  intro M hM
  obtain ⟨Cs, hCs, hsbank⟩ := hs M (hM.trans (min_le_left _ _))
  obtain ⟨Cg, hCg, hgbank⟩ := hg M (hM.trans (min_le_right _ _))
  refine ⟨max Cs Cg, hCs.trans_le (le_max_left _ _), ?_⟩
  intro L m z
  by_cases hscope : L = ⊤ ∨ ∃ l : ℕ, L = l ∧ m ≤ l
  · obtain ⟨K, hK, hone, hm, hc⟩ := hsbank L m hscope z
    exact ⟨K, hK, hone, hm.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)), hc⟩
  · have hL : L ≠ ⊤ := fun h => hscope (Or.inl h)
    obtain ⟨l, rfl⟩ := WithTop.ne_top_iff_exists.mp hL
    have hml : ¬m ≤ l := fun h => hscope (Or.inr ⟨l, rfl, h⟩)
    obtain ⟨K, hK, hone, hm, hc⟩ := hgbank l (m - l) (by omega) z
    have heq : l + (m - l) = m := by omega
    rw [heq] at hc
    refine ⟨K, hK, hone, hm.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)), ?_⟩
    filter_upwards [hc] with ω hω
    exact hω.exponent_mono (zero_le_one.trans (hone ω)) hB.le

end Paper
end aux_lim_lem_mean_exit_inline_10



noncomputable section aux_lim_lem_mean_exit_inline_11

/-! First actual application of B1, on a fixed unit cube inside the side-four
reference cube. General-p trace and padded coercivity are discharged by their
existing exports. This is an internal deterministic application, with no
process, environment or new source assumption. -/

open MeasureTheory Set Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open scoped ENNReal
namespace Paper

lemma aux_lim_lem_mean_exit_inlined_killed_sobolev_trace_supplier {d : ℕ} (hd : 2 ≤ d)
    {r0 : ℝ} (hr0 : 0 < r0) :
    ∃ C : ℝ, 0 < C ∧ KilledTraceBound d r0 C := by
  obtain ⟨C, hC, htrace⟩ := aux_tight_subharmonic_aux_trace_Lp d (1 / 2) (3 / 4)
    (killedSobolevExponent d) r0 (killedSobolevExponent_ge_two hd)
    (by norm_num) hr0 (killedSobolev_trace_margin hd)
  refine ⟨C, hC, ?_⟩
  intro V ν Km hKm hfin hV hac hsupp hgrowth f hfm hfL
  simpa only [killedFractionalEnergy, show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num] using
    htrace V ν Km hKm hfin hV hac hsupp hgrowth f hfm hfL

/-- All-H10 deterministic B1 on arbitrary measurable domains inside an open
padded domain. The trace constant is fixed before the measure and coefficients;
the general-p trace premise is discharged by its actual proved supplier. -/
theorem aux_lim_lem_mean_exit_inlined_killed_sobolev_of_padded_coercivity {d : ℕ} (hd : 2 ≤ d)
    {r0 : ℝ} (hr0 : 0 < r0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U V : Set (SpatialCoordinates d)),
      MeasurableSet U → IsOpen V → U ⊆ V →
      ∀ (μ : Measure (SpatialCoordinates d)), μ ≪ volume →
      ∀ [IsFiniteMeasure (μ.restrict U)] (Km Kc : ℝ), 0 < Km → 0 ≤ Kc →
      (μ.restrict U) {x | ¬ Metric.closedBall x r0 ⊆ V} = 0 →
      (∀ y ∈ V, ∀ r : ℝ, 0 < r → r ≤ r0 →
        (μ.restrict U) (Metric.ball y r) ≤ ENNReal.ofReal (Km * r ^ ((d : ℝ) - 1 / 2))) →
      ∀ A : SpatialCoordinates d → ℝ,
      (∀ w : H10Function V,
        killedFractionalEnergy V w.toFun + ∫⁻ x in V, ENNReal.ofReal (w.toFun x ^ 2) ≤
          ENNReal.ofReal Kc * killedCoefficientEnergy A w.toH1Function) →
      ∀ v : H10Function U,
        eLpNorm v.toFun (ENNReal.ofReal (killedSobolevExponent d)) (μ.restrict U) ^ 2 ≤
          ENNReal.ofReal (killedSobolevConstant d r0 C Km ((μ.restrict U) univ).toReal Kc) *
            killedCoefficientEnergy A v.toH1Function := by
  obtain ⟨C, hC, htrace⟩ := aux_lim_lem_mean_exit_inlined_killed_sobolev_trace_supplier hd hr0
  refine ⟨C, hC, ?_⟩
  intro U V hU hV hUV μ hμ inst Km Kc hKm hKc hsupp hgrowth A hcoer v
  exact killed_sobolev_all_h10 hd hU hV hUV μ hμ hr0 hC.le hKm hKc
    htrace hsupp hgrowth A hcoer v

/-- The first fixed-cube application of `lim:eq-killed-sobolev`, with its exact
source exponent. The static certificate supplies all mass and coercivity
premises, uniformly for every native H10 function. -/
theorem aux_lim_lem_mean_exit_inlined_killed_sobolev_of_static {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b A : SpatialCoordinates d → ℝ) (K B : ℝ),
      1 ≤ K → tight_static_estimates b A 4 K B →
      ∀ v : H10Function (Metric.ball (0 : SpatialCoordinates d) (1 / 2)),
        eLpNorm v.toFun (ENNReal.ofReal (killedSobolevExponent d))
          ((volume.withDensity (fun x => ENNReal.ofReal (b x))).restrict
            (Metric.ball (0 : SpatialCoordinates d) (1 / 2))) ^ 2 ≤
          ENNReal.ofReal (killedSobolevConstant d (1 / 4) C K
            (((volume.withDensity (fun x => ENNReal.ofReal (b x))).restrict
              (Metric.ball (0 : SpatialCoordinates d) (1 / 2))) univ).toReal
            (K * (2 : ℝ) ^ B)) * killedCoefficientEnergy A v.toH1Function := by
  obtain ⟨C, hC, htrace⟩ := aux_lim_lem_mean_exit_inlined_killed_sobolev_trace_supplier hd (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨C, hC, ?_⟩
  intro b A K B hK hstatic v
  let μ := volume.withDensity (fun x => ENNReal.ofReal (b x))
  let U : Set (SpatialCoordinates d) := Metric.ball 0 (1 / 2)
  let V : Set (SpatialCoordinates d) := Metric.ball 0 1
  have hKm : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hUV : U ⊆ V := Metric.ball_subset_ball (by norm_num)
  have hUref : U ⊆ Metric.ball (0 : SpatialCoordinates d) (4 / 2) :=
    Metric.ball_subset_ball (by norm_num)
  have hmass := (hstatic.1 0 (1 / 2) (by norm_num) (by norm_num) hUref).2
  have hfin : μ U < ⊤ := lt_of_le_of_lt hmass ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure (μ.restrict U) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
  have hsupp : (μ.restrict U) {x | ¬ Metric.closedBall x (1 / 4) ⊆ V} = 0 := by
    have hsub : {x | ¬ Metric.closedBall x (1 / 4) ⊆ V} ⊆ Uᶜ := by
      intro x hx hxU
      apply hx
      intro y hy
      have hx0 : dist x (0 : SpatialCoordinates d) < 1 / 2 := hxU
      have hyx : dist y x ≤ 1 / 4 := hy
      change dist y 0 < 1
      linarith [dist_triangle y x (0 : SpatialCoordinates d)]
    apply measure_mono_null hsub
    rw [Measure.restrict_apply measurableSet_ball.compl, compl_inter_self, measure_empty]
  have hgrowth : ∀ y ∈ V, ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      (μ.restrict U) (Metric.ball y r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2)) := by
    intro y hy r hr hr0
    have hball : Metric.ball y r ⊆ Metric.ball (0 : SpatialCoordinates d) (4 / 2) := by
      intro x hx
      have hy0 : dist y (0 : SpatialCoordinates d) < 1 := hy
      have hxy : dist x y < r := hx
      change dist x 0 < 4 / 2
      linarith [dist_triangle x y (0 : SpatialCoordinates d)]
    exact (Measure.restrict_le_self (μ := μ) (s := U) _).trans
      ((hstatic.1 y r hr (by linarith) hball).2)
  have hcoer : ∀ w : H10Function V,
      killedFractionalEnergy V w.toFun + ∫⁻ x in V, ENNReal.ofReal (w.toFun x ^ 2) ≤
        ENNReal.ofReal (K * (2 : ℝ) ^ B) * killedCoefficientEnergy A w.toH1Function := by
    intro w
    have hc := (hstatic.2.1 (1 / 2) (by norm_num) (by norm_num)).2
    have hrad : (4 : ℝ) * ((1 / 2 : ℚ) : ℝ) / 2 = 1 := by norm_num
    rw [hrad] at hc
    have hden : ((1 / 2 : ℚ).den : ℝ) = 2 := by norm_num
    rw [hden] at hc
    simpa only [V, killedFractionalEnergy, killedCoefficientEnergy] using hc w
  exact killed_sobolev_all_h10 hd measurableSet_ball Metric.isOpen_ball hUV μ
    (withDensity_absolutelyContinuous _ _) (by norm_num) hC.le hKm
    (mul_nonneg hKm.le (Real.rpow_nonneg (by norm_num) _)) htrace hsupp hgrowth A hcoer v

end Paper
end aux_lim_lem_mean_exit_inline_11



noncomputable section aux_lim_lem_mean_exit_inline_12

/-! The two static projections needed for the moment bank. The application
uses the proved B1 theorem; lower mass and cutoff tests are unnecessary. -/

open MeasureTheory Set Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace Paper

/-- A bounded deterministic export from upper mass and padded killed coercivity.
The constant is chosen before coefficients, samples and H10 tests. -/
theorem aux_lim_lem_mean_exit_inlined_killed_sobolev_of_mass_coercivity {d : ℕ} (hd : 2 ≤ d) (B : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b A : SpatialCoordinates d → ℝ) (K : ℝ), 1 ≤ K →
      (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) 2, ∀ r : ℝ, 0 < r → r ≤ 1 →
        weightedMeasure b (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2))) →
      (∀ w : H10Function (Metric.ball (0 : SpatialCoordinates d) 1),
        killedFractionalEnergy (Metric.ball (0 : SpatialCoordinates d) 1) w.toFun +
            ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) 1, ENNReal.ofReal (w.toFun x ^ 2) ≤
          ENNReal.ofReal (K * (2 : ℝ) ^ B) * killedCoefficientEnergy A w.toH1Function) →
      CoefficientOn (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) A →
      KilledSobolevBound (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) b A (D * K ^ 2) := by
  obtain ⟨C, hC, hSob⟩ := aux_lim_lem_mean_exit_inlined_killed_sobolev_of_padded_coercivity hd
    (by norm_num : (0 : ℝ) < 1 / 4)
  let D := (C * (1 + (1 / 4 : ℝ) ^ (-((d : ℝ) / 2)))) ^ 2 * (2 : ℝ) ^ B + 1
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro b A K hK hmass hcoer hA
  let μ := weightedMeasure b
  let U : Set (SpatialCoordinates d) := Metric.ball 0 (1 / 2)
  let V : Set (SpatialCoordinates d) := Metric.ball 0 1
  have hKm : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmass0 := hmass 0 (Metric.mem_ball_self (by norm_num)) (1 / 2)
    (by norm_num) (by norm_num)
  have hpow : (1 / 2 : ℝ) ^ ((d : ℝ) - 1 / 2) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
  have hmassLe : μ U ≤ ENNReal.ofReal K := hmass0.trans
    (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hKm.le hpow))
  letI : IsFiniteMeasure (μ.restrict U) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      lt_of_le_of_lt hmassLe ENNReal.ofReal_lt_top⟩
  have hm : ((μ.restrict U) univ).toReal ≤ K := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmassLe
    rw [ENNReal.toReal_ofReal hKm.le] at h
    simpa only [Measure.restrict_apply_univ] using h
  have hsupp : (μ.restrict U) {x | ¬ Metric.closedBall x (1 / 4) ⊆ V} = 0 := by
    have hsub : {x | ¬ Metric.closedBall x (1 / 4) ⊆ V} ⊆ Uᶜ := by
      intro x hx hxU
      apply hx
      intro y hy
      have hx0 : dist x (0 : SpatialCoordinates d) < 1 / 2 := hxU
      have hyx : dist y x ≤ 1 / 4 := hy
      change dist y 0 < 1
      linarith [dist_triangle y x (0 : SpatialCoordinates d)]
    apply measure_mono_null hsub
    rw [Measure.restrict_apply measurableSet_ball.compl, compl_inter_self, measure_empty]
  have hgrowth : ∀ y ∈ V, ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      (μ.restrict U) (Metric.ball y r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2)) := by
    intro y hy r hr hr0
    have hy2 : y ∈ Metric.ball (0 : SpatialCoordinates d) 2 :=
      (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hy
    exact (Measure.restrict_le_self (μ := μ) (s := U) _).trans
      (hmass y hy2 r hr (by linarith))
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  apply killedSobolevBound_of_lower hA (mul_nonneg hD0 (sq_nonneg K))
  intro v
  have hbound := hSob U V measurableSet_ball Metric.isOpen_ball
    (Metric.ball_subset_ball (by norm_num)) μ (withDensity_absolutelyContinuous _ _)
    K (K * (2 : ℝ) ^ B) hKm (by positivity) hsupp hgrowth A hcoer v
  have hKs : killedSobolevConstant d (1 / 4) C K ((μ.restrict U) univ).toReal
      (K * (2 : ℝ) ^ B) ≤ D * K ^ 2 := by
    refine (killedSobolevConstant_le_sq hd (by norm_num) hC.le hK
      ENNReal.toReal_nonneg hm (Real.rpow_nonneg (by norm_num) _)).trans ?_
    exact mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (sq_nonneg K)
  exact hbound.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hKs) _)

end Paper
end aux_lim_lem_mean_exit_inline_12



noncomputable section aux_lim_lem_mean_exit_inline_13

/-! Concrete consumer on the actual weighted carrier and real Dirichlet energy.
The deterministic coefficient regularity premise is exactly `CoefficientOn`;
attachment to the two model families is reserved for B2-P and B2-B. -/

open MeasureTheory Set Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace Paper

/-- A fixed deterministic D turns the static constant K into D*K^2, sufficient
for subsequent torsion and Nash consumers, with genuine weighted MemLp. -/
theorem aux_lim_lem_mean_exit_inlined_killed_sobolev_unit_cube_consumer {d : ℕ} (hd : 2 ≤ d) (B : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b A : SpatialCoordinates d → ℝ) (K : ℝ),
      1 ≤ K → tight_static_estimates b A 4 K B →
      CoefficientOn (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) A →
      ∀ v : H10Function (Metric.ball (0 : SpatialCoordinates d) (1 / 2)),
        MemLp v.toFun (ENNReal.ofReal (killedSobolevExponent d))
          ((weightedMeasure b).restrict (Metric.ball (0 : SpatialCoordinates d) (1 / 2))) ∧
        lpSq b (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
            (killedSobolevExponent d) v.toFun ≤
          ENNReal.ofReal (D * K ^ 2 *
            energy A (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) v.toH1Function) ∧
        (eLpNorm v.toFun (ENNReal.ofReal (killedSobolevExponent d))
          ((weightedMeasure b).restrict (Metric.ball (0 : SpatialCoordinates d) (1 / 2)))).toReal ^ 2 ≤
          D * K ^ 2 * energy A (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) v.toH1Function := by
  obtain ⟨C, hC, hSob⟩ := aux_lim_lem_mean_exit_inlined_killed_sobolev_of_static hd
  let D := (C * (1 + (1 / 4 : ℝ) ^ (-((d : ℝ) / 2)))) ^ 2 * (2 : ℝ) ^ B + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro b A K hK hstatic hA v
  let U : Set (SpatialCoordinates d) := Metric.ball 0 (1 / 2)
  let μ := weightedMeasure b
  let mass := ((μ.restrict U) univ).toReal
  have hKm : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmass0 : 0 ≤ mass := ENNReal.toReal_nonneg
  have hUref : U ⊆ Metric.ball (0 : SpatialCoordinates d) (4 / 2) :=
    Metric.ball_subset_ball (by norm_num)
  have hmass := (hstatic.1 0 (1 / 2) (by norm_num) (by norm_num) hUref).2
  have hpow : (1 / 2 : ℝ) ^ ((d : ℝ) - 1 / 2) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
  have hmassLe : μ U ≤ ENNReal.ofReal K := hmass.trans
    (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hKm.le hpow))
  have hm : mass ≤ K := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmassLe
    rw [ENNReal.toReal_ofReal hKm.le] at h
    simpa only [mass, Measure.restrict_apply_univ] using h
  let Ks := killedSobolevConstant d (1 / 4) C K mass (K * (2 : ℝ) ^ B)
  have hKs0 : 0 ≤ Ks := killedSobolevConstant_nonneg _ _ _ _ _
    (mul_nonneg hKm.le (Real.rpow_nonneg (by norm_num) _))
  have hKs : Ks ≤ D * K ^ 2 := by
    refine (killedSobolevConstant_le_sq hd (by norm_num) hC.le hK hmass0 hm
      (Real.rpow_nonneg (by norm_num) _)).trans ?_
    exact mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (sq_nonneg K)
  have hbound : eLpNorm v.toFun (ENNReal.ofReal (killedSobolevExponent d)) (μ.restrict U) ^ 2 ≤
      ENNReal.ofReal Ks * killedCoefficientEnergy A v.toH1Function := hSob b A K B hK hstatic v
  have hbounded := hbound.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hKs)
    (zero_le (killedCoefficientEnergy A v.toH1Function)))
  have hnonneg : 0 ≤ D * K ^ 2 := mul_nonneg hD.le (sq_nonneg K)
  have hreal := killed_sobolev_real_of_bound μ (withDensity_absolutelyContinuous _ _) hA v
    hnonneg hbounded
  exact ⟨hreal.1, killed_lpSq_le_of_bound hA v hnonneg hbounded, hreal.2⟩

end Paper
end aux_lim_lem_mean_exit_inline_13



noncomputable section aux_lim_lem_mean_exit_inline_14




open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set SubdiffusiveProcess
open SubdiffusiveProcess.Section10
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Assumptions.CoefficientRegularity
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.Section10.PhysicalAttachment
open scoped ENNReal NNReal
namespace Paper

/-- Static estimates produce the exact unit-cube cap for any actual LocalDiffusion.
The pointwise half exposes precisely the separate starting-point regularity slot. -/
theorem aux_lim_lem_mean_exit_inlined_torsion_exit_unit_cube_consumer {d : ℕ} (hd : 2 ≤ d) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b A : SpatialCoordinates d → ℝ),
      Continuous b → (∀ x, 0 < b x) → Continuous A → (∀ x, 0 < A x) →
      ∀ law : Kernel (SpatialCoordinates d) (Path d), IsMarkovKernel law →
        LocalDiffusion A b law → ∀ K : ℝ, 1 ≤ K → tight_static_estimates b A 4 K B →
          (∀ᵐ x ∂(weightedMeasure b).restrict (Metric.ball 0 (1 / 2)),
            meanExit law (Metric.ball 0 (1 / 2)) x ≤ ENNReal.ofReal
              (C * K ^ 2 * (weightedMeasure b (Metric.ball 0 (1 / 2))).toReal ^ (1 / (d : ℝ)))) ∧
          (UnitDiscountOccupationLSC law (Metric.ball 0 (1 / 2)) →
            ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (1 / 2),
              meanExit law (Metric.ball 0 (1 / 2)) x ≤ ENNReal.ofReal
                (C * K ^ 2 * (weightedMeasure b (Metric.ball 0 (1 / 2))).toReal ^ (1 / (d : ℝ)))) := by
  obtain ⟨D, hD, hKilled⟩ := aux_lim_lem_mean_exit_inlined_killed_sobolev_unit_cube_consumer hd B
  let p : ℝ := 2 * (d : ℝ) / ((d : ℝ) - 1)
  let C : ℝ := torsionConstant p * D
  refine ⟨C, mul_pos (torsionConstant_pos p) hD, ?_⟩
  intro b A hb hbpos hA hApos law hMarkov hlocal K hK hstatic
  letI := hMarkov
  let U : Set (SpatialCoordinates d) := Metric.ball 0 (1 / 2)
  have hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_ball 0 (by norm_num)
  have hne : U.Nonempty := ⟨0, Metric.mem_ball_self (by norm_num)⟩
  have hAb : CoefficientOn U A := coefficientOn_of_continuous_pos hA hApos hU.isBoundedDomain.isBounded
  have hbb : CoefficientOn U b := coefficientOn_of_continuous_pos hb hbpos hU.isBoundedDomain.isBounded
  have hKsob : 0 < D * K ^ 2 := mul_pos hD (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hK))
  have hSob : TorsionSobolevBound A b U p (D * K ^ 2) :=
    fun v => (hKilled b A K hK hstatic hAb v).2.1
  have hp : 2 < p := killedSobolevExponent_gt_two hd
  have hpower : 1 - 2 / p = 1 / (d : ℝ) := killedSobolev_one_sub_two_div hd
  have hconstant : torsionConstant p * (D * K ^ 2) = C * K ^ 2 := by dsimp only [C]; ring
  constructor
  · simpa only [hpower, hconstant] using localDiffusion_meanExit_ae_le hlocal hU hne hbb hp hKsob hSob
  · intro hls
    simpa only [hpower, hconstant] using localDiffusion_meanExit_le hlocal hU hne hbb hp hKsob hSob hls



theorem aux_lim_lem_mean_exit_inlined_torsion_exit_physical_family_consumer {d : ℕ} (hd : 2 ≤ d) (B : ℝ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess) (M : GMCModel d) :
    ∃ C : ℝ, 0 < C ∧ ∃ X : WithTop ℕ → PhysicalKernel d,
      (∀ L, IsMarkovKernel (X L)) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ, ∀ K : ℝ, 1 ≤ K →
        tight_static_estimates (coefficientAt M L omega) (coefficientAt M L omega) 4 K B →
        (∀ᵐ x ∂(weightedMeasure (coefficientAt M L omega)).restrict (Metric.ball 0 (1 / 2)),
          meanExit ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath)
            (Metric.ball 0 (1 / 2)) x ≤ ENNReal.ofReal (C * K ^ 2 *
              (weightedMeasure (coefficientAt M L omega) (Metric.ball 0 (1 / 2))).toReal ^ (1 / (d : ℝ)))) ∧
        (FellerUnitCubeDiscountOccupationLSC → ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (1 / 2),
          meanExit ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath)
            (Metric.ball 0 (1 / 2)) x ≤ ENNReal.ofReal (C * K ^ 2 *
              (weightedMeasure (coefficientAt M L omega) (Metric.ball 0 (1 / 2))).toReal ^ (1 / (d : ℝ)))) := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hconsumer⟩ := aux_lim_lem_mean_exit_inlined_torsion_exit_unit_cube_consumer hd B
  obtain ⟨X, hX, hactual⟩ := exists_physical_localDiffusion_family hFOT M
  refine ⟨C, hC, X, hX, ?_⟩
  filter_upwards [hactual] with omega homega
  intro L K hK hstatic
  obtain ⟨hlocal, D, hdense, _, hcons, hfdd⟩ := homega L
  letI := hX L
  letI : IsMarkovKernel (physicalSlice (X L) omega) := by dsimp only [physicalSlice]; infer_instance
  letI : IsMarkovKernel ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath) :=
    Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
  obtain ⟨hae, hpoint⟩ := hconsumer (coefficientAt M L omega) (coefficientAt M L omega)
    (continuous_coefficientAt M L omega) (coefficientAt_pos M L omega)
    (continuous_coefficientAt M L omega) (coefficientAt_pos M L omega)
    ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath) inferInstance hlocal K hK hstatic
  refine ⟨hae, fun hreg => hpoint ?_⟩
  exact hreg d (D.fellerKernelSemigroup hdense) hcons
    (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense)
    (physicalSlice (X L) omega) inferInstance hfdd

end Paper
end aux_lim_lem_mean_exit_inline_14



noncomputable section aux_lim_lem_mean_exit_inline_15

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
open SubdiffusiveProcess.Section10
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.Probability.Diffusion
open SubdiffusiveProcess
open scoped ZeroAtInfty NNReal Pointwise
namespace Paper

variable {d : ℕ}

/-- Reuse the proved `physical_rescaling` weak-equation supplier, adding the literal
translation of the physical coefficient. No clock conversion theorem is reproved. -/
theorem aux_lim_lem_mean_exit_inlined_physical_local_datum_weak (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (omega : AnchoredC11Sample d) (D : C0ResolventDatum (Vec d))
    (hD : IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D) :
    IsWeakEllipticResolvent (localCoefficient M L m z omega) (localSpeed M L m z omega)
      (transportedDatum D (physicalCoordinates m z) (rawClock M L m) (rawClock_pos M L m)) := by
  let a : ℝ := (3 : ℝ) ^ m
  let r : ℝ := (ahom M (activeScale L m))⁻¹
  let alpha : ℝ := (localFactor M L m z omega)⁻¹
  have ha : 0 < a := pow_pos (by norm_num) _
  have hr : 0 < r := inv_pos.mpr (ahom_pos M _)
  have halpha : 0 < alpha := inv_pos.mpr (localFactor_pos M L m z omega)
  have hclock : (rawClock M L m : ℝ) = r * a ^ 2 := by
    dsimp [rawClock, a, r]
    rw [← pow_mul, Nat.mul_comm m 2]
    ring
  intro mu f W hW
  let e := physicalCoordinates (d := d) m z
  let f0 := pullback e.symm f
  have hscaled : IsOpenBoundedConvexDomain (a • W) := by
    have hb : IsBoundedDomain (a • W) := by
      obtain ⟨K, hK, hbound⟩ := hW.isBoundedDomain
      refine ⟨a * K, mul_pos ha hK, ?_⟩
      rintro x ⟨y, hy, rfl⟩ i
      change |a * y i| ≤ a * K
      rw [abs_mul, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_left (hbound y hy i) ha.le
    exact ⟨(Homeomorph.smulOfNeZero a ha.ne').isOpen_image.mpr hW.isOpen,
      hb, hW.convex.smul a⟩
  obtain ⟨u, hu, hweak⟩ := hD
    (dividedShift (rawClock M L m) (rawClock_pos M L m) mu) f0
    (translateSet z (a • W)) (hscaled.translateSet z)
  let v := H1Function.untranslate z u
  have hv := isMassiveWeakSolutionOn_untranslate z u hweak
  have hmass := aux_physical_rescaling_kernel_conjugacy_massive_unscale
    (U := W) (a := a) (α := alpha) (r := r) (μ := (mu : ℝ))
    (lam := (mu : ℝ) / (rawClock M L m : ℝ))
    (c := fun y => coefficientAt M L omega (y + z))
    (rho := fun y => coefficientAt M L omega (y + z))
    (C := localCoefficient M L m z omega) (R := localSpeed M L m z omega)
    (u := v) (f0 := fun y => f0 (y + z)) (f := fun y => f y)
    ha halpha.ne' hr.ne'
    (by rw [← hclock]; field_simp [(show 0 < (rawClock M L m : ℝ) from rawClock_pos M L m).ne'])
    (fun x => by dsimp [localCoefficient, localSpeed, alpha, r, a]; rw [add_comm]; ring)
    (fun x => by dsimp [localSpeed, alpha, a]; rw [add_comm])
    (fun x => by change f (e.symm (a • x + z)) = f x
                 rw [show a • x + z = e x by dsimp [e, physicalCoordinates, a]; simp [add_comm]]
                 rw [e.symm_apply_apply]) hv
  refine ⟨(r * a ^ 2)⁻¹ • v.unscale ha, ?_, hmass⟩
  intro x hx
  simp only [H1Function.smul_toFun, H1Function.unscale_toFun]
  change (r * a ^ 2)⁻¹ * u.toFun (a • x + z) = _
  rw [hu (a • x + z) ⟨a • x, ⟨x, hx, rfl⟩, rfl⟩]
  change (r * a ^ 2)⁻¹ * D.solution
      (dividedShift (rawClock M L m) (rawClock_pos M L m) mu) f0 (a • x + z) =
    (rawClock M L m : ℝ)⁻¹ * D.solution
      (dividedShift (rawClock M L m) (rawClock_pos M L m) mu) f0 (e x)
  rw [← hclock]
  congr 1
  dsimp [e, physicalCoordinates, a]
  simp [add_comm]

/-- Change variables in the already supplied Laplace integral, at the literal clock. -/
theorem aux_lim_lem_mean_exit_inlined_physical_local_laplace_dilation {F G : ℝ → ℝ} (c : ℝ) (hc : 0 < c)
    (h : ∀ mu : ℝ, 0 < mu →
      (∫ s in Ioi (0 : ℝ), Real.exp (-(mu * s)) * F s) =
        c⁻¹ * ∫ s in Ioi (0 : ℝ), Real.exp (-((mu / c) * s)) * G s) :
    ∀ mu : ℝ, 0 < mu →
      (∫ s in Ioi (0 : ℝ), Real.exp (-(mu * s)) * F s) =
        ∫ s in Ioi (0 : ℝ), Real.exp (-(mu * s)) * G (c * s) := by
  intro mu hmu
  have hchange := MeasureTheory.integral_comp_mul_left_Ioi
    (fun s : ℝ => Real.exp (-((mu / c) * s)) * G s) 0 hc
  calc
    (∫ s in Ioi (0 : ℝ), Real.exp (-(mu * s)) * F s) =
        c⁻¹ * ∫ s in Ioi (0 : ℝ), Real.exp (-((mu / c) * s)) * G s := h mu hmu
    _ = ∫ s in Ioi (0 : ℝ), Real.exp (-((mu / c) * (c * s))) * G (c * s) := by
      simpa only [Function.comp_apply, mul_zero, zero_mul, smul_eq_mul] using hchange.symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      dsimp only
      rw [show (mu / c) * (c * s) = mu * s by
        rw [← mul_assoc, div_mul_cancel₀ _ hc.ne']]

/-- The constructed local datum has the source's every-start transition kernels. -/
theorem aux_lim_lem_mean_exit_inlined_physical_local_datum_conjugacy
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (e : Vec d ≃ₜ Vec d) (c : ℝ≥0) (hc : 0 < c) :
    SubMarkovKernelSemigroup.IsRescaledConjugate (D.fellerKernelSemigroup hdense)
      ((transportedDatum D e c hc).fellerKernelSemigroup
        (transportedDatum_dense D hdense e c hc)) e.symm c := by
  let E := transportedDatum D e c hc
  let he := transportedDatum_dense D hdense e c hc
  let P := D.fellerKernelSemigroup hdense
  let Q := E.fellerKernelSemigroup he
  have hPF := D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  have hQF := E.isFellerKernelSemigroup_fellerKernelSemigroup he
  intro t x
  simp only [Homeomorph.symm_symm]
  change Q t x = (((P (c * t)) (e x)).map e.symm)
  haveI : IsFiniteMeasure (Q t x) :=
    ⟨lt_of_le_of_lt (Q.isSubMarkovKernel t x) (by norm_num)⟩
  haveI : IsFiniteMeasure ((P (c * t)) (e x)) :=
    ⟨lt_of_le_of_lt (P.isSubMarkovKernel _ _) (by norm_num)⟩
  haveI : IsFiniteMeasure (((P (c * t)) (e x)).map e.symm) :=
    Measure.isFiniteMeasure_map _ _
  refine Measure.ext_of_integral_eq_on_compactlySupported fun g => ?_
  let f : C₀(Vec d, ℝ) :=
    ⟨⟨fun y => g y, g.continuous⟩, zero_at_infty g⟩
  let f0 := pullback e.symm f
  let F : ℝ → ℝ := fun s => kernelIntegral (Q (Real.toNNReal s)) f x
  let G : ℝ → ℝ := fun s => kernelIntegral (P (Real.toNNReal s)) f0 (e x)
  have hFc : Continuous F := E7.continuous_kernelIntegral_of_feller Q hQF f x
  have hGc : Continuous G := E7.continuous_kernelIntegral_of_feller P hPF f0 (e x)
  have hlap : ∀ mu : ℝ, 0 < mu →
      (∫ s in Ioi (0 : ℝ), Real.exp (-(mu * s)) * F s) =
        ∫ s in Ioi (0 : ℝ), Real.exp (-(mu * s)) * G ((c : ℝ) * s) := by
    apply aux_lim_lem_mean_exit_inlined_physical_local_laplace_dilation (c : ℝ) hc
    intro mu hmu
    have hsol := E.solution_eq_laplace he ⟨mu, hmu⟩ f x
    change (c : ℝ)⁻¹ * D.solution (dividedShift c hc ⟨mu, hmu⟩) f0 (e x) = _ at hsol
    rw [D.solution_eq_laplace hdense] at hsol
    simpa only [F, G, dividedShift, neg_mul] using hsol.symm
  have hFb : ∀ s, |F s| ≤ max ‖f‖ ‖f0‖ :=
    fun s => (E7.abs_kernelIntegral_le Q _ f x).trans (le_max_left _ _)
  have hGb : ∀ s, |G ((c : ℝ) * s)| ≤ max ‖f‖ ‖f0‖ :=
    fun s => (E7.abs_kernelIntegral_le P _ f0 (e x)).trans (le_max_right _ _)
  have htime := eq_of_forall_integral_exp_neg_mul_eq hFc
    (hGc.comp (continuous_const.mul continuous_id)) hFb hGb hlap (t : ℝ) t.coe_nonneg
  have hn : Real.toNNReal ((c : ℝ) * (t : ℝ)) = c * t := by
    change Real.toNNReal ((c * t : ℝ≥0) : ℝ) = c * t
    exact Real.toNNReal_coe
  have hint : kernelIntegral (Q t) f x = kernelIntegral (P (c * t)) f0 (e x) := by
    change kernelIntegral (Q (Real.toNNReal (t : ℝ))) f x =
      kernelIntegral (P (Real.toNNReal ((c : ℝ) * (t : ℝ)))) f0 (e x) at htime
    rw [Real.toNNReal_coe, hn] at htime
    exact htime
  have hmap : (∫ y, g y ∂(((P (c * t)) (e x)).map e.symm)) =
      ∫ y, g (e.symm y) ∂((P (c * t)) (e x)) :=
    integral_map e.symm.measurable.aemeasurable
      (show AEStronglyMeasurable (fun y : Vec d => g y)
        (((P (c * t)) (e x)).map e.symm) from
        (show Continuous (fun y : Vec d => g y) from g.continuous).aestronglyMeasurable)
  rw [hmap]
  exact hint

variable [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]

/-- This FDD step is the already proved rescaling application with its concluding
comparison removed: finite-time conjugacy identifies the explicit mapped path law. -/
theorem aux_lim_lem_mean_exit_inlined_physical_local_rescaled_fdd
    (P P' : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (K : Kernel (Vec d) (DiffusionPath d)) (hK : IsMarkovKernel K)
    (hKmarg : ∀ I x, (K x).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (e : Vec d ≃ₜ Vec d) (c : ℝ≥0) (hc : 0 < c)
    (hconj : SubMarkovKernelSemigroup.IsRescaledConjugate P P' e c) :
    ∀ I x, ((K (e.symm x)).map (ContinuousPath.rescale e c)).map
        (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P' I x := by
  classical
  letI : IsMarkovKernel K := hK
  intro I x
  let hmapPath : Measurable
      ((FiniteOrderedTimes.mapPath e : (I → Vec d) → I → Vec d) ∘
        SubMarkovKernelSemigroup.orderedPathToFiniteSet I) :=
    (FiniteOrderedTimes.measurable_mapPath e.measurable).comp
      (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)
  let hfinite : Measurable (ContinuousPath.finiteEvaluation
      (α := Vec d) (fun i => ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc) i)) :=
    ContinuousPath.measurable_finiteEvaluation _
  have hcomp : ContinuousPath.finsetEvaluation I ∘ ContinuousPath.rescale e c =
      ((FiniteOrderedTimes.mapPath e : (I → Vec d) → I → Vec d) ∘
        SubMarkovKernelSemigroup.orderedPathToFiniteSet I) ∘ ContinuousPath.finiteEvaluation
          (fun i => ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc) i) := by
    funext path t
    show e (path (c * (t : NNReal))) = e (path (c * SubMarkovKernelSemigroup.finiteSetTimes I
      ((I.orderIsoOfFin rfl).symm t)))
    rw [SubMarkovKernelSemigroup.finiteSetTimes_orderIsoOfFin_symm_apply]
  have hordered := aux_physical_rescaling_ordered_marginal P hP (K (e.symm x)) (e.symm x)
    (fun J => hKmarg J (e.symm x)) ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc)
  have hfinite' := congrArg (fun Q : Kernel (Vec d) (I → Vec d) => Q x)
    (hconj.finiteSetKernel_eq hc hP I)
  dsimp only at hfinite'
  rw [Kernel.map_apply _ hmapPath, Kernel.comap_apply] at hfinite'
  calc
    ((K (e.symm x)).map (ContinuousPath.rescale e c)).map (ContinuousPath.finsetEvaluation I) =
        (K (e.symm x)).map (ContinuousPath.finsetEvaluation I ∘ ContinuousPath.rescale e c) :=
      Measure.map_map (ContinuousPath.measurable_finsetEvaluation I) (ContinuousPath.measurable_rescale e c)
    _ = ((K (e.symm x)).map (ContinuousPath.finiteEvaluation
        (fun i => ((SubMarkovKernelSemigroup.finiteSetTimes I).rescale c hc) i))).map
          ((FiniteOrderedTimes.mapPath e : (I → Vec d) → I → Vec d) ∘
            SubMarkovKernelSemigroup.orderedPathToFiniteSet I) := by
      rw [hcomp, ← Measure.map_map hmapPath hfinite]
    _ = _ := by rw [hordered]; exact hfinite'.symm

/-- Full physical-source characterization retained for the very kernel being transported. -/
def aux_lim_lem_mean_exit_inlined_physical_local_source_characterization (M : GMCModel d) (L : WithTop ℕ)
    (X : PhysicalAttachment.PhysicalKernel d) : Prop :=
  ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
    ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
      IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
      (D.fellerKernelSemigroup hdense).IsConservative ∧
      ∀ I x, (X (omega, x)).map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x

/-- Complete model application: the actual anchored finite/top family, at every start,
has the local coefficient, exact raw clock and literal affine path law from the paper. -/
theorem aux_lim_lem_mean_exit_actual_physical_local_family (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) (z : Vec d) :
    ∃ X Y : PhysicalAttachment.PhysicalKernel d,
      IsMarkovKernel X ∧ IsMarkovKernel Y ∧
      aux_lim_lem_mean_exit_inlined_physical_local_source_characterization M L X ∧
      (∀ omega x, Y (omega, x) =
        (X (omega, physicalCoordinates m z x)).map
          (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m))) ∧
      ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
        ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
          IsWeakEllipticResolvent (localCoefficient M L m z omega) (localSpeed M L m z omega) D ∧
          (D.fellerKernelSemigroup hdense).IsConservative ∧
          ∀ I x, (Y (omega, x)).map (ContinuousPath.finsetEvaluation I) =
            SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
  letI : NeZero d := ⟨by have hd := M.shellPrefix.dimension; omega⟩
  obtain ⟨X, hX⟩ := PhysicalAttachment.exists_physical_family M
  let Y := ((X L).comap
    (fun p : AnchoredC11Sample d × Vec d => (p.1, physicalCoordinates m z p.2))
    (measurable_fst.prodMk ((physicalCoordinates m z).measurable.comp measurable_snd))).map
      (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m))
  letI : IsMarkovKernel (X L) := hX.1 L
  have hY : IsMarkovKernel Y := by
    dsimp only [Y]
    exact Kernel.IsMarkovKernel.map _ (ContinuousPath.measurable_rescale _ _)
  have hYeq : ∀ omega x, Y (omega, x) = (X L (omega, physicalCoordinates m z x)).map
      (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m)) := by
    intro omega x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_rescale _ _), Kernel.comap_apply]
  have hsource : aux_lim_lem_mean_exit_inlined_physical_local_source_characterization M L (X L) := by
    filter_upwards [hX.2] with omega h
    obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := h L
    refine ⟨D, hdense, hweak, hcons, ?_⟩
    intro I x
    rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    exact hfdd I x
  refine ⟨X L, Y, hX.1 L, hY, hsource, hYeq, ?_⟩
  filter_upwards [hX.2] with omega h
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := h L
  let E := transportedDatum D (physicalCoordinates m z) (rawClock M L m) (rawClock_pos M L m)
  let he := transportedDatum_dense D hdense (physicalCoordinates m z) (rawClock M L m)
    (rawClock_pos M L m)
  have hconj := aux_lim_lem_mean_exit_inlined_physical_local_datum_conjugacy D hdense (physicalCoordinates m z)
    (rawClock M L m) (rawClock_pos M L m)
  refine ⟨E, he, aux_lim_lem_mean_exit_inlined_physical_local_datum_weak M L m z omega D hweak,
    hconj.isConservative hcons, ?_⟩
  have hslice : IsMarkovKernel (PhysicalAttachment.physicalSlice (X L) omega) := by
    dsimp only [PhysicalAttachment.physicalSlice]
    infer_instance
  have hsliceF : ∀ J y,
      ((PhysicalAttachment.physicalSlice (X L) omega) y).map
        (ContinuousPath.finsetEvaluation J) =
      SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) J y := by
    intro J y
    change (X L (omega, y)).map (ContinuousPath.finsetEvaluation J) = _
    rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation J)]
    exact hfdd J y
  intro I x
  rw [hYeq]
  exact aux_lim_lem_mean_exit_inlined_physical_local_rescaled_fdd _ _ hcons (PhysicalAttachment.physicalSlice (X L) omega)
    hslice hsliceF
    (physicalCoordinates m z).symm (rawClock M L m) (rawClock_pos M L m) hconj I x

/-- Finite-cutoff application against the correct bilateral window law. There are no
caller-supplied process, coefficient-identity, moment-bank or growth witnesses. -/
theorem aux_lim_lem_mean_exit_actual_finite_local_transport (M : GMCModel d) (l m : ℕ) (z : Vec d) :
    ∃ X Y : PhysicalAttachment.PhysicalKernel d,
      IsMarkovKernel X ∧ IsMarkovKernel Y ∧
      aux_lim_lem_mean_exit_inlined_physical_local_source_characterization M l X ∧
      (∀ omega x, Y (omega, x) =
        (X (omega, physicalCoordinates m z x)).map
          (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M l m))) ∧
      ∀ᵐ eta ∂nativeLaw M,
        ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
          IsWeakEllipticResolvent
            (finiteLocalCoefficient M l m (bilateralEnvironment eta))
            (finiteLocalSpeed M l m (bilateralEnvironment eta)) D ∧
          (D.fellerKernelSemigroup hdense).IsConservative ∧
          ∀ I x, (Y (physicalEnvironment M m z eta, x)).map
              (ContinuousPath.finsetEvaluation I) =
            SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
  obtain ⟨X, Y, hX, hY, hsource, heq, hgood⟩ := aux_lim_lem_mean_exit_actual_physical_local_family M l m z
  refine ⟨X, Y, hX, hY, hsource, heq, ?_⟩
  filter_upwards [(physicalEnvironment_preserving M m z).quasiMeasurePreserving.ae hgood,
    finite_local_identification M l m z] with eta h hid
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := h
  have hc : localCoefficient M l m z (physicalEnvironment M m z eta) =
      finiteLocalCoefficient M l m (bilateralEnvironment eta) := funext fun x => (hid x).2
  have hb : localSpeed M l m z (physicalEnvironment M m z eta) =
      finiteLocalSpeed M l m (bilateralEnvironment eta) := funext fun x => (hid x).1
  rw [hc, hb] at hweak
  exact ⟨D, hdense, hweak, hcons, hfdd⟩

/-- The constructed affine physical law is the unique every-start local law.
Candidate data are quantified in the conclusion; the model supplies the actual datum. -/
theorem aux_lim_lem_mean_exit_actual_physical_local_law_characterization (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) (z : Vec d) :
    ∃ X Y : PhysicalAttachment.PhysicalKernel d,
      IsMarkovKernel X ∧ IsMarkovKernel Y ∧
      aux_lim_lem_mean_exit_inlined_physical_local_source_characterization M L X ∧
      (∀ omega x, Y (omega, x) =
        (X (omega, physicalCoordinates m z x)).map
          (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m))) ∧
      ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
        ∀ (E : C0ResolventDatum (Vec d)) (hedense : ∀ mu, DenseRange (E.operator mu))
          (Q : Kernel (Vec d) (ContinuousPath (Vec d))),
          IsWeakEllipticResolvent (localCoefficient M L m z omega)
            (localSpeed M L m z omega) E →
          (∀ I x, Q.map (ContinuousPath.finsetEvaluation I) x =
            SubMarkovKernelSemigroup.finiteSetKernel (E.fellerKernelSemigroup hedense) I x) →
          PhysicalAttachment.physicalSlice Y omega = Q := by
  obtain ⟨X, Y, hX, hY, hsource, heq, hgood⟩ := aux_lim_lem_mean_exit_actual_physical_local_family M L m z
  refine ⟨X, Y, hX, hY, hsource, heq, ?_⟩
  filter_upwards [hgood] with omega h
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := h
  intro E hedense Q hE hQ
  letI : IsMarkovKernel Y := hY
  have hslice : IsMarkovKernel (PhysicalAttachment.physicalSlice Y omega) := by
    dsimp only [PhysicalAttachment.physicalSlice]
    infer_instance
  apply local_law_unique M L m z omega D E hweak hE hdense hedense _ Q hslice
  · intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    exact hfdd I x
  · exact hQ

/-- Top uses the constructed full infrared field, on the actual chaos law. -/
theorem aux_lim_lem_mean_exit_actual_top_local_transport (M : GMCModel d) (m : ℕ) (z : Vec d) :
    ∃ X Y : PhysicalAttachment.PhysicalKernel d,
      IsMarkovKernel X ∧ IsMarkovKernel Y ∧
      aux_lim_lem_mean_exit_inlined_physical_local_source_characterization M ⊤ X ∧
      (∀ omega x, Y (omega, x) =
        (X (omega, physicalCoordinates m z x)).map
          (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M ⊤ m))) ∧
      ∀ᵐ eta ∂nativeLaw M,
        ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
          IsWeakEllipticResolvent
            (cutoffCoefficient M (infraredField M) (bilateralEnvironment eta) m)
            (cutoffSpeedDensity M (infraredField M) (bilateralEnvironment eta) m) D ∧
          (D.fellerKernelSemigroup hdense).IsConservative ∧
          ∀ I x, (Y (physicalEnvironment M m z eta, x)).map
              (ContinuousPath.finsetEvaluation I) =
            SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
  obtain ⟨X, Y, hX, hY, hsource, heq, hgood⟩ := aux_lim_lem_mean_exit_actual_physical_local_family M ⊤ m z
  refine ⟨X, Y, hX, hY, hsource, heq, ?_⟩
  filter_upwards [(physicalEnvironment_preserving M m z).quasiMeasurePreserving.ae hgood,
    top_local_identification M m z] with eta h hid
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := h
  have hc : localCoefficient M ⊤ m z (physicalEnvironment M m z eta) =
      cutoffCoefficient M (infraredField M) (bilateralEnvironment eta) m := funext fun x => (hid x).2
  have hb : localSpeed M ⊤ m z (physicalEnvironment M m z eta) =
      cutoffSpeedDensity M (infraredField M) (bilateralEnvironment eta) m := funext fun x => (hid x).1
  rw [hc, hb] at hweak
  exact ⟨D, hdense, hweak, hcons, hfdd⟩

/-- The landed canonical Feller restart theorem supplies strong Markov for the
actual local law, after its every-start FDD characterization is proved. -/
theorem aux_lim_lem_mean_exit_actual_local_strongMarkov_family (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) (z : Vec d) :
    ∃ Y : PhysicalAttachment.PhysicalKernel d, IsMarkovKernel Y ∧
      ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
        StrongMarkov ((PhysicalAttachment.physicalSlice Y omega).map LifetimePath.ofContinuousPath) ∧
        ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
          IsWeakEllipticResolvent (localCoefficient M L m z omega) (localSpeed M L m z omega) D ∧
          (D.fellerKernelSemigroup hdense).IsConservative ∧
          ∀ I x, (Y (omega, x)).map (ContinuousPath.finsetEvaluation I) =
            SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
  obtain ⟨X, Y, hX, hY, hsource, heq, hgood⟩ := aux_lim_lem_mean_exit_actual_physical_local_family M L m z
  refine ⟨Y, hY, ?_⟩
  filter_upwards [hgood] with omega h
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := h
  letI : IsMarkovKernel Y := hY
  have hslice : IsMarkovKernel (PhysicalAttachment.physicalSlice Y omega) := by
    dsimp only [PhysicalAttachment.physicalSlice]
    infer_instance
  have hF : ∀ I x, (PhysicalAttachment.physicalSlice Y omega).map
      (ContinuousPath.finsetEvaluation I) x =
        SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    exact hfdd I x
  exact ⟨SubdiffusiveProcess.Probability.Diffusion.strongMarkov_of_restart
    (PhysicalAttachment.fellerRestart d _ hcons
      (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense)
      (PhysicalAttachment.physicalSlice Y omega) hslice hF), D, hdense, hweak, hcons, hfdd⟩

end Paper
end aux_lim_lem_mean_exit_inline_15



noncomputable section aux_lim_lem_mean_exit_inline_16




open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set SubdiffusiveProcess
open SubdiffusiveProcess.Section10
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Assumptions.CoefficientRegularity
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.Section10.PhysicalAttachment
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal NNReal
namespace Paper

/-- Actual local weak realization and every-start regularity, with no
Sobolev or exit-bound input. All finite cutoffs (including zero and m>L)
and top use the unchanged raw clock. -/
theorem aux_lim_lem_mean_exit_inlined_torsion_exit_actual_local_regularity_of_smooth_density
    (hDensity : SmoothReversibleKilledDensitySupplier) {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess) :
    ∀ (M : GMCModel d) (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
      ∃ X Y : PhysicalKernel d,
      IsMarkovKernel X ∧ IsMarkovKernel Y ∧
      aux_lim_lem_mean_exit_inlined_physical_local_source_characterization M L X ∧
      (∀ omega x, Y (omega, x) = (X (omega, physicalCoordinates m z x)).map
        (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m))) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure,
        let law := (physicalSlice Y omega).map LifetimePath.ofContinuousPath
        let U : Set (SpatialCoordinates d) := Metric.ball 0 (1 / 2)
        LocalDiffusion (localCoefficient M L m z omega) (localSpeed M L m z omega) law ∧
        UnitDiscountOccupationLSC law U := by
  letI : NeZero d := ⟨by omega⟩
  intro M L m z
  obtain ⟨X, Y, hX, hY, hsource, heq, hactual⟩ := aux_lim_lem_mean_exit_actual_physical_local_family M L m z
  refine ⟨X, Y, hX, hY, hsource, heq, ?_⟩
  filter_upwards [hactual, hsource] with omega homega hphysical
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := homega
  obtain ⟨D0, hdense0, hweak0, hcons0, hfdd0⟩ := hphysical
  letI := hX
  letI := hY
  letI : IsMarkovKernel (physicalSlice X omega) := by dsimp only [physicalSlice]; infer_instance
  letI : IsMarkovKernel (physicalSlice Y omega) := by dsimp only [physicalSlice]; infer_instance
  letI : IsMarkovKernel ((physicalSlice Y omega).map LifetimePath.ofContinuousPath) :=
    Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
  have hfdd0' : ∀ I x, (physicalSlice X omega).map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D0.fellerKernelSemigroup hdense0) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    exact hfdd0 I x
  have hdens := hDensity d hd (coefficientAt M L omega) (coefficientAt_pos M L omega)
    (locallyC11_coefficientAt M L omega) D0 hdense0 hweak0 hcons0
    (physicalSlice X omega) inferInstance hfdd0'
  let U : Set (SpatialCoordinates d) := Metric.ball 0 (1 / 2)
  let e := physicalCoordinates (d := d) m z
  have hU : IsOpen U := Metric.isOpen_ball
  have hUb : Bornology.IsBounded U := Metric.isBounded_ball
  have heUb : Bornology.IsBounded (e '' U) :=
    (hUb.isCompact_closure.image e.continuous).isBounded.subset (image_mono subset_closure)
  have hdens' : HasContinuousKilledDensityOn (coefficientAt M L omega)
      ((physicalSlice X omega).map LifetimePath.ofContinuousPath) (e '' U) := by
    obtain ⟨p, hm, hp, he, hc⟩ := hdens (e '' U) (e.isOpen_image.mpr hU) heUb
    exact ⟨p, ⟨hm, hp, he⟩, hc⟩
  have hls : UnitDiscountOccupationLSC
      ((physicalSlice Y omega).map LifetimePath.ofContinuousPath) U := fun _ =>
    discountedUnitOccupation_lowerSemicontinuousOn_of_rescaled_density
      (physicalSlice X omega) (physicalSlice Y omega) e (rawClock M L m) (rawClock_pos M L m)
      (fun x => heq omega x) hU hdens' _
  have hfdd' : ∀ I x, (physicalSlice Y omega).map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    exact hfdd I x
  have hF := D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  have hsm := SubdiffusiveProcess.Probability.Diffusion.strongMarkov_of_restart
    (fellerRestart d _ hcons hF (physicalSlice Y omega) inferInstance hfdd')
  have hb := continuous_localSpeed M L m z omega
  have hbpos := localSpeed_pos M L m z omega
  have hA : Continuous (localCoefficient M L m z omega) := continuous_const.mul hb
  have hApos (x : SpatialCoordinates d) : 0 < localCoefficient M L m z omega x :=
    mul_pos (inv_pos.mpr (ahom_pos M _)) (hbpos x)
  have hgen := SubdiffusiveProcess.E7.killedGenerator_of_leaf hA hb hApos hbpos
    (D.fellerKernelSemigroup hdense) hcons hF D hweak (D.solution_eq_laplace hdense)
    (physicalSlice Y omega) hfdd' hFOT
  have hlocal : LocalDiffusion (localCoefficient M L m z omega) (localSpeed M L m z omega)
      ((physicalSlice Y omega).map LifetimePath.ofContinuousPath) := by
    refine ⟨hsm, ?_, ?_⟩
    · intro S hS
      exact ⟨coefficientOn_of_continuous_pos hA hApos hS.isBounded,
        coefficientOn_of_continuous_pos hb hbpos hS.isBounded⟩
    · intro V hV hVb s hs f hf
      exact SubdiffusiveProcess.Probability.Diffusion.killedResolvent_clause_of_killedGenerator hgen hV hVb
        (coefficientOn_of_continuous_pos hA hApos hVb)
        (coefficientOn_of_continuous_pos hb hbpos hVb) hs hf
  exact ⟨hlocal, hls⟩



theorem aux_lim_lem_mean_exit_inlined_torsion_exit_actual_local_sobolev_consumer_of_smooth_density
    (hDensity : SmoothReversibleKilledDensitySupplier) {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess)
    (M : GMCModel d) (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d) :
    ∃ X Y : PhysicalKernel d,
      IsMarkovKernel X ∧ IsMarkovKernel Y ∧
      aux_lim_lem_mean_exit_inlined_physical_local_source_characterization M L X ∧
      (∀ omega x, Y (omega, x) = (X (omega, physicalCoordinates m z x)).map
        (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m))) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure,
        let law := (physicalSlice Y omega).map LifetimePath.ofContinuousPath
        let U : Set (SpatialCoordinates d) := Metric.ball 0 (1 / 2)
        UnitDiscountOccupationLSC law U ∧ ∀ Ksob : ℝ, 0 < Ksob →
          TorsionSobolevBound (localCoefficient M L m z omega) (localSpeed M L m z omega) U
            (2 * (d : ℝ) / ((d : ℝ) - 1)) Ksob →
          ∀ x ∈ U, meanExit law U x ≤ ENNReal.ofReal
            (torsionConstant (2 * (d : ℝ) / ((d : ℝ) - 1)) * Ksob *
              (weightedMeasure (localSpeed M L m z omega) U).toReal ^ (1 / (d : ℝ))) := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨X, Y, hX, hY, hsource, heq, hactual⟩ :=
    aux_lim_lem_mean_exit_inlined_torsion_exit_actual_local_regularity_of_smooth_density hDensity hd hFOT M L m z
  refine ⟨X, Y, hX, hY, hsource, heq, ?_⟩
  filter_upwards [hactual] with omega homega
  refine ⟨homega.2, ?_⟩
  intro Ksob hKsob hSob
  letI := hY
  letI : IsMarkovKernel (physicalSlice Y omega) := by dsimp only [physicalSlice]; infer_instance
  letI : IsMarkovKernel ((physicalSlice Y omega).map LifetimePath.ofContinuousPath) :=
    Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
  have hU : IsOpenBoundedConvexDomain (Metric.ball (0 : Vec d) (1 / 2)) :=
    isOpenBoundedConvexDomain_ball 0 (by norm_num)
  have hne : (Metric.ball (0 : Vec d) (1 / 2)).Nonempty :=
    ⟨0, Metric.mem_ball_self (by norm_num)⟩
  have hb := coefficientOn_of_continuous_pos (continuous_localSpeed M L m z omega)
    (localSpeed_pos M L m z omega) hU.isBoundedDomain.isBounded
  have hp := killedSobolevExponent_gt_two hd
  have hpower := killedSobolev_one_sub_two_div hd
  simpa only [hpower] using
    localDiffusion_meanExit_le homega.1 hU hne hb hp hKsob hSob homega.2

end Paper
end aux_lim_lem_mean_exit_inline_16



noncomputable section aux_lim_lem_mean_exit_inline_17

open MeasureTheory ProbabilityTheory Homogenization MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace Paper

/-- Every finite/top actual local family has an every-start upper mean-exit
bank. The sole unproduced input is the precise smooth killed-density supplier;
FOT and all analytic estimates are discharged by their actual providers. -/
theorem aux_lim_lem_mean_exit_inlined_mean_exit_actual_local_upper_bank
    (hDensity : SmoothReversibleKilledDensitySupplier) {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∀ q : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
      ∃ C : ℝ, 0 < C ∧ ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
        ∃ X Y : PhysicalAttachment.PhysicalKernel d, ∃ K : AnchoredC11Sample d → ℝ,
          IsMarkovKernel X ∧ IsMarkovKernel Y ∧
          aux_lim_lem_mean_exit_inlined_physical_local_source_characterization M L X ∧
          (∀ ω x, Y (ω, x) = (X (ω, physicalCoordinates m z x)).map
            (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m))) ∧
          Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
          (∫⁻ ω, ENNReal.ofReal (K ω ^ q)
            ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
          ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
            ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (1 / 2),
              meanExit ((PhysicalAttachment.physicalSlice Y ω).map LifetimePath.ofContinuousPath)
                (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) x ≤ ENNReal.ofReal (K ω) := by
  obtain ⟨B, hB, hstatic⟩ := aux_lim_lem_mean_exit_inlined_physical_sobolev_static_bank hd
  obtain ⟨D, hD, hdet⟩ := aux_lim_lem_mean_exit_inlined_killed_sobolev_of_mass_coercivity hd B
  let T := torsionConstant (2 * (d : ℝ) / ((d : ℝ) - 1))
  have hT : 0 < T := torsionConstant_pos _
  let E := T * D
  have hE : 0 < E := mul_pos hT hD
  intro q
  obtain ⟨δ, hδ, hmodels⟩ := hstatic (meanExitMomentOrder q) (le_max_left _ _)
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨Cs, hCs, hbank⟩ := hmodels M hM
  let C := if 0 < q then 1 + E ^ q * Cs else 1
  refine ⟨C, by dsimp [C]; split_ifs <;> positivity, ?_⟩
  intro L m z
  obtain ⟨Ks, hKs, hsone, hsmoment, hscert⟩ := hbank L m z
  let K := fun ω => meanExitBankConstant E (Ks ω)
  have hKm : Measurable K := measurable_const.max
    (measurable_const.mul (hKs.pow_const 3))
  have hm := meanExitBankConstant_moment (PhysicalAttachment.physicalLaw M).toMeasure
    hKs hsone hE.le hCs.le hsmoment
  obtain ⟨X, Y, hX, hY, hsource, heq, hlocal⟩ :=
    aux_lim_lem_mean_exit_inlined_torsion_exit_actual_local_sobolev_consumer_of_smooth_density hDensity hd
      inputs_classical_fot_part_process M L m z
  refine ⟨X, Y, K, hX, hY, hsource, heq, hKm, fun _ => le_max_left _ _, hm, ?_⟩
  filter_upwards [hscert, hlocal] with ω hs hl
  have hAb := localCoefficientOn M L m z ω
    (U := Metric.ball (0 : SpatialCoordinates d) (1 / 2)) Metric.isBounded_ball
  have hSob := hdet _ _ _ (hsone ω) hs.1 hs.2 hAb
  have hpos : 0 < D * Ks ω ^ 2 := mul_pos hD
    (sq_pos_of_pos (zero_lt_one.trans_le (hsone ω)))
  have hcap := hl.2 (D * Ks ω ^ 2) hpos (fun v => (hSob v).2.2.1)
  intro x hx
  apply (hcap x hx).trans
  apply ENNReal.ofReal_le_ofReal
  have hmass := hs.unitCube_mass_power_le hd (hsone ω)
  have hscalar := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg hT.le (mul_nonneg hD.le (sq_nonneg (Ks ω))))
  have hfactor : T * (D * Ks ω ^ 2) * Ks ω = E * Ks ω ^ 3 := by
    dsimp only [E]
    ring
  rw [hfactor] at hscalar
  exact hscalar.trans (le_max_right _ _)

end Paper
end aux_lim_lem_mean_exit_inline_17



noncomputable section aux_lim_lem_mean_exit_inline_18

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal



namespace Paper

/-- The cube `z + 𝖢_m` of side `3^m` centred at `z` (the open sup-norm ball of radius `3^m/2`). -/
def aux_lim_lem_mean_exit_cube {d : ℕ} (z : SpatialCoordinates d) (m : ℤ) :
    Set (SpatialCoordinates d) :=
  Metric.ball z ((3 : ℝ) ^ m / 2)

/-- The time unit `3^{2m}/ahom_{m ∧ L}` of the local normalization (`tight:eq-local-time`); for the
untruncated diffusion (`L = ⊤`) it is `3^{2m}/ahom_m`. -/
def aux_lim_lem_mean_exit_localTime {d : ℕ} (M : GMCModel d) (L : WithTop ℕ) (m : ℕ) : ℝ :=
  (3 : ℝ) ^ (2 * m) / ahom M (match L with | ⊤ => m | (l : ℕ) => min m l)

/-- `𝐄[τ_U^p]` for the path law `Q` and the exit time `τ_U` from `U`. -/
def aux_lim_lem_mean_exit_exitMoment {d : ℕ} (Q : Measure (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂Q

/-- The probability space of the environment of the diffusions `X^{(L)}` and `X`: the layers
`(γ_k)_{k ≥ 0}` on the anchored `C^{1,1}` carrier (`SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw`).
(Body identical to `SubdiffusiveProcess.Section10.PhysicalAttachment.physicalLaw`.) -/
def aux_lim_lem_mean_exit_physicalLaw {d : ℕ} (M : GMCModel d) :
    ProbabilityMeasure (AnchoredC11Sample d) :=
  anchoredC11SampleLaw M (Section6Anchored.measurableSet_anchoredC11GoodSet d)
    (Section6Anchored.measure_anchoredC11GoodSet_eq_one M)

/-- `X L` is a Markov kernel `(ω, x) ↦ 𝐏_x^ω` of path laws whose finite-dimensional distributions,
for almost every environment and every start `x`, are those of the conservative Feller semigroup of
the weak elliptic resolvent of the coefficient `coefficientAt M L ω` (the truncation `a_L` for a
finite `L`, the anchored coefficient `a` for `L = ⊤`), with reversible measure `a dx`.  This is the
paper's definition of `X^{(L)}` and `X` (generator `a^{-1} ∇·(a ∇)`); by finite-dimensional
determination it fixes the law of the process at every start.  (The family exists:
`SubdiffusiveProcess.Section10.PhysicalAttachment.exists_physical_family`.) -/
def aux_lim_lem_mean_exit_IsPhysicalFamily {d : ℕ} (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)) :
    Prop :=
  ∀ᵐ omega ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
    ∃ D : C0ResolventDatum (SpatialCoordinates d),
    ∃ hdense : ∀ mu, DenseRange (D.operator mu),
      IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
      (D.fellerKernelSemigroup hdense).IsConservative ∧
      ∀ (I : Finset ℝ≥0) (x : SpatialCoordinates d),
        ((X L).map (ContinuousPath.finsetEvaluation I)) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x


end Paper
end aux_lim_lem_mean_exit_inline_18



noncomputable section aux_lim_lem_mean_exit_inline_19

open MeasureTheory Homogenization MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.Section10.ExitMomentPassage
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace Paper

theorem aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_physicalLaw_eq {d : ℕ} (M : GMCModel d) :
    aux_lim_lem_mean_exit_physicalLaw M = SubdiffusiveProcess.Section10.PhysicalAttachment.physicalLaw M := rfl

theorem aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_localTime_eq {d : ℕ} (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) :
    aux_lim_lem_mean_exit_localTime M L m = (rawClock M L m : ℝ) := by
  cases L using WithTop.recTopCoe with
  | top => simp only [aux_lim_lem_mean_exit_localTime, rawClock, NNReal.coe_mk,
      activeScale, WithTop.untopD_top, min_self]
  | coe l => simp only [aux_lim_lem_mean_exit_localTime, rawClock, NNReal.coe_mk,
      activeScale, WithTop.untopD_coe]

theorem aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_cube_image {d : ℕ} (m : ℕ) (z : SpatialCoordinates d) :
    physicalCoordinates m z '' Metric.ball (0 : SpatialCoordinates d) (1 / 2) =
      aux_lim_lem_mean_exit_cube z (m : ℤ) := by
  rw [physicalCoordinates_image_ball]
  simp only [aux_lim_lem_mean_exit_cube, zpow_natCast, div_eq_mul_inv, one_mul, mul_comm]

theorem aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_inner_cube_image {d : ℕ} (m : ℕ) (z : SpatialCoordinates d) :
    physicalCoordinates m z '' Metric.ball (0 : SpatialCoordinates d) (1 / 18) =
      aux_lim_lem_mean_exit_cube z ((m : ℤ) - 2) := by
  rw [physicalCoordinates_image_ball]
  unfold aux_lim_lem_mean_exit_cube
  congr 1
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  norm_num
  ring

/-- Restore the literal raw clock for an actual affine local law, without
any finiteness assumption on its exit time. -/
theorem aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_clock_transport {d : ℕ} (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d)
    (X Y : SubdiffusiveProcess.Section10.PhysicalAttachment.PhysicalKernel d)
    (hY : ∀ ω x, Y (ω, x) = (X (ω, physicalCoordinates m z x)).map
      (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m)))
    (ω : AnchoredC11Sample d) (x : SpatialCoordinates d) :
    aux_lim_lem_mean_exit_exitMoment (X (ω, physicalCoordinates m z x))
      (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1 =
      ENNReal.ofReal (aux_lim_lem_mean_exit_localTime M L m) *
        meanExit ((SubdiffusiveProcess.Section10.PhysicalAttachment.physicalSlice Y ω).map
          LifetimePath.ofContinuousPath) (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) x := by
  rw [SubdiffusiveProcess.Section10.ExitTailMoments.continuous_meanExit_transport _ _ Metric.isOpen_ball]
  change _ = ENNReal.ofReal (aux_lim_lem_mean_exit_localTime M L m) *
    ∫⁻ w, ContinuousPath.exitTime (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) w ∂Y (ω, x)
  rw [hY]
  have h := exitMoment_eq_clock_mul_map (X (ω, physicalCoordinates m z x))
    (physicalCoordinates m z) (rawClock M L m) (rawClock_pos M L m)
    (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) Metric.isOpen_ball 1 (by norm_num)
  simpa only [aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_cube_image, ENNReal.rpow_one,
    aux_lim_lem_mean_exit_exitMoment, aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_localTime_eq,
    ENNReal.ofReal_coe_nnreal] using h

end Paper
end aux_lim_lem_mean_exit_inline_19



noncomputable section aux_lim_lem_mean_exit_inline_20

open Filter MeasureTheory ProbabilityTheory Homogenization MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.Section10.PhysicalAttachment
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Section10
open scoped ENNReal
namespace Paper

/-- The uniform upper moment bank for every physical family in the reviewed
root, with its actual raw clock. Only the precise density supplier is pending. -/
theorem aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_upper_bank
    (hDensity : SmoothReversibleKilledDensitySupplier) {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∀ q : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
      ∃ C : ℝ, 0 < C ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
            (∫⁻ ω, ENNReal.ofReal (K ω ^ q)
              ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
            ∀ᵐ ω ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure,
              ∀ x ∈ aux_lim_lem_mean_exit_cube z (m : ℤ),
                aux_lim_lem_mean_exit_exitMoment (X L (ω, x))
                  (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1 ≤
                  ENNReal.ofReal (K ω * aux_lim_lem_mean_exit_localTime M L m) := by
  intro q
  obtain ⟨δ, hδ, hmodels⟩ := aux_lim_lem_mean_exit_inlined_mean_exit_actual_local_upper_bank hDensity hd q
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨C, hC, hbank⟩ := hmodels M hM
  refine ⟨C, hC, ?_⟩
  intro X hX hphysical L m z
  obtain ⟨X0, Y, K, hX0, hY, hsource, heq, hK, hone, hm, hcap⟩ := hbank L m z
  refine ⟨K, hK, hone, hm, ?_⟩
  filter_upwards [hcap, hsource, hphysical] with ω hω hωsource hωphysical
  obtain ⟨D, hdense, hweak, _, hfdd⟩ := hωphysical L
  obtain ⟨E, hedense, heweak, _, hefdd⟩ := hωsource
  letI := hX L
  have hslice : IsMarkovKernel (physicalSlice (X L) ω) := by
    dsimp only [physicalSlice]
    infer_instance
  have hDfd : ∀ I x, (physicalSlice (X L) ω).map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    have h := hfdd I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)] at h
    exact h
  have hEfd : ∀ I x, (physicalSlice X0 ω).map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (E.fellerKernelSemigroup hedense) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    exact hefdd I x
  have hsame := physical_law_unique M L ω D E hweak heweak hdense hedense
    (physicalSlice (X L) ω) (physicalSlice X0 ω) hslice hDfd hEfd
  intro x hx
  rw [← aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_cube_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hrow : X L (ω, physicalCoordinates m z y) = X0 (ω, physicalCoordinates m z y) :=
    congrArg (fun law => law (physicalCoordinates m z y)) hsame
  rw [hrow, aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_clock_transport M L m z X0 Y heq]
  calc
    _ ≤ ENNReal.ofReal (aux_lim_lem_mean_exit_localTime M L m) * ENNReal.ofReal (K ω) :=
      mul_le_mul_right (hω y hy) _
    _ = ENNReal.ofReal (K ω * aux_lim_lem_mean_exit_localTime M L m) := by
      rw [← ENNReal.ofReal_mul (by
        rw [aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_localTime_eq]
        exact (rawClock M L m).coe_nonneg), mul_comm]

end Paper
end aux_lim_lem_mean_exit_inline_20



noncomputable section aux_lim_lem_mean_exit_inline_21

open Filter MeasureTheory ProbabilityTheory SubdiffusiveProcess MarkovProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
namespace Paper

/-- The first reviewed display, from the proved q=1 upper bank. The source
uses the literal lower integral of the supremum; no envelope premise is added. -/
theorem aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_averaged_upper
    (hDensity : SmoothReversibleKilledDensitySupplier)
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ C : ℝ, 0 < C ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          (∫⁻ omega, (⨆ x ∈ aux_lim_lem_mean_exit_cube z (m : ℤ),
              aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1)
            ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤
            ENNReal.ofReal (C * aux_lim_lem_mean_exit_localTime M L m) := by
  obtain ⟨δ, hδ, hmodels⟩ := aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_upper_bank hDensity hd 1
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨C, hC, hbank⟩ := hmodels M hM
  refine ⟨C, hC, ?_⟩
  intro X hX hphysical L m z
  obtain ⟨K, hK, hone, hm, hs⟩ := hbank X hX hphysical L m z
  have ht : 0 < aux_lim_lem_mean_exit_localTime M L m := by
    rw [aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_localTime_eq]
    exact rawClock_pos M L m
  have hKm : (∫⁻ ω, ENNReal.ofReal (K ω)
      ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal C := by
    simpa only [Real.rpow_one] using hm
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (K ω * aux_lim_lem_mean_exit_localTime M L m)
          ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure := by
      apply lintegral_mono_ae
      filter_upwards [hs] with ω hω
      exact iSup_le fun x => iSup_le fun hx => hω x hx
    _ = ENNReal.ofReal (aux_lim_lem_mean_exit_localTime M L m) *
        ∫⁻ ω, ENNReal.ofReal (K ω)
          ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure := by
      simp_rw [mul_comm (K _) (aux_lim_lem_mean_exit_localTime M L m),
        ENNReal.ofReal_mul ht.le]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (aux_lim_lem_mean_exit_localTime M L m) * ENNReal.ofReal C :=
      mul_le_mul_right hKm _
    _ = _ := by rw [← ENNReal.ofReal_mul ht.le, mul_comm]

end Paper
end aux_lim_lem_mean_exit_inline_21



noncomputable section aux_lim_lem_mean_exit_inline_22

open Filter MeasureTheory ProbabilityTheory SubdiffusiveProcess MarkovProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
namespace Paper

/-- Exact reviewed conclusion relative to its two named unproduced dependencies.
This conditional assembly is not the source root: P3 and the actual physical
fast-exit moment bank must be supplied before sealing the unchanged principal. -/
theorem aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_of_density_fast_exit
    (hDensity : SmoothReversibleKilledDensitySupplier)
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (hFast : ∀ Q : ℝ, 1 ≤ Q → ∃ δ : ℝ, 0 < δ ∧
      ∀ M : GMCModel d, M.delta ≤ δ → ∃ C : ℝ, 0 < C ∧
        ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
          ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
            ∃ F : AnchoredC11Sample d → ℝ, Measurable F ∧ (∀ ω, 1 ≤ F ω) ∧
              (∫⁻ ω, ENNReal.ofReal (F ω ^ Q)
                ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
              ∀ᵐ ω ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure,
                ∀ t : ℝ, 0 < t → ∀ x ∈ aux_lim_lem_mean_exit_cube z ((m : ℤ) - 2),
                  X L (ω, x) {w | ContinuousPath.exitTime (aux_lim_lem_mean_exit_cube z (m : ℤ)) w ≤
                    ENNReal.ofReal (t * aux_lim_lem_mean_exit_localTime M L m)} ≤
                      ENNReal.ofReal (F ω * Real.sqrt t)) :
    (∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ C : ℝ, 0 < C ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          (∫⁻ omega, (⨆ x ∈ aux_lim_lem_mean_exit_cube z (m : ℤ),
              aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1)
            ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤
            ENNReal.ofReal (C * aux_lim_lem_mean_exit_localTime M L m)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ q : ℝ,
      ∃ deltaq : ℝ, 0 < deltaq ∧
      ∀ M : GMCModel d, M.delta ≤ deltaq →
      ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
            (∫⁻ omega, ENNReal.ofReal (K omega ^ q)
              ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal Cq ∧
            ∀ᵐ omega ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure,
              (∀ x ∈ aux_lim_lem_mean_exit_cube z (m : ℤ),
                aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                  (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1 ≤
                  ENNReal.ofReal (K omega * aux_lim_lem_mean_exit_localTime M L m)) ∧
              (∀ x ∈ aux_lim_lem_mean_exit_cube z ((m : ℤ) - 2),
                ENNReal.ofReal (c * K omega ^ (-2 : ℤ) * aux_lim_lem_mean_exit_localTime M L m) ≤
                  aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                    (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1)) := by
  constructor
  · exact aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_averaged_upper hDensity hd
  · refine ⟨1 / 8, by norm_num, ?_⟩
    intro q
    obtain ⟨δu, hδu, hupper⟩ := aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_upper_bank hDensity hd q
    let Q := max 1 q
    obtain ⟨δf, hδf, hfast⟩ := hFast Q (le_max_left _ _)
    refine ⟨min δu δf, lt_min hδu hδf, ?_⟩
    intro M hM
    obtain ⟨Cu, hCu, hu⟩ := hupper M (hM.trans (min_le_left _ _))
    obtain ⟨Cf, hCf, hf⟩ := hfast M (hM.trans (min_le_right _ _))
    let C := if 0 < q then Cu + Cf else 1
    refine ⟨C, by dsimp [C]; split_ifs <;> positivity, ?_⟩
    intro X hX hphysical L m z
    obtain ⟨Ku, hKu, huone, hum, hucert⟩ := hu X hX hphysical L m z
    obtain ⟨F, hF, hfone, hfm, hfcert⟩ := hf X hX hphysical L m z
    let K := fun ω => max (Ku ω) (F ω)
    have hone : ∀ ω, 1 ≤ K ω := fun ω => (huone ω).trans (le_max_left _ _)
    refine ⟨K, hKu.max hF, hone, ?_, ?_⟩
    · dsimp only [C]
      split_ifs with hq
      · have hfmq : (∫⁻ ω, ENNReal.ofReal (F ω ^ q)
            ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal Cf :=
          (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow_of_exponent_le (hfone ω) (le_max_right 1 q))).trans hfm
        exact lintegral_max_rpow_le (aux_lim_lem_mean_exit_physicalLaw M).toMeasure hKu
          (fun ω => zero_le_one.trans (huone ω)) (fun ω => zero_le_one.trans (hfone ω))
          hq.le hCu.le hCf.le hum hfmq
      · calc
          _ ≤ ∫⁻ _ : AnchoredC11Sample d, (1 : ℝ≥0∞)
              ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure := lintegral_mono fun ω => by
            simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
              (Real.rpow_le_one_of_one_le_of_nonpos (hone ω) (le_of_not_gt hq))
          _ = _ := by simp
    · filter_upwards [hucert, hfcert] with ω hωu hωf
      have ht : 0 < aux_lim_lem_mean_exit_localTime M L m := by
        rw [aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_localTime_eq]
        exact rawClock_pos M L m
      constructor
      · intro x hx
        exact (hωu x hx).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le))
      · intro x hx
        letI := hX L
        have htau : Measurable (ContinuousPath.exitTime (aux_lim_lem_mean_exit_cube z (m : ℤ))) :=
          ContinuousPath.measurable_exitTime _ Metric.isOpen_ball
        have h := meanExit_ge_of_fast_exit (X L (ω, x)) _ htau (hone ω) ht (fun t ht =>
          (hωf t ht x hx).trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))))
        simpa only [aux_lim_lem_mean_exit_exitMoment, ENNReal.rpow_one] using h

end Paper
end aux_lim_lem_mean_exit_inline_22



noncomputable section aux_lim_lem_mean_exit_inline_23

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
namespace Paper

/-- Actual all-H10 physical killed Sobolev application for every finite cutoff and top.
B and D precede q; Q=max(1,2q) precedes the disorder threshold; both moment
constants precede L,m,z. CoefficientOn is supplied by the actual coefficients. -/
theorem aux_lim_lem_mean_exit_inlined_physical_killed_sobolev_moment_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ B D : ℝ, 0 < B ∧ 0 < D ∧ ∀ q : ℝ,
      ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
        ∃ Cs Csob : ℝ, 0 < Cs ∧ 0 < Csob ∧ ∀ (L : WithTop ℕ) (m : ℕ),
          ∀ z : SpatialCoordinates d,
          ∃ Kphys Ksob : AnchoredC11Sample d → ℝ,
            Measurable Kphys ∧ (∀ ω, 1 ≤ Kphys ω) ∧
            Measurable Ksob ∧ (∀ ω, 1 ≤ Ksob ω) ∧
            (∀ ω, Ksob ω = max 1 (D * Kphys ω ^ 2)) ∧
            (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ killedSobolevMomentOrder q)
              ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal Cs ∧
            (∫⁻ ω, ENNReal.ofReal (Ksob ω ^ q)
              ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal Csob ∧
            ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
              PhysicalStaticBounds (localSpeed M L m z ω) (localCoefficient M L m z ω) B (Kphys ω) ∧
              KilledSobolevBound (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
                (localSpeed M L m z ω) (localCoefficient M L m z ω) (Ksob ω) := by
  obtain ⟨B, hB, hstatic⟩ := aux_lim_lem_mean_exit_inlined_physical_sobolev_static_bank hd
  obtain ⟨D, hD, hdet⟩ := aux_lim_lem_mean_exit_inlined_killed_sobolev_of_mass_coercivity hd B
  refine ⟨B, D, hB, hD, ?_⟩
  intro q
  let Q := killedSobolevMomentOrder q
  obtain ⟨δ, hδ, hmodels⟩ := hstatic Q (killedSobolevMomentOrder_ge_one q)
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨Cs, hCs, hscales⟩ := hmodels M hM
  let Csob := if 0 < q then 1 + D ^ q * Cs else 1
  have hCsob : 0 < Csob := by dsimp [Csob]; split_ifs <;> positivity
  refine ⟨Cs, Csob, hCs, hCsob, ?_⟩
  intro L m z
  obtain ⟨Kphys, hKp, hone, hmom, hbounds⟩ := hscales L m z
  have hA (ω : AnchoredC11Sample d) :
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.CoefficientOn
        (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) (localCoefficient M L m z ω) :=
    localCoefficientOn M L m z ω Metric.isBounded_ball
  have hSob : ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
      KilledSobolevBound (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
        (localSpeed M L m z ω) (localCoefficient M L m z ω) (D * Kphys ω ^ 2) := by
    filter_upwards [hbounds] with ω hω
    exact hdet _ _ _ (hone ω) hω.1 hω.2 (hA ω)
  obtain ⟨Ksob, hKs, hKsone, hKsm, hKseq, hKsb⟩ :=
    killedSobolev_moment_bank_of_bound (PhysicalAttachment.physicalLaw M).toMeasure
      (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
      (fun ω => localSpeed M L m z ω) (fun ω => localCoefficient M L m z ω)
      Kphys D Cs q hKp hone hD.le hCs.le hmom hA hSob
  refine ⟨Kphys, Ksob, hKp, hone, hKs, hKsone, hKseq, hmom, hKsm, ?_⟩
  filter_upwards [hbounds, hKsb] with ω hb hs using ⟨hb, hs⟩

end Paper
end aux_lim_lem_mean_exit_inline_23



noncomputable section aux_lim_lem_mean_exit_inline_24

open Filter MeasureTheory ProbabilityTheory SubdiffusiveProcess MarkovProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10
open scoped ENNReal
namespace Paper

/-- Term-level consumer at the full reviewed conclusion. Its two explicit
supplier inputs identify precisely why the source root is not yet sealed. -/
theorem aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_exact_consumer
    (hDensity : SmoothReversibleKilledDensitySupplier)
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (hFast : ∀ Q : ℝ, 1 ≤ Q → ∃ δ : ℝ, 0 < δ ∧
      ∀ M : GMCModel d, M.delta ≤ δ → ∃ C : ℝ, 0 < C ∧
        ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
          ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
            ∃ F : AnchoredC11Sample d → ℝ, Measurable F ∧ (∀ ω, 1 ≤ F ω) ∧
              (∫⁻ ω, ENNReal.ofReal (F ω ^ Q)
                ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
              ∀ᵐ ω ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure,
                ∀ t : ℝ, 0 < t → ∀ x ∈ aux_lim_lem_mean_exit_cube z ((m : ℤ) - 2),
                  X L (ω, x) {w | ContinuousPath.exitTime (aux_lim_lem_mean_exit_cube z (m : ℤ)) w ≤
                    ENNReal.ofReal (t * aux_lim_lem_mean_exit_localTime M L m)} ≤
                      ENNReal.ofReal (F ω * Real.sqrt t)) :
    (∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ C : ℝ, 0 < C ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          (∫⁻ omega, (⨆ x ∈ aux_lim_lem_mean_exit_cube z (m : ℤ),
              aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1)
            ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤
            ENNReal.ofReal (C * aux_lim_lem_mean_exit_localTime M L m)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ q : ℝ,
      ∃ deltaq : ℝ, 0 < deltaq ∧
      ∀ M : GMCModel d, M.delta ≤ deltaq →
      ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
            (∫⁻ omega, ENNReal.ofReal (K omega ^ q)
              ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal Cq ∧
            ∀ᵐ omega ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure,
              (∀ x ∈ aux_lim_lem_mean_exit_cube z (m : ℤ),
                aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                  (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1 ≤
                  ENNReal.ofReal (K omega * aux_lim_lem_mean_exit_localTime M L m)) ∧
              (∀ x ∈ aux_lim_lem_mean_exit_cube z ((m : ℤ) - 2),
                ENNReal.ofReal (c * K omega ^ (-2 : ℤ) * aux_lim_lem_mean_exit_localTime M L m) ≤
                  aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                    (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1)) := by
  exact aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_of_density_fast_exit hDensity hd hFast

/-- Convert the single named physical early-exit supplier to the exact source
auxiliary formulas. The physical family predicate is definitionally identical;
only the finite/top clock expression needs its already proved equality. -/
theorem aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_early_exit_interface {d : ℕ}
    (hEarlyExit : PhysicalMeanExitEarlyExitSupplier d) :
    ∀ Q : ℝ, 1 ≤ Q → ∃ δ : ℝ, 0 < δ ∧
      ∀ M : GMCModel d, M.delta ≤ δ → ∃ C : ℝ, 0 < C ∧
        ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
          ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
            ∃ F : AnchoredC11Sample d → ℝ, Measurable F ∧ (∀ ω, 1 ≤ F ω) ∧
              (∫⁻ ω, ENNReal.ofReal (F ω ^ Q)
                ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
              ∀ᵐ ω ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure,
                ∀ t : ℝ, 0 < t → ∀ x ∈ aux_lim_lem_mean_exit_cube z ((m : ℤ) - 2),
                  X L (ω, x) {w | ContinuousPath.exitTime (aux_lim_lem_mean_exit_cube z (m : ℤ)) w ≤
                    ENNReal.ofReal (t * aux_lim_lem_mean_exit_localTime M L m)} ≤
                      ENNReal.ofReal (F ω * Real.sqrt t) := by
  simpa only [PhysicalMeanExitEarlyExitSupplier, IsPhysicalMeanExitFamily,
    aux_lim_lem_mean_exit_IsPhysicalFamily, aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_physicalLaw_eq,
    aux_lim_lem_mean_exit_cube, aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_localTime_eq] using hEarlyExit

/-- Full reviewed mean-exit conclusion with exactly the two named suppliers.
This application is ready for sealing when both actual producers land;
it is an internal conditional theorem, not the unconditional source root. -/
theorem aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_of_suppliers
    (hDensity : SmoothReversibleKilledDensitySupplier)
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (hEarlyExit : PhysicalMeanExitEarlyExitSupplier d) :
    (∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ C : ℝ, 0 < C ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          (∫⁻ omega, (⨆ x ∈ aux_lim_lem_mean_exit_cube z (m : ℤ),
              aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1)
            ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤
            ENNReal.ofReal (C * aux_lim_lem_mean_exit_localTime M L m)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ q : ℝ,
      ∃ deltaq : ℝ, 0 < deltaq ∧
      ∀ M : GMCModel d, M.delta ≤ deltaq →
      ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
            (∫⁻ omega, ENNReal.ofReal (K omega ^ q)
              ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal Cq ∧
            ∀ᵐ omega ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure,
              (∀ x ∈ aux_lim_lem_mean_exit_cube z (m : ℤ),
                aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                  (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1 ≤
                  ENNReal.ofReal (K omega * aux_lim_lem_mean_exit_localTime M L m)) ∧
              (∀ x ∈ aux_lim_lem_mean_exit_cube z ((m : ℤ) - 2),
                ENNReal.ofReal (c * K omega ^ (-2 : ℤ) * aux_lim_lem_mean_exit_localTime M L m) ≤
                  aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                    (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1)) := by
  exact aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_of_density_fast_exit hDensity hd
    (aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_early_exit_interface hEarlyExit)



end Paper
end aux_lim_lem_mean_exit_inline_24

/- Inlined proved source application: SubdiffusiveProcess.Section10.MeanExitReversibleStatic. -/
noncomputable section aux_lim_lem_mean_exit_inline_25

/-! Exact source application with the reversible density input that is being
proved. Existing completed bank/assembly proofs are consumed directly;
no arbitrary-drift density statement is inferred. -/

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10.PhysicalAttachment SubdiffusiveProcess.Section10.PhysicalLocalTransport Paper
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Section10

/-- Full frozen source conclusion from the exact reversible supplier and static statement. -/
theorem aux_lim_lem_mean_exit_lim_lem_mean_exit_of_reversibleDensity_tightStatic
    (hDensity : SmoothReversibleKilledDensitySupplier)
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (hStatic : aux_lim_lem_mean_exit_TightStaticEstimateInput) :
    (∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ C : ℝ, 0 < C ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          (∫⁻ omega, (⨆ x ∈ aux_lim_lem_mean_exit_cube z (m : ℤ),
              aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1)
            ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤
            ENNReal.ofReal (C * aux_lim_lem_mean_exit_localTime M L m)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ q : ℝ,
      ∃ deltaq : ℝ, 0 < deltaq ∧
      ∀ M : GMCModel d, M.delta ≤ deltaq →
      ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
            (∫⁻ omega, ENNReal.ofReal (K omega ^ q)
              ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal Cq ∧
            ∀ᵐ omega ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure,
              (∀ x ∈ aux_lim_lem_mean_exit_cube z (m : ℤ),
                aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                  (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1 ≤
                  ENNReal.ofReal (K omega * aux_lim_lem_mean_exit_localTime M L m)) ∧
              (∀ x ∈ aux_lim_lem_mean_exit_cube z ((m : ℤ) - 2),
                ENNReal.ofReal (c * K omega ^ (-2 : ℤ) * aux_lim_lem_mean_exit_localTime M L m) ≤
                  aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                    (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1)) := by
  exact aux_lim_lem_mean_exit_inlined_lim_lem_mean_exit_of_suppliers hDensity hd
    (physicalMeanExitEarlyExitSupplier_of_localBank hd hDensity
      inputs_classical_fot_part_process
      (aux_lim_lem_mean_exit_physicalLocalExitMomentBank_of_tightStatic (by omega) hStatic))

end SubdiffusiveProcess.Section10
end aux_lim_lem_mean_exit_inline_25

noncomputable section aux_lim_lem_mean_exit_principal

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal



namespace Paper

theorem lim_lem_mean_exit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    (∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ C : ℝ, 0 < C ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          (∫⁻ omega, (⨆ x ∈ aux_lim_lem_mean_exit_cube z (m : ℤ),
              aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1)
            ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤
            ENNReal.ofReal (C * aux_lim_lem_mean_exit_localTime M L m)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ q : ℝ,
      ∃ deltaq : ℝ, 0 < deltaq ∧
      ∀ M : GMCModel d, M.delta ≤ deltaq →
      ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
            (∫⁻ omega, ENNReal.ofReal (K omega ^ q)
              ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal Cq ∧
            ∀ᵐ omega ∂(aux_lim_lem_mean_exit_physicalLaw M).toMeasure,
              (∀ x ∈ aux_lim_lem_mean_exit_cube z (m : ℤ),
                aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                  (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1 ≤
                  ENNReal.ofReal (K omega * aux_lim_lem_mean_exit_localTime M L m)) ∧
              (∀ x ∈ aux_lim_lem_mean_exit_cube z ((m : ℤ) - 2),
                ENNReal.ofReal (c * K omega ^ (-2 : ℤ) * aux_lim_lem_mean_exit_localTime M L m) ≤
                  aux_lim_lem_mean_exit_exitMoment (X L (omega, x))
                    (aux_lim_lem_mean_exit_cube z (m : ℤ)) 1)) := by
  exact SubdiffusiveProcess.Section10.aux_lim_lem_mean_exit_lim_lem_mean_exit_of_reversibleDensity_tightStatic lim_killed_density_continuity hd tight_lem_static

end Paper
end aux_lim_lem_mean_exit_principal
