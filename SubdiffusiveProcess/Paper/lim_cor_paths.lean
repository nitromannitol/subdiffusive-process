module

public import SubdiffusiveProcess.Section10.PhysicalSobolevBankBounds
public import SubdiffusiveProcess.Paper.tight_static
public import SubdiffusiveProcess.Paper.lfsgs_response_bank
public import SubdiffusiveProcess.Paper.inputs_J_witness
public import SubdiffusiveProcess.Paper.inputs_poincare_witness
public import SubdiffusiveProcess.Paper.inputs_Sf_witness
public import SubdiffusiveProcess.Section10.PhysicalSobolevBankDescent
public import SubdiffusiveProcess.Section10.PhysicalLocalTransportInfrared
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Section10.PhysicalSobolevBankTail
public import SubdiffusiveProcess.Paper.tight_static_coer
public import SubdiffusiveProcess.Section10.PhysicalSobolevBankLargeDomain
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowMomentTranslatedEllipticity
public import SubdiffusiveProcess.Analysis.ContinuousCubeCoefficient
public import Homogenization.Book.Ch04.Theorems.DilationLaw
public import SubdiffusiveProcess.Section10.PhysicalSobolevBankLargeEllipticity
public import SubdiffusiveProcess.Section10.PhysicalSobolevBankLargeCoercivity
public import SubdiffusiveProcess.Section10.PhysicalLargeMassMoment
public import SubdiffusiveProcess.Section10.KilledSobolev
public import SubdiffusiveProcess.Paper.tight_subharmonic
public import SubdiffusiveProcess.Section10.KilledSobolevMomentEnergy
public import SubdiffusiveProcess.Section10.KilledSobolevEnergy
public import SubdiffusiveProcess.Section10.KilledSobolevConstants
public import SubdiffusiveProcess.Section10.TorsionExitPhysical
public import SubdiffusiveProcess.Section10.PhysicalLocalTransportResolvent
public import SubdiffusiveProcess.Section10.PhysicalLocalTransportUniqueness
public import SubdiffusiveProcess.Paper.physical_rescaling
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellTransport
public import SubdiffusiveProcess.Processes.E7.FellerFromResolvent
public import SubdiffusiveProcess.Section10.TorsionExitDensityPhysical
public import SubdiffusiveProcess.Section10.TorsionExitDensityTransport
public import SubdiffusiveProcess.Paper.inputs_classical_fot_part_process
public import SubdiffusiveProcess.Section10.MeanExitBankConstants
public import Mathlib
public import SubdiffusiveProcess.Main.DiffusionPath
public import MarkovProcess.Path.ExitTime
public import MarkovProcess.Main
public import MarkovProcess.FiniteTime.ProjectiveFamily
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierGrowth
public import SubdiffusiveProcess.Frozen.Section6.Defs.CoefficientAt
public import SubdiffusiveProcess.Section10.ExitMomentPassageAffine
public import SubdiffusiveProcess.Section10.ExitTailMomentsPhysical
public import SubdiffusiveProcess.Section10.PhysicalAttachmentUniqueness
public import SubdiffusiveProcess.Paper.in_crossing
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import SubdiffusiveProcess.Section10.EndpointPathsMean
public import SubdiffusiveProcess.Section10.EndpointPathsMoments
public import SubdiffusiveProcess.Section10.TorsionExitConsumer
public import SubdiffusiveProcess.Section10.PhysicalAttachmentKilled
public import SubdiffusiveProcess.Section10.PrelimitExitPaths
public import SubdiffusiveProcess.Section10.ExitLowerMomentsMeanBank
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import SubdiffusiveProcess.Section10.SmallDisplacementMoments
public import SubdiffusiveProcess.Paper.lim_brownian_law
public import SubdiffusiveProcess.Section10.BrownianScalingApplications
public import SubdiffusiveProcess.Section10.ExitScaling
public import SubdiffusiveProcess.Section10.ExitLawPassage
public import SubdiffusiveProcess.Section10.ExitCarrier
public import SubdiffusiveProcess.Section10.NonbrownianExitSummability
public import SubdiffusiveProcess.Section10.ExitMomentPassage
public import MarkovProcess.Trajectory.Equivariance
public import SubdiffusiveProcess.Section10.PhysicalAttachmentRestart
public import SubdiffusiveProcess.Section10.StrictDecayProvider
public import SubdiffusiveProcess.Section10.TorsionExitDensityMartingaleBridge
public import SubdiffusiveProcess.Paper.lim_killed_density_continuity

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- Inlined proved source application: SubdiffusiveProcess.Paper.PhysicalSobolevBankBilateralStatic. -/
noncomputable section aux_lim_cor_paths_inline_0

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

/-- The actual two-projection static bank; its standing analytic packages and
response input are supplied by proved constructors, before any model application. -/
theorem aux_lim_cor_paths_inlined_physical_sobolev_bilateral_static_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ B : ℝ, 0 < B ∧ ∀ Q : ℝ, 1 ≤ Q →
      ∃ δ : ℝ, 0 < δ ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ δ →
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
  have : NeZero d := ⟨by omega⟩
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

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_0

/- Inlined proved source application: SubdiffusiveProcess.Paper.PhysicalSobolevBankTop. -/
noncomputable section aux_lim_cor_paths_inline_1

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

/-- Top physical static bank on the actual anchored physical law, after genuine
measurable descent from the exact native coupling. -/
theorem aux_lim_cor_paths_inlined_physical_sobolev_top_static_bank {d : ℕ}
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
  obtain ⟨B, hB, hbank⟩ := aux_lim_cor_paths_inlined_physical_sobolev_bilateral_static_bank hd
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
  have : StandardBorelSpace (AnchoredC11Sample d) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d).standardBorel
  have : MeasurableEq (AnchoredC11Sample d) := by
    let u := upgradeStandardBorel (AnchoredC11Sample d)
    let : TopologicalSpace (AnchoredC11Sample d) := u.toTopologicalSpace
    let : BorelSpace (AnchoredC11Sample d) := u.toBorelSpace
    let : PolishSpace (AnchoredC11Sample d) := u.toPolishSpace
    infer_instance
  have : Nonempty (NativeEnvironment d) := ⟨fun _ => zeroNativePotentialField d⟩
  exact physicalBank_measurable_descent (nativeLaw M) (PhysicalAttachment.physicalLaw M).toMeasure
    (physicalEnvironment_preserving M m z) hKn (fun η => hKone _) (by linarith) hC.le hKnm
    (fun ω k => PhysicalStaticBounds (localSpeed M ⊤ m z ω) (localCoefficient M ⊤ m z ω) B k)
    (fun ω k k' hkk hs => hs.mono hkk) hKns

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_1

/- Inlined proved source application: SubdiffusiveProcess.Paper.PhysicalSobolevBankFinite. -/
noncomputable section aux_lim_cor_paths_inline_2

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10 TopologicalSpace
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

/-- Finite m<=l physical bank, with the literal truncated infrared correction,
true anchored law, saturated source normalization and measurable marginal descent.
The static order 2Q and infrared exponential order 4Q precede the threshold. -/
theorem aux_lim_cor_paths_inlined_physical_sobolev_finite_static_bank {d : ℕ}
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
  obtain ⟨B, hB, hbank⟩ := aux_lim_cor_paths_inlined_physical_sobolev_bilateral_static_bank hd
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
  have : StandardBorelSpace (AnchoredC11Sample d) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d).standardBorel
  have : MeasurableEq (AnchoredC11Sample d) := by
    let u := upgradeStandardBorel (AnchoredC11Sample d)
    let : TopologicalSpace (AnchoredC11Sample d) := u.toTopologicalSpace
    let : BorelSpace (AnchoredC11Sample d) := u.toBorelSpace
    let : PolishSpace (AnchoredC11Sample d) := u.toPolishSpace
    infer_instance
  have : Nonempty (NativeEnvironment d) := ⟨fun _ => zeroNativePotentialField d⟩
  exact physicalBank_measurable_descent (nativeLaw M) (PhysicalAttachment.physicalLaw M).toMeasure
    (physicalEnvironment_preserving M m z) hKt hKtone (by linarith) (by positivity) hKtm
    (fun ω k => PhysicalStaticBounds (localSpeed M l m z ω) (localCoefficient M l m z ω) B k)
    (fun ω k k' hkk hs => hs.mono hkk) hKts

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_2

/- Inlined proved source application: SubdiffusiveProcess.Paper.PhysicalSobolevBank. -/
noncomputable section aux_lim_cor_paths_inline_3

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

/-- The two completed physical branches, with one exponent and one moment
constant before L,m,z. This bounded export explicitly excludes finite l<m. -/
theorem aux_lim_cor_paths_inlined_physical_sobolev_static_bank_small_scale {d : ℕ}
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
  obtain ⟨Bt, hBt, htop⟩ := aux_lim_cor_paths_inlined_physical_sobolev_top_static_bank hd
  obtain ⟨Bf, hBf, hfinite⟩ := aux_lim_cor_paths_inlined_physical_sobolev_finite_static_bank hd
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

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_3

/- Inlined proved source application: SubdiffusiveProcess.Paper.PhysicalSobolevBankLargeDeterministic. -/
noncomputable section aux_lim_cor_paths_inline_4

/-! The literal native H10 coercivity projection from the lower ellipticity
factor on the scale-(m+1) padded physical cube. No microcube partition is used. -/
open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.Section10
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

/-- Exact rescaling of the unit native chart to the unnormalized physical
cutoff field. Only descendants of the unit root are read by lambdaSq. -/
theorem aux_lim_cor_paths_inlined_physical_large_chart_lambda {d : ℕ} [NeZero d]
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
    rw [dite_eq_left hG]
  rw [hnorm]
  simpa only [Nat.add_zero, Int.ofNat_zero] using
    Ch04.lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      hF n 0 s (.finite 1)

/-- Every native H10 test on the unit ball, with actual lower-integral energy.
The saturated normalization is ahom_l and the padding cost is deterministic. -/
theorem aux_lim_cor_paths_inlined_physical_large_killed_of_lambda {d : ℕ} [NeZero d]
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
  have : NeZero d := ⟨by omega⟩
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
  have hf : Continuous f := (continuous_aCutoff M l ωz).comp (by fun_prop)
  have hfpos : ∀ x, 0 < f x := fun x => aCutoff_pos M l ωz _
  let b := continuousCubeCoefficient 0 1 one_pos f hf hfpos
  have hb := continuousCubeCoefficient_ae 0 1 one_pos f hf hfpos
  have hlam := aux_lim_cor_paths_inlined_physical_large_chart_lambda J M l (m + 1) ωz (1 / 16) (by norm_num) b hb
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
      (by fun_prop))
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

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_4

/- Inlined proved source application: SubdiffusiveProcess.Paper.PhysicalSobolevBankLargeKilled. -/
noncomputable section aux_lim_cor_paths_inline_5

/-! The actual retained-window killed bank and actual physical-law consumer.
Mass is deliberately supplied by its separate projection. -/
open MeasureTheory Homogenization Homogenization.Book SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

/-- The killed projection, uniform in the retained length and omitted depth.
No response or static estimate is an input to this actual-model theorem. -/
theorem aux_lim_cor_paths_inlined_physical_retained_window_killed_bank {d : ℕ}
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
  have : NeZero d := ⟨by omega⟩
  obtain ⟨D, hD, hdet⟩ := aux_lim_cor_paths_inlined_physical_large_killed_of_lambda hd
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
  have : StandardBorelSpace (AnchoredC11Sample d) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d).standardBorel
  have : Nonempty (AnchoredC11Sample d) := ⟨defaultAnchored M⟩
  exact physicalBank_measurable_descent (PhysicalAttachment.physicalLaw M).toMeasure
    (windowLaw M l m) (physicalWindow_preserving M l m 0)
    (hK0.const_mul D0) (fun ω => by nlinarith [hone ω])
    (zero_lt_one.trans_le hQ) hC1.le hKm
    (fun ξ K => PhysicalKilledCoercivity (retainedWindowCoefficient M l ξ) K)
    (fun ξ K K' hKK hs => hs.mono hKK) hKs

/-- Concrete actual physical-law consumer, obtained through the exact window
pushforward at every deterministic center. The constant C is unchanged. -/
theorem aux_lim_cor_paths_inlined_physical_large_killed_moment_bank {d : ℕ}
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
  obtain ⟨δ, C, hδ, hC, hwindow⟩ := aux_lim_cor_paths_inlined_physical_retained_window_killed_bank hd Q hQ
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro M hM l k hk z
  obtain ⟨K, hK, hone, hm, hs⟩ := hwindow M hM l k hk
  exact physicalRetainedWindow_killed_pullback M (by omega) z hK hone hm hs

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_5

/- Inlined proved source application: SubdiffusiveProcess.Paper.PhysicalRetainedMass. -/
noncomputable section aux_lim_cor_paths_inline_6

open MeasureTheory SubdiffusiveProcess Homogenization TopologicalSpace
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open scoped ENNReal BigOperators
namespace SubdiffusiveProcess.Paper

/-- Actual finite l<m mass bank. The cell input order 2dQ is fixed before δ;
C is chosen before l,k,z. Every test ball is controlled on one finite event. -/
theorem aux_lim_cor_paths_inlined_physical_retained_mass_bank {d : ℕ}
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
  obtain ⟨B, _, hbank⟩ := aux_lim_cor_paths_inlined_physical_sobolev_finite_static_bank hd
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
theorem aux_lim_cor_paths_inlined_actual_retained_window_mass_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
      ∃ C : ℝ, 0 < C ∧ ∀ l k : ℕ, 1 ≤ k →
        ∃ K : (Fin (l + 1) → C(SpatialCoordinates d, ℝ)) → ℝ,
          Measurable K ∧ (∀ ξ, 1 ≤ K ξ) ∧
          (∫⁻ ξ, ENNReal.ofReal (K ξ ^ Q) ∂windowLaw M l (l + k)) ≤ ENNReal.ofReal C ∧
          ∀ᵐ ξ ∂windowLaw M l (l + k), PhysicalMassBounds (retainedWindowSpeed M l ξ) (K ξ) := by
  obtain ⟨δ, hδ, hmodels⟩ := aux_lim_cor_paths_inlined_physical_retained_mass_bank hd Q hQ
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨C0, hC0, hcutoffs⟩ := hmodels M hM
  refine ⟨1 + 2 * C0, by positivity, ?_⟩
  intro l k hk
  obtain ⟨Kp, hKp, hpone, hpmom, hpbound⟩ := hcutoffs l k hk 0
  have : StandardBorelSpace (AnchoredC11Sample d) :=
    (Section6Anchored.measurableSet_anchoredC11GoodSet d).standardBorel
  have : Nonempty (AnchoredC11Sample d) := ⟨defaultAnchored M⟩
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

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_6

/- Inlined proved source application: SubdiffusiveProcess.Paper.PhysicalSobolevBankComplete. -/
noncomputable section aux_lim_cor_paths_inline_7

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

/-- Actual finite retained-window mass and killed projections, joined on the
same window law and pulled back by the literal physicalWindow. -/
theorem aux_lim_cor_paths_inlined_physical_sobolev_large_static_bank {d : ℕ}
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
  obtain ⟨δm, hδm, hmass⟩ := aux_lim_cor_paths_inlined_actual_retained_window_mass_bank hd Q hQ
  obtain ⟨δc, Cc, hδc, hCc, hcoer⟩ := aux_lim_cor_paths_inlined_physical_retained_window_killed_bank hd Q hQ
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
theorem aux_lim_cor_paths_inlined_physical_sobolev_static_bank {d : ℕ}
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
  obtain ⟨B, hB, hsmall⟩ := aux_lim_cor_paths_inlined_physical_sobolev_static_bank_small_scale hd
  refine ⟨B, hB, ?_⟩
  intro Q hQ
  obtain ⟨δs, hδs, hs⟩ := hsmall Q hQ
  obtain ⟨δg, hδg, hg⟩ := aux_lim_cor_paths_inlined_physical_sobolev_large_static_bank hd Q hQ
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

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_7

/- Inlined proved source application: SubdiffusiveProcess.Paper.KilledSobolevApplication. -/
noncomputable section aux_lim_cor_paths_inline_8

/-! First actual application of B1, on a fixed unit cube inside the side-four
reference cube. General-p trace and padded coercivity are discharged by their
existing exports. This is an internal deterministic application, with no
process, environment or new source assumption. -/

open MeasureTheory Set Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

lemma aux_lim_cor_paths_inlined_killed_sobolev_trace_supplier {d : ℕ} (hd : 2 ≤ d)
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
theorem aux_lim_cor_paths_inlined_killed_sobolev_of_padded_coercivity {d : ℕ} (hd : 2 ≤ d)
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
  obtain ⟨C, hC, htrace⟩ := aux_lim_cor_paths_inlined_killed_sobolev_trace_supplier hd hr0
  refine ⟨C, hC, ?_⟩
  intro U V hU hV hUV μ hμ inst Km Kc hKm hKc hsupp hgrowth A hcoer v
  exact killed_sobolev_all_h10 hd hU hV hUV μ hμ hr0 hC.le hKm hKc
    htrace hsupp hgrowth A hcoer v

/-- The first fixed-cube application of `lim:eq-killed-sobolev`, with its exact
source exponent. The static certificate supplies all mass and coercivity
premises, uniformly for every native H10 function. -/
theorem aux_lim_cor_paths_inlined_killed_sobolev_of_static {d : ℕ} (hd : 2 ≤ d) :
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
  obtain ⟨C, hC, htrace⟩ := aux_lim_cor_paths_inlined_killed_sobolev_trace_supplier hd (by norm_num : (0 : ℝ) < 1 / 4)
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
  let : IsFiniteMeasure (μ.restrict U) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
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

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_8

/- Inlined proved source application: SubdiffusiveProcess.Paper.KilledSobolevMomentDeterministic. -/
noncomputable section aux_lim_cor_paths_inline_9

/-! The two static projections needed for the moment bank. The application
uses the proved B1 theorem; lower mass and cutoff tests are unnecessary. -/

open MeasureTheory Set Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

/-- A bounded deterministic export from upper mass and padded killed coercivity.
The constant is chosen before coefficients, samples and H10 tests. -/
theorem aux_lim_cor_paths_inlined_killed_sobolev_of_mass_coercivity {d : ℕ} (hd : 2 ≤ d) (B : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b A : SpatialCoordinates d → ℝ) (K : ℝ), 1 ≤ K →
      (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) 2, ∀ r : ℝ, 0 < r → r ≤ 1 →
        weightedMeasure b (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2))) →
      (∀ w : H10Function (Metric.ball (0 : SpatialCoordinates d) 1),
        killedFractionalEnergy (Metric.ball (0 : SpatialCoordinates d) 1) w.toFun +
            ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) 1, ENNReal.ofReal (w.toFun x ^ 2) ≤
          ENNReal.ofReal (K * (2 : ℝ) ^ B) * killedCoefficientEnergy A w.toH1Function) →
      CoefficientOn (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) A →
      KilledSobolevBound (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) b A (D * K ^ 2) := by
  obtain ⟨C, hC, hSob⟩ := aux_lim_cor_paths_inlined_killed_sobolev_of_padded_coercivity hd
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
  let : IsFiniteMeasure (μ.restrict U) := ⟨by
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

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_9

/- Inlined proved source application: SubdiffusiveProcess.Paper.KilledSobolevConsumer. -/
noncomputable section aux_lim_cor_paths_inline_10

/-! Concrete consumer on the actual weighted carrier and real Dirichlet energy.
The deterministic coefficient regularity premise is exactly `CoefficientOn`;
attachment to the two model families is reserved for B2-P and B2-B. -/

open MeasureTheory Set Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

/-- A fixed deterministic D turns the static constant K into D*K^2, sufficient
for subsequent torsion and Nash consumers, with genuine weighted MemLp. -/
theorem aux_lim_cor_paths_inlined_killed_sobolev_unit_cube_consumer {d : ℕ} (hd : 2 ≤ d) (B : ℝ) :
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
  obtain ⟨C, hC, hSob⟩ := aux_lim_cor_paths_inlined_killed_sobolev_of_static hd
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
    bot_le)
  have hnonneg : 0 ≤ D * K ^ 2 := mul_nonneg hD.le (sq_nonneg K)
  have hreal := killed_sobolev_real_of_bound μ (withDensity_absolutelyContinuous _ _) hA v
    hnonneg hbounded
  exact ⟨hreal.1, killed_lpSq_le_of_bound hA v hnonneg hbounded, hreal.2⟩

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_10

/- Inlined proved source application: SubdiffusiveProcess.Paper.TorsionExitStaticConsumer. -/
noncomputable section aux_lim_cor_paths_inline_11

/-! Concrete consumers discharge the all-H10 slot with the native static package.
No promised torsion, resolvent or mean-exit bound is used. -/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set SubdiffusiveProcess
open SubdiffusiveProcess.Section10
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Assumptions.CoefficientRegularity
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.Section10.PhysicalAttachment
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper

/-- Static estimates produce the exact unit-cube cap for any actual LocalDiffusion.
The pointwise half exposes precisely the separate starting-point regularity slot. -/
theorem aux_lim_cor_paths_inlined_torsion_exit_unit_cube_consumer {d : ℕ} (hd : 2 ≤ d) (B : ℝ) :
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
  obtain ⟨D, hD, hKilled⟩ := aux_lim_cor_paths_inlined_killed_sobolev_unit_cube_consumer hd B
  let p : ℝ := 2 * (d : ℝ) / ((d : ℝ) - 1)
  let C : ℝ := torsionConstant p * D
  refine ⟨C, mul_pos (torsionConstant_pos p) hD, ?_⟩
  intro b A hb hbpos hA hApos law hMarkov hlocal K hK hstatic
  let := hMarkov
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

/-- The actual finite/top physical family, relative to FOT, with the deterministic
Sobolev slot discharged. The actual local static bank supplies `hstatic` next. -/
theorem aux_lim_cor_paths_inlined_torsion_exit_physical_family_consumer {d : ℕ} (hd : 2 ≤ d) (B : ℝ)
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
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hconsumer⟩ := aux_lim_cor_paths_inlined_torsion_exit_unit_cube_consumer hd B
  obtain ⟨X, hX, hactual⟩ := exists_physical_localDiffusion_family hFOT M
  refine ⟨C, hC, X, hX, ?_⟩
  filter_upwards [hactual] with omega homega
  intro L K hK hstatic
  obtain ⟨hlocal, D, hdense, _, hcons, hfdd⟩ := homega L
  let := hX L
  let : IsMarkovKernel (physicalSlice (X L) omega) := by dsimp only [physicalSlice]; infer_instance
  let : IsMarkovKernel ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath) :=
    Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
  obtain ⟨hae, hpoint⟩ := hconsumer (coefficientAt M L omega) (coefficientAt M L omega)
    (continuous_coefficientAt M L omega) (coefficientAt_pos M L omega)
    (continuous_coefficientAt M L omega) (coefficientAt_pos M L omega)
    ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath) inferInstance hlocal K hK hstatic
  refine ⟨hae, fun hreg => hpoint ?_⟩
  exact hreg d (D.fellerKernelSemigroup hdense) hcons
    (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense)
    (physicalSlice (X L) omega) inferInstance hfdd

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_11

/- Inlined proved source application: SubdiffusiveProcess.Paper.PhysicalLocalTransportConsumer. -/
noncomputable section aux_lim_cor_paths_inline_12

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
open SubdiffusiveProcess.Section10
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.Probability.Diffusion
open SubdiffusiveProcess
open scoped ZeroAtInfty NNReal Pointwise
namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-- Reuse the proved `physical_rescaling` weak-equation supplier, adding the literal
translation of the physical coefficient. No clock conversion theorem is reproved. -/
theorem aux_lim_cor_paths_inlined_physical_local_datum_weak (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
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
    change (3 : ℝ) ^ (2 * m) / ahom M (activeScale L m) = r * a ^ 2
    dsimp only [a, r]
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
theorem aux_lim_cor_paths_inlined_physical_local_laplace_dilation {F G : ℝ → ℝ} (c : ℝ) (hc : 0 < c)
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
theorem aux_lim_cor_paths_inlined_physical_local_datum_conjugacy
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
  have : IsFiniteMeasure (Q t x) :=
    ⟨lt_of_le_of_lt (Q.isSubMarkovKernel t x) (by norm_num)⟩
  have : IsFiniteMeasure ((P (c * t)) (e x)) :=
    ⟨lt_of_le_of_lt (P.isSubMarkovKernel _ _) (by norm_num)⟩
  have : IsFiniteMeasure (((P (c * t)) (e x)).map e.symm) :=
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
    apply aux_lim_cor_paths_inlined_physical_local_laplace_dilation (c : ℝ) hc
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
theorem aux_lim_cor_paths_inlined_physical_local_rescaled_fdd
    (P P' : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (K : Kernel (Vec d) (DiffusionPath d)) (hK : IsMarkovKernel K)
    (hKmarg : ∀ I x, (K x).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (e : Vec d ≃ₜ Vec d) (c : ℝ≥0) (hc : 0 < c)
    (hconj : SubMarkovKernelSemigroup.IsRescaledConjugate P P' e c) :
    ∀ I x, ((K (e.symm x)).map (ContinuousPath.rescale e c)).map
        (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P' I x := by
  classical
  let : IsMarkovKernel K := hK
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
def aux_lim_cor_paths_inlined_physical_local_source_characterization (M : GMCModel d) (L : WithTop ℕ)
    (X : PhysicalAttachment.PhysicalKernel d) : Prop :=
  ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
    ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
      IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
      (D.fellerKernelSemigroup hdense).IsConservative ∧
      ∀ I x, (X (omega, x)).map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x

/-- Complete model application: the actual anchored finite/top family, at every start,
has the local coefficient, exact raw clock and literal affine path law from the paper. -/
theorem aux_lim_cor_paths_actual_physical_local_family (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) (z : Vec d) :
    ∃ X Y : PhysicalAttachment.PhysicalKernel d,
      IsMarkovKernel X ∧ IsMarkovKernel Y ∧
      aux_lim_cor_paths_inlined_physical_local_source_characterization M L X ∧
      (∀ omega x, Y (omega, x) =
        (X (omega, physicalCoordinates m z x)).map
          (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m))) ∧
      ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
        ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
          IsWeakEllipticResolvent (localCoefficient M L m z omega) (localSpeed M L m z omega) D ∧
          (D.fellerKernelSemigroup hdense).IsConservative ∧
          ∀ I x, (Y (omega, x)).map (ContinuousPath.finsetEvaluation I) =
            SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
  let : NeZero d := ⟨by have hd := M.shellPrefix.dimension; omega⟩
  obtain ⟨X, hX⟩ := PhysicalAttachment.exists_physical_family M
  let Y := ((X L).comap
    (fun p : AnchoredC11Sample d × Vec d => (p.1, physicalCoordinates m z p.2))
    (measurable_fst.prodMk ((physicalCoordinates m z).measurable.comp measurable_snd))).map
      (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m))
  let : IsMarkovKernel (X L) := hX.1 L
  have hY : IsMarkovKernel Y := by
    dsimp only [Y]
    exact Kernel.IsMarkovKernel.map _ (ContinuousPath.measurable_rescale _ _)
  have hYeq : ∀ omega x, Y (omega, x) = (X L (omega, physicalCoordinates m z x)).map
      (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m)) := by
    intro omega x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_rescale _ _), Kernel.comap_apply]
  have hsource : aux_lim_cor_paths_inlined_physical_local_source_characterization M L (X L) := by
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
  have hconj := aux_lim_cor_paths_inlined_physical_local_datum_conjugacy D hdense (physicalCoordinates m z)
    (rawClock M L m) (rawClock_pos M L m)
  refine ⟨E, he, aux_lim_cor_paths_inlined_physical_local_datum_weak M L m z omega D hweak,
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
  exact aux_lim_cor_paths_inlined_physical_local_rescaled_fdd _ _ hcons (PhysicalAttachment.physicalSlice (X L) omega)
    hslice hsliceF
    (physicalCoordinates m z).symm (rawClock M L m) (rawClock_pos M L m) hconj I x

/-- Finite-cutoff application against the correct bilateral window law. There are no
caller-supplied process, coefficient-identity, moment-bank or growth witnesses. -/
theorem aux_lim_cor_paths_actual_finite_local_transport (M : GMCModel d) (l m : ℕ) (z : Vec d) :
    ∃ X Y : PhysicalAttachment.PhysicalKernel d,
      IsMarkovKernel X ∧ IsMarkovKernel Y ∧
      aux_lim_cor_paths_inlined_physical_local_source_characterization M l X ∧
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
  obtain ⟨X, Y, hX, hY, hsource, heq, hgood⟩ := aux_lim_cor_paths_actual_physical_local_family M l m z
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
theorem aux_lim_cor_paths_actual_physical_local_law_characterization (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) (z : Vec d) :
    ∃ X Y : PhysicalAttachment.PhysicalKernel d,
      IsMarkovKernel X ∧ IsMarkovKernel Y ∧
      aux_lim_cor_paths_inlined_physical_local_source_characterization M L X ∧
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
  obtain ⟨X, Y, hX, hY, hsource, heq, hgood⟩ := aux_lim_cor_paths_actual_physical_local_family M L m z
  refine ⟨X, Y, hX, hY, hsource, heq, ?_⟩
  filter_upwards [hgood] with omega h
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := h
  intro E hedense Q hE hQ
  let : IsMarkovKernel Y := hY
  have hslice : IsMarkovKernel (PhysicalAttachment.physicalSlice Y omega) := by
    dsimp only [PhysicalAttachment.physicalSlice]
    infer_instance
  apply local_law_unique M L m z omega D E hweak hE hdense hedense _ Q hslice
  · intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    exact hfdd I x
  · exact hQ

/-- Top uses the constructed full infrared field, on the actual chaos law. -/
theorem aux_lim_cor_paths_actual_top_local_transport (M : GMCModel d) (m : ℕ) (z : Vec d) :
    ∃ X Y : PhysicalAttachment.PhysicalKernel d,
      IsMarkovKernel X ∧ IsMarkovKernel Y ∧
      aux_lim_cor_paths_inlined_physical_local_source_characterization M ⊤ X ∧
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
  obtain ⟨X, Y, hX, hY, hsource, heq, hgood⟩ := aux_lim_cor_paths_actual_physical_local_family M ⊤ m z
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

/-- The proved canonical Feller restart theorem supplies strong Markov for the
actual local law, after its every-start FDD characterization is proved. -/
theorem aux_lim_cor_paths_actual_local_strongMarkov_family (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) (z : Vec d) :
    ∃ Y : PhysicalAttachment.PhysicalKernel d, IsMarkovKernel Y ∧
      ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
        StrongMarkov ((PhysicalAttachment.physicalSlice Y omega).map LifetimePath.ofContinuousPath) ∧
        ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
          IsWeakEllipticResolvent (localCoefficient M L m z omega) (localSpeed M L m z omega) D ∧
          (D.fellerKernelSemigroup hdense).IsConservative ∧
          ∀ I x, (Y (omega, x)).map (ContinuousPath.finsetEvaluation I) =
            SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
  obtain ⟨X, Y, hX, hY, hsource, heq, hgood⟩ := aux_lim_cor_paths_actual_physical_local_family M L m z
  refine ⟨Y, hY, ?_⟩
  filter_upwards [hgood] with omega h
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := h
  let : IsMarkovKernel Y := hY
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

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_12

/- Inlined proved source application: SubdiffusiveProcess.Paper.TorsionExitDensityLocalConsumer. -/
noncomputable section aux_lim_cor_paths_inline_13

/-! Concrete actual local-family consumer. Proposal 3 is applied to the
original same-coefficient physical datum; only its survival regularity is
transported. The actual local A,b and rawClock remain exactly those of the native static package. -/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set SubdiffusiveProcess
open SubdiffusiveProcess.Section10
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Assumptions.CoefficientRegularity
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.Section10.PhysicalAttachment
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper

/-- Actual local weak realization and every-start regularity, with no
Sobolev or exit-bound input. All finite cutoffs (including zero and m>L)
and top use the unchanged raw clock. -/
theorem aux_lim_cor_paths_inlined_torsion_exit_actual_local_regularity_of_smooth_density
    (hDensity : SmoothReversibleKilledDensitySupplier) {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess) :
    ∀ (M : GMCModel d) (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
      ∃ X Y : PhysicalKernel d,
      IsMarkovKernel X ∧ IsMarkovKernel Y ∧
      aux_lim_cor_paths_inlined_physical_local_source_characterization M L X ∧
      (∀ omega x, Y (omega, x) = (X (omega, physicalCoordinates m z x)).map
        (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m))) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure,
        let law := (physicalSlice Y omega).map LifetimePath.ofContinuousPath
        let U : Set (SpatialCoordinates d) := Metric.ball 0 (1 / 2)
        LocalDiffusion (localCoefficient M L m z omega) (localSpeed M L m z omega) law ∧
        UnitDiscountOccupationLSC law U := by
  let : NeZero d := ⟨by omega⟩
  intro M L m z
  obtain ⟨X, Y, hX, hY, hsource, heq, hactual⟩ := aux_lim_cor_paths_actual_physical_local_family M L m z
  refine ⟨X, Y, hX, hY, hsource, heq, ?_⟩
  filter_upwards [hactual, hsource] with omega homega hphysical
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := homega
  obtain ⟨D0, hdense0, hweak0, hcons0, hfdd0⟩ := hphysical
  let := hX
  let := hY
  let : IsMarkovKernel (physicalSlice X omega) := by dsimp only [physicalSlice]; infer_instance
  let : IsMarkovKernel (physicalSlice Y omega) := by dsimp only [physicalSlice]; infer_instance
  let : IsMarkovKernel ((physicalSlice Y omega).map LifetimePath.ofContinuousPath) :=
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

/-- Literal p=2*d/(d-1) and mass exponent 1/d for the actual local family.
Only the all-native-H10 deterministic Sobolev slot remains in this helper;
the actual moment-bank consumer discharges it. -/
theorem aux_lim_cor_paths_inlined_torsion_exit_actual_local_sobolev_consumer_of_smooth_density
    (hDensity : SmoothReversibleKilledDensitySupplier) {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess)
    (M : GMCModel d) (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d) :
    ∃ X Y : PhysicalKernel d,
      IsMarkovKernel X ∧ IsMarkovKernel Y ∧
      aux_lim_cor_paths_inlined_physical_local_source_characterization M L X ∧
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
  let : NeZero d := ⟨by omega⟩
  obtain ⟨X, Y, hX, hY, hsource, heq, hactual⟩ :=
    aux_lim_cor_paths_inlined_torsion_exit_actual_local_regularity_of_smooth_density hDensity hd hFOT M L m z
  refine ⟨X, Y, hX, hY, hsource, heq, ?_⟩
  filter_upwards [hactual] with omega homega
  refine ⟨homega.2, ?_⟩
  intro Ksob hKsob hSob
  let := hY
  let : IsMarkovKernel (physicalSlice Y omega) := by dsimp only [physicalSlice]; infer_instance
  let : IsMarkovKernel ((physicalSlice Y omega).map LifetimePath.ofContinuousPath) :=
    Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
  have hU : IsOpenBoundedConvexDomain (Metric.ball (0 : Vec d) (1 / 2)) :=
    isOpenBoundedConvexDomain_ball 0 (by norm_num)
  have hne : (Metric.ball (0 : Vec d) (1 / 2)).Nonempty :=
    ⟨0, Metric.mem_ball_self (by norm_num)⟩
  have hb := coefficientOn_of_continuous_pos (continuous_localSpeed M L m z omega)
    (localSpeed_pos M L m z omega) hU.isBoundedDomain.isBounded
  have hp := killedSobolevExponent_gt_two hd
  have hpower := killedSobolev_one_sub_two_div hd
  simpa only [hpower] using!
    localDiffusion_meanExit_le homega.1 hU hne hb hp hKsob hSob homega.2

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_13

/- Inlined proved source application: SubdiffusiveProcess.Paper.MeanExitUpperLocal. -/
noncomputable section aux_lim_cor_paths_inline_14

open MeasureTheory ProbabilityTheory Homogenization MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Section10
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

/-- Every finite/top actual local family has an every-start upper mean-exit
bank. The sole unproduced input is the precise smooth killed-density supplier;
FOT and all analytic estimates are discharged by their actual providers. -/
theorem aux_lim_cor_paths_inlined_mean_exit_actual_local_upper_bank
    (hDensity : SmoothReversibleKilledDensitySupplier) {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∀ q : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
      ∃ C : ℝ, 0 < C ∧ ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
        ∃ X Y : PhysicalAttachment.PhysicalKernel d, ∃ K : AnchoredC11Sample d → ℝ,
          IsMarkovKernel X ∧ IsMarkovKernel Y ∧
          aux_lim_cor_paths_inlined_physical_local_source_characterization M L X ∧
          (∀ ω x, Y (ω, x) = (X (ω, physicalCoordinates m z x)).map
            (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m))) ∧
          Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
          (∫⁻ ω, ENNReal.ofReal (K ω ^ q)
            ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
          ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
            ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (1 / 2),
              meanExit ((PhysicalAttachment.physicalSlice Y ω).map LifetimePath.ofContinuousPath)
                (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) x ≤ ENNReal.ofReal (K ω) := by
  obtain ⟨B, hB, hstatic⟩ := aux_lim_cor_paths_inlined_physical_sobolev_static_bank hd
  obtain ⟨D, hD, hdet⟩ := aux_lim_cor_paths_inlined_killed_sobolev_of_mass_coercivity hd B
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
    aux_lim_cor_paths_inlined_torsion_exit_actual_local_sobolev_consumer_of_smooth_density hDensity hd
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

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_14

/- Inlined proved source application: SubdiffusiveProcess.Paper.MeanExitSourceDefinitions. -/
noncomputable section aux_lim_cor_paths_inline_15

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal



namespace SubdiffusiveProcess.Paper

/-- The cube `z + 𝖢_m` of side `3^m` centred at `z` (the open sup-norm ball of radius `3^m/2`). -/
def aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube {d : ℕ} (z : SpatialCoordinates d) (m : ℤ) :
    Set (SpatialCoordinates d) :=
  Metric.ball z ((3 : ℝ) ^ m / 2)

/-- The time unit `3^{2m}/ahom_{m ∧ L}` of the local normalization (`tight:eq-local-time`); for the
untruncated diffusion (`L = ⊤`) it is `3^{2m}/ahom_m`. -/
def aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime {d : ℕ} (M : GMCModel d) (L : WithTop ℕ) (m : ℕ) : ℝ :=
  (3 : ℝ) ^ (2 * m) / ahom M (match L with | ⊤ => m | (l : ℕ) => min m l)

/-- `𝐄[τ_U^p]` for the path law `Q` and the exit time `τ_U` from `U`. -/
def aux_lim_cor_paths_inlined_lim_lem_mean_exit_exitMoment {d : ℕ} (Q : Measure (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂Q

/-- The probability space of the environment of the diffusions `X^{(L)}` and `X`: the layers
`(γ_k)_{k ≥ 0}` on the anchored `C^{1,1}` carrier (`SubdiffusiveProcess.Model.anchoredC11SampleLaw`).
(Body identical to `SubdiffusiveProcess.Section10.PhysicalAttachment.physicalLaw`.) -/
def aux_lim_cor_paths_inlined_lim_lem_mean_exit_physicalLaw {d : ℕ} (M : GMCModel d) :
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
def aux_lim_cor_paths_inlined_lim_lem_mean_exit_IsPhysicalFamily {d : ℕ} (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)) :
    Prop :=
  ∀ᵐ omega ∂(aux_lim_cor_paths_inlined_lim_lem_mean_exit_physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
    ∃ D : C0ResolventDatum (SpatialCoordinates d),
    ∃ hdense : ∀ mu, DenseRange (D.operator mu),
      IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
      (D.fellerKernelSemigroup hdense).IsConservative ∧
      ∀ (I : Finset ℝ≥0) (x : SpatialCoordinates d),
        ((X L).map (ContinuousPath.finsetEvaluation I)) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x


end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_15

/- Inlined proved source application: SubdiffusiveProcess.Paper.MeanExitTransport. -/
noncomputable section aux_lim_cor_paths_inline_16

open MeasureTheory Homogenization MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.Section10.ExitMomentPassage
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

theorem aux_lim_cor_paths_inlined_lim_lem_mean_exit_physicalLaw_eq {d : ℕ} (M : GMCModel d) :
    aux_lim_cor_paths_inlined_lim_lem_mean_exit_physicalLaw M = SubdiffusiveProcess.Section10.PhysicalAttachment.physicalLaw M := rfl

theorem aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime_eq {d : ℕ} (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) :
    aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m = (rawClock M L m : ℝ) := by
  cases L using WithTop.recTopCoe with
  | top => simp only [aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime, rawClock, activeScale, WithTop.untopD_top, min_self] ; rfl
  | coe l => simp only [aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime, rawClock, activeScale, WithTop.untopD_coe] ; rfl

theorem aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube_image {d : ℕ} (m : ℕ) (z : SpatialCoordinates d) :
    physicalCoordinates m z '' Metric.ball (0 : SpatialCoordinates d) (1 / 2) =
      aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube z (m : ℤ) := by
  rw [physicalCoordinates_image_ball]
  simp only [aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube, zpow_natCast, div_eq_mul_inv, one_mul, mul_comm]

theorem aux_lim_cor_paths_inlined_lim_lem_mean_exit_inner_cube_image {d : ℕ} (m : ℕ) (z : SpatialCoordinates d) :
    physicalCoordinates m z '' Metric.ball (0 : SpatialCoordinates d) (1 / 18) =
      aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube z ((m : ℤ) - 2) := by
  rw [physicalCoordinates_image_ball]
  unfold aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube
  congr 1
  rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  norm_num
  ring

/-- Restore the literal raw clock for an actual affine local law, without
any finiteness assumption on its exit time. -/
theorem aux_lim_cor_paths_inlined_lim_lem_mean_exit_clock_transport {d : ℕ} (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d)
    (X Y : SubdiffusiveProcess.Section10.PhysicalAttachment.PhysicalKernel d)
    (hY : ∀ ω x, Y (ω, x) = (X (ω, physicalCoordinates m z x)).map
      (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m)))
    (ω : AnchoredC11Sample d) (x : SpatialCoordinates d) :
    aux_lim_cor_paths_inlined_lim_lem_mean_exit_exitMoment (X (ω, physicalCoordinates m z x))
      (aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube z (m : ℤ)) 1 =
      ENNReal.ofReal (aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m) *
        meanExit ((SubdiffusiveProcess.Section10.PhysicalAttachment.physicalSlice Y ω).map
          LifetimePath.ofContinuousPath) (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) x := by
  rw [SubdiffusiveProcess.Section10.ExitTailMoments.continuous_meanExit_transport _ _ Metric.isOpen_ball]
  change _ = ENNReal.ofReal (aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m) *
    ∫⁻ w, ContinuousPath.exitTime (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) w ∂Y (ω, x)
  rw [hY]
  have h := exitMoment_eq_clock_mul_map (X (ω, physicalCoordinates m z x))
    (physicalCoordinates m z) (rawClock M L m) (rawClock_pos M L m)
    (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) Metric.isOpen_ball 1 (by norm_num)
  simpa only [aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube_image, ENNReal.rpow_one,
    aux_lim_cor_paths_inlined_lim_lem_mean_exit_exitMoment, aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime_eq,
    ENNReal.ofReal_coe_nnreal] using h

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_16

/- Inlined proved source application: SubdiffusiveProcess.Paper.MeanExitUpperPhysical. -/
noncomputable section aux_lim_cor_paths_inline_17

open Filter MeasureTheory ProbabilityTheory Homogenization MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.Section10.PhysicalAttachment
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Section10
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

/-- The uniform upper moment bank for every physical family in the reviewed
root, with its actual raw clock. The density supplier is an explicit hypothesis of this helper. -/
theorem aux_lim_cor_paths_inlined_lim_lem_mean_exit_upper_bank
    (hDensity : SmoothReversibleKilledDensitySupplier) {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∀ q : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ M : GMCModel d, M.delta ≤ δ →
      ∃ C : ℝ, 0 < C ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_inlined_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
            (∫⁻ ω, ENNReal.ofReal (K ω ^ q)
              ∂(aux_lim_cor_paths_inlined_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
            ∀ᵐ ω ∂(aux_lim_cor_paths_inlined_lim_lem_mean_exit_physicalLaw M).toMeasure,
              ∀ x ∈ aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube z (m : ℤ),
                aux_lim_cor_paths_inlined_lim_lem_mean_exit_exitMoment (X L (ω, x))
                  (aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube z (m : ℤ)) 1 ≤
                  ENNReal.ofReal (K ω * aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m) := by
  intro q
  obtain ⟨δ, hδ, hmodels⟩ := aux_lim_cor_paths_inlined_mean_exit_actual_local_upper_bank hDensity hd q
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
  let := hX L
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
  rw [← aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hrow : X L (ω, physicalCoordinates m z y) = X0 (ω, physicalCoordinates m z y) :=
    congrArg (fun law => law (physicalCoordinates m z y)) hsame
  rw [hrow, aux_lim_cor_paths_inlined_lim_lem_mean_exit_clock_transport M L m z X0 Y heq]
  calc
    _ ≤ ENNReal.ofReal (aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m) * ENNReal.ofReal (K ω) :=
      mul_le_mul_right (hω y hy) _
    _ = ENNReal.ofReal (K ω * aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m) := by
      rw [← ENNReal.ofReal_mul (by
        rw [aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime_eq]
        exact (rawClock M L m).coe_nonneg), mul_comm]

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_17

/- Inlined proved source application: SubdiffusiveProcess.Paper.MeanExitAverage. -/
noncomputable section aux_lim_cor_paths_inline_18

open Filter MeasureTheory ProbabilityTheory SubdiffusiveProcess MarkovProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

/-- The first reviewed display, from the proved q=1 upper bank. The source
uses the literal lower integral of the supremum; no envelope premise is added. -/
theorem aux_lim_cor_paths_inlined_lim_lem_mean_exit_averaged_upper
    (hDensity : SmoothReversibleKilledDensitySupplier)
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ C : ℝ, 0 < C ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_inlined_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          (∫⁻ omega, (⨆ x ∈ aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube z (m : ℤ),
              aux_lim_cor_paths_inlined_lim_lem_mean_exit_exitMoment (X L (omega, x))
                (aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube z (m : ℤ)) 1)
            ∂(aux_lim_cor_paths_inlined_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤
            ENNReal.ofReal (C * aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m) := by
  obtain ⟨δ, hδ, hmodels⟩ := aux_lim_cor_paths_inlined_lim_lem_mean_exit_upper_bank hDensity hd 1
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨C, hC, hbank⟩ := hmodels M hM
  refine ⟨C, hC, ?_⟩
  intro X hX hphysical L m z
  obtain ⟨K, hK, hone, hm, hs⟩ := hbank X hX hphysical L m z
  have ht : 0 < aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m := by
    rw [aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime_eq]
    exact rawClock_pos M L m
  have hKm : (∫⁻ ω, ENNReal.ofReal (K ω)
      ∂(aux_lim_cor_paths_inlined_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤ ENNReal.ofReal C := by
    simpa only [Real.rpow_one] using hm
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (K ω * aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m)
          ∂(aux_lim_cor_paths_inlined_lim_lem_mean_exit_physicalLaw M).toMeasure := by
      apply lintegral_mono_ae
      filter_upwards [hs] with ω hω
      exact iSup_le fun x => iSup_le fun hx => hω x hx
    _ = ENNReal.ofReal (aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m) *
        ∫⁻ ω, ENNReal.ofReal (K ω)
          ∂(aux_lim_cor_paths_inlined_lim_lem_mean_exit_physicalLaw M).toMeasure := by
      simp_rw [mul_comm (K _) (aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m),
        ENNReal.ofReal_mul ht.le]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m) * ENNReal.ofReal C :=
      mul_le_mul_right hKm _
    _ = _ := by rw [← ENNReal.ofReal_mul ht.le, mul_comm]

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_18

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorPathsDefs. -/
noncomputable section aux_lim_cor_paths_inline_19

open Filter MeasureTheory ProbabilityTheory Topology Set Asymptotics MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal



namespace SubdiffusiveProcess.Paper

/-- The probability space of the environment of the diffusions `X^{(L)}` and `X`: the layers
`(γ_k)_{k ≥ 0}` on the anchored `C^{1,1}` carrier.  (Body identical to
`SubdiffusiveProcess.Section10.PhysicalAttachment.physicalLaw`.) -/
def aux_lim_cor_paths_physicalLaw {d : ℕ} (M : GMCModel d) :
    ProbabilityMeasure (AnchoredC11Sample d) :=
  anchoredC11SampleLaw M (Section6Anchored.measurableSet_anchoredC11GoodSet d)
    (Section6Anchored.measure_anchoredC11GoodSet_eq_one M)

/-- `X L` (`L ∈ ℕ₀` the truncation `X^{(L)}`, `L = ⊤` the untruncated diffusion `X`) is a Markov kernel
`(ω, x) ↦ 𝐏_x^ω` of path laws whose finite-dimensional distributions, for almost every environment
and every start `x`, are those of the conservative Feller semigroup of the weak elliptic resolvent
of `coefficientAt M L ω` (generator `a^{-1} ∇·(a ∇)`, reversible measure `a dx`). -/
def aux_lim_cor_paths_IsPhysicalFamily {d : ℕ} (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)) :
    Prop :=
  ∀ᵐ omega ∂(aux_lim_cor_paths_physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
    ∃ D : C0ResolventDatum (SpatialCoordinates d),
    ∃ hdense : ∀ mu, DenseRange (D.operator mu),
      IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
      (D.fellerKernelSemigroup hdense).IsConservative ∧
      ∀ (I : Finset ℝ≥0) (x : SpatialCoordinates d),
        ((X L).map (ContinuousPath.finsetEvaluation I)) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x

/-- The rescaled path `Z_t = 3^{-n} X_{3^{2n} t/ahom_n}` (`Z^{(L)}` of `s.tightness`, also for the
untruncated diffusion). -/
def aux_lim_cor_paths_rescale {d : ℕ} (M : GMCModel d) (n : ℕ) (w : DiffusionPath d) :
    DiffusionPath d :=
  ⟨fun t => (3 : ℝ) ^ (-(n : ℤ)) •
    w (Real.toNNReal ((3 : ℝ) ^ (2 * n) / ahom M n) * t), by fun_prop⟩

/-- The truncation index of the family: `n` (the cutoff diffusion `X^{(n)}`) or `⊤` (the
untruncated diffusion `X`). -/
def aux_lim_cor_paths_familyCutoff (untruncated : Bool) (n : ℕ) : WithTop ℕ :=
  if untruncated then ⊤ else (n : WithTop ℕ)

/-- `σ_k`: the exit time of `Z - Z_0` from the cube `3^{-k} 𝖢_0`. -/
def aux_lim_cor_paths_smallExit {d : ℕ} (k : ℕ) (w : DiffusionPath d) : ℝ≥0∞ :=
  ContinuousPath.exitTime (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w

/-- `P` is a subsequential limit of the annealed laws `𝐄[K_{N,x}^ω]` of either family (truncated for
`untruncated = false`, untruncated for `true`), along the subsequence `phi` and the deterministic
starting points `3^{phi n} xs n` in physical coordinates (`xs n → x` in rescaled coordinates): weak
convergence against bounded continuous path functionals.  The environment is sampled once and
kept fixed along the entire path. -/
def aux_lim_cor_paths_IsAnnealedLimit {d : ℕ} (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (untruncated : Bool) (phi : ℕ → ℕ) (xs : ℕ → SpatialCoordinates d)
    (P : ProbabilityMeasure (DiffusionPath d)) : Prop :=
  ∀ G : BoundedContinuousFunction (DiffusionPath d) ℝ,
    Tendsto (fun n => ∫ omega,
      (∫ w, G (aux_lim_cor_paths_rescale M (phi n) w)
        ∂X (aux_lim_cor_paths_familyCutoff untruncated (phi n))
          (omega, (3 : ℝ) ^ (phi n) • xs n))
      ∂(aux_lim_cor_paths_physicalLaw M).toMeasure) atTop
        (𝓝 (∫ w, G w ∂(P : Measure (DiffusionPath d))))

/-- Convergence of the quenched path laws `K_{N,x}^ω → K_x^ω` locally uniformly in `x`, almost surely
(Theorem A(i), `eq:mfd-main-as`), for the rescaled cutoff path kernels `KN` attached to `in_crossing`.
`K` is the limit kernel of Theorem A. -/
def aux_lim_cor_paths_QuenchedConv {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) : Prop :=
  ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
    ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
        pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K hK omega x) < epsilon

/-- `Z*_t = sup_{0 ≤ s ≤ t} |Z_s - Z_0|` (Euclidean norm): the running maximal displacement. -/
def aux_lim_cor_paths_maximum {d : ℕ} (t : ℝ≥0) (w : DiffusionPath d) : ℝ :=
  ⨆ s : Set.Icc (0 : ℝ≥0) t, Homogenization.euclideanNorm (w s - w 0)

/-- Parts (i)–(iii) of Corollary `lim:cor-paths` for one path `w` (Euclidean `Z*_t = maximum t w`,
`σ_k = smallExit k w`), for the exponent `eta`, the constant `cepsilon` and the parameter `epsilon`:
* (i) oscillation: `Z*_t ≥ c_ε (t/(log(1/t))^{1+ε})^{1/(2+η)}` for all sufficiently small `t > 0`;
  in particular `Z*_t/√t → ∞` as `t ↓ 0`;
* (ii) Hölder exponent: every `γ ≥ 0` with `|Z_t - Z_0| = O(t^γ)` as `t ↓ 0` satisfies
  `γ ≤ 1/(2+η)`;
* (iii) exit times: `σ_k ≤ k^{1+ε} 3^{-(2+η)k}` for all sufficiently large `k`. -/
def aux_lim_cor_paths_SmallTime {d : ℕ} (eta cepsilon epsilon : ℝ) (w : DiffusionPath d) :
    Prop :=
  (∀ᶠ t : ℝ≥0 in 𝓝[>] 0,
    cepsilon * ((t : ℝ) / Real.log (1 / (t : ℝ)) ^ (1 + epsilon)) ^ (1 / (2 + eta)) ≤
      aux_lim_cor_paths_maximum t w) ∧
  Tendsto (fun t : ℝ≥0 => aux_lim_cor_paths_maximum t w / Real.sqrt t) (𝓝[>] 0) atTop ∧
  (∀ gamma : ℝ, 0 ≤ gamma →
    (fun t : ℝ≥0 => Homogenization.euclideanNorm (w t - w 0))
      =O[𝓝[>] 0] (fun t : ℝ≥0 => (t : ℝ) ^ gamma) → gamma ≤ 1 / (2 + eta)) ∧
  (∀ᶠ k : ℕ in atTop, aux_lim_cor_paths_smallExit k w ≤
    ENNReal.ofReal ((k : ℝ) ^ (1 + epsilon) * (3 : ℝ) ^ (-((2 + eta) * (k : ℝ)))))

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_19

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorPathsAssemblyDefs. -/
noncomputable section aux_lim_cor_paths_inline_20

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper

/-- The byte-copied frozen paths conclusion; no source principal is asserted. -/
def aux_lim_cor_paths_inlined_lim_cor_paths_Conclusion (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] : Prop :=
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ eta Cdecay : ℝ, 0 < eta ∧ 0 < Cdecay ∧
        (d = 2 → eta = tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          ahom M m / ahom M l ≤ Cdecay * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) ∧
        (∀ epsilon : ℝ, 0 < epsilon → ∃ cepsilon : ℝ, 0 < cepsilon ∧
          (∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
            (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_IsPhysicalFamily M X →
            ∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
            ∀ (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d),
              Tendsto xs atTop (𝓝 x) →
            ∀ P : ProbabilityMeasure (DiffusionPath d),
              aux_lim_cor_paths_IsAnnealedLimit M X untruncated phi xs P →
              ∀ᵐ w ∂(P : Measure (DiffusionPath d)),
                aux_lim_cor_paths_SmallTime eta cepsilon epsilon w) ∧
          (∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
            ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
              (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
              (hKN : ∀ N, IsMarkovKernel (KN N)), in_crossing M H PN KN →
            ∀ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
              (hK : IsMarkovKernel K), aux_lim_cor_paths_QuenchedConv M KN hKN K hK →
            ∀ x : SpatialCoordinates d,
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                ∀ᵐ w ∂K (omega, x), aux_lim_cor_paths_SmallTime eta cepsilon epsilon w)) ∧
        (∀ p : ℝ, 0 < p → ∃ cp : ℝ, 0 < cp ∧
          ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
            (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_IsPhysicalFamily M X →
            ∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
            ∀ (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d),
              Tendsto xs atTop (𝓝 x) →
            ∀ P : ProbabilityMeasure (DiffusionPath d),
              aux_lim_cor_paths_IsAnnealedLimit M X untruncated phi xs P →
              ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
                ENNReal.ofReal (cp * (t : ℝ) ^ (p / (2 + eta))) ≤
                  ∫⁻ w, ENNReal.ofReal (aux_lim_cor_paths_maximum t w ^ p)
                    ∂(P : Measure (DiffusionPath d)))

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_20

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorExitMomentsDefs. -/
noncomputable section aux_lim_cor_paths_inline_21

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal



namespace SubdiffusiveProcess.Paper

/-- The probability space of the environment of the diffusions `X^{(L)}` and `X`: the layers
`(γ_k)_{k ≥ 0}` on the anchored `C^{1,1}` carrier.  (Body identical to
`SubdiffusiveProcess.Section10.PhysicalAttachment.physicalLaw`.) -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_physicalLaw {d : ℕ} (M : GMCModel d) :
    ProbabilityMeasure (AnchoredC11Sample d) :=
  anchoredC11SampleLaw M (Section6Anchored.measurableSet_anchoredC11GoodSet d)
    (Section6Anchored.measure_anchoredC11GoodSet_eq_one M)

/-- `X L` (`L ∈ ℕ₀` the truncation `X^{(L)}`, `L = ⊤` the untruncated diffusion `X`) is a Markov kernel
`(ω, x) ↦ 𝐏_x^ω` of path laws whose finite-dimensional distributions, for almost every environment
and every start `x`, are those of the conservative Feller semigroup of the weak elliptic resolvent
of `coefficientAt M L ω` (generator `a^{-1} ∇·(a ∇)`, reversible measure `a dx`). -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsPhysicalFamily {d : ℕ} (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)) :
    Prop :=
  ∀ᵐ omega ∂(aux_lim_cor_paths_inlined_lim_cor_exit_moments_physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
    ∃ D : C0ResolventDatum (SpatialCoordinates d),
    ∃ hdense : ∀ mu, DenseRange (D.operator mu),
      IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
      (D.fellerKernelSemigroup hdense).IsConservative ∧
      ∀ (I : Finset ℝ≥0) (x : SpatialCoordinates d),
        ((X L).map (ContinuousPath.finsetEvaluation I)) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x

/-- The rescaled path `Z_t = 3^{-n} X_{3^{2n} t/ahom_n}` (`Z^{(L)}` of `s.tightness`, also for the
untruncated diffusion). -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_rescale {d : ℕ} (M : GMCModel d) (n : ℕ) (w : DiffusionPath d) :
    DiffusionPath d :=
  ⟨fun t => (3 : ℝ) ^ (-(n : ℤ)) •
    w (Real.toNNReal ((3 : ℝ) ^ (2 * n) / ahom M n) * t), by fun_prop⟩

/-- The truncation index of the family: `n` (the cutoff diffusion `X^{(n)}`) or `⊤` (the
untruncated diffusion `X`). -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_familyCutoff (untruncated : Bool) (n : ℕ) : WithTop ℕ :=
  if untruncated then ⊤ else (n : WithTop ℕ)

/-- The cube `z + 𝖢_m` of side `3^m` centred at `z` (the open sup-norm ball of radius `3^m/2`). -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube {d : ℕ} (z : SpatialCoordinates d) (m : ℤ) :
    Set (SpatialCoordinates d) :=
  Metric.ball z ((3 : ℝ) ^ m / 2)

/-- The time unit `3^{2m}/ahom_{m ∧ L}` of the local normalization; `3^{2m}/ahom_m` for `L = ⊤`
(the untruncated diffusion). -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime {d : ℕ} (M : GMCModel d) (L : WithTop ℕ) (m : ℕ) : ℝ :=
  (3 : ℝ) ^ (2 * m) / ahom M (match L with | ⊤ => m | (l : ℕ) => min m l)

/-- `𝐄[τ_U^p]` for the path law `Q` and the exit time `τ_U` from `U`. -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment {d : ℕ} (Q : Measure (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂Q

/-- `σ_k`: the exit time of `Z - Z_0` from the cube `3^{-k} 𝖢_0`. -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_smallExit {d : ℕ} (k : ℕ) (w : DiffusionPath d) : ℝ≥0∞ :=
  ContinuousPath.exitTime (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w

/-- `P` is a subsequential limit of the annealed laws `𝐄[K_{N,x}^ω]` of either family (truncated for
`untruncated = false`, untruncated for `true`), along the subsequence `phi` and the deterministic
starting points `3^{phi n} xs n` in physical coordinates (`xs n → x` in rescaled coordinates): weak
convergence against bounded continuous path functionals.  The environment is sampled once and
kept fixed along the entire path. -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsAnnealedLimit {d : ℕ} (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (untruncated : Bool) (phi : ℕ → ℕ) (xs : ℕ → SpatialCoordinates d)
    (P : ProbabilityMeasure (DiffusionPath d)) : Prop :=
  ∀ G : BoundedContinuousFunction (DiffusionPath d) ℝ,
    Tendsto (fun n => ∫ omega,
      (∫ w, G (aux_lim_cor_paths_inlined_lim_cor_exit_moments_rescale M (phi n) w)
        ∂X (aux_lim_cor_paths_inlined_lim_cor_exit_moments_familyCutoff untruncated (phi n))
          (omega, (3 : ℝ) ^ (phi n) • xs n))
      ∂(aux_lim_cor_paths_inlined_lim_cor_exit_moments_physicalLaw M).toMeasure) atTop
        (𝓝 (∫ w, G w ∂(P : Measure (DiffusionPath d))))

/-- `Z*_t = sup_{0 ≤ s ≤ t} |Z_s - Z_0|` (Euclidean norm): the running maximal displacement. -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_maximum {d : ℕ} (t : ℝ≥0) (w : DiffusionPath d) : ℝ :=
  ⨆ s : Set.Icc (0 : ℝ≥0) t, Homogenization.euclideanNorm (w s - w 0)

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_21

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorPathsAttachment. -/
noncomputable section aux_lim_cor_paths_inline_22

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Paper

/-- Precise remaining physical/bilateral law-identification producer boundary.
For each deterministic start, the very limiting kernel's averaged row is a
subsequential physical annealed limit in the frozen definition. No exit,
endpoint, moment, or regularity conclusion is part of this input. -/
def aux_lim_cor_paths_inlined_lim_cor_paths_LimitingLawAttachment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) : Prop :=
  ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
    ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
      (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
      (hKN : ∀ N, IsMarkovKernel (KN N)), in_crossing M H PN KN →
    ∀ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
      (hK : IsMarkovKernel K), aux_lim_cor_paths_QuenchedConv M KN hKN K hK →
    ∀ x : SpatialCoordinates d,
      ∃ X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d),
      ∃ _hX : ∀ L, IsMarkovKernel (X L),
        aux_lim_cor_paths_IsPhysicalFamily M X ∧
      ∃ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi ∧
      ∃ xs : ℕ → SpatialCoordinates d, Tendsto xs atTop (𝓝 x) ∧
      ∃ P : ProbabilityMeasure (DiffusionPath d),
        aux_lim_cor_paths_IsAnnealedLimit M X untruncated phi xs P ∧
        (P : Measure (DiffusionPath d)) =
          K.comap (fun omega => (omega,x)) (measurable_id.prodMk measurable_const) ∘ₘ
            (chaosSampleLaw M).toMeasure

/-- All ordinary vocabulary is definitionally identical between the two
specified roots, so their physical-family and limiting-law consumer stays literal. -/
theorem aux_lim_cor_paths_inlined_lim_cor_paths_family_iff {d : ℕ} (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)) :
    aux_lim_cor_paths_IsPhysicalFamily M X ↔ aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsPhysicalFamily M X := Iff.rfl

theorem aux_lim_cor_paths_inlined_lim_cor_paths_limit_iff {d : ℕ} (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (untruncated : Bool) (phi : ℕ → ℕ) (xs : ℕ → SpatialCoordinates d)
    (P : ProbabilityMeasure (DiffusionPath d)) :
    aux_lim_cor_paths_IsAnnealedLimit M X untruncated phi xs P ↔
      aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsAnnealedLimit M X untruncated phi xs P := Iff.rfl

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_22

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorPathsMeanConsumer. -/
noncomputable section aux_lim_cor_paths_inline_23

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10.EndpointPaths
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Paper

/-- Literal specified SmallTime application. Its mean input is the physical
prelimit/limit bank, which remains a separate source-assembly obligation. -/
theorem aux_lim_cor_paths_inlined_lim_cor_paths_smallTime_of_mean_decay {d : ℕ}
    (P : ProbabilityMeasure (DiffusionPath d)) (C eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hmean : ∀ k : ℕ, (∫⁻ w, aux_lim_cor_paths_smallExit k w
      ∂(P : Measure (DiffusionPath d))) ≤
        ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))) :
    0 < oscillationConstant eta epsilon ∧
      ∀ᵐ w ∂(P : Measure (DiffusionPath d)),
        aux_lim_cor_paths_SmallTime eta (oscillationConstant eta epsilon) epsilon w := by
  refine ⟨oscillationConstant_pos eta epsilon heta, ?_⟩
  simpa only [aux_lim_cor_paths_SmallTime, aux_lim_cor_paths_smallExit,
    aux_lim_cor_paths_maximum, smallExit, maximum, endpoint] using
    ae_endpoint_consequences_of_mean_decay (P : Measure (DiffusionPath d)) C eta epsilon
      heta hepsilon hmean

/-- Part (iv) at every positive real moment order, with a constant before P
and t. Enlarging C to max 1 C handles the initial geometric scale. -/
theorem aux_lim_cor_paths_inlined_lim_cor_paths_maximal_lower_of_mean_decay {d : ℕ}
    (C eta p : ℝ) (heta : 0 < eta) (hp : 0 < p) :
    ∃ cp : ℝ, 0 < cp ∧ ∀ P : ProbabilityMeasure (DiffusionPath d),
      (∀ k : ℕ, (∫⁻ w, aux_lim_cor_paths_smallExit k w
        ∂(P : Measure (DiffusionPath d))) ≤
          ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))) →
      ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
        ENNReal.ofReal (cp * (t : ℝ)^(p/(2+eta))) ≤
          ∫⁻ w, ENNReal.ofReal (aux_lim_cor_paths_maximum t w ^ p)
            ∂(P : Measure (DiffusionPath d)) := by
  let C' : ℝ := max 1 C
  have hC' : 0 < C' := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨momentRadiusConstant C' eta ^ p / 2,
    div_pos (Real.rpow_pos_of_pos (momentRadiusConstant_pos C' eta hC') p)
      (by norm_num), ?_⟩
  intro P hmean t ht ht1
  exact maximal_moment_lower_of_mean_exits (P : Measure (DiffusionPath d)) C' eta
    (le_max_left _ _) heta
    (fun k => by simpa only [ENNReal.rpow_one] using!
      (SubdiffusiveProcess.Section10.ExitMomentPassage.smallExit_rpow_lsc k 1 (by norm_num)).measurable)
    (fun k => (hmean k).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right 1 C) (Real.rpow_nonneg (by norm_num) _))))
    p hp t ht ht1

/-- Quenched consequence for each deterministic start, from the literal
averaged row moments of the same limiting joint kernel. Identifying this
average with a physical annealed limit is the remaining producer boundary. -/
theorem aux_lim_cor_paths_inlined_lim_cor_paths_quenched_of_averaged_mean {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (x : SpatialCoordinates d) (C eta epsilon : ℝ)
    (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hmean : ∀ k : ℕ,
      (∫⁻ omega, ∫⁻ w, aux_lim_cor_paths_smallExit k w ∂K (omega,x)
        ∂(chaosSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ᵐ w ∂K (omega,x),
        aux_lim_cor_paths_SmallTime eta (oscillationConstant eta epsilon) epsilon w := by
  let := hK
  let row := K.comap (fun omega => (omega,x)) (measurable_id.prodMk measurable_const)
  let P : ProbabilityMeasure (DiffusionPath d) :=
    ⟨row ∘ₘ (chaosSampleLaw M).toMeasure, inferInstance⟩
  have hbar : ∀ k : ℕ, (∫⁻ w, aux_lim_cor_paths_smallExit k w
      ∂(P : Measure (DiffusionPath d))) ≤
        ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ)))) := by
    intro k
    have hf : Measurable (aux_lim_cor_paths_smallExit (d := d) k) := by
      simpa only [ENNReal.rpow_one] using!
        (SubdiffusiveProcess.Section10.ExitMomentPassage.smallExit_rpow_lsc k 1 (by norm_num)).measurable
    change (∫⁻ w, aux_lim_cor_paths_smallExit k w
      ∂(chaosSampleLaw M).toMeasure.bind row) ≤ _
    rw [Measure.lintegral_bind (Kernel.aemeasurable row) hf.aemeasurable]
    exact hmean k
  have hs := (aux_lim_cor_paths_inlined_lim_cor_paths_smallTime_of_mean_decay P C eta epsilon heta hepsilon hbar).2
  change ∀ᵐ w ∂(row ∘ₘ (chaosSampleLaw M).toMeasure),
    aux_lim_cor_paths_SmallTime eta (oscillationConstant eta epsilon) epsilon w at hs
  exact Measure.ae_ae_of_ae_comp (κ := row) (μ := (chaosSampleLaw M).toMeasure) hs

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_23

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorExitMomentsAssemblyDefs. -/
noncomputable section aux_lim_cor_paths_inline_24

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper

/-- The exact frozen conclusion, shared only by internal source-assembly helpers. -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_Conclusion (d : ℕ) : Prop :=
    ∃ deltaBase : ℝ, 0 < deltaBase ∧
    ∃ eta Cdecay : GMCModel d → ℝ,
      (∀ M : GMCModel d, M.delta ≤ deltaBase →
        0 < eta M ∧ 0 < Cdecay M ∧
        (d = 2 → eta M = tauSq M.P / Real.log 3) ∧
        ∀ l m : ℕ, l ≤ m →
          ahom M m / ahom M l ≤ Cdecay M * (3 : ℝ) ^ (-(eta M) * ((m : ℝ) - (l : ℝ)))) ∧
      ∀ p : ℝ, 0 < p → ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ deltaBase ∧
        ∀ M : GMCModel d, M.delta ≤ delta0 →
        ∃ cp Cp : ℝ, 0 < cp ∧ cp ≤ Cp ∧
        ∀ q : ℝ, 0 < q → q < p * (2 + eta M) → ∃ Cpq : ℝ, 0 < Cpq ∧
        ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsPhysicalFamily M X →
          (∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
            (∫⁻ omega, (⨆ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ),
                aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega, x))
                  (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) p)
              ∂(aux_lim_cor_paths_inlined_lim_cor_exit_moments_physicalLaw M).toMeasure) ≤
              ENNReal.ofReal (Cp * aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m ^ p) ∧
            ENNReal.ofReal (cp * aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m ^ p) ≤
              (∫⁻ omega, (⨅ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z ((m : ℤ) - 2),
                aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega, x))
                  (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) p)
                ∂(aux_lim_cor_paths_inlined_lim_cor_exit_moments_physicalLaw M).toMeasure)) ∧
          (∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
            ∀ (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d),
              Tendsto xs atTop (𝓝 x) →
            ∀ P : ProbabilityMeasure (DiffusionPath d),
              aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsAnnealedLimit M X untruncated phi xs P →
              (∀ k : ℕ, (∫⁻ w, aux_lim_cor_paths_inlined_lim_cor_exit_moments_smallExit k w ^ p
                  ∂(P : Measure (DiffusionPath d))) ≤
                ENNReal.ofReal (Cp * (3 : ℝ) ^ (-((p * (2 + eta M)) * (k : ℝ))))) ∧
              (∀ t epsilon : ℝ≥0, 0 < t → t ≤ 1 → 0 < epsilon → epsilon ≤ 1 →
                (P : Measure (DiffusionPath d))
                  {w | aux_lim_cor_paths_inlined_lim_cor_exit_moments_maximum t w ≤
                    (epsilon : ℝ) * (t : ℝ) ^ (1 / (2 + eta M))} ≤
                  ENNReal.ofReal (Cp * (epsilon : ℝ) ^ (p * (2 + eta M)))) ∧
              ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
                (∫⁻ w, ENNReal.ofReal (aux_lim_cor_paths_inlined_lim_cor_exit_moments_maximum t w) ^ (-q)
                  ∂(P : Measure (DiffusionPath d))) ≤
                  ENNReal.ofReal (Cpq * (t : ℝ) ^ (-q / (2 + eta M))))

/-- Explicit random first-mean induction input. This is a conditional helper
interface; it is not an asserted mean-exit source theorem. -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_RandomMeanBank (d : ℕ) : Prop :=
(∃ c : ℝ, 0 < c ∧ ∀ q : ℝ,
      ∃ deltaq : ℝ, 0 < deltaq ∧
      ∀ M : GMCModel d, M.delta ≤ deltaq →
      ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
            (∫⁻ omega, ENNReal.ofReal (K omega ^ q)
              ∂(aux_lim_cor_paths_inlined_lim_cor_exit_moments_physicalLaw M).toMeasure) ≤ ENNReal.ofReal Cq ∧
            ∀ᵐ omega ∂(aux_lim_cor_paths_inlined_lim_cor_exit_moments_physicalLaw M).toMeasure,
              (∀ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ),
                aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega, x))
                  (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) 1 ≤
                  ENNReal.ofReal (K omega * aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m)) ∧
              (∀ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z ((m : ℤ) - 2),
                ENNReal.ofReal (c * K omega ^ (-2 : ℤ) * aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m) ≤
                  aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega, x))
                    (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) 1))

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_24

/- Inlined proved source application: SubdiffusiveProcess.Paper.PrelimitExitStaticBank. -/
noncomputable section aux_lim_cor_paths_inline_25

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Section10
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
namespace SubdiffusiveProcess.Paper

def aux_lim_cor_paths_inlined_prelimit_exit_price (d : ℕ) (D K : ℝ) : ℝ :=
  max 1 (torsionConstant (2 * (d : ℝ) / ((d : ℝ)-1)) * D) * K ^ (2 + 1/(d : ℝ))

/-- The two actual physical projections give the same-coefficient torsion bound. -/
theorem aux_lim_cor_paths_inlined_prelimit_torsion_of_static {d : ℕ} (hd : 2 ≤ d) (B : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b A : SpatialCoordinates d → ℝ) (K : ℝ),
      1 ≤ K → PhysicalStaticBounds b A B K →
      CoefficientOn (Metric.ball (0 : SpatialCoordinates d) (1/2)) A →
      TorsionSobolevBound A b (Metric.ball 0 (1/2))
        (2 * (d : ℝ) / ((d : ℝ)-1)) (D * K^2) := by
  obtain ⟨D, hD, hdet⟩ := aux_lim_cor_paths_inlined_killed_sobolev_of_mass_coercivity hd B
  exact ⟨D, hD, fun b A K hK hs hA v => (hdet b A K hK hs.1 hs.2 hA v).2.2.1⟩

/-- The unit cube mass costs at most the actual static coefficient K. -/
theorem aux_lim_cor_paths_inlined_prelimit_mass_le {d : ℕ} (hd : 2 ≤ d)
    {b A : SpatialCoordinates d → ℝ} {B K : ℝ}
    (hK : 1 ≤ K) (hs : PhysicalStaticBounds b A B K) :
    weightedMeasure b (Metric.ball (0 : SpatialCoordinates d) (1/2)) ≤ ENNReal.ofReal K := by
  have hdR : 2 ≤ (d : ℝ) := by exact_mod_cast hd
  refine (hs.1 0 (Metric.mem_ball_self (by norm_num)) (1/2)
    (by norm_num) (by norm_num)).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_of_le_one_right (zero_le_one.trans hK)
    (Real.rpow_le_one (by norm_num) (by norm_num) (by linarith))

/-- The moment bank is uniform before N,k and the deterministic translated start.
Only the genuine finite window N-k<=N is used. No all-scale bank is assumed. -/
theorem aux_lim_cor_paths_inlined_prelimit_exit_price_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ B D : ℝ, 0 < B ∧ 0 < D ∧
      (∀ b A K, 1 ≤ K → PhysicalStaticBounds b A B K →
        CoefficientOn (Metric.ball (0 : SpatialCoordinates d) (1/2)) A →
        TorsionSobolevBound A b (Metric.ball 0 (1/2))
          (2 * (d : ℝ) / ((d : ℝ)-1)) (D*K^2)) ∧
      ∀ p : ℝ, 0 < p → ∃ delta : ℝ, 0 < delta ∧
        ∀ M : GMCModel d, M.delta ≤ delta → ∃ Cp : ℝ, 0 < Cp ∧
          ∀ N k : ℕ, k ≤ N → ∀ x : SpatialCoordinates d,
            ∃ K : AnchoredC11Sample d → ℝ,
              Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
              Measurable (fun omega => aux_lim_cor_paths_inlined_prelimit_exit_price d D (K omega)) ∧
              (∀ omega, 1 ≤ aux_lim_cor_paths_inlined_prelimit_exit_price d D (K omega)) ∧
              (∫⁻ omega, ENNReal.ofReal (aux_lim_cor_paths_inlined_prelimit_exit_price d D (K omega) ^ p)
                ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal Cp ∧
              ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
                PhysicalStaticBounds
                  (localSpeed M N (N-k) ((3 : ℝ)^N • x) omega)
                  (localCoefficient M N (N-k) ((3 : ℝ)^N • x) omega) B (K omega) := by
  obtain ⟨B, hB, hstatic⟩ := aux_lim_cor_paths_inlined_physical_sobolev_static_bank_small_scale hd
  obtain ⟨D, hD, htor⟩ := aux_lim_cor_paths_inlined_prelimit_torsion_of_static hd B
  refine ⟨B, D, hB, hD, htor, ?_⟩
  intro p hp
  let s : ℝ := 2 + 1/(d : ℝ)
  let Q : ℝ := max 1 (s*p)
  obtain ⟨delta, hdelta, hmodels⟩ := hstatic Q (le_max_left _ _)
  refine ⟨delta, hdelta, ?_⟩
  intro M hM
  obtain ⟨Cs, hCs, hscales⟩ := hmodels M hM
  let F := max 1 (torsionConstant (2 * (d : ℝ) / ((d : ℝ)-1)) * D)
  have hF : 0 < F := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨F^p * Cs, mul_pos (Real.rpow_pos_of_pos hF p) hCs, ?_⟩
  intro N k _ x
  obtain ⟨K, hK, hone, hmom, hs⟩ := hscales N (N-k)
    (Or.inr ⟨N, rfl, Nat.sub_le N k⟩) ((3 : ℝ)^N • x)
  refine ⟨K, hK, hone, ?_, ?_, ?_, hs⟩
  · exact measurable_const.mul (hK.pow_const s)
  · intro omega
    have hkp : 1 ≤ K omega ^ s := Real.one_le_rpow (hone omega) (by dsimp [s]; positivity)
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ _ := mul_le_mul (le_max_left _ _) hkp (by norm_num)
        (zero_le_one.trans (le_max_left _ _))
  · calc
      _ ≤ ∫⁻ omega, ENNReal.ofReal (F^p) * ENNReal.ofReal (K omega ^ Q)
          ∂(PhysicalAttachment.physicalLaw M).toMeasure := by
        apply lintegral_mono
        intro omega
        dsimp only
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hF.le p)]
        apply ENNReal.ofReal_le_ofReal
        change (F * K omega ^ s)^p ≤ _
        rw [Real.mul_rpow hF.le (Real.rpow_nonneg (zero_le_one.trans (hone omega)) s),
          ← Real.rpow_mul (zero_le_one.trans (hone omega))]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (hone omega) (le_max_right _ _))
          (Real.rpow_nonneg hF.le p)
      _ = ENNReal.ofReal (F^p) *
          ∫⁻ omega, ENNReal.ofReal (K omega ^ Q)
            ∂(PhysicalAttachment.physicalLaw M).toMeasure :=
        lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hK.pow_const Q))
      _ ≤ ENNReal.ofReal (F^p) * ENNReal.ofReal Cs := mul_le_mul_right hmom _
      _ = _ := (ENNReal.ofReal_mul (Real.rpow_nonneg hF.le p)).symm

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_25

/- Inlined proved source application: SubdiffusiveProcess.Paper.PrelimitExitPhysical. -/
noncomputable section aux_lim_cor_paths_inline_26

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalLocalTransport SubdiffusiveProcess.Section10.PhysicalAttachment
open SubdiffusiveProcess.Probability.Diffusion SubdiffusiveProcess
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper
variable {d : ℕ}

/-- Literal local path map of the supplied characterized physical kernel. -/
def aux_lim_cor_paths_inlined_prelimit_localKernel (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (X : PhysicalKernel d) : PhysicalKernel d :=
  (X.comap (fun p : AnchoredC11Sample d × Vec d => (p.1, physicalCoordinates m z p.2))
    (measurable_fst.prodMk ((physicalCoordinates m z).measurable.comp measurable_snd))).map
      (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m))

instance aux_lim_cor_paths_inlined_prelimit_localKernel_markov (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (X : PhysicalKernel d) [IsMarkovKernel X] :
    IsMarkovKernel (aux_lim_cor_paths_inlined_prelimit_localKernel M L m z X) :=
  Kernel.IsMarkovKernel.map _ (ContinuousPath.measurable_rescale _ _)

theorem aux_lim_cor_paths_inlined_prelimit_localKernel_apply (M : GMCModel d) (L : WithTop ℕ) (m : ℕ)
    (z : Vec d) (X : PhysicalKernel d) (omega : AnchoredC11Sample d) (x : Vec d) :
    aux_lim_cor_paths_inlined_prelimit_localKernel M L m z X (omega,x) =
      (X (omega, physicalCoordinates m z x)).map
        (ContinuousPath.rescale (physicalCoordinates m z).symm (rawClock M L m)) := by
  rw [aux_lim_cor_paths_inlined_prelimit_localKernel, Kernel.map_apply _ (ContinuousPath.measurable_rescale _ _),
    Kernel.comap_apply]

/-- Transport the very supplied physical KN. FOT supplies killed association;
the already proved Feller restart supplies StrongMarkov, without a density leaf. -/
theorem aux_lim_cor_paths_inlined_prelimit_localDiffusion (hFOT : E7.FOTPartProcess) (M : GMCModel d)
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    [NeZero d] (L : WithTop ℕ) (m : ℕ) (z : Vec d)
    (X : PhysicalKernel d) [IsMarkovKernel X]
    (hsource : aux_lim_cor_paths_inlined_physical_local_source_characterization M L X) :
    ∀ᵐ omega ∂(physicalLaw M).toMeasure,
      LocalDiffusion (localCoefficient M L m z omega) (localSpeed M L m z omega)
        ((physicalSlice (aux_lim_cor_paths_inlined_prelimit_localKernel M L m z X) omega).map
          LifetimePath.ofContinuousPath) := by
  filter_upwards [hsource] with omega h
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := h
  let E := transportedDatum D (physicalCoordinates m z) (rawClock M L m) (rawClock_pos M L m)
  let he := transportedDatum_dense D hdense (physicalCoordinates m z) (rawClock M L m)
    (rawClock_pos M L m)
  have hconj := aux_lim_cor_paths_inlined_physical_local_datum_conjugacy D hdense (physicalCoordinates m z)
    (rawClock M L m) (rawClock_pos M L m)
  have hE := aux_lim_cor_paths_inlined_physical_local_datum_weak M L m z omega D hweak
  let Y := physicalSlice (aux_lim_cor_paths_inlined_prelimit_localKernel M L m z X) omega
  let : IsMarkovKernel (physicalSlice X omega) := by
    dsimp only [physicalSlice]; infer_instance
  let : IsMarkovKernel Y := by
    dsimp only [Y, physicalSlice]; infer_instance
  have hF : ∀ I x, Y.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (E.fellerKernelSemigroup he) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    change (aux_lim_cor_paths_inlined_prelimit_localKernel M L m z X (omega,x)).map _ = _
    rw [aux_lim_cor_paths_inlined_prelimit_localKernel_apply]
    exact aux_lim_cor_paths_inlined_physical_local_rescaled_fdd _ _ hcons (physicalSlice X omega) inferInstance
      hfdd (physicalCoordinates m z).symm (rawClock M L m) (rawClock_pos M L m) hconj I x
  have hc : Continuous (localCoefficient M L m z omega) :=
    continuous_const.mul (continuous_localSpeed M L m z omega)
  have hb := continuous_localSpeed M L m z omega
  have hcp : ∀ x, 0 < localCoefficient M L m z omega x := fun x =>
    mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _))
      (localSpeed_pos M L m z omega x)
  have hbp := localSpeed_pos M L m z omega
  have hrestart := fellerRestart d _ (hconj.isConservative hcons)
    (E.isFellerKernelSemigroup_fellerKernelSemigroup he) Y inferInstance hF
  have hgen := E7.killedGenerator_of_leaf hc hb hcp hbp (E.fellerKernelSemigroup he)
    (hconj.isConservative hcons) (E.isFellerKernelSemigroup_fellerKernelSemigroup he)
    E hE (E.solution_eq_laplace he) Y hF hFOT
  refine ⟨strongMarkov_of_restart hrestart, ?_, ?_⟩
  · intro S hS
    exact ⟨SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos hc hcp hS.isBounded,
      SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos hb hbp hS.isBounded⟩
  · intro U hU hUb s hs f hf
    exact killedResolvent_clause_of_killedGenerator hgen hU hUb
      (SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos hc hcp hUb)
      (SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos hb hbp hUb) hs hf

/-- Construct one actual characterized KN family before every moment order.
Subsequent applications accept this same family; no new law is selected per p. -/
theorem aux_lim_cor_paths_inlined_exists_characterized_prelimitFamily (M : GMCModel d) [NeZero d]
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] :
    ∃ X : ℕ → PhysicalKernel d, (∀ N, IsMarkovKernel (X N)) ∧
      ∀ N : ℕ, aux_lim_cor_paths_inlined_physical_local_source_characterization M N (X N) := by
  obtain ⟨X, hX, hgood⟩ := exists_physical_family M
  refine ⟨fun N => X N, fun N => hX N, ?_⟩
  intro N
  filter_upwards [hgood] with omega h
  obtain ⟨D, hdense, hweak, hcons, hF⟩ := h N
  refine ⟨D, hdense, hweak, hcons, ?_⟩
  intro I x
  rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
  exact hF I x

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_26

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorExitMomentsAdapters. -/
noncomputable section aux_lim_cor_paths_inline_27

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalAttachment SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.Section10.PrelimitExitPaths
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper

/-- The actual strict-decay supplier chooses the functions before all moment
orders, exactly as required by the specified exit-moment principal. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_strict_rate {d : ℕ} (hd : 2 ≤ d) :
    ∃ deltaBase : ℝ, 0 < deltaBase ∧ ∃ eta Cdecay : GMCModel d → ℝ,
      ∀ M : GMCModel d, M.delta ≤ deltaBase →
        0 < eta M ∧ 0 < Cdecay M ∧
        (d = 2 → eta M = tauSq M.P / Real.log 3) ∧
        ∀ l m : ℕ, l ≤ m →
          ahom M m / ahom M l ≤ Cdecay M * (3 : ℝ)^(-(eta M)*((m : ℝ)-(l : ℝ))) := by
  classical
  obtain ⟨deltaBase, hdelta, hmodels⟩ := strict_decay hd
  have hchoose : ∀ M : GMCModel d, ∃ eta C : ℝ,
      M.delta ≤ deltaBase → 0 < eta ∧ 0 < C ∧
        (d = 2 → eta = tauSq M.P / Real.log 3) ∧
        ∀ l m : ℕ, l ≤ m → ahom M m / ahom M l ≤
          C * (3 : ℝ)^(-eta*((m : ℝ)-(l : ℝ))) := by
    intro M
    by_cases hM : M.delta ≤ deltaBase
    · obtain ⟨C, eta, c, hC, heta, _, hplanar, hdec, _, _⟩ := hmodels M hM
      refine ⟨eta, C, fun _ => ⟨heta, hC, hplanar, ?_⟩⟩
      simpa only [neg_mul] using hdec
    · exact ⟨1, 1, fun h => False.elim (hM h)⟩
  choose eta C hrate using hchoose
  exact ⟨deltaBase, hdelta, eta, C, hrate⟩

/-- Extract the characterization of the supplied row kernel from the common
environment event of the frozen family. No replacement family is selected. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_row_characterization {d : ℕ}
    (M : GMCModel d) (X : WithTop ℕ → PhysicalKernel d)
    (hfamily : aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsPhysicalFamily M X) (L : WithTop ℕ) :
    aux_lim_cor_paths_inlined_physical_local_source_characterization M L (X L) := by
  filter_upwards [hfamily] with omega hw
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := hw L
  refine ⟨D, hdense, hweak, hcons, ?_⟩
  intro I x
  simpa only [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)] using hfdd I x

/-- The specified local-time definition is precisely the proved raw clock,
including cutoff zero, the saturated branch m>L, and the untruncated branch. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime_eq {d : ℕ} (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) :
    aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m = (rawClock M L m : ℝ) := by
  cases L with
  | top => simp only [aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime, rawClock, activeScale,
      WithTop.untopD_top, min_self] ; rfl
  | coe l => rfl

/-- Literal path-map identity, retaining the source clock 3^(2N)/ahom_N. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_rescale_eq {d : ℕ} (M : GMCModel d) (N : ℕ) :
    aux_lim_cor_paths_inlined_lim_cor_exit_moments_rescale M N = prelimitPath M N := by
  have hclock : Real.toNNReal ((3 : ℝ)^(2*N)/ahom M N) = rawClock M N N := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (div_pos (pow_pos (by norm_num) _) (ahom_pos M N)).le]
    simp only [rawClock, activeScale_coe, min_self] ; rfl
  funext w
  ext t
  simp only [aux_lim_cor_paths_inlined_lim_cor_exit_moments_rescale, ContinuousMap.coe_mk,
    prelimitPath, ContinuousPath.rescale_apply, physicalCoordinates_symm_apply,
    sub_zero, zpow_neg, zpow_natCast, hclock]

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_27

/- Inlined proved source application: SubdiffusiveProcess.Paper.PrelimitExitClassicalFOT. -/
noncomputable section aux_lim_cor_paths_inline_28

namespace SubdiffusiveProcess.Paper

/-- Discharge the explicit generic FOT slot from its now proved canonical supplier. -/
theorem aux_lim_cor_paths_inlined_prelimit_fotPartProcess : SubdiffusiveProcess.E7.FOTPartProcess := by
  intro d m hm hpos E hE P hP hF K hK hfdd hassoc U hU
  exact inputs_classical_fot_part_process d m hm hpos E hE P hP hF K hK hfdd hassoc U hU

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_28

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorExitMomentsNormalize. -/
noncomputable section aux_lim_cor_paths_inline_29

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalAttachment SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.Section10.ExitMomentPassage
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper

/-- The physical chart sends both the exit cube and its inner starting cube
to the literal specified physical cubes. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_image_cube {d : ℕ}
    (m : ℕ) (z : SpatialCoordinates d) (j : ℤ) :
    physicalCoordinates m z '' aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube (0 : SpatialCoordinates d) j =
      aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (j+(m : ℤ)) := by
  rw [aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube, physicalCoordinates_image_ball,
    aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  congr 1
  ring

/-- Exact all-p row normalization on the same supplied physical kernel. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_local_moment {d : ℕ} (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d) (X : PhysicalKernel d)
    (omega : AnchoredC11Sample d) (x : SpatialCoordinates d) (p : ℝ) (hp : 0 < p) :
    (∫⁻ w, ContinuousPath.exitTime
      (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube (0 : SpatialCoordinates d) 0) w ^ p
      ∂aux_lim_cor_paths_inlined_prelimit_localKernel M L m z X (omega,x)) =
      ((rawClock M L m : ℝ≥0∞)^p)⁻¹ *
        aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X (omega,physicalCoordinates m z x))
          (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) p := by
  rw [aux_lim_cor_paths_inlined_prelimit_localKernel_apply]
  have h := exitMoment_map_rescale (X (omega, physicalCoordinates m z x))
    (physicalCoordinates m z) (rawClock M L m) (rawClock_pos M L m)
    (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube 0 0) Metric.isOpen_ball p hp
  rw [aux_lim_cor_paths_inlined_lim_cor_exit_moments_image_cube] at h
  simpa only [zero_add, aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment] using! h

/-- The genuine law characterization supplies normalized strong Markov using
the proved FOT command. This is independent of the mean-exit producer. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_local_strongMarkov {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : GMCModel d) (X : WithTop ℕ → PhysicalKernel d)
    (hX : ∀ L, IsMarkovKernel (X L))
    (hfamily : aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsPhysicalFamily M X)
    (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d) :
    ∀ᵐ omega ∂(physicalLaw M).toMeasure,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov
        ((physicalSlice (aux_lim_cor_paths_inlined_prelimit_localKernel M L m z (X L)) omega).map
          LifetimePath.ofContinuousPath) := by
  let : NeZero d := ⟨by omega⟩
  let := hX L
  exact (aux_lim_cor_paths_inlined_prelimit_localDiffusion aux_lim_cor_paths_inlined_prelimit_fotPartProcess M L m z (X L)
    (aux_lim_cor_paths_inlined_lim_cor_exit_moments_row_characterization M X hfamily L)).mono (fun _ h => h.1)

/-- Raw physical mean bounds become normalized mean bounds with no loss in K
or c. The root's saturated/local clock is used, not an ahom_0 normalization. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_normalized_mean_bank {d : ℕ}
    (M : GMCModel d) (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d)
    (X : PhysicalKernel d) (K : AnchoredC11Sample d → ℝ) (c : ℝ)
    (hK : ∀ omega, 1 ≤ K omega)
    (hraw : ∀ᵐ omega ∂(physicalLaw M).toMeasure,
      (∀ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ),
        aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X (omega,x))
          (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) 1 ≤
            ENNReal.ofReal (K omega * aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m)) ∧
      (∀ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z ((m : ℤ)-2),
        ENNReal.ofReal (c * K omega ^ (-2 : ℤ) * aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m) ≤
          aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X (omega,x))
            (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) 1)) :
    ∀ᵐ omega ∂(physicalLaw M).toMeasure,
      (∀ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube (0 : SpatialCoordinates d) 0,
        (∫⁻ w, ContinuousPath.exitTime
          (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube (0 : SpatialCoordinates d) 0) w
          ∂aux_lim_cor_paths_inlined_prelimit_localKernel M L m z X (omega,x)) ≤ ENNReal.ofReal (K omega)) ∧
      (∀ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube (0 : SpatialCoordinates d) (-2),
        ENNReal.ofReal (c/(K omega)^2) ≤
          ∫⁻ w, ContinuousPath.exitTime
            (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube (0 : SpatialCoordinates d) 0) w
            ∂aux_lim_cor_paths_inlined_prelimit_localKernel M L m z X (omega,x)) := by
  let T := rawClock M L m
  have hT : 0 < (T : ℝ) := rawClock_pos M L m
  have hconvert (omega : AnchoredC11Sample d) (x : SpatialCoordinates d) :
      (∫⁻ w, ContinuousPath.exitTime
        (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube (0 : SpatialCoordinates d) 0) w
        ∂aux_lim_cor_paths_inlined_prelimit_localKernel M L m z X (omega,x)) =
          (T : ℝ≥0∞)⁻¹ * aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment
            (X (omega,physicalCoordinates m z x)) (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) 1 := by
    simpa only [ENNReal.rpow_one] using!
      aux_lim_cor_paths_inlined_lim_cor_exit_moments_local_moment M L m z X omega x 1 (by norm_num)
  have him0 := aux_lim_cor_paths_inlined_lim_cor_exit_moments_image_cube m z 0
  have him2 := aux_lim_cor_paths_inlined_lim_cor_exit_moments_image_cube m z (-2)
  simp only [zero_add] at him0
  rw [show (-2 : ℤ)+(m : ℤ) = (m : ℤ)-2 by ring] at him2
  filter_upwards [hraw] with omega hr
  have hKpos : 0 < K omega := lt_of_lt_of_le (by norm_num) (hK omega)
  constructor
  · intro x hx
    rw [hconvert]
    have hx' : physicalCoordinates m z x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ) := by
      rw [← him0]
      exact mem_image_of_mem _ hx
    have h := mul_le_mul_right (hr.1 _ hx') (T : ℝ≥0∞)⁻¹
    rw [aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime_eq, ENNReal.ofReal_mul hKpos.le,
      ENNReal.ofReal_coe_nnreal, mul_comm (ENNReal.ofReal (K omega)), ← mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr (rawClock_pos M L m).ne')
        ENNReal.coe_ne_top, one_mul] at h
    exact h
  · intro x hx
    rw [hconvert]
    have hx' : physicalCoordinates m z x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z ((m : ℤ)-2) := by
      rw [← him2]
      exact mem_image_of_mem _ hx
    have h := mul_le_mul_right (hr.2 _ hx') (T : ℝ≥0∞)⁻¹
    rw [aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime_eq] at h
    change (T : ℝ≥0∞)⁻¹ * ENNReal.ofReal (c*K omega^(-2 : ℤ)*(T : ℝ)) ≤ _ at h
    rw [ENNReal.ofReal_mul' hT.le, ENNReal.ofReal_coe_nnreal,
      mul_comm (ENNReal.ofReal (c*K omega^(-2 : ℤ))) (T : ℝ≥0∞), ← mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr (rawClock_pos M L m).ne')
        ENNReal.coe_ne_top, one_mul] at h
    simpa only [zpow_neg, zpow_ofNat, div_eq_mul_inv] using! h

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_29

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorExitMomentsPhysicalBank. -/
noncomputable section aux_lim_cor_paths_inline_30

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalAttachment SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.Section10.ExitTailMoments SubdiffusiveProcess.Section10.ExitLowerMoments
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper

/-- All positive powered physical moments from the actual random mean bank.
Constants use only the supplied uniform environment moments; mean estimates
are the mathematical induction input, never a source conclusion assumed here. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_physical_moments_of_mean_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : GMCModel d) (X : WithTop ℕ → PhysicalKernel d)
    (hX : ∀ L, IsMarkovKernel (X L))
    (hfamily : aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsPhysicalFamily M X)
    (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d)
    (K : AnchoredC11Sample d → ℝ) (hK : Measurable K) (hKone : ∀ omega, 1 ≤ K omega)
    (Cmean : ℝ≥0) (hCmean : 1 ≤ Cmean)
    (hmean : (∫⁻ omega, ENNReal.ofReal (K omega) ∂(physicalLaw M).toMeasure) ≤ Cmean)
    (c Cmoment p : ℝ) (hc : 0 < c) (hp : 0 < p)
    (hmoment : (∫⁻ omega, ENNReal.ofReal (K omega ^ p) ∂(physicalLaw M).toMeasure) ≤
      ENNReal.ofReal Cmoment)
    (hraw : ∀ᵐ omega ∂(physicalLaw M).toMeasure,
      (∀ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ),
        aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega,x))
          (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) 1 ≤
            ENNReal.ofReal (K omega * aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m)) ∧
      (∀ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z ((m : ℤ)-2),
        ENNReal.ofReal (c * K omega ^ (-2 : ℤ) * aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m) ≤
          aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega,x))
            (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) 1)) :
    (∫⁻ omega, (⨆ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ),
      aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega,x))
        (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) p) ∂(physicalLaw M).toMeasure) ≤
      ENNReal.ofReal ((upperMomentConstant p * Cmoment) *
        aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m ^ p) ∧
    ENNReal.ofReal (meanBankLowerConstant c Cmean p *
      aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m ^ p) ≤
        ∫⁻ omega, (⨅ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z ((m : ℤ)-2),
          aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega,x))
            (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) p) ∂(physicalLaw M).toMeasure := by
  let := hX L
  let Y := aux_lim_cor_paths_inlined_prelimit_localKernel M L m z (X L)
  let U := aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube (0 : SpatialCoordinates d) 0
  let V := aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube (0 : SpatialCoordinates d) (-2)
  let T := rawClock M L m
  let a : ℝ≥0∞ := (T : ℝ≥0∞)^p
  let Knn := fun omega => Real.toNNReal (K omega)
  have hT : 0 < (T : ℝ) := rawClock_pos M L m
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos
    (by exact_mod_cast (rawClock_pos M L m)) ENNReal.coe_ne_top).ne'
  have haf : a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.coe_ne_top
  have hKpos : ∀ omega, 0 < K omega := fun omega => lt_of_lt_of_le (by norm_num) (hKone omega)
  have hKcoe : ∀ omega, (Knn omega : ℝ) = K omega := fun omega =>
    Real.coe_toNNReal _ (hKpos omega).le
  have hKn : ∀ omega, 1 ≤ Knn omega := by
    intro omega
    apply NNReal.coe_le_coe.mp
    simpa only [hKcoe, NNReal.coe_one] using hKone omega
  let : ∀ omega, IsMarkovKernel (physicalSlice Y omega) := fun omega => by
    dsimp only [physicalSlice]; infer_instance
  have hn := aux_lim_cor_paths_inlined_lim_cor_exit_moments_normalized_mean_bank M L m z (X L) K c hKone hraw
  have hs := aux_lim_cor_paths_inlined_lim_cor_exit_moments_local_strongMarkov hd M X hX hfamily L m z
  have hrow (omega : AnchoredC11Sample d) (x : SpatialCoordinates d) :
      aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega,physicalCoordinates m z x))
        (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) p =
          a * ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂Y (omega,x) := by
    rw [aux_lim_cor_paths_inlined_lim_cor_exit_moments_local_moment M L m z (X L) omega x p hp,
      ← mul_assoc, ENNReal.mul_inv_cancel ha0 haf, one_mul]
  have him0 := aux_lim_cor_paths_inlined_lim_cor_exit_moments_image_cube m z 0
  have him2 := aux_lim_cor_paths_inlined_lim_cor_exit_moments_image_cube m z (-2)
  simp only [zero_add] at him0
  rw [show (-2 : ℤ)+(m : ℤ) = (m : ℤ)-2 by ring] at him2
  have ha : a = ENNReal.ofReal (aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m ^ p) := by
    rw [aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime_eq]
    change (T : ℝ≥0∞)^p = ENNReal.ofReal ((T : ℝ)^p)
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg hT.le hp.le]
  constructor
  · have hup : ∀ᵐ omega ∂(physicalLaw M).toMeasure,
        (⨆ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ),
          aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega,x))
            (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) p) ≤
              a * ENNReal.ofReal (upperMomentConstant p * K omega ^ p) := by
      filter_upwards [hn, hs] with omega hnorm hsm
      apply iSup_le
      intro y
      apply iSup_le
      intro hy
      rw [← him0] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hrow]
      apply mul_le_mul_right
      have h := (continuous_tail_and_upper_moment (physicalSlice Y omega) hsm U
        Metric.isOpen_ball (Knn omega) (hKn omega) hnorm.1).2 p hp
      have hpw : (∫⁻ w, ContinuousPath.exitTime U w ^ p ∂Y (omega,x)) ≤
          ⨆ y ∈ U, ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂Y (omega,y) :=
        le_iSup_of_le x (le_iSup_of_le hx le_rfl)
      exact hpw.trans (by simpa only [hKcoe] using! h)
    calc
      _ ≤ ∫⁻ omega, a * ENNReal.ofReal (upperMomentConstant p * K omega ^ p)
          ∂(physicalLaw M).toMeasure := lintegral_mono_ae hup
      _ = a * (ENNReal.ofReal (upperMomentConstant p) *
          ∫⁻ omega, ENNReal.ofReal (K omega ^ p) ∂(physicalLaw M).toMeasure) := by
        simp_rw [ENNReal.ofReal_mul (upperMomentConstant_pos p hp).le]
        rw [lintegral_const_mul' a _ haf,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ a * (ENNReal.ofReal (upperMomentConstant p) * ENNReal.ofReal Cmoment) :=
        mul_le_mul_right (mul_le_mul_right hmoment _) _
      _ = _ := by
        rw [ha, ← ENNReal.ofReal_mul (upperMomentConstant_pos p hp).le,
          mul_comm, ← ENNReal.ofReal_mul' (Real.rpow_nonneg (by
            rw [aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime_eq]; exact hT.le) p)]
  · have hlo := averaged_lower_moment_of_mean_bank (physicalLaw M).toMeasure
      (fun omega => physicalSlice Y omega) U V Metric.isOpen_ball Knn hK.real_toNNReal
      hKn Cmean hCmean hmean c hc hs (by
        simpa only [physicalSlice, Kernel.comap_apply, hKcoe] using! hn) p hp
    calc
      _ = a * ENNReal.ofReal (meanBankLowerConstant c Cmean p) := by
        rw [ha, ENNReal.ofReal_mul' (Real.rpow_nonneg (by
          rw [aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime_eq]; exact hT.le) p), mul_comm]
      _ ≤ a * ∫⁻ omega, (⨅ x ∈ V, ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂Y (omega,x))
          ∂(physicalLaw M).toMeasure := mul_le_mul_right hlo _
      _ = ∫⁻ omega, a * (⨅ x ∈ V, ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂Y (omega,x))
          ∂(physicalLaw M).toMeasure := (lintegral_const_mul' a _ haf).symm
      _ ≤ _ := by
        apply lintegral_mono
        intro omega
        apply le_iInf
        intro y
        apply le_iInf
        intro hy
        rw [← him2] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [hrow]
        exact mul_le_mul_right (iInf_le_of_le x (iInf_le _ hx)) _

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_30

/- Inlined proved source application: SubdiffusiveProcess.Paper.PrelimitExitUpperBank. -/
noncomputable section aux_lim_cor_paths_inline_31

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalLocalTransport SubdiffusiveProcess.Section10.PhysicalAttachment
open SubdiffusiveProcess
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper
variable {d : ℕ}

/-- The actual E2 every-start implication, with its precise occupation-LSC input. -/
theorem aux_lim_cor_paths_inlined_prelimit_mean_le_price (hd : 2 ≤ d) {b A : Vec d → ℝ}
    {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    (hlocal : LocalDiffusion A b law) {B D K : ℝ} (hD : 0 < D) (hK : 1 ≤ K)
    (hs : PhysicalStaticBounds b A B K)
    (hSob : TorsionSobolevBound A b (Metric.ball (0 : Vec d) (1/2))
      (2 * (d : ℝ) / ((d : ℝ)-1)) (D*K^2))
    (hls : UnitDiscountOccupationLSC law (Metric.ball (0 : Vec d) (1/2))) :
    ∀ x ∈ Metric.ball (0 : Vec d) (1/2), meanExit law (Metric.ball 0 (1/2)) x ≤
      ENNReal.ofReal (aux_lim_cor_paths_inlined_prelimit_exit_price d D K) := by
  have hkn : 0 ≤ K := zero_le_one.trans hK
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hmass := aux_lim_cor_paths_inlined_prelimit_mass_le hd hK hs
  have hmassR : (weightedMeasure b (Metric.ball (0 : Vec d) (1/2))).toReal ≤ K :=
    ENNReal.toReal_le_of_le_ofReal hkn hmass
  have hbound := localDiffusion_meanExit_le hlocal
    (isOpenBoundedConvexDomain_ball 0 (by norm_num))
    ⟨0, Metric.mem_ball_self (by norm_num)⟩
    (coefficientOn_mono Metric.ball_subset_closedBall
      (hlocal.2.1 _ (isCompact_closedBall 0 (1/2))).2)
    (killedSobolevExponent_gt_two hd) (mul_pos hD (sq_pos_of_pos (zero_lt_one.trans_le hK)))
    hSob hls
  have hmasspow := Real.rpow_le_rpow ENNReal.toReal_nonneg hmassR
    (inv_nonneg.mpr hd0.le)
  rw [← one_div] at hmasspow
  have hcap : torsionConstant (2 * (d : ℝ) / ((d : ℝ)-1)) * (D*K^2) *
      (weightedMeasure b (Metric.ball (0 : Vec d) (1/2))).toReal ^ (1/(d : ℝ)) ≤
      aux_lim_cor_paths_inlined_prelimit_exit_price d D K := by
    calc
      _ ≤ torsionConstant (2 * (d : ℝ) / ((d : ℝ)-1)) * (D*K^2) * K^(1/(d : ℝ)) :=
        mul_le_mul_of_nonneg_left hmasspow
          (mul_nonneg (torsionConstant_pos _).le (mul_nonneg hD.le (sq_nonneg K)))
      _ = (torsionConstant (2 * (d : ℝ) / ((d : ℝ)-1)) * D) * K^(2+1/(d : ℝ)) := by
        rw [Real.rpow_add (zero_lt_one.trans_le hK), Real.rpow_two]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg hkn _)
  intro x hx
  have hxbound : meanExit law (Metric.ball 0 (1/2)) x ≤
      ENNReal.ofReal (torsionConstant (2 * (d : ℝ) / ((d : ℝ)-1)) * (D*K^2) *
        (weightedMeasure b (Metric.ball (0 : Vec d) (1/2))).toReal ^ (1/(d : ℝ))) := by
    simpa only [killedSobolev_one_sub_two_div hd] using! hbound x hx
  exact hxbound.trans (ENNReal.ofReal_le_ofReal hcap)

/-- Actual finite prelimit upper moment bank. The uniform static bank is applied
internally. Only the registered FOT leaf and actual countable occupation LSC
remain conditional; no mean-exit or moment conclusion is assumed. -/
theorem aux_lim_cor_paths_inlined_prelimit_local_upper_moment_bank
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (hd : 2 ≤ d) (hFOT : E7.FOTPartProcess) (p : ℝ) (hp : 0 < p) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ M : GMCModel d, M.delta ≤ delta →
      ∃ Cp : ℝ, 0 < Cp ∧ ∀ N k : ℕ, k ≤ N → ∀ x : Vec d,
        ∀ X : PhysicalKernel d, IsMarkovKernel X →
          aux_lim_cor_paths_inlined_physical_local_source_characterization M N X →
          (∀ᵐ omega ∂(physicalLaw M).toMeasure,
            UnitDiscountOccupationLSC
              ((physicalSlice (aux_lim_cor_paths_inlined_prelimit_localKernel M N (N-k) ((3 : ℝ)^N • x) X) omega).map
                LifetimePath.ofContinuousPath) (Metric.ball (0 : Vec d) (1/2))) →
          (∫⁻ omega, ∫⁻ w, ContinuousPath.exitTime (Metric.ball (0 : Vec d) (1/2)) w ^ p
            ∂aux_lim_cor_paths_inlined_prelimit_localKernel M N (N-k) ((3 : ℝ)^N • x) X (omega,0)
            ∂(physicalLaw M).toMeasure) ≤ ENNReal.ofReal Cp := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨B, D, _, hD, htor, hbank⟩ := aux_lim_cor_paths_inlined_prelimit_exit_price_bank hd
  obtain ⟨delta, hdelta, hmodels⟩ := hbank p hp
  refine ⟨delta, hdelta, ?_⟩
  intro M hM
  obtain ⟨Cbank, hCbank, hscales⟩ := hmodels M hM
  let F := ExitTailMoments.upperMomentConstant p
  have hF : 0 < F := ExitTailMoments.upperMomentConstant_pos p hp
  refine ⟨F*Cbank, mul_pos hF hCbank, ?_⟩
  intro N k hk x X hX hsource hls
  let := hX
  obtain ⟨K, _, hone, hmeas, hprice, hmom, hs⟩ := hscales N k hk x
  have hlocal := aux_lim_cor_paths_inlined_prelimit_localDiffusion hFOT M N (N-k) ((3 : ℝ)^N • x) X hsource
  calc
    _ ≤ ∫⁻ omega, ENNReal.ofReal F *
        ENNReal.ofReal (aux_lim_cor_paths_inlined_prelimit_exit_price d D (K omega)^p)
        ∂(physicalLaw M).toMeasure := by
      apply lintegral_mono_ae
      filter_upwards [hs, hlocal, hls] with omega hs hl hls
      let V := aux_lim_cor_paths_inlined_prelimit_localKernel M N (N-k) ((3 : ℝ)^N • x) X
      let : IsMarkovKernel (physicalSlice V omega) := by
        dsimp only [V, physicalSlice]; infer_instance
      let : IsMarkovKernel ((physicalSlice V omega).map LifetimePath.ofContinuousPath) :=
        Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
      let price : ℝ≥0 := ⟨aux_lim_cor_paths_inlined_prelimit_exit_price d D (K omega), zero_le_one.trans (hprice omega)⟩
      have ht := htor _ _ _ (hone omega) hs
        (localCoefficientOn M N (N-k) ((3 : ℝ)^N • x) omega Metric.isBounded_ball)
      have hmean := aux_lim_cor_paths_inlined_prelimit_mean_le_price hd hl hD (hone omega) hs ht hls
      have hmean' : ∀ y ∈ Metric.ball (0 : Vec d) (1/2),
          meanExit ((physicalSlice V omega).map LifetimePath.ofContinuousPath)
            (Metric.ball 0 (1/2)) y ≤ (price : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal (p := price)]
        exact hmean
      have hm := ExitTailMoments.lifetime_upper_moment
        ((physicalSlice V omega).map LifetimePath.ofContinuousPath) hl.1
        (Metric.ball 0 (1/2)) Metric.isOpen_ball price (hprice omega) hmean' p hp 0
      change (∫⁻ w, LifetimePath.exitTime _ w ^ p ∂_) ≤ _ at hm
      rw [ExitTailMoments.continuous_exitMoment_transport _ _ Metric.isOpen_ball] at hm
      change (∫⁻ w, ContinuousPath.exitTime _ w ^ p ∂V (omega,0)) ≤
        ENNReal.ofReal (F * aux_lim_cor_paths_inlined_prelimit_exit_price d D (K omega)^p) at hm
      rwa [ENNReal.ofReal_mul hF.le] at hm
    _ = ENNReal.ofReal F *
        ∫⁻ omega, ENNReal.ofReal (aux_lim_cor_paths_inlined_prelimit_exit_price d D (K omega)^p)
          ∂(physicalLaw M).toMeasure :=
      lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hmeas.pow_const p))
    _ ≤ ENNReal.ofReal F * ENNReal.ofReal Cbank := mul_le_mul_right hmom _
    _ = _ := (ENNReal.ofReal_mul hF.le).symm

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_31

/- Inlined proved source application: SubdiffusiveProcess.Paper.PrelimitExitAnnealed. -/
noncomputable section aux_lim_cor_paths_inline_32

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalLocalTransport SubdiffusiveProcess.Section10.PhysicalAttachment
open SubdiffusiveProcess.Section10.PrelimitExitPaths SubdiffusiveProcess
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Paper
variable {d : ℕ}

/-- The actual joint law at the deterministic translated start, with the global
raw-clock path map. This is a probability kernel, including exceptional fibres. -/
def aux_lim_cor_paths_inlined_prelimit_rowKernel (M : GMCModel d) (N : ℕ) (x : Vec d) (X : PhysicalKernel d) :
    Kernel (AnchoredC11Sample d) (DiffusionPath d) :=
  (X.comap (fun omega => (omega, (3 : ℝ)^N • x))
    (measurable_id.prodMk measurable_const)).map (prelimitPath M N)

instance aux_lim_cor_paths_inlined_prelimit_rowKernel_markov (M : GMCModel d) (N : ℕ) (x : Vec d)
    (X : PhysicalKernel d) [IsMarkovKernel X] :
    IsMarkovKernel (aux_lim_cor_paths_inlined_prelimit_rowKernel M N x X) :=
  Kernel.IsMarkovKernel.map _ (ContinuousPath.measurable_rescale _ _)

def aux_lim_cor_paths_inlined_annealedPrelimit (M : GMCModel d) (X : ℕ → PhysicalKernel d)
    (hX : ∀ N, IsMarkovKernel (X N)) (x : ℕ → Vec d) (N : ℕ) :
    ProbabilityMeasure (DiffusionPath d) := by
  letI := hX N
  exact ⟨aux_lim_cor_paths_inlined_prelimit_rowKernel M N (x N) (X N) ∘ₘ (physicalLaw M).toMeasure, inferInstance⟩

/-- Literal centered exit moments of the global path equal the powered raw
clock ratio times local unit-cube moments. Starting at local zero is proved
from the actual StrongMarkov characterization, not imposed on each path. -/
theorem aux_lim_cor_paths_inlined_prelimit_powered_exit_conversion
    (M : GMCModel d) {N k : ℕ} (hk : k ≤ N) (x : Vec d)
    (X : PhysicalKernel d) [IsMarkovKernel X] (p : ℝ) (hp : 0 < p)
    (hlocal : ∀ᵐ omega ∂(physicalLaw M).toMeasure,
      LocalDiffusion
        (localCoefficient M N (N-k) ((3 : ℝ)^N • x) omega)
        (localSpeed M N (N-k) ((3 : ℝ)^N • x) omega)
        ((physicalSlice (aux_lim_cor_paths_inlined_prelimit_localKernel M N (N-k) ((3 : ℝ)^N • x) X) omega).map
          LifetimePath.ofContinuousPath)) :
    (∫⁻ w, EndpointPaths.smallExit k w ^ p
      ∂(aux_lim_cor_paths_inlined_prelimit_rowKernel M N x X ∘ₘ (physicalLaw M).toMeasure)) =
      (((rawClock M N (N-k) / rawClock M N N : ℝ≥0) : ℝ≥0∞)^p) *
        ∫⁻ omega, ∫⁻ w, ContinuousPath.exitTime (Metric.ball (0 : Vec d) (1/2)) w ^ p
          ∂aux_lim_cor_paths_inlined_prelimit_localKernel M N (N-k) ((3 : ℝ)^N • x) X (omega,0)
          ∂(physicalLaw M).toMeasure := by
  let z : Vec d := (3 : ℝ)^N • x
  let Y := aux_lim_cor_paths_inlined_prelimit_localKernel M N (N-k) z X
  let rho : ℝ≥0 := rawClock M N (N-k) / rawClock M N N
  let f := fun w : DiffusionPath d => EndpointPaths.smallExit k w ^ p
  have hf : Measurable f := (ExitMomentPassage.smallExit_rpow_lsc k p hp).measurable
  have hu : Measurable (fun w : DiffusionPath d =>
      ContinuousPath.exitTime (Metric.ball (0 : Vec d) (1/2)) w ^ p) :=
    (ENNReal.continuous_rpow_const (y := p)).measurable.comp
      (ContinuousPath.isStoppingTime_exitTime _ Metric.isOpen_ball).measurable'
  change (∫⁻ w, f w ∂(physicalLaw M).toMeasure.bind (aux_lim_cor_paths_inlined_prelimit_rowKernel M N x X)) = _
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,
    ← lintegral_const_mul _ (by
      exact (hu.lintegral_kernel (κ := Y)).comp
        (measurable_id.prodMk measurable_const))]
  apply lintegral_congr_ae
  filter_upwards [hlocal] with omega hl
  have hstart := hl.1.2.1 0
  rw [Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath] at hstart
  have hstart' := ae_of_ae_map LifetimePath.measurable_ofContinuousPath.aemeasurable hstart
  have hyzero : ∀ᵐ v ∂Y (omega,0), v 0 = 0 := by
    filter_upwards [hstart'] with v hv
    exact Sum.inl.inj (by simpa only [LifetimePath.coordinate_ofContinuousPath] using hv)
  rw [aux_lim_cor_paths_inlined_prelimit_localKernel_apply] at hyzero
  simp only [physicalCoordinates_apply, smul_zero, add_zero] at hyzero
  have hwzero := ae_of_ae_map (ContinuousPath.measurable_rescale _ _).aemeasurable hyzero
  rw [aux_lim_cor_paths_inlined_prelimit_rowKernel, Kernel.map_apply _ (show Measurable (prelimitPath M N) from
      ContinuousPath.measurable_rescale _ _),
    Kernel.comap_apply, lintegral_map hf (show Measurable (prelimitPath M N) from
      ContinuousPath.measurable_rescale _ _)]
  change (∫⁻ w, f (prelimitPath M N w) ∂X (omega,z)) =
    (rho : ℝ≥0∞)^p * ∫⁻ w, ContinuousPath.exitTime (Metric.ball (0 : Vec d) (1/2)) w ^ p
      ∂Y (omega,0)
  rw [show Y (omega,0) = (X (omega,z)).map
      (ContinuousPath.rescale (physicalCoordinates (N-k) z).symm (rawClock M N (N-k))) by
        rw [aux_lim_cor_paths_inlined_prelimit_localKernel_apply, physicalCoordinates_apply, smul_zero, add_zero],
    lintegral_map hu (ContinuousPath.measurable_rescale _ _)]
  have hg : Measurable (fun w : DiffusionPath d =>
      ContinuousPath.exitTime (Metric.ball (0 : Vec d) (1/2))
        (ContinuousPath.rescale (physicalCoordinates (N-k) z).symm (rawClock M N (N-k)) w)^p) :=
    hu.comp (ContinuousPath.measurable_rescale _ _)
  rw [← lintegral_const_mul (μ := X (omega,z)) ((rho : ℝ≥0∞)^p) hg]
  apply lintegral_congr_ae
  filter_upwards [hwzero] with w hw
  dsimp only [z] at hw
  dsimp only [f]
  rw [smallExit_prelimit M hk x w, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp only [EndpointPaths.smallExit, hw, Nat.cast_zero, neg_zero, zpow_zero]
  rfl

/-- From the internally proved finite local moment bank to the actual annealed
prelimit exit decay, for any one already fixed strict-decay rate. -/
theorem aux_lim_cor_paths_inlined_prelimit_annealed_exit_bank
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (hd : 2 ≤ d) (hFOT : E7.FOTPartProcess) (p : ℝ) (hp : 0 < p) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ M : GMCModel d, M.delta ≤ delta →
      ∀ C eta : ℝ, 0 < C →
        (∀ l m : ℕ, l ≤ m → SubdiffusiveProcess.CoarseGrainingVocab.ahom M m / SubdiffusiveProcess.CoarseGrainingVocab.ahom M l ≤
          C * (3 : ℝ)^(-(eta*((m : ℝ)-(l : ℝ))))) →
        ∃ Cp : ℝ, 0 < Cp ∧ ∀ (X : ℕ → PhysicalKernel d)
          (hX : ∀ N, IsMarkovKernel (X N)) (x : ℕ → Vec d),
          (∀ N : ℕ, aux_lim_cor_paths_inlined_physical_local_source_characterization M N (X N)) →
          (∀ N k : ℕ, k ≤ N → ∀ᵐ omega ∂(physicalLaw M).toMeasure,
            UnitDiscountOccupationLSC
              ((physicalSlice (aux_lim_cor_paths_inlined_prelimit_localKernel M N (N-k) ((3 : ℝ)^N • x N) (X N)) omega).map
                LifetimePath.ofContinuousPath) (Metric.ball (0 : Vec d) (1/2))) →
          ∀ k N : ℕ, k ≤ N →
            (∫⁻ w, EndpointPaths.smallExit k w ^ p
              ∂(aux_lim_cor_paths_inlined_annealedPrelimit M X hX x N : Measure (DiffusionPath d))) ≤
              ENNReal.ofReal (Cp * (3 : ℝ)^(-(p*(2+eta)*(k : ℝ)))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨delta, hdelta, hmodels⟩ := aux_lim_cor_paths_inlined_prelimit_local_upper_moment_bank hd hFOT p hp
  refine ⟨delta, hdelta, ?_⟩
  intro M hM
  obtain ⟨Cbank, hCbank, hbank⟩ := hmodels M hM
  intro C eta hC hdec
  refine ⟨C^p * Cbank, mul_pos (Real.rpow_pos_of_pos hC p) hCbank, ?_⟩
  intro X hX x hsource hls k N hk
  let := hX N
  have hlocal := aux_lim_cor_paths_inlined_prelimit_localDiffusion hFOT M N (N-k) ((3 : ℝ)^N • x N) (X N) (hsource N)
  have hmoment := hbank N k hk (x N) (X N) (hX N) (hsource N) (hls N k hk)
  change (∫⁻ w, EndpointPaths.smallExit k w ^ p
    ∂(aux_lim_cor_paths_inlined_prelimit_rowKernel M N (x N) (X N) ∘ₘ (physicalLaw M).toMeasure)) ≤ _
  rw [aux_lim_cor_paths_inlined_prelimit_powered_exit_conversion M hk (x N) (X N) p hp hlocal]
  have hclock := PrelimitExitClock.rawClock_ratio_le M hdec hk
  have hclockp := Real.rpow_le_rpow (by positivity) hclock hp.le
  have hrho : ENNReal.ofReal
      ((rawClock M N (N-k) : ℝ) / (rawClock M N N : ℝ)) =
      ((rawClock M N (N-k) / rawClock M N N : ℝ≥0) : ℝ≥0∞) := by
    rw [← NNReal.coe_div]
    exact ENNReal.ofReal_coe_nnreal
  calc
    _ ≤ ENNReal.ofReal (((rawClock M N (N-k) : ℝ) / (rawClock M N N : ℝ))^p) *
        ENNReal.ofReal Cbank := by
      rw [← hrho, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le]
      exact mul_le_mul_right hmoment _
    _ ≤ ENNReal.ofReal ((C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))^p) * ENNReal.ofReal Cbank :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal hclockp) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity),
        Real.mul_rpow hC.le (Real.rpow_nonneg (by norm_num) _),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      rw [show -((2+eta)*(k : ℝ))*p = -(p*(2+eta)*(k : ℝ)) by ring]
      ring

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_32

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorExitMomentsWeak. -/
noncomputable section aux_lim_cor_paths_inline_33

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalAttachment SubdiffusiveProcess.Section10.PrelimitExitPaths
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Paper

/-- The actual annealed sequence from the frozen weak-limit definition, for
either cutoff family and the supplied subsequence and deterministic starts. -/
def aux_lim_cor_paths_inlined_lim_cor_exit_moments_annealedSequence {d : ℕ}
    (M : GMCModel d) (X : WithTop ℕ → PhysicalKernel d) (hX : ∀ L, IsMarkovKernel (X L))
    (untruncated : Bool) (phi : ℕ → ℕ) (xs : ℕ → SpatialCoordinates d) (n : ℕ) :
    ProbabilityMeasure (DiffusionPath d) := by
  letI := hX (aux_lim_cor_paths_inlined_lim_cor_exit_moments_familyCutoff untruncated (phi n))
  exact ⟨aux_lim_cor_paths_inlined_prelimit_rowKernel M (phi n) (xs n)
    (X (aux_lim_cor_paths_inlined_lim_cor_exit_moments_familyCutoff untruncated (phi n))) ∘ₘ
      (physicalLaw M).toMeasure, inferInstance⟩

/-- Unpack the actual kernel/environment integrals in the specified annealed
limit definition. No process characterization or convergence theorem is assumed. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_annealedSequence_integral {d : ℕ}
    (M : GMCModel d) (X : WithTop ℕ → PhysicalKernel d) (hX : ∀ L, IsMarkovKernel (X L))
    (untruncated : Bool) (phi : ℕ → ℕ) (xs : ℕ → SpatialCoordinates d) (n : ℕ)
    (G : BoundedContinuousFunction (DiffusionPath d) ℝ) :
    (∫ w, G w ∂(aux_lim_cor_paths_inlined_lim_cor_exit_moments_annealedSequence M X hX untruncated phi xs n :
      Measure (DiffusionPath d))) =
        ∫ omega, ∫ w, G (aux_lim_cor_paths_inlined_lim_cor_exit_moments_rescale M (phi n) w)
          ∂X (aux_lim_cor_paths_inlined_lim_cor_exit_moments_familyCutoff untruncated (phi n))
            (omega,(3 : ℝ)^(phi n) • xs n)
          ∂(aux_lim_cor_paths_inlined_lim_cor_exit_moments_physicalLaw M).toMeasure := by
  let L := aux_lim_cor_paths_inlined_lim_cor_exit_moments_familyCutoff untruncated (phi n)
  let := hX L
  let row := aux_lim_cor_paths_inlined_prelimit_rowKernel M (phi n) (xs n) (X L)
  change (∫ w, G w ∂(row ∘ₘ (physicalLaw M).toMeasure)) = _
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (G.integrable _),
    Kernel.const_apply]
  apply integral_congr_ae
  apply ae_of_all
  intro omega
  change (∫ w, G w ∂aux_lim_cor_paths_inlined_prelimit_rowKernel M (phi n) (xs n) (X L) omega) = _
  rw [aux_lim_cor_paths_inlined_prelimit_rowKernel, Kernel.map_apply _ (show Measurable (prelimitPath M (phi n)) from
    ContinuousPath.measurable_rescale _ _), Kernel.comap_apply,
    integral_map (show Measurable (prelimitPath M (phi n)) from
      ContinuousPath.measurable_rescale _ _).aemeasurable G.continuous.measurable.aestronglyMeasurable,
    aux_lim_cor_paths_inlined_lim_cor_exit_moments_rescale_eq]

/-- The frozen test-function definition implies ordinary weak convergence of
these very probability laws, ready for the existing powered Portmanteau step. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_annealedSequence_tendsto {d : ℕ}
    (M : GMCModel d) (X : WithTop ℕ → PhysicalKernel d) (hX : ∀ L, IsMarkovKernel (X L))
    (untruncated : Bool) (phi : ℕ → ℕ) (xs : ℕ → SpatialCoordinates d)
    (P : ProbabilityMeasure (DiffusionPath d))
    (hlimit : aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsAnnealedLimit M X untruncated phi xs P) :
    Tendsto (aux_lim_cor_paths_inlined_lim_cor_exit_moments_annealedSequence M X hX untruncated phi xs)
      atTop (𝓝 P) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro G
  simpa only [aux_lim_cor_paths_inlined_lim_cor_exit_moments_annealedSequence_integral] using hlimit G

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_33

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorExitMomentsPrelimit. -/
noncomputable section aux_lim_cor_paths_inline_34

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalAttachment SubdiffusiveProcess.Section10.PhysicalLocalTransport
open SubdiffusiveProcess.Section10.PrelimitExitPaths SubdiffusiveProcess.Section10.ExitMomentPassage
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper

/-- Every supplied physical row starts at its prescribed point, on the same
full-measure family event. This uses the proved Feller restart, without FOT. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_physical_starts {d : ℕ}
    (M : GMCModel d) (X : WithTop ℕ → PhysicalKernel d) (hX : ∀ L, IsMarkovKernel (X L))
    (hfamily : aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsPhysicalFamily M X) (L : WithTop ℕ) :
    ∀ᵐ omega ∂(physicalLaw M).toMeasure,
      ∀ x : SpatialCoordinates d, ∀ᵐ w ∂X L (omega,x), w 0 = x := by
  let := hX L
  filter_upwards [aux_lim_cor_paths_inlined_lim_cor_exit_moments_row_characterization M X hfamily L] with omega h
  obtain ⟨D, hdense, _hweak, hcons, hfdd⟩ := h
  let Y := physicalSlice (X L) omega
  let : IsMarkovKernel Y := by dsimp only [Y, physicalSlice]; infer_instance
  have hF : ∀ I x, Y.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    exact hfdd I x
  have hr := fellerRestart d _ hcons (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense)
    Y inferInstance hF
  intro x
  have hs := hr.2.1 x
  rw [Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath] at hs
  have hs' := ae_of_ae_map LifetimePath.measurable_ofContinuousPath.aemeasurable hs
  filter_upwards [hs'] with w hw
  exact Sum.inl.inj (by simpa only [LifetimePath.coordinate_ofContinuousPath] using hw)

/-- Literal exit conversion into the actual physical cube at scale N-k. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_smallExit_physical {d : ℕ}
    (M : GMCModel d) {N k : ℕ} (hk : k ≤ N) (z : SpatialCoordinates d)
    (w : DiffusionPath d) (hstart : w 0 = z) :
    EndpointPaths.smallExit k (prelimitPath M N w) =
      (rawClock M N N : ℝ≥0∞)⁻¹ *
        ContinuousPath.exitTime (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z ((N-k : ℕ) : ℤ)) w := by
  have hrad : ((3 : ℝ)^(-(k : ℤ))/2)*(3 : ℝ)^N = (3 : ℝ)^(N-k)/2 := by
    rw [zpow_neg, zpow_natCast, pow_sub₀ (3 : ℝ) (by norm_num) hk]
    ring
  simp only [EndpointPaths.smallExit, prelimitPath,
    centered_exit_affine _ _ _ (rawClock_pos M N N), hstart, hrad,
    aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube, zpow_natCast]

/-- For either source family the active local scale is N-k, including k=N. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_prelimit_localTime {d : ℕ}
    (M : GMCModel d) (untruncated : Bool) (N k : ℕ) :
    aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M
      (aux_lim_cor_paths_inlined_lim_cor_exit_moments_familyCutoff untruncated N) (N-k) =
        (rawClock M N (N-k) : ℝ) := by
  rw [aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime_eq]
  cases untruncated
  · rfl
  · change (rawClock M ⊤ (N-k) : ℝ) = (rawClock M N (N-k) : ℝ)
    simp only [rawClock, activeScale, WithTop.untopD_top,
      Nat.cast_withTop, WithTop.untopD_coe, min_self, min_eq_left (Nat.sub_le N k)]

/-- The supplied physical all-scale powered bank bounds the same annealed
prelimit law, for both finite and top cutoffs. The bank is the mean/semigroup
producer boundary; this theorem introduces no moment premise at a source root. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_prelimit_bound {d : ℕ}
    (M : GMCModel d) (X : WithTop ℕ → PhysicalKernel d) (hX : ∀ L, IsMarkovKernel (X L))
    (hfamily : aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsPhysicalFamily M X)
    (Cbank C eta p : ℝ) (hCbank : 0 < Cbank) (hp : 0 < p)
    (hdec : ∀ l m : ℕ, l ≤ m → ahom M m / ahom M l ≤
      C * (3 : ℝ)^(-(eta*((m : ℝ)-(l : ℝ)))))
    (hbank : ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
      (∫⁻ omega, (⨆ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ),
        aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega,x))
          (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) p)
        ∂(physicalLaw M).toMeasure) ≤
          ENNReal.ofReal (Cbank * aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m ^ p))
    (untruncated : Bool) (phi : ℕ → ℕ) (xs : ℕ → SpatialCoordinates d)
    (k n : ℕ) (hk : k ≤ phi n) :
    (∫⁻ w, aux_lim_cor_paths_inlined_lim_cor_exit_moments_smallExit k w ^ p
      ∂(aux_lim_cor_paths_inlined_lim_cor_exit_moments_annealedSequence M X hX untruncated phi xs n :
        Measure (DiffusionPath d))) ≤
          ENNReal.ofReal ((C^p*Cbank) * (3 : ℝ)^(-(p*(2+eta)*(k : ℝ)))) := by
  let N := phi n
  let L := aux_lim_cor_paths_inlined_lim_cor_exit_moments_familyCutoff untruncated N
  let z := (3 : ℝ)^N • xs n
  let U := aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z ((N-k : ℕ) : ℤ)
  let c := rawClock M N N
  let := hX L
  have hf : Measurable (fun w : DiffusionPath d => EndpointPaths.smallExit k w ^ p) :=
    (smallExit_rpow_lsc k p hp).measurable
  have hu : Measurable (fun w : DiffusionPath d => ContinuousPath.exitTime U w ^ p) :=
    (ENNReal.continuous_rpow_const (y := p)).measurable.comp
      (ContinuousPath.isStoppingTime_exitTime U Metric.isOpen_ball).measurable'
  have hr : (∫⁻ w, aux_lim_cor_paths_inlined_lim_cor_exit_moments_smallExit k w ^ p
      ∂(aux_lim_cor_paths_inlined_lim_cor_exit_moments_annealedSequence M X hX untruncated phi xs n :
        Measure (DiffusionPath d))) ≤
        ((c : ℝ≥0∞)^p)⁻¹ * ENNReal.ofReal
          (Cbank * (rawClock M N (N-k) : ℝ)^p) := by
    change (∫⁻ w, EndpointPaths.smallExit k w ^ p
      ∂(physicalLaw M).toMeasure.bind (aux_lim_cor_paths_inlined_prelimit_rowKernel M N (xs n) (X L))) ≤ _
    rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
    calc
      _ = ((c : ℝ≥0∞)^p)⁻¹ *
          ∫⁻ omega, ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂X L (omega,z)
            ∂(physicalLaw M).toMeasure := by
        have hmeas : Measurable (fun omega : AnchoredC11Sample d =>
            ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂X L (omega,z)) :=
          (hu.lintegral_kernel (κ := X L)).comp (measurable_id.prodMk measurable_const)
        rw [← lintegral_const_mul _ hmeas]
        apply lintegral_congr_ae
        filter_upwards [aux_lim_cor_paths_inlined_lim_cor_exit_moments_physical_starts M X hX hfamily L] with omega hs
        rw [aux_lim_cor_paths_inlined_prelimit_rowKernel, Kernel.map_apply _ (show Measurable (prelimitPath M N) from
          ContinuousPath.measurable_rescale _ _), Kernel.comap_apply,
          lintegral_map hf (show Measurable (prelimitPath M N) from
            ContinuousPath.measurable_rescale _ _), ← lintegral_const_mul _ hu]
        apply lintegral_congr_ae
        filter_upwards [hs z] with w hw
        rw [aux_lim_cor_paths_inlined_lim_cor_exit_moments_smallExit_physical M hk z w hw,
          ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.inv_rpow]
      _ ≤ ((c : ℝ≥0∞)^p)⁻¹ * ENNReal.ofReal
          (Cbank * aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L (N-k)^p) := by
        apply mul_le_mul_right
        apply le_trans _ (hbank L (N-k) z)
        apply lintegral_mono
        intro omega
        exact le_iSup_of_le z (le_iSup_of_le (Metric.mem_ball_self (by positivity)) le_rfl)
      _ = _ := by rw [aux_lim_cor_paths_inlined_lim_cor_exit_moments_prelimit_localTime]
  have hclock := PrelimitExitClock.rawClock_ratio_le M hdec hk
  have hc : 0 < (c : ℝ) := rawClock_pos M N N
  have hcp : 0 < (c : ℝ)^p := Real.rpow_pos_of_pos hc p
  have hscalar := Real.rpow_le_rpow (by positivity) hclock hp.le
  have hC : 0 ≤ C := by
    have h := hdec 0 0 le_rfl
    have h1 : 1 ≤ C := by simpa [div_self (ahom_pos M 0).ne'] using h
    exact zero_le_one.trans h1
  apply hr.trans
  have hcoe : (c : ℝ≥0∞)^p = ENNReal.ofReal ((c : ℝ)^p) := by
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg hc.le hp.le]
  rw [hcoe, mul_comm, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos hcp]
  apply ENNReal.ofReal_le_ofReal
  rw [show Cbank * (rawClock M N (N-k) : ℝ)^p / (c : ℝ)^p =
    Cbank * ((rawClock M N (N-k) : ℝ)/(c : ℝ))^p by
      rw [Real.div_rpow (by positivity) hc.le]; ring]
  calc
    _ ≤ Cbank * (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))^p :=
      mul_le_mul_of_nonneg_left hscalar hCbank.le
    _ = _ := by
      rw [Real.mul_rpow hC (Real.rpow_nonneg (by norm_num) _),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        show -((2+eta)*(k : ℝ))*p = -(p*(2+eta)*(k : ℝ)) by ring]
      ring

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_34

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorExitMomentsConsequences. -/
noncomputable section aux_lim_cor_paths_inline_35

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalAttachment
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper

/-- One enlargement of the moment coefficient covers both the powered exit
bound and the paper's small-displacement bound. It precedes k and the law. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_displacementConstant_ge (C p eta : ℝ)
    (hp : 0 < p) (heta : 0 < eta) : C ≤ SmallDisplacement.displacementConstant C p eta := by
  have hA : 0 ≤ p*(2+eta) := mul_nonneg hp.le (by linarith)
  have hpow : 1 ≤ (12 : ℝ)^(p*(2+eta)) := Real.one_le_rpow (by norm_num) hA
  exact (le_max_right 1 C).trans
    (le_mul_of_one_le_right (le_trans (by norm_num) (le_max_left 1 C)) hpow)

/-- Full literal limiting-exit/displacement application for both physical
families. The producer boundary is the powered prelimit bound for the actual
annealedSequence; the specified weak-limit definition is discharged here. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_limit_consequences {d : ℕ}
    (C p eta : ℝ) (hp : 0 < p) (heta : 0 < eta) :
    ∃ Cp : ℝ, 0 < Cp ∧ C ≤ Cp ∧
      ∀ q : ℝ, 0 < q → q < p*(2+eta) → ∃ Cpq : ℝ, 0 < Cpq ∧
        ∀ (M : GMCModel d) (X : WithTop ℕ → PhysicalKernel d)
          (hX : ∀ L, IsMarkovKernel (X L)) (untruncated : Bool) (phi : ℕ → ℕ),
          StrictMono phi → ∀ (xs : ℕ → SpatialCoordinates d)
            (P : ProbabilityMeasure (DiffusionPath d)),
          aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsAnnealedLimit M X untruncated phi xs P →
          (∀ k n : ℕ, k ≤ phi n →
            (∫⁻ w, aux_lim_cor_paths_inlined_lim_cor_exit_moments_smallExit k w ^ p
              ∂(aux_lim_cor_paths_inlined_lim_cor_exit_moments_annealedSequence M X hX untruncated phi xs n :
                Measure (DiffusionPath d))) ≤
                  ENNReal.ofReal (C * (3 : ℝ)^(-(p*(2+eta)*(k : ℝ))))) →
          (∀ k : ℕ, (∫⁻ w, aux_lim_cor_paths_inlined_lim_cor_exit_moments_smallExit k w ^ p
            ∂(P : Measure (DiffusionPath d))) ≤
              ENNReal.ofReal (Cp * (3 : ℝ)^(-(p*(2+eta)*(k : ℝ))))) ∧
          (∀ t epsilon : ℝ≥0, 0 < t → t ≤ 1 → 0 < epsilon → epsilon ≤ 1 →
            (P : Measure (DiffusionPath d))
              {w | aux_lim_cor_paths_inlined_lim_cor_exit_moments_maximum t w ≤
                (epsilon : ℝ)*(t : ℝ)^(1/(2+eta))} ≤
                  ENNReal.ofReal (Cp * (epsilon : ℝ)^(p*(2+eta)))) ∧
          (∀ t : ℝ≥0, 0 < t → t ≤ 1 →
            (∫⁻ w, ENNReal.ofReal (aux_lim_cor_paths_inlined_lim_cor_exit_moments_maximum t w)^(-q)
              ∂(P : Measure (DiffusionPath d))) ≤
                ENNReal.ofReal (Cpq * (t : ℝ)^(-q/(2+eta)))) := by
  let Cp := SmallDisplacement.displacementConstant C p eta
  have hCp : 0 < Cp := SmallDisplacement.displacementConstant_pos C p eta
  have hge : C ≤ Cp := aux_lim_cor_paths_inlined_lim_cor_exit_moments_displacementConstant_ge C p eta hp heta
  refine ⟨Cp, hCp, hge, ?_⟩
  intro q hq hqA
  refine ⟨SmallDisplacement.negativeMomentConstant Cp (p*(2+eta)) q,
    SmallDisplacement.negativeMomentConstant_pos Cp (p*(2+eta)) q hCp.le hqA, ?_⟩
  intro M X hX untruncated phi hphi xs P hlimit hpre
  have hconv := aux_lim_cor_paths_inlined_lim_cor_exit_moments_annealedSequence_tendsto
    M X hX untruncated phi xs P hlimit
  have hm : ∀ k : ℕ, (∫⁻ w, EndpointPaths.smallExit k w ^ p
      ∂(P : Measure (DiffusionPath d))) ≤
        ENNReal.ofReal (C * (3 : ℝ)^(-(p*(2+eta)*(k : ℝ)))) := by
    apply ExitMomentPassage.smallExit_moment_decay_of_prelimit P
      (aux_lim_cor_paths_inlined_lim_cor_exit_moments_annealedSequence M X hX untruncated phi xs) hconv C eta p hp
    intro k
    exact eventually_atTop.mpr ⟨k, fun n hn => hpre k n (hn.trans (hphi.id_le n))⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact (hm k).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hge (Real.rpow_nonneg (by norm_num) _)))
  · intro t epsilon ht ht1 he he1
    exact SmallDisplacement.scaled_small_displacement (P : Measure (DiffusionPath d))
      C p eta hp heta hm t ht ht1 epsilon (by exact_mod_cast he) (by exact_mod_cast he1)
  · intro t ht ht1
    exact SmallDisplacement.maximal_negative_moment_of_exit_moments
      (P : Measure (DiffusionPath d)) C p eta hp heta hm q hq hqA t ht ht1

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_35

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorExitMomentsAssembly. -/
noncomputable section aux_lim_cor_paths_inline_36

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.PhysicalAttachment
open SubdiffusiveProcess.Section10.ExitTailMoments SubdiffusiveProcess.Section10.ExitLowerMoments
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper

/-- Complete internal assembly of the faithful exit-moments conclusion.
The explicit random first-mean supplier is the sole remaining producer input;
strict decay, restart, FOT, all-p passage and weak-limit conversion are proved. -/
theorem aux_lim_cor_paths_inlined_lim_cor_exit_moments_of_random_mean_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (hbank : aux_lim_cor_paths_inlined_lim_cor_exit_moments_RandomMeanBank d) :
    aux_lim_cor_paths_inlined_lim_cor_exit_moments_Conclusion d := by
  obtain ⟨c, hc, horders⟩ := hbank
  obtain ⟨deltaBase, hdeltaBase, eta, Cdecay, hrates⟩ := aux_lim_cor_paths_inlined_lim_cor_exit_moments_strict_rate hd
  refine ⟨deltaBase, hdeltaBase, eta, Cdecay, hrates, ?_⟩
  intro p hp
  let Q : ℝ := max 1 p
  obtain ⟨deltaq, hdeltaq, hmodels⟩ := horders Q
  refine ⟨min deltaq deltaBase, lt_min hdeltaq hdeltaBase, min_le_right _ _, ?_⟩
  intro M hM
  obtain ⟨Cq, hCq, hrows⟩ := hmodels M (hM.trans (min_le_left _ _))
  obtain ⟨heta, hCdecay, _hplanar, hdec⟩ := hrates M (hM.trans (min_le_right _ _))
  have hdec' : ∀ l m : ℕ, l ≤ m → ahom M m / ahom M l ≤
      Cdecay M * (3 : ℝ)^(-(eta M*((m : ℝ)-(l : ℝ)))) := by
    simpa only [neg_mul] using hdec
  let Cmean : ℝ≥0 := Real.toNNReal (max 1 Cq)
  have hCmean : 1 ≤ Cmean := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (le_trans (by norm_num) (le_max_left 1 Cq))]
    exact le_max_left _ _
  let cp := meanBankLowerConstant c Cmean p
  let Cphysical := upperMomentConstant p * Cq
  have hcp : 0 < cp := meanBankLowerConstant_pos c Cmean p hc hCmean
  have hCphysical : 0 < Cphysical := mul_pos (upperMomentConstant_pos p hp) hCq
  have hphysical : ∀ (X : WithTop ℕ → PhysicalKernel d) (hX : ∀ L, IsMarkovKernel (X L)),
      aux_lim_cor_paths_inlined_lim_cor_exit_moments_IsPhysicalFamily M X →
      ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
        (∫⁻ omega, (⨆ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ),
          aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega,x))
            (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) p) ∂(physicalLaw M).toMeasure) ≤
          ENNReal.ofReal (Cphysical * aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m ^ p) ∧
        ENNReal.ofReal (cp * aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime M L m ^ p) ≤
          ∫⁻ omega, (⨅ x ∈ aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z ((m : ℤ)-2),
            aux_lim_cor_paths_inlined_lim_cor_exit_moments_exitMoment (X L (omega,x))
              (aux_lim_cor_paths_inlined_lim_cor_exit_moments_cube z (m : ℤ)) p) ∂(physicalLaw M).toMeasure := by
    intro X hX hf L m z
    obtain ⟨K, hK, hKone, hKmom, hraw⟩ := hrows X hX hf L m z
    have hfirst : (∫⁻ omega, ENNReal.ofReal (K omega) ∂(physicalLaw M).toMeasure) ≤ Cmean := by
      calc
        _ ≤ ∫⁻ omega, ENNReal.ofReal (K omega ^ Q) ∂(physicalLaw M).toMeasure := by
          apply lintegral_mono
          intro omega
          apply ENNReal.ofReal_le_ofReal
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le (hKone omega) (le_max_left 1 p)
        _ ≤ ENNReal.ofReal Cq := hKmom
        _ ≤ Cmean := ENNReal.ofReal_le_ofReal (le_max_right _ _)
    have hpmom : (∫⁻ omega, ENNReal.ofReal (K omega ^ p) ∂(physicalLaw M).toMeasure) ≤
        ENNReal.ofReal Cq := by
      apply le_trans _ hKmom
      apply lintegral_mono
      intro omega
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_le (hKone omega) (le_max_right 1 p))
    exact aux_lim_cor_paths_inlined_lim_cor_exit_moments_physical_moments_of_mean_bank hd M X hX hf L m z
      K hK hKone Cmean hCmean hfirst c Cq p hc hp hpmom hraw
  let Climit := Cdecay M ^ p * Cphysical
  obtain ⟨D, hD, _hClimitD, hlimits⟩ :=
    aux_lim_cor_paths_inlined_lim_cor_exit_moments_limit_consequences (d := d) Climit p (eta M) hp heta
  let Cp := max cp (max Cphysical D)
  have hcpCp : cp ≤ Cp := le_max_left _ _
  have hphysCp : Cphysical ≤ Cp := (le_max_left _ _).trans (le_max_right _ _)
  have hDCp : D ≤ Cp := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨cp, Cp, hcp, hcpCp, ?_⟩
  intro q hq hqA
  obtain ⟨Cpq, hCpq, hlimit⟩ := hlimits q hq hqA
  refine ⟨Cpq, hCpq, ?_⟩
  intro X hX hf
  constructor
  · intro L m z
    have h := hphysical X hX hf L m z
    refine ⟨h.1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hphysCp (Real.rpow_nonneg (by
        rw [aux_lim_cor_paths_inlined_lim_cor_exit_moments_localTime_eq]
        exact (SubdiffusiveProcess.Section10.PhysicalLocalTransport.rawClock_pos M L m).le) p))), h.2⟩
  · intro untruncated phi hphi xs _x _hxs P hP
    have hpre : ∀ k n : ℕ, k ≤ phi n →
        (∫⁻ w, aux_lim_cor_paths_inlined_lim_cor_exit_moments_smallExit k w ^ p
          ∂(aux_lim_cor_paths_inlined_lim_cor_exit_moments_annealedSequence M X hX untruncated phi xs n :
            Measure (DiffusionPath d))) ≤
              ENNReal.ofReal (Climit * (3 : ℝ)^(-(p*(2+eta M)*(k : ℝ)))) := by
      intro k n hk
      exact aux_lim_cor_paths_inlined_lim_cor_exit_moments_prelimit_bound M X hX hf Cphysical (Cdecay M)
        (eta M) p hCphysical hp hdec' (fun L m z => (hphysical X hX hf L m z).1)
        untruncated phi xs k n hk
    obtain ⟨hexit, hsmall, hnegative⟩ := hlimit M X hX untruncated phi hphi xs P hP hpre
    refine ⟨?_, ?_, hnegative⟩
    · intro k
      exact (hexit k).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hDCp (Real.rpow_nonneg (by norm_num) _)))
    · intro t epsilon ht ht1 he he1
      exact (hsmall t epsilon ht ht1 he he1).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hDCp (Real.rpow_nonneg epsilon.coe_nonneg _)))

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_36

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimCorPathsAssembly. -/
noncomputable section aux_lim_cor_paths_inline_37

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10 SubdiffusiveProcess.Section10.EndpointPaths
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Paper

/-- Complete internal application to the frozen paths conclusion. The physical
random first-mean bank and the explicit limiting-law identity are the separate
producer boundaries. No path behavior is asserted as an input. -/
theorem aux_lim_cor_paths_inlined_lim_cor_paths_of_mean_bank_and_attachment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (hbank : aux_lim_cor_paths_inlined_lim_cor_exit_moments_RandomMeanBank d)
    (deltaAttach : ℝ) (hdeltaAttach : 0 < deltaAttach)
    (hattach : ∀ M : GMCModel d, M.delta ≤ deltaAttach → aux_lim_cor_paths_inlined_lim_cor_paths_LimitingLawAttachment M) :
    aux_lim_cor_paths_inlined_lim_cor_paths_Conclusion d := by
  obtain ⟨deltaBase, _hdeltaBase, eta, Cdecay, hrates, horders⟩ :=
    aux_lim_cor_paths_inlined_lim_cor_exit_moments_of_random_mean_bank hd hbank
  obtain ⟨delta1, hdelta1, hdelta1Base, hmodels⟩ := horders 1 (by norm_num)
  refine ⟨min delta1 deltaAttach, lt_min hdelta1 hdeltaAttach, ?_⟩
  intro M hM
  obtain ⟨heta, hCdecay, hplanar, hdec⟩ :=
    hrates M ((hM.trans (min_le_left _ _)).trans hdelta1Base)
  obtain ⟨_cp, Cp, hcp, hcpCp, hqorders⟩ := hmodels M (hM.trans (min_le_left _ _))
  have hCp : 0 < Cp := hcp.trans_le hcpCp
  obtain ⟨_Cneg, _hCneg, hlaws⟩ := hqorders 1 (by norm_num) (by linarith)
  have hmean : ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d)
      (DiffusionPath d)) (hX : ∀ L, IsMarkovKernel (X L)),
      aux_lim_cor_paths_IsPhysicalFamily M X →
      ∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
      ∀ (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d), Tendsto xs atTop (𝓝 x) →
      ∀ P : ProbabilityMeasure (DiffusionPath d),
        aux_lim_cor_paths_IsAnnealedLimit M X untruncated phi xs P →
        ∀ k : ℕ, (∫⁻ w, aux_lim_cor_paths_smallExit k w ∂(P : Measure (DiffusionPath d))) ≤
          ENNReal.ofReal (Cp * (3 : ℝ)^(-((2+eta M)*(k : ℝ)))) := by
    intro X hX hf untruncated phi hphi xs x hxs P hP k
    have hm := ((hlaws X hX ((aux_lim_cor_paths_inlined_lim_cor_paths_family_iff M X).mp hf)).2
      untruncated phi hphi xs x hxs P
        ((aux_lim_cor_paths_inlined_lim_cor_paths_limit_iff M X untruncated phi xs P).mp hP)).1 k
    simpa only [ENNReal.rpow_one, one_mul] using! hm
  refine ⟨eta M, Cdecay M, heta, hCdecay, hplanar, ?_, ?_, ?_⟩
  · simpa only [neg_mul] using hdec
  · intro epsilon hepsilon
    refine ⟨oscillationConstant (eta M) epsilon,
      oscillationConstant_pos (eta M) epsilon heta, ?_, ?_⟩
    · intro X hX hf untruncated phi hphi xs x hxs P hP
      exact (aux_lim_cor_paths_inlined_lim_cor_paths_smallTime_of_mean_decay P Cp (eta M) epsilon heta hepsilon
        (hmean X hX hf untruncated phi hphi xs x hxs P hP)).2
    · intro H hH PN KN hKN hcross K hK hconv x
      obtain ⟨X, hX, hf, untruncated, phi, hphi, xs, hxs, P, hP, hbar⟩ :=
        hattach M (hM.trans (min_le_right _ _)) H hH PN KN hKN hcross K hK hconv x
      have havg : ∀ k : ℕ,
          (∫⁻ omega, ∫⁻ w, aux_lim_cor_paths_smallExit k w ∂K (omega,x)
            ∂(chaosSampleLaw M).toMeasure) ≤
              ENNReal.ofReal (Cp * (3 : ℝ)^(-((2+eta M)*(k : ℝ)))) := by
        intro k
        have hm := hmean X hX hf untruncated phi hphi xs x hxs P hP k
        have hmeas : Measurable (aux_lim_cor_paths_smallExit (d := d) k) := by
          simpa only [ENNReal.rpow_one] using!
            (ExitMomentPassage.smallExit_rpow_lsc k 1 (by norm_num)).measurable
        rw [hbar] at hm
        change (∫⁻ w, aux_lim_cor_paths_smallExit k w
          ∂(chaosSampleLaw M).toMeasure.bind
            (K.comap (fun omega => (omega,x)) (measurable_id.prodMk measurable_const))) ≤ _ at hm
        rw [Measure.lintegral_bind (Kernel.aemeasurable _) hmeas.aemeasurable] at hm
        exact hm
      exact aux_lim_cor_paths_inlined_lim_cor_paths_quenched_of_averaged_mean M K hK x Cp (eta M) epsilon
        heta hepsilon havg
  · intro p hp
    obtain ⟨cp, hcp, hmax⟩ := aux_lim_cor_paths_inlined_lim_cor_paths_maximal_lower_of_mean_decay
      (d := d) Cp (eta M) p heta hp
    refine ⟨cp, hcp, ?_⟩
    intro X hX hf untruncated phi hphi xs x hxs P hP
    exact hmax P (hmean X hX hf untruncated phi hphi xs x hxs P hP)

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_37

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimThmNonbrownianDefs. -/
noncomputable section aux_lim_cor_paths_inline_38

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal



namespace SubdiffusiveProcess.Paper

/-- The probability space of the environment of the diffusions `X^{(L)}` and `X`: the layers
`(γ_k)_{k ≥ 0}` on the anchored `C^{1,1}` carrier.  (Body identical to
`SubdiffusiveProcess.Section10.PhysicalAttachment.physicalLaw`.) -/
def aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw {d : ℕ} (M : GMCModel d) :
    ProbabilityMeasure (AnchoredC11Sample d) :=
  anchoredC11SampleLaw M (Section6Anchored.measurableSet_anchoredC11GoodSet d)
    (Section6Anchored.measure_anchoredC11GoodSet_eq_one M)

/-- `X L` (`L ∈ ℕ₀` the truncation `X^{(L)}`, `L = ⊤` the untruncated diffusion `X`) is a Markov kernel
`(ω, x) ↦ 𝐏_x^ω` of path laws whose finite-dimensional distributions, for almost every environment
and every start `x`, are those of the conservative Feller semigroup of the weak elliptic resolvent
of `coefficientAt M L ω` (generator `a^{-1} ∇·(a ∇)`, reversible measure `a dx`). -/
def aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsPhysicalFamily {d : ℕ} (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)) :
    Prop :=
  ∀ᵐ omega ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
    ∃ D : C0ResolventDatum (SpatialCoordinates d),
    ∃ hdense : ∀ mu, DenseRange (D.operator mu),
      IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
      (D.fellerKernelSemigroup hdense).IsConservative ∧
      ∀ (I : Finset ℝ≥0) (x : SpatialCoordinates d),
        ((X L).map (ContinuousPath.finsetEvaluation I)) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x

/-- The rescaled path `Z_t = 3^{-n} X_{3^{2n} t/ahom_n}` (`Z^{(L)}` of `s.tightness`, also for the
untruncated diffusion). -/
def aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale {d : ℕ} (M : GMCModel d) (n : ℕ) (w : DiffusionPath d) :
    DiffusionPath d :=
  ⟨fun t => (3 : ℝ) ^ (-(n : ℤ)) •
    w (Real.toNNReal ((3 : ℝ) ^ (2 * n) / ahom M n) * t), by fun_prop⟩

/-- The truncation index of the family: `n` (the cutoff diffusion `X^{(n)}`) or `⊤` (the
untruncated diffusion `X`). -/
def aux_lim_cor_paths_inlined_lim_thm_nonbrownian_familyCutoff (untruncated : Bool) (n : ℕ) : WithTop ℕ :=
  if untruncated then ⊤ else (n : WithTop ℕ)

/-- `σ_k`: the exit time of `Z - Z_0` from the cube `3^{-k} 𝖢_0`. -/
def aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit {d : ℕ} (k : ℕ) (w : DiffusionPath d) : ℝ≥0∞ :=
  ContinuousPath.exitTime (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w

/-- `P` is a subsequential limit of the annealed laws `𝐄[K_{N,x}^ω]` of either family (truncated for
`untruncated = false`, untruncated for `true`), along the subsequence `phi` and the deterministic
starting points `3^{phi n} xs n` in physical coordinates (`xs n → x` in rescaled coordinates): weak
convergence against bounded continuous path functionals.  The environment is sampled once and
kept fixed along the entire path. -/
def aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsAnnealedLimit {d : ℕ} (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (untruncated : Bool) (phi : ℕ → ℕ) (xs : ℕ → SpatialCoordinates d)
    (P : ProbabilityMeasure (DiffusionPath d)) : Prop :=
  ∀ G : BoundedContinuousFunction (DiffusionPath d) ℝ,
    Tendsto (fun n => ∫ omega,
      (∫ w, G (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M (phi n) w)
        ∂X (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_familyCutoff untruncated (phi n))
          (omega, (3 : ℝ) ^ (phi n) • xs n))
      ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure) atTop
        (𝓝 (∫ w, G w ∂(P : Measure (DiffusionPath d))))

/-- Convergence of the quenched path laws `K_{N,x}^ω → K_x^ω` locally uniformly in `x`, almost surely
(Theorem A(i), `eq:mfd-main-as`), for the rescaled cutoff path kernels `KN` attached to `in_crossing`.
`K` is the limit kernel of Theorem A. -/
def aux_lim_cor_paths_inlined_lim_thm_nonbrownian_QuenchedConv {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) : Prop :=
  ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
    ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
        pathLevyProkhorovDist
          (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
          (jointPathProbabilityMeasure K hK omega x) < epsilon

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_38

/- Inlined proved source application: SubdiffusiveProcess.Paper.BrownianScalingApplications. -/
noncomputable section aux_lim_cor_paths_inline_39

/-! Applications to the specified Brownian predicate and the existing Section 10 exit carrier.
Limiting-law exit estimates and full mass are not supplied by this module. -/
open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped NNReal ENNReal Topology
namespace SubdiffusiveProcess.Paper

/-- Full centered Brownian path-law scaling: arbitrary start and finite PSD covariance,
including singular and zero matrices, on the actual `DiffusionPath` carrier. -/
theorem aux_lim_cor_paths_brownian_finite_psd_centered_scaling
    {d : ℕ} (Q : Measure (DiffusionPath d)) (hQ : lim_brownian_law Q)
    (a : ℝ) (ha : 0 < a) :
    Q.map (aux_lim_nonbrownian_scalePath a (Real.toNNReal (a⁻¹ ^ 2))) =
      Q.map (aux_lim_nonbrownian_scalePath 1 1) := by
  let : IsProbabilityMeasure Q := hQ.1
  obtain ⟨x0, S, hS, hstart, hinc⟩ := hQ.2
  exact SubdiffusiveProcess.Section10.map_centeredScale_inverse_square Q S hinc a ha

/-- The zero covariance branch identifies the centered law as a zero-path Dirac measure. -/
theorem aux_lim_cor_paths_inlined_sol19_zero_covariance_centered_law
    {d : ℕ} (Q : Measure (DiffusionPath d)) [IsProbabilityMeasure Q]
    (hinc : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
      ∀ xi : Fin n → SpatialCoordinates d,
        ∫ w, Complex.exp (Complex.I * ∑ j : Fin n, ∑ i : Fin d,
            ((xi j i * (w (t j.succ) i - w (t j.castSucc) i) : ℝ) : ℂ)) ∂Q =
          Complex.exp (-(1 / 2 : ℂ) * ∑ j : Fin n,
            ((((t j.succ : ℝ) - (t j.castSucc : ℝ)) *
              dotProduct (xi j) ((0 : Matrix (Fin d) (Fin d) ℝ).mulVec (xi j)) : ℝ) : ℂ))) :
    Q.map (aux_lim_nonbrownian_scalePath 1 1) = Measure.dirac (0 : DiffusionPath d) := by
  apply SubdiffusiveProcess.Section10.map_centeredScale_eq_dirac_zero_of_zero_increments
  intro n t ht xi
  simpa using hinc n t ht xi

/-- Constant-path laws at arbitrary starting points satisfy the specified predicate with S=0. -/
theorem aux_lim_cor_paths_inlined_sol19_brownian_constant_law {d : ℕ} (x : SpatialCoordinates d) :
    lim_brownian_law (Measure.dirac (ContinuousMap.const ℝ≥0 x)) := by
  refine ⟨inferInstance, x, 0, Matrix.PosSemidef.zero, ?_, ?_⟩
  · simp
  · intro n t ht xi
    simp

/-- Discharge the literal all-scale, all-ENNReal-threshold hypothesis of the exit carrier. -/
theorem aux_lim_cor_paths_inlined_sol19_brownian_exit_sublevel_scaling
    {d : ℕ} (Q : Measure (DiffusionPath d)) (hQ : lim_brownian_law Q)
    (k : ℕ) (threshold : ℝ≥0∞) :
    Q {w | (3 : ℝ≥0∞) ^ (2 * k) * ContinuousPath.exitTime
        (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w < threshold} =
      Q {w | ContinuousPath.exitTime (Metric.ball (w 0) (1 / 2)) w < threshold} := by
  let a : ℝ := (3 : ℝ) ^ k
  let c : ℝ≥0 := ((3 : ℝ≥0) ^ (2 * k))⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hmap := aux_lim_cor_paths_brownian_finite_psd_centered_scaling Q hQ a ha
  dsimp [a] at hmap
  rw [SubdiffusiveProcess.Section10.triadic_inverse_square_clock] at hmap
  have hcoef : (c : ℝ≥0∞)⁻¹ = (3 : ℝ≥0∞) ^ (2 * k) := by
    dsimp [c]
    rw [ENNReal.coe_inv (by positivity), ENNReal.coe_pow]
    norm_num
  have hradius : (1 / 2 : ℝ) / a = (3 : ℝ) ^ (-(k : ℤ)) / 2 := by
    dsimp [a]
    rw [zpow_neg, zpow_natCast]
    simp only [div_eq_mul_inv]
    ring
  let f : DiffusionPath d → ℝ≥0∞ := fun w =>
    ContinuousPath.exitTime (Metric.ball (w 0) (1 / 2)) w
  have hf : Measurable f := (aux_lim_nonbrownian_centered_exit_lsc _).measurable
  have hE : MeasurableSet {w : DiffusionPath d | f w < threshold} :=
    measurableSet_lt hf measurable_const
  have hleft : ∀ w : DiffusionPath d,
      f (aux_lim_nonbrownian_scalePath a c w) =
        (3 : ℝ≥0∞) ^ (2 * k) * ContinuousPath.exitTime
          (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w := by
    intro w
    have hz : aux_lim_nonbrownian_scalePath a c w 0 = 0 := by
      simp [aux_lim_nonbrownian_scalePath]
    dsimp [f]
    rw [hz, aux_lim_nonbrownian_scalePath_exit a ha c hc, hcoef, hradius]
  have hright : ∀ w : DiffusionPath d,
      f (aux_lim_nonbrownian_scalePath 1 1 w) = f w := by
    intro w
    have hz : aux_lim_nonbrownian_scalePath 1 1 w 0 = 0 := by
      simp [aux_lim_nonbrownian_scalePath]
    dsimp [f]
    rw [hz, aux_lim_nonbrownian_scalePath_exit 1 (by norm_num) 1 (by norm_num)]
    norm_num
  calc
    _ = (Q.map (aux_lim_nonbrownian_scalePath a c)) {w | f w < threshold} := by
      rw [Measure.map_apply (aux_lim_nonbrownian_scalePath_measurable a c) hE]
      simp only [Set.preimage_ofPred_eq, hleft]
    _ = (Q.map (aux_lim_nonbrownian_scalePath 1 1)) {w | f w < threshold} :=
      congrArg (fun P : Measure (DiffusionPath d) => P {w | f w < threshold}) hmap
    _ = _ := by
      rw [Measure.map_apply (aux_lim_nonbrownian_scalePath_measurable 1 1) hE]
      simp only [Set.preimage_ofPred_eq, hright]
      rfl

/-- One fixed measurable carrier, independent of the Brownian law, start and covariance. -/
def aux_lim_cor_paths_inlined_sol19_brownian_common_carrier (d : ℕ) : Set (DiffusionPath d) :=
  {w | Tendsto (fun k : ℕ => (3 : ℝ≥0∞) ^ (2 * k) *
    ContinuousPath.exitTime (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w)
      atTop (𝓝 0)}

theorem aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_measurable (d : ℕ) :
    MeasurableSet (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier d) := by
  exact measurableSet_tendsto (𝓝 0) (fun k =>
    measurable_const.mul (aux_lim_nonbrownian_centered_exit_lsc _).measurable)

/-- Every law satisfying the specified predicate gives the common carrier zero mass. -/
theorem aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_null
    {d : ℕ} (Q : Measure (DiffusionPath d)) (hQ : lim_brownian_law Q) :
    Q (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier d) = 0 := by
  let : IsProbabilityMeasure Q := hQ.1
  exact aux_lim_nonbrownian_common_carrier_of_exit_scaling Q
    (aux_lim_cor_paths_inlined_sol19_brownian_exit_sublevel_scaling Q hQ)

/-- The constant-path branch at any start has zero common-carrier mass. -/
theorem aux_lim_cor_paths_inlined_sol19_constant_path_common_carrier_null {d : ℕ} (x : SpatialCoordinates d) :
    (Measure.dirac (ContinuousMap.const ℝ≥0 x)) (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier d) = 0 :=
  aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_null _ (aux_lim_cor_paths_inlined_sol19_brownian_constant_law x)

/-- In particular, zero-covariance constant paths never lie in the carrier. -/
theorem aux_lim_cor_paths_inlined_sol19_constant_path_not_mem_common_carrier {d : ℕ} (x : SpatialCoordinates d) :
    ContinuousMap.const ℝ≥0 x ∉ aux_lim_cor_paths_inlined_sol19_brownian_common_carrier d := by
  intro hx
  have hnull := aux_lim_cor_paths_inlined_sol19_constant_path_common_carrier_null x
  rw [Measure.dirac_apply_of_mem hx] at hnull
  exact one_ne_zero hnull

/-- Measurable mixtures of any family of finite-PSD Brownian laws have the same null carrier. -/
theorem aux_lim_cor_paths_inlined_sol19_brownian_mixture_common_carrier_null
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (nu : Measure Θ) (kappa : Kernel Θ (DiffusionPath d))
    (hB : ∀ θ, lim_brownian_law (kappa θ)) :
    (nu.bind kappa) (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier d) = 0 := by
  rw [Measure.bind_apply (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_measurable d) kappa.aemeasurable]
  simp only [aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_null _ (hB _), lintegral_zero]

/-- Consume a separately supplied full-mass carrier without claiming its model estimates. -/
theorem aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_singular
    {d : ℕ} (P : Measure (DiffusionPath d))
    (hP : P (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier d)ᶜ = 0) :
    (∀ Q, lim_brownian_law Q → P ⟂ₘ Q) ∧
      (∀ (Θ : Type*) [MeasurableSpace Θ] (nu : Measure Θ)
        (kappa : Kernel Θ (DiffusionPath d)),
        (∀ θ, lim_brownian_law (kappa θ)) → P ⟂ₘ nu.bind kappa) := by
  constructor
  · intro Q hQ
    refine ⟨(aux_lim_cor_paths_inlined_sol19_brownian_common_carrier d)ᶜ,
      (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_measurable d).compl, hP, ?_⟩
    rw [compl_compl]
    exact aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_null Q hQ
  · intro Θ inst nu kappa hB
    exact aux_lim_nonbrownian_mixture_carrier P nu kappa _
      (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_measurable d) hP
      (fun θ => aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_null _ (hB θ))

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_39

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimThmNonbrownianCarrier. -/
noncomputable section aux_lim_cor_paths_inline_40

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Paper

/-- The positive strict-decay rate makes the source common carrier conull.
This is the full Step 2 application once Step 1 supplies its literal estimate. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_carrier_full_of_mean
    {d : ℕ} (P : Measure (DiffusionPath d)) (C eta : ℝ) (heta : 0 < eta)
    (hmean : ∀ k : ℕ, (∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w ∂P) ≤
      ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))) :
    P (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier d)ᶜ = 0 := by
  have hs : ∀ k, Measurable (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit (d := d) k) := fun k =>
    (aux_lim_nonbrownian_centered_exit_lsc _).measurable
  have hsum := SubdiffusiveProcess.Section10.nonbrownian_weighted_exit_tsum_ne_top P
    aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit hs C eta heta hmean
  have h := aux_lim_nonbrownian_summable_exits P
    (fun k w => (3 : ℝ≥0∞)^(2*k) * aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w)
    (fun k => measurable_const.mul (hs k)) hsum
  exact ae_iff.mp h

/-- Every Brownian law and every measurable Brownian mixture are excluded by
one event, with the quantifiers inside the same conclusion. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_singular_of_mean
    {d : ℕ} (P : Measure (DiffusionPath d)) (C eta : ℝ) (heta : 0 < eta)
    (hmean : ∀ k : ℕ, (∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w ∂P) ≤
      ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))) :
    (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q → P ⟂ₘ Q) ∧
      (∀ (Θ : Type*) [MeasurableSpace Θ] (nu : Measure Θ)
        (kappa : Kernel Θ (DiffusionPath d)),
        (∀ theta, lim_brownian_law (kappa theta)) → P ⟂ₘ nu.bind kappa) :=
  aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_singular P
    (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_carrier_full_of_mean P C eta heta hmean)

/-- Evaluation of a random probability law as a measurable Markov kernel.
This is its literal Giry coercion, not a substitute process or predicate. -/
def aux_lim_cor_paths_inlined_lim_thm_nonbrownian_evaluationKernel {d : ℕ} :
    Kernel (ProbabilityMeasure (DiffusionPath d)) (DiffusionPath d) :=
  ⟨fun P => P.toMeasure, measurable_subtype_coe⟩

instance aux_lim_cor_paths_inlined_lim_thm_nonbrownian_evaluationKernel_markov {d : ℕ} :
    IsMarkovKernel (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_evaluationKernel (d := d)) :=
  ⟨fun P => by change IsProbabilityMeasure P.toMeasure; infer_instance⟩

/-- A random law whose actual barycentre has the source mean bound is a.s.
conull on the same carrier; hence all Brownian and mixture quantifiers hold
simultaneously, without an uncountable intersection of law-dependent events. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_random_singular_of_barycentre_mean
    {d : ℕ} (Lam : Measure (ProbabilityMeasure (DiffusionPath d)))
    (C eta : ℝ) (heta : 0 < eta)
    (hmean : ∀ k : ℕ, (∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w
      ∂(Lam.bind aux_lim_cor_paths_inlined_lim_thm_nonbrownian_evaluationKernel)) ≤
      ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))) :
    ∀ᵐ (P : ProbabilityMeasure (DiffusionPath d)) ∂Lam,
      (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q →
        (P : Measure (DiffusionPath d)) ⟂ₘ Q) ∧
      (∀ (Θ : Type*) [MeasurableSpace Θ] (nu : Measure Θ)
        (kappa : Kernel Θ (DiffusionPath d)),
        (∀ theta, lim_brownian_law (kappa theta)) →
          (P : Measure (DiffusionPath d)) ⟂ₘ nu.bind kappa) := by
  have hbar := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_carrier_full_of_mean
    (Lam.bind aux_lim_cor_paths_inlined_lim_thm_nonbrownian_evaluationKernel) C eta heta hmean
  have h := aux_lim_nonbrownian_barycentre_carrier Lam
    aux_lim_cor_paths_inlined_lim_thm_nonbrownian_evaluationKernel (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier d)
    (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_measurable d) hbar
  filter_upwards [h] with P hP
  exact aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_singular (P : Measure (DiffusionPath d)) hP

/-- Canonical quenched laws inherit the carrier simultaneously for every
Brownian law and mixture, from the averaged mean estimate at the same start. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_quenched_singular_of_averaged_mean
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : GMCModel d)
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (x : SpatialCoordinates d) (C eta : ℝ) (heta : 0 < eta)
    (hmean : ∀ k : ℕ,
      (∫⁻ omega, ∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w ∂K (omega,x)
        ∂(chaosSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q → K (omega,x) ⟂ₘ Q) ∧
      (∀ (Θ : Type*) [MeasurableSpace Θ] (nu : Measure Θ)
        (kappa : Kernel Θ (DiffusionPath d)),
        (∀ theta, lim_brownian_law (kappa theta)) → K (omega,x) ⟂ₘ nu.bind kappa) := by
  let row := K.comap (fun omega => (omega,x)) (measurable_id.prodMk measurable_const)
  have hbar : ∀ k, (∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w
      ∂(chaosSampleLaw M).toMeasure.bind row) ≤
      ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ)))) := by
    intro k
    have hf : Measurable (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit (d := d) k) :=
      (aux_lim_nonbrownian_centered_exit_lsc _).measurable
    rw [Measure.lintegral_bind row.aemeasurable hf.aemeasurable]
    exact hmean k
  have h := aux_lim_nonbrownian_barycentre_carrier (chaosSampleLaw M).toMeasure row
    (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier d) (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_measurable d)
    (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_carrier_full_of_mean _ C eta heta hbar)
  filter_upwards [h] with omega hmass
  exact aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_singular (K (omega,x)) hmass

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_40

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimThmNonbrownianWeak. -/
noncomputable section aux_lim_cor_paths_inline_41

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Paper

/-- The reviewed raw-clock map is the installed affine path rescaling. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale_eq {d : ℕ} (M : GMCModel d) (N : ℕ) :
    aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M N =
      ContinuousPath.rescale (physicalCoordinates N (0 : SpatialCoordinates d)).symm
        (rawClock M N N) := by
  have hclock : Real.toNNReal ((3 : ℝ)^(2*N) / ahom M N) = rawClock M N N := by
    apply NNReal.eq
    simp only [rawClock, activeScale_coe, min_self]
    exact max_eq_left (div_pos (pow_pos (by norm_num) _) (ahom_pos M N)).le
  funext w
  apply ContinuousMap.ext
  intro t
  simp only [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale, ContinuousMap.coe_mk,
    ContinuousPath.rescale_apply, physicalCoordinates_symm_apply,
    sub_zero, zpow_neg, zpow_natCast, hclock]

/-- The precise annealed laws in the source predicate, for either family. -/
def aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence {d : ℕ}
    (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L)) (untruncated : Bool) (phi : ℕ → ℕ)
    (xs : ℕ → SpatialCoordinates d) (n : ℕ) : ProbabilityMeasure (DiffusionPath d) := by
  letI := hX (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_familyCutoff untruncated (phi n))
  let row := ((X (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_familyCutoff untruncated (phi n))).comap
    (fun omega => (omega,(3 : ℝ)^(phi n) • xs n))
    (measurable_id.prodMk measurable_const)).map
      (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M (phi n))
  have hm : Measurable (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M (phi n)) := by
    rw [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale_eq]
    exact ContinuousPath.measurable_rescale _ _
  letI : IsMarkovKernel row := Kernel.IsMarkovKernel.map _ hm
  exact ⟨row ∘ₘ (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure, inferInstance⟩

/-- The literal two integrals in the reviewed statement equal integration
against these probability laws. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence_integral {d : ℕ}
    (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L)) (untruncated : Bool) (phi : ℕ → ℕ)
    (xs : ℕ → SpatialCoordinates d) (n : ℕ)
    (G : BoundedContinuousFunction (DiffusionPath d) ℝ) :
    (∫ w, G w ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence M X hX untruncated phi xs n :
      Measure (DiffusionPath d))) =
      ∫ omega, ∫ w, G (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M (phi n) w)
        ∂X (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_familyCutoff untruncated (phi n))
          (omega,(3 : ℝ)^(phi n) • xs n)
        ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure := by
  let L := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_familyCutoff untruncated (phi n)
  let := hX L
  have hm : Measurable (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M (phi n)) := by
    rw [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale_eq]
    exact ContinuousPath.measurable_rescale _ _
  change (∫ w, G w ∂(_ ∘ₘ (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure)) = _
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (G.integrable _),
    Kernel.const_apply]
  apply integral_congr_ae
  apply ae_of_all
  intro omega
  dsimp only
  rw [Kernel.map_apply _ hm, Kernel.comap_apply,
    integral_map hm.aemeasurable G.continuous.measurable.aestronglyMeasurable]

/-- The exact source weak-limit predicate supplies ordinary weak convergence. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence_tendsto {d : ℕ}
    (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L)) (untruncated : Bool) (phi : ℕ → ℕ)
    (xs : ℕ → SpatialCoordinates d) (P : ProbabilityMeasure (DiffusionPath d))
    (hlimit : aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsAnnealedLimit M X untruncated phi xs P) :
    Tendsto (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence M X hX untruncated phi xs)
      atTop (𝓝 P) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro G
  simpa only [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence_integral] using hlimit G

/-- The actual barycentre of a law of probability laws, on the Giry carrier. -/
def aux_lim_cor_paths_inlined_lim_thm_nonbrownian_barycentre {d : ℕ}
    (Lam : Measure (ProbabilityMeasure (DiffusionPath d))) [IsProbabilityMeasure Lam] :
    ProbabilityMeasure (DiffusionPath d) :=
  ⟨Lam.bind aux_lim_cor_paths_inlined_lim_thm_nonbrownian_evaluationKernel, inferInstance⟩

/-- This equality is the barycentre identity used verbatim in the random-law clause. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_barycentre_integral {d : ℕ}
    (Lam : Measure (ProbabilityMeasure (DiffusionPath d))) [IsProbabilityMeasure Lam]
    (G : BoundedContinuousFunction (DiffusionPath d) ℝ) :
    (∫ w, G w ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_barycentre Lam : Measure (DiffusionPath d))) =
      ∫ P : ProbabilityMeasure (DiffusionPath d), ∫ w, G w ∂(P : Measure (DiffusionPath d))
        ∂Lam := by
  change (∫ w, G w ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_evaluationKernel ∘ₘ Lam)) = _
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (G.integrable _),
    Kernel.const_apply]
  rfl

/-- Barycentre convergence, exactly as assumed by the stronger reviewed random-law clause. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_barycentre_tendsto {d : ℕ}
    (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L)) (untruncated : Bool) (phi : ℕ → ℕ)
    (xs : ℕ → SpatialCoordinates d)
    (Lam : Measure (ProbabilityMeasure (DiffusionPath d))) [IsProbabilityMeasure Lam]
    (hlimit : ∀ G : BoundedContinuousFunction (DiffusionPath d) ℝ,
      Tendsto (fun n => ∫ omega, ∫ w, G (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M (phi n) w)
        ∂X (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_familyCutoff untruncated (phi n))
          (omega,(3 : ℝ)^(phi n) • xs n)
        ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure) atTop
          (𝓝 (∫ P : ProbabilityMeasure (DiffusionPath d),
            ∫ w, G w ∂(P : Measure (DiffusionPath d)) ∂Lam))) :
    Tendsto (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence M X hX untruncated phi xs)
      atTop (𝓝 (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_barycentre Lam)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro G
  simpa only [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence_integral,
    aux_lim_cor_paths_inlined_lim_thm_nonbrownian_barycentre_integral] using hlimit G

/-- All scales, including k=0, pass by the existing centered-exit Portmanteau lemma. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_mean_of_prelimit {d : ℕ}
    (P : ProbabilityMeasure (DiffusionPath d))
    (PN : ℕ → ProbabilityMeasure (DiffusionPath d))
    (hconv : Tendsto PN atTop (𝓝 P)) (C eta : ℝ)
    (hpre : ∀ k : ℕ, ∀ᶠ n in atTop,
      (∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w ∂(PN n : Measure (DiffusionPath d))) ≤
        ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))) :
    ∀ k : ℕ, (∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w ∂(P : Measure (DiffusionPath d))) ≤
      ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ)))) := by
  intro k
  exact aux_lim_nonbrownian_exit_passage _ P PN hconv _ (hpre k)

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_41

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimThmNonbrownianPrelimit. -/
noncomputable section aux_lim_cor_paths_inline_42

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10.PhysicalLocalTransport SubdiffusiveProcess.Section10.PrelimitExitPaths
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Paper

/-- The reviewed characterization fixes the initial point at every start;
this uses the installed zero-time FDD theorem, without a density or Itô input. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physical_start {d : ℕ}
    (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L))
    (hphysical : aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsPhysicalFamily M X) :
    ∀ᵐ omega ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure,
      ∀ L : WithTop ℕ, ∀ x : SpatialCoordinates d, ∀ᵐ w ∂X L (omega,x), w 0 = x := by
  filter_upwards [hphysical] with omega h
  intro L x
  let := hX L
  obtain ⟨D, hdense, _hweak, hcons, hfdd⟩ := h L
  let row := (X L).comap (Prod.mk omega) measurable_prodMk_left
  have hfdd' : ∀ I, row.map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I := by
    intro I
    ext y B hB
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I), Kernel.comap_apply]
    have hf := hfdd I y
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)] at hf
    exact congrArg (fun Q : Measure (I → SpatialCoordinates d) => Q B) hf
  have hzero := congrArg (fun K : Kernel (SpatialCoordinates d) (SpatialCoordinates d) => K x)
    (SubMarkovKernelSemigroup.IsConservative.realization_map_eval_zero
      (D.fellerKernelSemigroup hdense) hcons row hfdd')
  have hm : Measurable (fun w : DiffusionPath d => w 0) :=
    ContinuousPath.measurable_coordinateProcess 0
  change (row.map (fun w => w 0)) x = Kernel.id x at hzero
  rw [Kernel.id_apply, Kernel.map_apply _ hm] at hzero
  apply (mem_ae_iff_prob_eq_one (hm (MeasurableSet.singleton x))).mpr
  have hzero' : (X L (omega,x)).map (fun w => w 0) = Measure.dirac x := hzero
  rw [← Measure.map_apply hm (MeasurableSet.singleton x), hzero']
  simp

/-- Both the finite and the top branch have active scale N-k in Step 1. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_activeScale (untruncated : Bool) (N k : ℕ) :
    activeScale (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_familyCutoff untruncated N) (N-k) = N-k := by
  cases untruncated
  · change activeScale (N : WithTop ℕ) (N-k) = N-k
    rw [activeScale_coe, min_eq_left (Nat.sub_le N k)]
  · change activeScale (⊤ : WithTop ℕ) (N-k) = N-k
    simp only [activeScale, WithTop.untopD_top, min_self]

/-- The actual raw-clock exit conversion at every path, with all infinite-exit cases retained. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescaled_exit {d : ℕ} (M : GMCModel d)
    {N k : ℕ} (hk : k ≤ N) (w : DiffusionPath d) :
    aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M N w) =
      ((rawClock M N N : ℝ≥0∞))⁻¹ *
        ContinuousPath.exitTime (Metric.ball (w 0) ((3 : ℝ)^(N-k)/2)) w := by
  rw [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale_eq]
  change ContinuousPath.exitTime
    (Metric.ball ((ContinuousPath.rescale (physicalCoordinates N (0 : SpatialCoordinates d)).symm
      (rawClock M N N) w) 0) ((3 : ℝ)^(-(k : ℤ))/2))
    (ContinuousPath.rescale (physicalCoordinates N (0 : SpatialCoordinates d)).symm
      (rawClock M N N) w) = _
  rw [centered_exit_affine _ _ _ (rawClock_pos M _ _)]
  congr 2
  rw [zpow_neg, zpow_natCast, pow_sub₀ (3 : ℝ) (by norm_num) hk]
  ring

/-- Convert integration on the precise source annealed sequence to the two
literal kernel/environment integrals for any measurable extended functional. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence_lintegral {d : ℕ}
    (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L)) (untruncated : Bool) (phi : ℕ → ℕ)
    (xs : ℕ → SpatialCoordinates d) (n : ℕ)
    (f : DiffusionPath d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, f w ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence M X hX untruncated phi xs n :
      Measure (DiffusionPath d))) =
      ∫⁻ omega, ∫⁻ w, f (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M (phi n) w)
        ∂X (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_familyCutoff untruncated (phi n))
          (omega,(3 : ℝ)^(phi n) • xs n)
        ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure := by
  have hm : Measurable (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M (phi n)) := by
    rw [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale_eq]
    exact ContinuousPath.measurable_rescale _ _
  change (∫⁻ w, f w ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure.bind _) = _
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
  apply lintegral_congr_ae
  apply ae_of_all
  intro omega
  dsimp only
  rw [Kernel.map_apply _ hm, Kernel.comap_apply, lintegral_map hf hm]

/-- Consume only the exact physical mean bank needed for Step 1. Finite/top
and all centres remain literal; no occupation regularity is added to the source predicate. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_prelimit_exit_bound {d : ℕ}
    (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L))
    (hphysical : aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsPhysicalFamily M X)
    (Cmean Cdecay eta : ℝ) (hCmean : 0 ≤ Cmean)
    (hdec : ∀ l m : ℕ, l ≤ m → ahom M m / ahom M l ≤
      Cdecay * (3 : ℝ)^(-(eta*((m : ℝ)-(l : ℝ)))))
    (hbank : ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
      (∫⁻ omega, (⨆ y ∈ Metric.ball z ((3 : ℝ)^m/2),
        ∫⁻ w, ContinuousPath.exitTime (Metric.ball z ((3 : ℝ)^m/2)) w ∂X L (omega,y))
        ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure) ≤
          ENNReal.ofReal (Cmean * (rawClock M L m : ℝ)))
    (untruncated : Bool) (phi : ℕ → ℕ) (xs : ℕ → SpatialCoordinates d)
    (k n : ℕ) (hkn : k ≤ phi n) :
    (∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w
      ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence M X hX untruncated phi xs n :
        Measure (DiffusionPath d))) ≤
      ENNReal.ofReal ((Cmean*Cdecay) * (3 : ℝ)^(-((2+eta)*(k : ℝ)))) := by
  let N := phi n
  let L := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_familyCutoff untruncated N
  let z := (3 : ℝ)^N • xs n
  let E := (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure
  let c : ℝ≥0 := rawClock M N N
  let r : ℝ := (3 : ℝ)^(N-k)/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hc : 0 < c := rawClock_pos M _ _
  have hf : Measurable (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit (d := d) k) :=
    (aux_lim_nonbrownian_centered_exit_lsc _).measurable
  rw [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence_lintegral M X hX untruncated phi xs n _ hf]
  have ht : Measurable (fun w : DiffusionPath d =>
      ContinuousPath.exitTime (Metric.ball z r) w) :=
    (ContinuousPath.isStoppingTime_exitTime _ Metric.isOpen_ball).measurable'
  have hstart := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physical_start M X hX hphysical
  have hrow : ∀ᵐ omega ∂E,
      (∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M N w)
        ∂X L (omega,z)) =
      (c : ℝ≥0∞)⁻¹ * (∫⁻ w, ContinuousPath.exitTime (Metric.ball z r) w ∂X L (omega,z)) := by
    filter_upwards [hstart] with omega hs
    have he : (fun w => aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k
        (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M N w)) =ᵐ[X L (omega,z)]
      (fun w => (c : ℝ≥0∞)⁻¹ * ContinuousPath.exitTime (Metric.ball z r) w) := by
      filter_upwards [hs L z] with w hw
      rw [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescaled_exit M hkn, hw]
    rw [lintegral_congr_ae he, lintegral_const_mul _ ht]
  have htrow : Measurable (fun omega => ∫⁻ w,
      ContinuousPath.exitTime (Metric.ball z r) w ∂X L (omega,z)) :=
    (ht.lintegral_kernel (κ := X L)).comp (measurable_id.prodMk measurable_const)
  rw [lintegral_congr_ae hrow, lintegral_const_mul _ htrow]
  have hbank' := hbank L (N-k) z
  have hactive := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_activeScale untruncated N k
  have hclock : rawClock M L (N-k) = rawClock M N (N-k) := by
    apply NNReal.eq
    change (3 : ℝ)^(2*(N-k)) / ahom M (activeScale L (N-k)) =
      (3 : ℝ)^(2*(N-k)) / ahom M (activeScale (N : WithTop ℕ) (N-k))
    rw [hactive, activeScale_coe, min_eq_left (Nat.sub_le N k)]
  rw [hclock] at hbank'
  have hcenter : (∫⁻ omega, ∫⁻ w, ContinuousPath.exitTime (Metric.ball z r) w ∂X L (omega,z)
      ∂E) ≤ ENNReal.ofReal (Cmean * (rawClock M N (N-k) : ℝ)) := by
    apply le_trans (lintegral_mono (fun omega => ?_)) hbank'
    exact le_iSup_of_le z (le_iSup_of_le (Metric.mem_ball_self hr) le_rfl)
  have hrho := SubdiffusiveProcess.Section10.PrelimitExitClock.rawClock_ratio_le M hdec hkn
  calc
    _ ≤ (c : ℝ≥0∞)⁻¹ * ENNReal.ofReal (Cmean * (rawClock M N (N-k) : ℝ)) :=
      mul_le_mul_right hcenter _
    _ = ENNReal.ofReal (Cmean * ((rawClock M N (N-k) : ℝ) / (c : ℝ))) := by
      rw [show (c : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((c : ℝ)⁻¹) by
          rw [← ENNReal.coe_inv hc.ne', ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal],
        ← ENNReal.ofReal_mul (inv_nonneg.mpr c.coe_nonneg)]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact (mul_le_mul_of_nonneg_left hrho hCmean).trans_eq (by ring)

/-- Every source subsequence tends to infinity, so the same C and eta bound
all k in any annealed weak limit, with no restriction on the deterministic starts. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_mean_of_physical_bank {d : ℕ}
    (M : GMCModel d)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L))
    (hphysical : aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsPhysicalFamily M X)
    (Cmean Cdecay eta : ℝ) (hCmean : 0 ≤ Cmean)
    (hdec : ∀ l m : ℕ, l ≤ m → ahom M m / ahom M l ≤
      Cdecay * (3 : ℝ)^(-(eta*((m : ℝ)-(l : ℝ)))))
    (hbank : ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
      (∫⁻ omega, (⨆ y ∈ Metric.ball z ((3 : ℝ)^m/2),
        ∫⁻ w, ContinuousPath.exitTime (Metric.ball z ((3 : ℝ)^m/2)) w ∂X L (omega,y))
        ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure) ≤
          ENNReal.ofReal (Cmean * (rawClock M L m : ℝ)))
    (untruncated : Bool) (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (xs : ℕ → SpatialCoordinates d) (P : ProbabilityMeasure (DiffusionPath d))
    (hlimit : aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsAnnealedLimit M X untruncated phi xs P) :
    ∀ k : ℕ, (∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w ∂(P : Measure (DiffusionPath d))) ≤
      ENNReal.ofReal ((Cmean*Cdecay) * (3 : ℝ)^(-((2+eta)*(k : ℝ)))) := by
  apply aux_lim_cor_paths_inlined_lim_thm_nonbrownian_mean_of_prelimit _ _
    (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence_tendsto M X hX untruncated phi xs P hlimit)
  intro k
  filter_upwards [eventually_ge_atTop k] with n hn
  exact aux_lim_cor_paths_inlined_lim_thm_nonbrownian_prelimit_exit_bound M X hX hphysical
    Cmean Cdecay eta hCmean hdec hbank untruncated phi xs k n
    (hn.trans (hphi.id_le n))

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_42

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimThmNonbrownianQuenched. -/
noncomputable section aux_lim_cor_paths_inline_43

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Paper

/-- The exact frozen locally uniform quenched convergence implies weak
convergence at each deterministic start, on the installed path-law topology. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_quenched_tendsto {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hconv : aux_lim_cor_paths_inlined_lim_thm_nonbrownian_QuenchedConv M KN hKN K hK)
    (x : SpatialCoordinates d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      Tendsto (fun N => jointPathProbabilityMeasure (KN N) (hKN N) omega x) atTop
        (𝓝 (jointPathProbabilityMeasure K hK omega x)) := by
  filter_upwards [hconv] with omega h
  let : MetricSpace (DiffusionPath d) :=
    TopologicalSpace.completelyMetrizableMetric (DiffusionPath d)
  have ht : Tendsto
      (fun N => LevyProkhorov.ofMeasure (jointPathProbabilityMeasure (KN N) (hKN N) omega x))
      atTop (𝓝 (LevyProkhorov.ofMeasure (jointPathProbabilityMeasure K hK omega x))) := by
    apply Metric.tendsto_atTop.mpr
    intro epsilon hepsilon
    obtain ⟨N0, hN0⟩ := h {x} isCompact_singleton epsilon hepsilon
    refine ⟨N0, fun N hN => ?_⟩
    simpa only [LevyProkhorov.dist_probabilityMeasure_def, pathLevyProkhorovDist] using
      hN0 N hN x (mem_singleton x)
  exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto _ |>.comp ht

/-- Average the actual canonical joint path kernels at the same deterministic start. -/
def aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedRow {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (x : SpatialCoordinates d) :
    ProbabilityMeasure (DiffusionPath d) := by
  letI := hK
  exact ⟨K.comap (fun omega => (omega,x)) (measurable_id.prodMk measurable_const) ∘ₘ
    (chaosSampleLaw M).toMeasure, inferInstance⟩

theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedRow_integral {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (x : SpatialCoordinates d)
    (G : BoundedContinuousFunction (DiffusionPath d) ℝ) :
    (∫ w, G w ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedRow M K hK x : Measure (DiffusionPath d))) =
      ∫ omega, ∫ w, G w ∂K (omega,x) ∂(chaosSampleLaw M).toMeasure := by
  let := hK
  change (∫ w, G w ∂(_ ∘ₘ (chaosSampleLaw M).toMeasure)) = _
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (G.integrable _),
    Kernel.const_apply]
  rfl

/-- No environment identification is hidden here: this is direct dominated
convergence for the canonical KN/K rows supplied in the source statement. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_quenched_annealed_tendsto {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hconv : aux_lim_cor_paths_inlined_lim_thm_nonbrownian_QuenchedConv M KN hKN K hK)
    (x : SpatialCoordinates d) :
    Tendsto (fun N => aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedRow M (KN N) (hKN N) x) atTop
      (𝓝 (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedRow M K hK x)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro G
  simp only [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedRow_integral]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖G‖)
  · intro N
    exact (G.continuous.measurable.stronglyMeasurable.integral_kernel
      (κ := (KN N).comap (fun omega => (omega,x))
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    let := hKN N
    apply ae_of_all
    intro omega
    simpa using norm_integral_le_of_norm_le_const
      (μ := KN N (omega,x)) (ae_of_all _ (fun w => G.norm_coe_le_norm w))
  · filter_upwards [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_quenched_tendsto M KN hKN K hK hconv x]
      with omega ht
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht G

/-- Conditional source application with precisely the outstanding same-law
canonical prelimit mean bank; its bound passes directly to K then disintegrates. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_quenched_singular_of_prelimit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (M : GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hconv : aux_lim_cor_paths_inlined_lim_thm_nonbrownian_QuenchedConv M KN hKN K hK)
    (x : SpatialCoordinates d) (C eta : ℝ) (heta : 0 < eta)
    (hpre : ∀ k : ℕ, ∀ᶠ N in atTop,
      (∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w
        ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedRow M (KN N) (hKN N) x :
          Measure (DiffusionPath d))) ≤
        ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q → K (omega,x) ⟂ₘ Q) ∧
      (∀ (Θ : Type*) [MeasurableSpace Θ] (nu : Measure Θ)
        (kappa : Kernel Θ (DiffusionPath d)),
        (∀ theta, lim_brownian_law (kappa theta)) → K (omega,x) ⟂ₘ nu.bind kappa) := by
  let row := K.comap (fun omega => (omega,x)) (measurable_id.prodMk measurable_const)
  have ht := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_quenched_annealed_tendsto M KN hKN K hK hconv x
  have hmean := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_mean_of_prelimit _ _ ht C eta hpre
  have hmass := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_carrier_full_of_mean _ C eta heta hmean
  have hf := aux_lim_nonbrownian_barycentre_carrier (chaosSampleLaw M).toMeasure row
    (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier d) (aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_measurable d) hmass
  filter_upwards [hf] with omega hfull
  exact aux_lim_cor_paths_inlined_sol19_brownian_common_carrier_singular (K (omega,x)) hfull

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_43

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimThmNonbrownianAttachment. -/
noncomputable section aux_lim_cor_paths_inline_44

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.Section10.PhysicalLocalTransport SubdiffusiveProcess.Section10.PhysicalAttachment
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Paper

/-- Any supplied characterization of the actual infrared field agrees with
its installed construction, on one full bilateral event. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_infrared_unique {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, H omega = infraredField M omega := by
  filter_upwards [hH.2, (infraredField_spec M).2] with omega h h'
  exact tendsto_nhds_unique h h'

/-- Actual same-law attachment: the rescaled TOP physical law and the source
canonical KN agree at EVERY start on the native coupling. Raw clocks have no
extra ahom_0, and arbitrary characterized infrared versions are allowed. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_top_path_attachment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L))
    (hphysical : aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsPhysicalFamily M X) (N : ℕ) :
    ∀ᵐ eta ∂nativeLaw M, ∀ x : SpatialCoordinates d,
      (X ⊤ (physicalEnvironment M N 0 eta, (3 : ℝ)^N • x)).map
        (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M N) = KN N (bilateralEnvironment eta,x) := by
  let := hX ⊤
  let := hKN N
  have hp := (physicalEnvironment_preserving M N 0).quasiMeasurePreserving.ae hphysical
  have hb1 := (bilateralEnvironment_preserving M).quasiMeasurePreserving.ae hin.1
  have hb3 := (bilateralEnvironment_preserving M).quasiMeasurePreserving.ae hin.2.2
  have hH' := (bilateralEnvironment_preserving M).quasiMeasurePreserving.ae
    (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_infrared_unique M H hH)
  filter_upwards [hp, hb1, hb3, hH', top_local_identification M N 0]
    with eta hphysical' hres hFDD hHeta hid
  let omega := physicalEnvironment M N 0 eta
  let xi := bilateralEnvironment eta
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := hphysical' ⊤
  obtain ⟨E, hedense, hEweak, hElaplace⟩ := hres N
  let c := rawClock M ⊤ N
  let e := physicalCoordinates (d := d) N 0
  let D' := transportedDatum D e c (rawClock_pos M ⊤ N)
  let hdense' := transportedDatum_dense D hdense e c (rawClock_pos M ⊤ N)
  let Q := (KN N).comap (Prod.mk xi) measurable_prodMk_left
  let Y := ((X ⊤).comap (fun x => (omega,e x)) (measurable_const.prodMk e.measurable)).map
    (ContinuousPath.rescale e.symm c)
  let : IsMarkovKernel Q := by dsimp [Q]; infer_instance
  let : IsMarkovKernel Y := Kernel.IsMarkovKernel.map _ (ContinuousPath.measurable_rescale _ _)
  have hQF : ∀ I x, Q.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (PN N xi) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I), Kernel.comap_apply]
    have h := hFDD N I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)] at h
    exact h
  have hPN := (SubdiffusiveProcess.E7.isFeller_of_realization_and_datum
    (PN N xi) E hedense hElaplace Q hQF).1
  have hDweak : IsWeakEllipticResolvent (localCoefficient M ⊤ N 0 omega)
      (localSpeed M ⊤ N 0 omega) D' :=
    aux_lim_cor_paths_inlined_physical_local_datum_weak M ⊤ N 0 omega D hweak
  have hc : localCoefficient M ⊤ N 0 omega = cutoffCoefficient M H xi N := by
    funext x
    have hh : cutoffCoefficient M H xi N x =
        cutoffCoefficient M (infraredField M) xi N x := by
      unfold cutoffCoefficient cutoffPotential
      rw [show H xi = infraredField M xi from hHeta]
    exact (hid x).2.trans hh.symm
  have hb : localSpeed M ⊤ N 0 omega = cutoffSpeedDensity M H xi N := by
    funext x
    have hh : cutoffSpeedDensity M H xi N x =
        cutoffSpeedDensity M (infraredField M) xi N x := by
      unfold cutoffSpeedDensity cutoffPotential
      rw [show H xi = infraredField M xi from hHeta]
    exact (hid x).1.trans hh.symm
  rw [← hc, ← hb] at hEweak
  have hconj := aux_lim_cor_paths_inlined_physical_local_datum_conjugacy D hdense e c (rawClock_pos M ⊤ N)
  have hYF : ∀ I x, Y.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D'.fellerKernelSemigroup hdense') I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    dsimp only [Y]
    rw [Kernel.map_apply _ (ContinuousPath.measurable_rescale _ _), Kernel.comap_apply]
    change ((X ⊤ (omega,e x)).map (ContinuousPath.rescale e.symm c)).map _ = _
    apply aux_lim_cor_paths_inlined_physical_local_rescaled_fdd _ _ hcons
      ((X ⊤).comap (Prod.mk omega) measurable_prodMk_left) inferInstance
      (fun J y => ?_) e.symm c (rawClock_pos M ⊤ N) hconj I x
    have h := hfdd J y
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation J)] at h
    exact h
  have hEQ : Y = Q := local_law_unique M ⊤ N 0 omega D' E hDweak hEweak
    hdense' hedense Y Q inferInstance hYF (by intro I x; simpa only [hPN] using hQF I x)
  intro x
  have hrow := congrArg (fun Z : Kernel (SpatialCoordinates d) (DiffusionPath d) => Z x) hEQ
  dsimp only [Y, Q] at hrow
  rw [Kernel.map_apply _ (ContinuousPath.measurable_rescale _ _), Kernel.comap_apply,
    Kernel.comap_apply] at hrow
  change (X ⊤ (omega,e x)).map (ContinuousPath.rescale e.symm c) = KN N (xi,x) at hrow
  have hclock : c = rawClock M N N := by
    apply NNReal.eq
    change (3 : ℝ)^(2*N) / ahom M (activeScale ⊤ N) =
      (3 : ℝ)^(2*N) / ahom M (activeScale (N : WithTop ℕ) N)
    have htop : activeScale (⊤ : WithTop ℕ) N = N := by
      simp only [activeScale, WithTop.untopD_top, min_self]
    have hfinite : activeScale (N : WithTop ℕ) N = N :=
      (activeScale_coe N N).trans (min_self N)
    rw [htop, hfinite]
  simpa only [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale_eq, e, physicalCoordinates_apply,
    zero_add, hclock] using hrow

/-- Equality of the literal annealed measures follows from the actual two
coupling marginals and the same-law attachment, for any characterized family. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_top_annealed_attachment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN)
    (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d))
    (hX : ∀ L, IsMarkovKernel (X L))
    (hphysical : aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsPhysicalFamily M X) (N : ℕ)
    (x : SpatialCoordinates d) :
    aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence M X hX true id (fun _ => x) N =
      aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedRow M (KN N) (hKN N) x := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro B hB
  have hm : Measurable (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M N) := by
    rw [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale_eq]
    exact ContinuousPath.measurable_rescale _ _
  let left := ((X ⊤).comap (fun omega => (omega,(3 : ℝ)^N • x))
    (measurable_id.prodMk measurable_const)).map (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M N)
  let right := (KN N).comap (fun xi => (xi,x)) (measurable_id.prodMk measurable_const)
  change ((aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure.bind left) B =
    ((chaosSampleLaw M).toMeasure.bind right) B
  rw [Measure.bind_apply hB left.aemeasurable, Measure.bind_apply hB right.aemeasurable]
  change (∫⁻ omega, left omega B ∂(physicalLaw M).toMeasure) = _
  rw [← (physicalEnvironment_preserving M N 0).lintegral_comp
      (Kernel.measurable_coe left hB),
    ← (bilateralEnvironment_preserving M).lintegral_comp (Kernel.measurable_coe right hB)]
  apply lintegral_congr_ae
  filter_upwards [aux_lim_cor_paths_inlined_lim_thm_nonbrownian_top_path_attachment M H hH PN KN hKN hin X hX hphysical N]
    with eta h
  dsimp only [left, right]
  rw [Kernel.map_apply _ hm, Kernel.comap_apply, Kernel.comap_apply, h x]

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_44

/- Inlined proved source application: SubdiffusiveProcess.Section10.PathsLimitingLawAttachment. -/
noncomputable section aux_lim_cor_paths_inline_45

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10.PhysicalAttachment
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Section10

/-- The actual limiting kernel's annealed row is an untruncated physical
annealed limit. The common native coupling identifies every top prelimit row;
the source quenched convergence then identifies its limit. This application
has no exit or moment premise and needs no disorder restriction. -/
theorem aux_lim_cor_paths_paths_limitingLawAttachment {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) : _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_cor_paths_LimitingLawAttachment M := by
  intro H hH PN KN hKN hin K hK hconv x
  obtain ⟨X, hX, hphysical⟩ := exists_physical_family M
  let P := _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedRow M K hK x
  refine ⟨X, hX, hphysical, true, id, strictMono_id, fun _ => x,
    tendsto_const_nhds, P, ?_, rfl⟩
  have ht := _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_thm_nonbrownian_quenched_annealed_tendsto
    M KN hKN K hK hconv x
  have hrows : _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence M X hX true id
      (fun _ => x) = fun N => _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedRow M (KN N) (hKN N) x := by
    funext N
    exact _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_thm_nonbrownian_top_annealed_attachment
      M H hH PN KN hKN hin X hX hphysical N x
  have hphysicalLimit : Tendsto
      (_root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence M X hX true id (fun _ => x))
      atTop (𝓝 P) := by
    rw [hrows]
    exact ht
  change _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsAnnealedLimit M X true id (fun _ => x) P
  intro G
  simpa only [_root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedSequence_integral] using
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hphysicalLimit G

/-- Complete application to the entire reviewed paths conclusion. The actual
random first-mean bank is the sole producer input; physical-to-canonical law
identification, weak passage, endpoint behavior and maximal moments are proved
by the consumed suppliers. This internal theorem does not assert the root. -/
theorem aux_lim_cor_paths_cor_paths_of_random_mean_bank {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (hbank : _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_cor_exit_moments_RandomMeanBank d) :
    _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_cor_paths_Conclusion d := by
  have : NeZero d := ⟨by omega⟩
  exact _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_cor_paths_of_mean_bank_and_attachment hd hbank 1 (by norm_num)
    (fun M _ => aux_lim_cor_paths_paths_limitingLawAttachment M)

end SubdiffusiveProcess.Section10
end aux_lim_cor_paths_inline_45

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimThmNonbrownianAssembly. -/
noncomputable section aux_lim_cor_paths_inline_46

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10.PhysicalLocalTransport SubdiffusiveProcess.Section10.PhysicalAttachment
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Paper

/-- INTERNAL CONDITIONAL ASSEMBLY, not the source theorem. Its only outstanding
premise is the actual upper mean-exit first display (with the named P3 proposition). Every later application, physical/bilateral
attachment, barycentre and quenched conclusion is discharged here. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_from_physical_mean_bank
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (hmean : ∃ deltaMean : ℝ, 0 < deltaMean ∧
      ∀ M : GMCModel d, M.delta ≤ deltaMean →
      ∃ Cmean : ℝ, 0 < Cmean ∧
        ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsPhysicalFamily M X →
          ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
            (∫⁻ omega, (⨆ y ∈ Metric.ball z ((3 : ℝ)^m/2),
              ∫⁻ w, ContinuousPath.exitTime (Metric.ball z ((3 : ℝ)^m/2)) w ∂X L (omega,y))
              ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure) ≤
                ENNReal.ofReal (Cmean * (rawClock M L m : ℝ))) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ eta Cdecay : ℝ, 0 < eta ∧ 0 < Cdecay ∧
        (d = 2 → eta = tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          ahom M m / ahom M l ≤ Cdecay * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) ∧
      ∃ C : ℝ, 0 < C ∧
        (∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsPhysicalFamily M X →
          ∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
          ∀ (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d),
            Tendsto xs atTop (𝓝 x) →
          ∀ P : ProbabilityMeasure (DiffusionPath d),
            aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsAnnealedLimit M X untruncated phi xs P →
            (∀ k : ℕ, (∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w ∂(P : Measure (DiffusionPath d))) ≤
              ENNReal.ofReal (C * (3 : ℝ) ^ (-((2 + eta) * (k : ℝ))))) ∧
            (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q →
              (P : Measure (DiffusionPath d)) ⟂ₘ Q) ∧
            (∀ (Θ : Type) [MeasurableSpace Θ] (nu : Measure Θ) [IsProbabilityMeasure nu]
                (kappa : Kernel Θ (DiffusionPath d)), (∀ θ, lim_brownian_law (kappa θ)) →
              (P : Measure (DiffusionPath d)) ⟂ₘ nu.bind kappa)) ∧
        (∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsPhysicalFamily M X →
          ∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
          ∀ (xs : ℕ → SpatialCoordinates d),
          ∀ Lam : Measure (ProbabilityMeasure (DiffusionPath d)), IsProbabilityMeasure Lam →
            (∀ G : BoundedContinuousFunction (DiffusionPath d) ℝ,
              Tendsto (fun n => ∫ omega,
                (∫ w, G (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_rescale M (phi n) w)
                  ∂X (aux_lim_cor_paths_inlined_lim_thm_nonbrownian_familyCutoff untruncated (phi n))
                    (omega, (3 : ℝ) ^ (phi n) • xs n))
                ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure) atTop
                  (𝓝 (∫ P : ProbabilityMeasure (DiffusionPath d),
                    (∫ w, G w ∂(P : Measure (DiffusionPath d))) ∂Lam))) →
            ∀ᵐ (P : ProbabilityMeasure (DiffusionPath d)) ∂Lam,
              (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q →
                (P : Measure (DiffusionPath d)) ⟂ₘ Q) ∧
              (∀ (Θ : Type) [MeasurableSpace Θ] (nu : Measure Θ) [IsProbabilityMeasure nu]
                  (kappa : Kernel Θ (DiffusionPath d)), (∀ θ, lim_brownian_law (kappa θ)) →
                (P : Measure (DiffusionPath d)) ⟂ₘ nu.bind kappa)) ∧
        (∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
          ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
            (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
            (hKN : ∀ N, IsMarkovKernel (KN N)), in_crossing M H PN KN →
          ∀ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
            (hK : IsMarkovKernel K), aux_lim_cor_paths_inlined_lim_thm_nonbrownian_QuenchedConv M KN hKN K hK →
          ∀ x : SpatialCoordinates d,
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q → K (omega, x) ⟂ₘ Q) ∧
              ∀ (Θ : Type) [MeasurableSpace Θ] (nu : Measure Θ) [IsProbabilityMeasure nu]
                (kappa : Kernel Θ (DiffusionPath d)), (∀ θ, lim_brownian_law (kappa θ)) →
                K (omega, x) ⟂ₘ nu.bind kappa) := by
  obtain ⟨deltaMean, hdeltaMean, hmeans⟩ := hmean
  obtain ⟨deltaDecay, hdeltaDecay, hdecays⟩ := SubdiffusiveProcess.Section10.strict_decay hd
  refine ⟨min deltaMean deltaDecay, lt_min hdeltaMean hdeltaDecay, ?_⟩
  intro M hM
  obtain ⟨Cmean, hCmean, hbank⟩ := hmeans M (hM.trans (min_le_left _ _))
  obtain ⟨Cdecay, eta, c, hCdecay, heta, _hc, hplanar, hdec, _hclock, _hcutoff⟩ :=
    hdecays M (hM.trans (min_le_right _ _))
  refine ⟨eta, Cdecay, heta, hCdecay, hplanar, hdec,
    Cmean*Cdecay, mul_pos hCmean hCdecay, ?_, ?_, ?_⟩
  · intro X hX hphysical untruncated phi hphi xs _x _hxs P hlimit
    have hm := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_mean_of_physical_bank M X hX hphysical
      Cmean Cdecay eta hCmean.le hdec (hbank X hX hphysical)
      untruncated phi hphi xs P hlimit
    have hs := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_singular_of_mean
      (P : Measure (DiffusionPath d)) (Cmean*Cdecay) eta heta hm
    refine ⟨hm, hs.1, ?_⟩
    intro Θ _inst nu _hnu kappa hB
    exact hs.2 Θ nu kappa hB
  · intro X hX hphysical untruncated phi hphi xs Lam hLam hlimit
    let := hLam
    have ht := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_barycentre_tendsto M X hX untruncated phi xs Lam hlimit
    have hm := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_mean_of_prelimit _ _ ht (Cmean*Cdecay) eta (by
      intro k
      filter_upwards [eventually_ge_atTop k] with n hn
      exact aux_lim_cor_paths_inlined_lim_thm_nonbrownian_prelimit_exit_bound M X hX hphysical
        Cmean Cdecay eta hCmean.le hdec (hbank X hX hphysical)
        untruncated phi xs k n (hn.trans (hphi.id_le n)))
    have hs := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_random_singular_of_barycentre_mean
      Lam (Cmean*Cdecay) eta heta hm
    filter_upwards [hs] with P hP
    refine ⟨hP.1, ?_⟩
    intro Θ _inst nu _hnu kappa hB
    exact hP.2 Θ nu kappa hB
  · intro H hH PN KN hKN hin K hK hconv x
    let : NeZero d := ⟨by omega⟩
    obtain ⟨X, hX, hphysical⟩ := exists_physical_family M
    have hpre : ∀ k : ℕ, ∀ᶠ N in atTop,
        (∫⁻ w, aux_lim_cor_paths_inlined_lim_thm_nonbrownian_smallExit k w
          ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_annealedRow M (KN N) (hKN N) x :
            Measure (DiffusionPath d))) ≤
          ENNReal.ofReal ((Cmean*Cdecay) * (3 : ℝ)^(-((2+eta)*(k : ℝ)))) := by
      intro k
      filter_upwards [eventually_ge_atTop k] with N hN
      rw [← aux_lim_cor_paths_inlined_lim_thm_nonbrownian_top_annealed_attachment
        M H hH PN KN hKN hin X hX hphysical N x]
      exact aux_lim_cor_paths_inlined_lim_thm_nonbrownian_prelimit_exit_bound M X hX hphysical
        Cmean Cdecay eta hCmean.le hdec (hbank X hX hphysical)
        true id (fun _ => x) k N hN
    have hs := aux_lim_cor_paths_inlined_lim_thm_nonbrownian_quenched_singular_of_prelimit M KN hKN K hK hconv
      x (Cmean*Cdecay) eta heta hpre
    filter_upwards [hs] with omega hsing
    refine ⟨hsing.1, ?_⟩
    intro Θ _inst nu _hnu kappa hB
    exact hsing.2 Θ nu kappa hB

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_46

/- Inlined proved source application: SubdiffusiveProcess.Paper.LimThmNonbrownianMeanInterface. -/
noncomputable section aux_lim_cor_paths_inline_47

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Paper

/-- Literal compatibility of the frozen first-display clock with the actual
raw clock, including L=0, top and scales beyond a finite cutoff. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_mean_clock_eq {d : ℕ} (M : GMCModel d)
    (L : WithTop ℕ) (m : ℕ) :
    aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m = (rawClock M L m : ℝ) := by
  cases L using WithTop.recTopCoe with
  | top => simp only [aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime, rawClock, activeScale, WithTop.untopD_top, min_self] ; rfl
  | coe l => simp only [aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime, rawClock, activeScale, WithTop.untopD_coe] ; rfl

/-- Convert exactly the reviewed mean-exit first display into the single
remaining input of the nonbrownian assembly. The producer is supplied
explicitly; this theorem does not assume the lim_lem_mean_exit source wrapper. -/
theorem aux_lim_cor_paths_inlined_lim_thm_nonbrownian_mean_bank_of_first_display
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hdisplay : ∃ deltaMean : ℝ, 0 < deltaMean ∧
      ∀ M : GMCModel d, M.delta ≤ deltaMean →
      ∃ Cmean : ℝ, 0 < Cmean ∧
        ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_inlined_lim_lem_mean_exit_IsPhysicalFamily M X →
          ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
            (∫⁻ omega, (⨆ y ∈ aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube z (m : ℤ),
              aux_lim_cor_paths_inlined_lim_lem_mean_exit_exitMoment (X L (omega,y))
                (aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube z (m : ℤ)) 1)
              ∂(aux_lim_cor_paths_inlined_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤
                ENNReal.ofReal (Cmean * aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m)) :
    ∃ deltaMean : ℝ, 0 < deltaMean ∧
      ∀ M : GMCModel d, M.delta ≤ deltaMean →
      ∃ Cmean : ℝ, 0 < Cmean ∧
        ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_inlined_lim_thm_nonbrownian_IsPhysicalFamily M X →
          ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
            (∫⁻ omega, (⨆ y ∈ Metric.ball z ((3 : ℝ)^m/2),
              ∫⁻ w, ContinuousPath.exitTime (Metric.ball z ((3 : ℝ)^m/2)) w ∂X L (omega,y))
              ∂(aux_lim_cor_paths_inlined_lim_thm_nonbrownian_physicalLaw M).toMeasure) ≤
                ENNReal.ofReal (Cmean * (rawClock M L m : ℝ)) := by
  obtain ⟨deltaMean, hdeltaMean, hmodels⟩ := hdisplay
  refine ⟨deltaMean, hdeltaMean, ?_⟩
  intro M hM
  obtain ⟨Cmean, hCmean, hbank⟩ := hmodels M hM
  refine ⟨Cmean, hCmean, ?_⟩
  intro X hX hphysical L m z
  have h := hbank X hX hphysical L m z
  simpa only [aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube, zpow_natCast,
    aux_lim_cor_paths_inlined_lim_lem_mean_exit_exitMoment, ENNReal.rpow_one,
    aux_lim_cor_paths_inlined_lim_thm_nonbrownian_mean_clock_eq] using! h

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_inline_47

/- Inlined proved source application: SubdiffusiveProcess.Section10.PathsUpperMeanConsumer. -/
noncomputable section aux_lim_cor_paths_inline_48

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10.EndpointPaths
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Section10

/-- The first display of the reviewed mean-exit root, at its literal physical
family, centered cubes, first exit moments and finite/top local clocks.
This producer boundary has no powered-moment or path-behavior premise. -/
def aux_lim_cor_paths_PhysicalUpperMeanExitDisplay (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] : Prop :=
  ∃ deltaMean : ℝ, 0 < deltaMean ∧
    ∀ M : GMCModel d, M.delta ≤ deltaMean →
    ∃ Cmean : ℝ, 0 < Cmean ∧
      ∀ X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d),
        (∀ L, IsMarkovKernel (X L)) → _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_lem_mean_exit_IsPhysicalFamily M X →
        ∀ (L : WithTop ℕ) (m : ℕ) (z : SpatialCoordinates d),
          (∫⁻ omega, (⨆ y ∈ _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube z (m : ℤ),
            _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_lem_mean_exit_exitMoment (X L (omega,y))
              (_root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_lem_mean_exit_cube z (m : ℤ)) 1)
            ∂(_root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_lem_mean_exit_physicalLaw M).toMeasure) ≤
              ENNReal.ofReal (Cmean * _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_lem_mean_exit_localTime M L m)

/-- The entire frozen paths conclusion follows already from the averaged
upper first-mean display. Strict decay fixes the same eta before epsilon and
all positive maximal moment orders. The actual top attachment supplies the
quenched clause, so no lower exit-mean or separate law-identification input is
needed. This conditional application leaves the source producer explicit. -/
theorem aux_lim_cor_paths_cor_paths_of_upper_mean_display {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (hdisplay : aux_lim_cor_paths_PhysicalUpperMeanExitDisplay d) :
    _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_cor_paths_Conclusion d := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨deltaMean, hdeltaMean, hmeans⟩ :=
    _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_thm_nonbrownian_mean_bank_of_first_display hdisplay
  obtain ⟨deltaDecay, hdeltaDecay, hdecays⟩ := strict_decay hd
  refine ⟨min deltaMean deltaDecay, lt_min hdeltaMean hdeltaDecay, ?_⟩
  intro M hM
  obtain ⟨Cmean, hCmean, hbank⟩ := hmeans M (hM.trans (min_le_left _ _))
  obtain ⟨Cdecay, eta, _c, hCdecay, heta, _hc, hplanar, hdec, _hclock, _hcutoff⟩ :=
    hdecays M (hM.trans (min_le_right _ _))
  have hmean : ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d)
      (DiffusionPath d)) (hX : ∀ L, IsMarkovKernel (X L)),
      _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_IsPhysicalFamily M X →
      ∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
      ∀ (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d), Tendsto xs atTop (𝓝 x) →
      ∀ P : ProbabilityMeasure (DiffusionPath d),
        _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_IsAnnealedLimit M X untruncated phi xs P →
        ∀ k : ℕ, (∫⁻ w, _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_smallExit k w ∂(P : Measure (DiffusionPath d))) ≤
          ENNReal.ofReal ((Cmean*Cdecay) * (3 : ℝ)^(-((2+eta)*(k : ℝ)))) := by
    intro X hX hf untruncated phi hphi xs _x _hxs P hP
    exact _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_thm_nonbrownian_mean_of_physical_bank M X hX hf
      Cmean Cdecay eta hCmean.le hdec (hbank X hX hf)
      untruncated phi hphi xs P hP
  refine ⟨eta, Cdecay, heta, hCdecay, hplanar, hdec, ?_, ?_⟩
  · intro epsilon hepsilon
    refine ⟨oscillationConstant eta epsilon, oscillationConstant_pos eta epsilon heta, ?_, ?_⟩
    · intro X hX hf untruncated phi hphi xs x hxs P hP
      exact (_root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_cor_paths_smallTime_of_mean_decay P (Cmean*Cdecay) eta epsilon
        heta hepsilon (hmean X hX hf untruncated phi hphi xs x hxs P hP)).2
    · intro H hH PN KN hKN hcross K hK hconv x
      obtain ⟨X, hX, hf, untruncated, phi, hphi, xs, hxs, P, hP, hbar⟩ :=
        aux_lim_cor_paths_paths_limitingLawAttachment M H hH PN KN hKN hcross K hK hconv x
      have havg : ∀ k : ℕ,
          (∫⁻ omega, ∫⁻ w, _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_smallExit k w ∂K (omega,x)
            ∂(chaosSampleLaw M).toMeasure) ≤
              ENNReal.ofReal ((Cmean*Cdecay) * (3 : ℝ)^(-((2+eta)*(k : ℝ)))) := by
        intro k
        have hm := hmean X hX hf untruncated phi hphi xs x hxs P hP k
        have hmeas : Measurable (_root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_smallExit (d := d) k) := by
          simpa only [ENNReal.rpow_one] using!
            (ExitMomentPassage.smallExit_rpow_lsc k 1 (by norm_num)).measurable
        rw [hbar] at hm
        change (∫⁻ w, _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_smallExit k w
          ∂(chaosSampleLaw M).toMeasure.bind
            (K.comap (fun omega => (omega,x)) (measurable_id.prodMk measurable_const))) ≤ _ at hm
        rw [Measure.lintegral_bind (Kernel.aemeasurable _) hmeas.aemeasurable] at hm
        exact hm
      exact _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_cor_paths_quenched_of_averaged_mean M K hK x (Cmean*Cdecay)
        eta epsilon heta hepsilon havg
  · intro p hp
    obtain ⟨cp, hcp, hmax⟩ := _root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_cor_paths_maximal_lower_of_mean_decay
      (d := d) (Cmean*Cdecay) eta p heta hp
    refine ⟨cp, hcp, ?_⟩
    intro X hX hf untruncated phi hphi xs x hxs P hP
    exact hmax P (hmean X hX hf untruncated phi hphi xs x hxs P hP)

end SubdiffusiveProcess.Section10
end aux_lim_cor_paths_inline_48

/- Inlined proved source application: SubdiffusiveProcess.Section10.CorPathsP3. -/
noncomputable section aux_lim_cor_paths_inline_49

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Paper
open scoped ENNReal NNReal ProbabilityTheory
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
namespace SubdiffusiveProcess.Section10

/-- The full reviewed paths conclusion, conditional only on the
named P3 proposition. All model, physical upper mean, actual law attachment,
endpoint and positive maximal moment inputs are discharged. The specified
unconditional source principal itself is left unchanged. -/
theorem aux_lim_cor_paths_lim_cor_paths_of_P3
    (hP3 : CompactMartingaleKilledDensityInput)
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ eta Cdecay : ℝ, 0 < eta ∧ 0 < Cdecay ∧
        (d = 2 → eta = tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          ahom M m / ahom M l ≤ Cdecay * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) ∧
        (∀ epsilon : ℝ, 0 < epsilon → ∃ cepsilon : ℝ, 0 < cepsilon ∧
          (∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
            (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_IsPhysicalFamily M X →
            ∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
            ∀ (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d),
              Tendsto xs atTop (𝓝 x) →
            ∀ P : ProbabilityMeasure (DiffusionPath d),
              aux_lim_cor_paths_IsAnnealedLimit M X untruncated phi xs P →
              ∀ᵐ w ∂(P : Measure (DiffusionPath d)),
                aux_lim_cor_paths_SmallTime eta cepsilon epsilon w) ∧
          (∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
            ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
              (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
              (hKN : ∀ N, IsMarkovKernel (KN N)), in_crossing M H PN KN →
            ∀ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
              (hK : IsMarkovKernel K), aux_lim_cor_paths_QuenchedConv M KN hKN K hK →
            ∀ x : SpatialCoordinates d,
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                ∀ᵐ w ∂K (omega, x), aux_lim_cor_paths_SmallTime eta cepsilon epsilon w)) ∧
        (∀ p : ℝ, 0 < p → ∃ cp : ℝ, 0 < cp ∧
          ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
            (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_IsPhysicalFamily M X →
            ∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
            ∀ (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d),
              Tendsto xs atTop (𝓝 x) →
            ∀ P : ProbabilityMeasure (DiffusionPath d),
              aux_lim_cor_paths_IsAnnealedLimit M X untruncated phi xs P →
              ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
                ENNReal.ofReal (cp * (t : ℝ) ^ (p / (2 + eta))) ≤
                  ∫⁻ w, ENNReal.ofReal (aux_lim_cor_paths_maximum t w ^ p)
                    ∂(P : Measure (DiffusionPath d))) := by
  exact aux_lim_cor_paths_cor_paths_of_upper_mean_display hd
    (_root_.SubdiffusiveProcess.Paper.aux_lim_cor_paths_inlined_lim_lem_mean_exit_averaged_upper
      (smoothReversibleKilledDensitySupplier_of_compactMartingaleDensity hP3) hd)

end SubdiffusiveProcess.Section10
end aux_lim_cor_paths_inline_49

/- Inlined proved source application: SubdiffusiveProcess.Section10.CorPathsReversible. -/
noncomputable section aux_lim_cor_paths_inline_50

/-! Exact source application with the reversible density input that is being
proved. Existing completed bank/assembly proofs are consumed directly;
no arbitrary-drift density statement is inferred. -/

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section10.PhysicalAttachment SubdiffusiveProcess.Section10.PhysicalLocalTransport _root_.SubdiffusiveProcess.Paper
open scoped ENNReal NNReal ProbabilityTheory
namespace SubdiffusiveProcess.Section10

/-- Full frozen source conclusion from the exact reversible supplier. -/
theorem aux_lim_cor_paths_lim_cor_paths_of_reversibleDensity
    (hDensity : SmoothReversibleKilledDensitySupplier)
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ eta Cdecay : ℝ, 0 < eta ∧ 0 < Cdecay ∧
        (d = 2 → eta = tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          ahom M m / ahom M l ≤ Cdecay * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) ∧
        (∀ epsilon : ℝ, 0 < epsilon → ∃ cepsilon : ℝ, 0 < cepsilon ∧
          (∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
            (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_IsPhysicalFamily M X →
            ∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
            ∀ (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d),
              Tendsto xs atTop (𝓝 x) →
            ∀ P : ProbabilityMeasure (DiffusionPath d),
              aux_lim_cor_paths_IsAnnealedLimit M X untruncated phi xs P →
              ∀ᵐ w ∂(P : Measure (DiffusionPath d)),
                aux_lim_cor_paths_SmallTime eta cepsilon epsilon w) ∧
          (∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
            ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
              (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
              (hKN : ∀ N, IsMarkovKernel (KN N)), in_crossing M H PN KN →
            ∀ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
              (hK : IsMarkovKernel K), aux_lim_cor_paths_QuenchedConv M KN hKN K hK →
            ∀ x : SpatialCoordinates d,
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                ∀ᵐ w ∂K (omega, x), aux_lim_cor_paths_SmallTime eta cepsilon epsilon w)) ∧
        (∀ p : ℝ, 0 < p → ∃ cp : ℝ, 0 < cp ∧
          ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
            (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_IsPhysicalFamily M X →
            ∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
            ∀ (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d),
              Tendsto xs atTop (𝓝 x) →
            ∀ P : ProbabilityMeasure (DiffusionPath d),
              aux_lim_cor_paths_IsAnnealedLimit M X untruncated phi xs P →
              ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
                ENNReal.ofReal (cp * (t : ℝ) ^ (p / (2 + eta))) ≤
                  ∫⁻ w, ENNReal.ofReal (aux_lim_cor_paths_maximum t w ^ p)
                    ∂(P : Measure (DiffusionPath d))) := by
  exact aux_lim_cor_paths_cor_paths_of_upper_mean_display hd
    (aux_lim_cor_paths_inlined_lim_lem_mean_exit_averaged_upper hDensity hd)

end SubdiffusiveProcess.Section10
end aux_lim_cor_paths_inline_50

noncomputable section aux_lim_cor_paths_principal

open Filter MeasureTheory ProbabilityTheory Topology Set Asymptotics MarkovProcess SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal



namespace SubdiffusiveProcess.Paper

theorem lim_cor_paths
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ eta Cdecay : ℝ, 0 < eta ∧ 0 < Cdecay ∧
        (d = 2 → eta = tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          ahom M m / ahom M l ≤ Cdecay * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) ∧
        (∀ epsilon : ℝ, 0 < epsilon → ∃ cepsilon : ℝ, 0 < cepsilon ∧
          (∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
            (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_IsPhysicalFamily M X →
            ∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
            ∀ (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d),
              Tendsto xs atTop (𝓝 x) →
            ∀ P : ProbabilityMeasure (DiffusionPath d),
              aux_lim_cor_paths_IsAnnealedLimit M X untruncated phi xs P →
              ∀ᵐ w ∂(P : Measure (DiffusionPath d)),
                aux_lim_cor_paths_SmallTime eta cepsilon epsilon w) ∧
          (∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
            ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
              (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
              (hKN : ∀ N, IsMarkovKernel (KN N)), in_crossing M H PN KN →
            ∀ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
              (hK : IsMarkovKernel K), aux_lim_cor_paths_QuenchedConv M KN hKN K hK →
            ∀ x : SpatialCoordinates d,
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                ∀ᵐ w ∂K (omega, x), aux_lim_cor_paths_SmallTime eta cepsilon epsilon w)) ∧
        (∀ p : ℝ, 0 < p → ∃ cp : ℝ, 0 < cp ∧
          ∀ (X : WithTop ℕ → Kernel (AnchoredC11Sample d × SpatialCoordinates d) (DiffusionPath d)),
            (∀ L, IsMarkovKernel (X L)) → aux_lim_cor_paths_IsPhysicalFamily M X →
            ∀ (untruncated : Bool) (phi : ℕ → ℕ), StrictMono phi →
            ∀ (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d),
              Tendsto xs atTop (𝓝 x) →
            ∀ P : ProbabilityMeasure (DiffusionPath d),
              aux_lim_cor_paths_IsAnnealedLimit M X untruncated phi xs P →
              ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
                ENNReal.ofReal (cp * (t : ℝ) ^ (p / (2 + eta))) ≤
                  ∫⁻ w, ENNReal.ofReal (aux_lim_cor_paths_maximum t w ^ p)
                    ∂(P : Measure (DiffusionPath d))) := by
  exact SubdiffusiveProcess.Section10.aux_lim_cor_paths_lim_cor_paths_of_reversibleDensity lim_killed_density_continuity hd

end SubdiffusiveProcess.Paper
end aux_lim_cor_paths_principal
