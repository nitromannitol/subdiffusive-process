import SubdiffusiveProcess.Paper.in_crossing
import SubdiffusiveProcess.Paper.classical_prokhorov_sequential
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
import MarkovProcess.Lifetime.NonexplosiveTransport
import SubdiffusiveProcess.Paper.tight_lem_static
import SubdiffusiveProcess.Paper.tight_lem_subharmonic
import SubdiffusiveProcess.Section10.PhysicalTightnessBankAssembly
import SubdiffusiveProcess.Section10.PhysicalTightnessActualFiniteHead
import SubdiffusiveProcess.Section10.PhysicalTightnessChainingConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped CompactlySupported ENNReal NNReal BigOperators

noncomputable section

namespace Paper

section StaticBank
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section11
open SubdiffusiveProcess.Section10
open SubdiffusiveProcess.Section10.PhysicalTightness
open SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal NNReal

private theorem aux_tight_prop_tightness_local_fields_raw {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (m : ℕ) (z : Vec d) (omega : AnchoredC11Sample d) :
    let j : ℕ := match L with | ⊤ => m | (l : ℕ) => min m l
    localSpeed M L m z omega =
      (fun x => (coefficientAt M L omega z / aCutoff M j omega.val z)⁻¹ *
        coefficientAt M L omega (z + (3 : ℝ) ^ m • x)) ∧
    localCoefficient M L m z omega =
      (fun x => (ahom M j)⁻¹ * ((coefficientAt M L omega z / aCutoff M j omega.val z)⁻¹ *
        coefficientAt M L omega (z + (3 : ℝ) ^ m • x))) := by
  induction L using WithTop.recTopCoe with
  | top => constructor <;> funext x
           <;> simp only [localCoefficient, localSpeed, localFactor, activeScale,
             WithTop.untopD_top, min_self]
  | coe l => exact ⟨rfl, rfl⟩



theorem aux_tight_prop_tightness_local_analytic_bank_from_static {d : ℕ} :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
        ∃ K : AnchoredC11Sample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
          (∫⁻ omega, ENNReal.ofReal (K omega ^ (2 : ℝ))
            ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
          ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure,
            LocalExitCertificate (localCoefficient M L m z omega) (localSpeed M L m z omega) (K omega) := by
  obtain ⟨B, hB, hstatic⟩ := Paper.tight_lem_static d (0 : Vec d) 1 (by norm_num) 1
    (fun _ => 0) (fun _ => 1 / 3) (fun _ => 1) (by intro i; norm_num)
    (by intro i; exact subset_rfl)
  obtain ⟨dc, hdc, hcut⟩ := hstatic 2 (by norm_num)
  obtain ⟨dm, hdm, hmoser⟩ := Paper.tight_lem_subharmonic d (0 : Vec d) (1 / 3)
    0 (1 / 9) (by norm_num) (Metric.closedBall_subset_ball (by norm_num)) 2 (by norm_num)
  let D : ℝ := (1 / 3 : ℝ) ^ (-B) * (1 / 2 : ℝ) ^ ((d : ℝ) - 1 / 2)
  have hD : 0 ≤ D := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by norm_num) _)
  refine ⟨min dc dm, lt_min hdc hdm, ?_⟩
  intro M hM
  obtain ⟨Cc, hCc, hKc⟩ := hcut M (hM.trans (min_le_left _ _))
  obtain ⟨Cm, hCm, hKm⟩ := hmoser M (hM.trans (min_le_right _ _))
  refine ⟨2 * D ^ 2 * Cc + 2 * Cm, by positivity, ?_⟩
  apply local_analytic_bank_of_cutoff_and_moser M D Cc Cm hD hCc.le hCm.le
  · intro L m z
    obtain ⟨K, hK, hKone, hKint, hKbound⟩ := hKc L m z
    refine ⟨K, hK, hKone, hKint, ?_⟩
    filter_upwards [hKbound] with omega homega
    have hest : Paper.aux_tight_lem_static_estimates (localSpeed M L m z omega)
        (localCoefficient M L m z omega) 0 1 (fun _ : Fin 1 => 0)
          (fun _ => 1 / 3) (fun _ => 1) (K omega) B := by
      rw [(aux_tight_prop_tightness_local_fields_raw M L m z omega).1, (aux_tight_prop_tightness_local_fields_raw M L m z omega).2]
      exact homega
    have hchi := hest.2.2 0 0 0 (by norm_num)
    have houter : Metric.ball ((fun _ : Fin 1 => (0 : Vec d)) 0)
        (((1 - ((0 + 1 : ℕ) : ℝ) / 2 ^ (0 : ℕ)) * (fun _ : Fin 1 => (1 / 3 : ℝ)) 0 +
          (((0 + 1 : ℕ) : ℝ) / 2 ^ (0 : ℕ)) * (fun _ : Fin 1 => (1 : ℝ)) 0) / 2) =
        Metric.ball (0 : Vec d) (1 / 2) := by congr 1; norm_num
    rw [houter] at hchi
    norm_num at hchi
    obtain ⟨chi, hchi01, hchi1, -, henergy⟩ := hchi
    refine ⟨chi, hchi01, by simpa [Metric.mem_ball, dist_eq_norm] using hchi1, ?_⟩
    apply energy_le_of_lintegral_le (localCoefficient M L m z omega)
      (fun x => (mul_pos (inv_pos.mpr (ahom_pos M _)) (localSpeed_pos M L m z omega x)).le)
      _ chi.toH1Function (D * K omega) (mul_nonneg hD (zero_le_one.trans (hKone omega)))
    have hb := henergy (0 : Vec d) (1 / 2) (by norm_num) (by norm_num)
    rw [inter_self] at hb
    convert hb using 1
    dsimp only [D]
    congr 1
    ring
  · intro L m z
    obtain ⟨K, hK, hKone, hKint, hKbound⟩ := hKm L m z
    refine ⟨K, hK, hKone, hKint, ?_⟩
    filter_upwards [hKbound] with omega homega
    dsimp only at homega
    rw [show Metric.ball (0 : Vec d) ((1 / 3 : ℝ) / 2) = Metric.ball 0 (1 / 6) by
      congr 1; norm_num,
      show Metric.ball (0 : Vec d) ((1 / 9 : ℝ) / 2) = Metric.ball 0 (1 / 18) by
      congr 1; norm_num] at homega
    rw [(aux_tight_prop_tightness_local_fields_raw M L m z omega).1, (aux_tight_prop_tightness_local_fields_raw M L m z omega).2]
    exact homega


end StaticBank

/-- A closed, uniformly tight set of probability measures on a Polish space is compact
(Prokhorov, from `classical_prokhorov_sequential` and the pseudo-metrizability of the weak topology). -/
theorem aux_tight_prop_tightness_isCompact_of_closed_tight
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : Set (ProbabilityMeasure X)) (hS : IsClosed S)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ K : Set X, IsCompact K ∧
      ∀ P ∈ S, (P : Measure X) Kᶜ ≤ ENNReal.ofReal ε) : IsCompact S := by
  letI : PseudoMetricSpace (ProbabilityMeasure X) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric (ProbabilityMeasure X)
  rw [UniformSpace.isCompact_iff_isSeqCompact]
  intro mu hmu
  have htightSet : IsTightMeasureSet (Set.range (fun n => (mu n : Measure X))) := by
    rw [IsTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hεtop : ε = ⊤
    · refine ⟨∅, isCompact_empty, fun ν _ => ?_⟩
      rw [hεtop]; exact le_top
    · obtain ⟨K, hK, hKS⟩ := htight ε.toReal (ENNReal.toReal_pos hε.ne' hεtop)
      refine ⟨K, hK, ?_⟩
      rintro ν ⟨n, rfl⟩
      exact (hKS (mu n) (hmu n)).trans (by rw [ENNReal.ofReal_toReal hεtop])
  obtain ⟨seq, nu, hseq, hlim⟩ := Paper.classical_prokhorov_sequential mu htightSet
  exact ⟨nu, hS.mem_of_tendsto hlim (Eventually.of_forall fun n => hmu (seq n)), seq, hseq, hlim⟩



theorem tight_prop_tightness {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (Hf : BilateralField d → C(SpatialCoordinates d, ℝ)), (Hf = H ∨ Hf = fun _ => 0) →
      ∀ (LN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (Path d))
        (hLN : ∀ N, IsMarkovKernel (LN N)),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          LocalDiffusionData (cutoffCoefficient M Hf omega N) (cutoffSpeedDensity M Hf omega N)
            (Kernel.comap (LN N) (fun x => (omega, x)) measurable_prodMk_left)) →
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N, ∀ x : SpatialCoordinates d,
          ∀ᵐ w ∂(LN N (omega, x)), w.lifetime = ⊤) ∧
        ∀ B : Set (SpatialCoordinates d), IsCompact B →
          ∀ epsilon : ℝ, 0 < epsilon →
            ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
              (∀ N : ℕ, ∃ G : BilateralField d → ℝ≥0∞, Measurable G ∧
                (∀ omega, ∀ x ∈ B,
                  (LN N (omega, x)) (LifetimePath.ofContinuousPath '' Kset)ᶜ ≤ G omega) ∧
                ∫⁻ omega, G omega ∂(chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal epsilon) ∧
              ∀ eta : ℝ, 0 < eta →
                ∃ Keta : Set (ProbabilityMeasure (DiffusionPath d)), IsCompact Keta ∧
                  ∀ N : ℕ, (chaosSampleLaw M).toMeasure
                      {omega : BilateralField d | ∃ x ∈ B,
                        ∀ mu : ProbabilityMeasure (DiffusionPath d),
                          (mu : Measure (DiffusionPath d)) =
                            (LN N (omega, x)).map (LifetimePath.continuousPathExtension
                              (ContinuousMap.const ℝ≥0 (0 : SpatialCoordinates d))) →
                          mu ∉ Keta}
                    ≤ ENNReal.ofReal eta := by
  obtain ⟨delta0, hdelta0, hbank⟩ :=
    aux_tight_prop_tightness_local_analytic_bank_from_static (d := d)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hM H hH Hf hHf LN hLN hdata
  obtain ⟨C, hC, hlocal⟩ := hbank M hM
  have hhead := SubdiffusiveProcess.Section10.PhysicalTightness.actual_finite_head_modulus_of_local_analytic_bank
    M H hH Hf hHf LN hLN hdata C hC hlocal
  exact SubdiffusiveProcess.Section10.PhysicalTightness.actual_full_header_application_of_local_bank_and_finite_head
    hd delta0 hdelta0 M hM H hH Hf hHf LN hLN hdata C hC hlocal hhead

end Paper
