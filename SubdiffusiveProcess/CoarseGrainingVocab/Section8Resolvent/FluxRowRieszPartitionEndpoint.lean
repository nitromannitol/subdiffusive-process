import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszPartitionEnergy




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.Frozen.Section8
open scoped BigOperators ENNReal

noncomputable section

/-- Analytic data carried by a stopping partition for the whole-space flux
row.  The positive cell energies use the overlapping cubes, while physical
pairings use their disjoint ownership pieces. -/
structure FluxRowRieszPartitionInput
    (d : ℕ) (Cell : Type*) [DecidableEq Cell]
    (P : FluxRowRieszPartition d Cell) (R sigma : ℝ)
    (F : Vec d → Vec d) where
  testMem : ∀ phi : SchwartzMap (Vec d) ℂ,
    MemLp (phi : Vec d → ℂ) 2
      (volume.withDensity fun xi ↦ fluxRowMassiveTestDensity R sigma xi)
  functional : Fin d → SchwartzMap (Vec d) ℂ →ₗ[ℂ] ℂ
  physical_integrable : ∀ i phi,
    Integrable
      (fun x ↦ Complex.ofReal (F x i) * inverseFourierSchwartz phi x) volume
  functional_eq_integral : ∀ i phi,
    functional i phi =
      ∫ x, Complex.ofReal (F x i) * inverseFourierSchwartz phi x ∂volume
  massWeight : Cell → ℝ≥0∞
  globalMassWeight : ℝ≥0∞
  massWeight_le : ∀ q, massWeight q ≤ globalMassWeight
  kernel : SchwartzMap (Vec d) ℂ → Vec d × Vec d → ℝ≥0∞
  density : SchwartzMap (Vec d) ℂ → Vec d → ℝ≥0∞
  globalEnergy_ne_top : ∀ phi,
    fluxRowGlobalPositiveEnergy volume globalMassWeight
      (kernel phi) (density phi) ≠ ∞
  fourierComparison : ℝ
  fourierComparison_nonneg : 0 ≤ fourierComparison
  globalEnergy_le : ∀ phi,
    (fluxRowGlobalPositiveEnergy volume globalMassWeight
      (kernel phi) (density phi)).toReal ≤
      fourierComparison *
        ‖fluxRowWeightedTestToLp volume
          (fluxRowMassiveTestDensity R sigma) (fluxRowSchwartzTestLinear d)
          testMem phi‖ ^ 2
  localNegative : Fin d → Cell → ℝ
  localNegative_nonneg : ∀ i q, 0 ≤ localNegative i q
  pairing_re_le : ∀ i phi q,
    |(P.cellPairing F i phi q).re| ≤
      localNegative i q *
        P.localPositiveNorm massWeight (kernel phi) (density phi) q
  pairing_im_le : ∀ i phi q,
    |(P.cellPairing F i phi q).im| ≤
      localNegative i q *
        P.localPositiveNorm massWeight (kernel phi) (density phi) q
  coefficientBudget : FluxRowRieszCoefficientBudget P localNegative
    ((P.overlapCount : ℝ) * fourierComparison)

variable {d : ℕ} {Cell : Type*} [DecidableEq Cell]
variable {P : FluxRowRieszPartition d Cell} {R sigma : ℝ}
variable {F : Vec d → Vec d}



theorem FluxRowRieszPartitionInput.exists_fluxHat
    (A : FluxRowRieszPartitionInput d Cell P R sigma F) (hR : 0 < R) :
    ∃ fluxHat : Vec d → Fin d → ℂ,
      IsFourierRepresentative F fluxHat ∧
      massiveNegativeSobolevNormSq R sigma fluxHat ≤
        ∑ i, A.coefficientBudget.coefficient i ^ 2 := by
  let K : ℝ := (P.overlapCount : ℝ) * A.fourierComparison
  have hK : 0 ≤ K :=
    mul_nonneg (Nat.cast_nonneg _) A.fourierComparison_nonneg
  let localTest : SchwartzMap (Vec d) ℂ → Cell → ℝ := fun phi ↦
    P.localPositiveNorm A.massWeight (A.kernel phi) (A.density phi)
  let pairingRe : Fin d → SchwartzMap (Vec d) ℂ → Cell → ℝ :=
    fun i phi q ↦ (P.cellPairing F i phi q).re
  let pairingIm : Fin d → SchwartzMap (Vec d) ℂ → Cell → ℝ :=
    fun i phi q ↦ (P.cellPairing F i phi q).im
  refine exists_fluxHat_massiveNegativeSobolevNormSq_le_of_stopping_exhaustion
    hR F A.testMem A.functional ?_ P.cells P.cellVolume A.localNegative
      localTest pairingRe pairingIm K hK ?_ ?_ ?_ ?_ ?_ ?_
      A.coefficientBudget.coefficient
      A.coefficientBudget.coefficient_nonneg ?_ ?_
  · intro i phi
    exact ⟨A.physical_integrable i phi, A.functional_eq_integral i phi⟩
  · intro n q hq
    exact (P.cellVolume_pos q).le
  · intro n i q hq
    exact A.localNegative_nonneg i q
  · intro n phi q hq
    exact Real.sqrt_nonneg _
  · intro n i phi q hq
    exact A.pairing_re_le i phi q
  · intro n i phi q hq
    exact A.pairing_im_le i phi q
  · intro n phi
    change fluxRowLocalTestSumSq (P.cells n) P.cellVolume
      (P.localPositiveNorm A.massWeight (A.kernel phi) (A.density phi)) ≤ _
    exact P.localTestSumSq_le_weightedNormSq n A.massWeight
      A.globalMassWeight (fun q _ ↦ A.massWeight_le q) (A.kernel phi)
      (A.density phi) (A.globalEnergy_ne_top phi)
      ‖fluxRowWeightedTestToLp volume
        (fluxRowMassiveTestDensity R sigma) (fluxRowSchwartzTestLinear d)
        A.testMem phi‖ A.fourierComparison (A.globalEnergy_le phi)
  · intro n i
    exact A.coefficientBudget.sqrt_two_mul_localNegativeSumSq_le hK n i
  · intro i phi
    have hlimit := P.tendsto_mk_localizedPairing F i phi
      (A.physical_integrable i phi)
    change Tendsto
      (fun n ↦ Complex.mk
        (fluxRowLocalizedPairing (P.cells n) P.cellVolume
          (fun q ↦ (P.cellPairing F i phi q).re))
        (fluxRowLocalizedPairing (P.cells n) P.cellVolume
          (fun q ↦ (P.cellPairing F i phi q).im)))
      atTop (𝓝 (A.functional i phi))
    rw [A.functional_eq_integral i phi]
    exact hlimit

/-- The flux-row estimate written directly as the sum of all per-cell prices. -/
theorem FluxRowRieszPartitionInput.exists_fluxHat_le_sum_tsum_cellPrice
    (A : FluxRowRieszPartitionInput d Cell P R sigma F) (hR : 0 < R) :
    ∃ fluxHat : Vec d → Fin d → ℂ,
      IsFourierRepresentative F fluxHat ∧
      massiveNegativeSobolevNormSq R sigma fluxHat ≤
        ∑ i, 2 * ((P.overlapCount : ℝ) * A.fourierComparison) *
          ∑' q, A.coefficientBudget.cellPrice i q := by
  obtain ⟨fluxHat, hrepresentative, hbound⟩ := A.exists_fluxHat hR
  refine ⟨fluxHat, hrepresentative, hbound.trans_eq ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  exact A.coefficientBudget.coefficient_sq
    (mul_nonneg (Nat.cast_nonneg _) A.fourierComparison_nonneg) i

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
