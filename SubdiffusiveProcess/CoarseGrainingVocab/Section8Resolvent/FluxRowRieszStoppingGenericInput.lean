module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszStoppingGeneric
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszPartitionEndpoint
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFluxCoefficient
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderAssembly

@[expose] public section

/-!
# Flux-row analytic input on a generic repaired stopping carrier

This is the carrier-polymorphic replacement for the raw-lattice abbreviation
`FluxRowRieszStoppingInput`.  It applies unchanged to a carrier consisting of
a selected cube paired with a finite half-grid offset.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model _root_.SubdiffusiveProcess.Section8
open scoped BigOperators

noncomputable section

variable {d : ℕ} {Cell : Type*} [Encodable Cell] [DecidableEq Cell]
variable {failure : TriadicCube d → Set (PotentialSample d)}
variable {omega : PotentialSample d}

/-- Analytic flux-row hypotheses on a generic repaired stopping family. -/
abbrev FluxRowRieszStoppingInputGeneric
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega)
    (R sigma : ℝ) (F : Vec d → Vec d) :=
  FluxRowRieszPartitionInput d Cell H.toPartition R sigma F

/-- Sphere-wise cell-price summation on a generic repaired carrier. -/
def fluxRowRieszStoppingCoefficientBudgetGeneric
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega)
    (localNegative : Fin d → Cell → ℝ) (K : ℝ)
    (hlocNonneg : ∀ i q, 0 ≤ localNegative i q)
    (cellPrice : Fin d → Cell → ℝ)
    (hpriceNonneg : ∀ i q, 0 ≤ cellPrice i q)
    (hlocal : ∀ i q,
      H.toPartition.cellVolume q * localNegative i q ^ 2 ≤ cellPrice i q)
    (levelCells : ℕ → Finset Cell) (level : Cell → ℕ)
    (hlevel : ∀ j q, q ∈ levelCells j ↔ level q = j)
    (shellPrice : Fin d → ℕ → ℝ)
    (hshellSummable : ∀ i, Summable (shellPrice i))
    (hshell : ∀ i j,
      ∑ q ∈ levelCells j, cellPrice i q ≤ shellPrice i j) :
    FluxRowRieszCoefficientBudget H.toPartition localNegative K :=
  fluxRowRieszCoefficientBudget_of_stoppingLevel_sums H.toPartition
    localNegative K hlocNonneg cellPrice hpriceNonneg hlocal levelCells level
    hlevel shellPrice hshellSummable hshell

/-- The generic repaired stopping hypotheses produces the Fourier representative
with its summed per-cell price. -/
theorem FluxRowRieszStoppingInputGeneric.exists_fluxHat_le_sum_tsum_cellPrice
    {H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega}
    {R sigma : ℝ} {F : Vec d → Vec d}
    (A : FluxRowRieszStoppingInputGeneric H R sigma F) (hR : 0 < R) :
    ∃ fluxHat : Vec d → Fin d → ℂ,
      IsFourierRepresentative F fluxHat ∧
      massiveNegativeSobolevNormSq R sigma fluxHat ≤
        ∑ i, 2 * ((H.toPartition.overlapCount : ℝ) * A.fourierComparison) *
          ∑' q, A.coefficientBudget.cellPrice i q :=
  FluxRowRieszPartitionInput.exists_fluxHat_le_sum_tsum_cellPrice A hR

/-- Exact whole-space flux clause on a generic repaired stopping carrier. -/
theorem FluxRowRieszStoppingInputGeneric.exists_wholeSpaceFluxHat
    (M : GMCModel d) (L : ℕ) {t : ℝ} {f : Vec d → ℝ}
    (u : WholeSpaceDivergenceResolventSolution (aCutoff M L omega) t f)
    {R sigma CSigma : ℝ} (Z : PotentialSample d → ℝ)
    (hscale : (3 : ℝ) ^ L ≤ R)
    {H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega}
    (A : FluxRowRieszStoppingInputGeneric H R sigma
      (fun x ↦ (aCutoff M L omega x - ahom M L) • u.grad x))
    (hcellPrice :
      (∑ i, 2 * ((H.toPartition.overlapCount : ℝ) * A.fourierComparison) *
          ∑' q, A.coefficientBudget.cellPrice i q) ≤
        CSigma * Z omega * ahom M L * t⁻¹ * R ^ (2 * sigma) *
          ∫ x, f x ^ 2 ∂volume) :
    ∃ fluxHat : Vec d → Fin d → ℂ,
      IsFourierRepresentative
        (fun x ↦ (aCutoff M L omega x - ahom M L) • u.grad x) fluxHat ∧
      massiveNegativeSobolevNormSq R sigma fluxHat ≤
        CSigma * Z omega * ahom M L * t⁻¹ * R ^ (2 * sigma) *
          ∫ x, f x ^ 2 ∂volume := by
  have hR : 0 < R := (pow_pos (by norm_num : (0 : ℝ) < 3) L).trans_le hscale
  obtain ⟨fluxHat, hrepresentative, hbound⟩ :=
    A.exists_fluxHat_le_sum_tsum_cellPrice hR
  exact ⟨fluxHat, hrepresentative, hbound.trans hcellPrice⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
