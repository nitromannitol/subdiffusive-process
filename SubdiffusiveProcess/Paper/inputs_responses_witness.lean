module

public import SubdiffusiveProcess.Paper.paper_responses_bank
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.AnnularRecombination
public import SubdiffusiveProcess.Frozen.Section5.HomogenizedCoefficientReciprocalLower

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The original-field response package, with a bound chosen before the model
and one positive threshold covering every order in the fixed finite bank. -/
theorem inputs_responses_witness (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (qmax : ℝ) (hqmax : 1 ≤ qmax) :
    ∃ Cresp delta0 : ℝ, 0 < Cresp ∧ 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
        ∃ Rm : in_responses d M, Rm.C ≤ Cresp ∧
          ∀ xi : ℝ, 1 ≤ xi → xi ≤ qmax →
            xi ≤ Rm.C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨Cresp, hCresp, hbank⟩ := paper_responses_bank d hd
  refine ⟨Cresp, 1 / (Cresp * qmax + 1), hCresp, ?_, ?_⟩
  · positivity
  intro M hsmall
  choose defect hdefect hmax using fun m y om => aux_rbpf_defect_exists M m y om
  have horder : ∀ n m : ℕ, n < m → ahom M m ≤ ahom M n ∧
      ahom M n ≤ Real.exp (2 * tauSq M.P * ((m : ℝ) - n)) * ahom M m := by
    intro n m hnm
    have hb := Section6Cutoff.cutoff_ahom_ratio_ordering M m hnm.le
    rw [min_eq_left hnm.le, min_self] at hb
    constructor
    · simpa only [one_mul] using (le_div_iff₀ (ahom_pos M m)).mp hb.1
    · simpa only [Nat.cast_sub hnm.le] using (div_le_iff₀ (ahom_pos M m)).mp hb.2
  obtain ⟨Rm, hRC, _, horders⟩ := hbank M horder (ahom_le_one M)
    (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M)
    defect hdefect hmax
  refine ⟨Rm, hRC.le, ?_⟩
  intro xi _ hxi
  exact hxi.trans (horders qmax hqmax hsmall).2

end SubdiffusiveProcess.Paper

