module

public import SubdiffusiveProcess.Paper.in_deterministic_good_scale_transfer
public import SubdiffusiveProcess.Paper.obl_ramp_threshold12_transfer
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodScaleSaturation

@[expose] public section

/-! A finite score `Z < 1` at scale `m` puts the sample in the threshold-12 good event at every
cutoff `L ≥ m`, and bounds the section-6 error of the cutoff field `a_L` by the score `Draw`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open Homogenization hiding Vec
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- The cutoff of the threshold-12 event is irrelevant at and above the scale. -/
theorem aux_lem_as_regularity_score_bridge_cutoff {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {L m : ℕ} (hmL : m ≤ L) (y : Vec d) (e s : ℝ) (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    g ∈ Paper.product_threshold_good_scale d M 12 (some m) m y e s ↔
      g ∈ Paper.product_threshold_good_scale d M 12 (some L) m y e s := by
  have h1 := goodResponse_some_iff_none_of_scale_le_cutoff M (le_refl m) y e s g
  have h2 := goodResponse_some_iff_none_of_scale_le_cutoff M hmL y e s g
  unfold Paper.product_threshold_good_scale
  simp only [Set.mem_setOf_eq]
  rw [h1, h2]



theorem lem_as_regularity_score_bridge (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s eps : ℝ),
      0 < s → s ≤ (1 / 32 : ℝ) → M.delta ≤ Real.sqrt s / 8 → eps < 1 →
      ∀ (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
        (goodEvt : ℕ → Vec d → Prop),
        Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt →
      ∀ (L m : ℕ), m ≤ L → ∀ (z : Vec d), Zsc m z < 1 → Dsc m z ≠ ⊤ →
        (∀ e : ℝ, eps ≤ e → e ≤ 1 →
          g ∈ Paper.product_threshold_good_scale d M 12 (some L) m z e s) ∧
        section6HomogenizationError M s L m g z ≤
          C * (2 * (s⁻¹ * M.delta ^ 2) + eps ^ 8 + (Dsc m z).toReal) := by
  obtain ⟨_, _, _, C, hC, hC4⟩ := obl_ramp_threshold12_transfer d
  refine ⟨C, hC, ?_⟩
  intro M s eps hs0 hsSmall hdelta heps1 g Fsc Psc Rsc Dsc Zsc goodEvt hPS L m hmL z hZ hD
  obtain ⟨h64, hs12, hb0, hb1, htau⟩ :=
    aux_in_deterministic_good_scale_transfer_params M s hs0 hsSmall hdelta
  refine ⟨fun e hee he1 => ?_, ?_⟩
  · exact (aux_lem_as_regularity_score_bridge_cutoff M hmL z e s g).1
      (aux_in_deterministic_good_scale_transfer_event M s eps g _ _ _ _ _ _ hPS m z hZ e hee he1)
  · set eps' : ℝ := max eps (s⁻¹ * M.delta ^ 2) with heps'
    have hev := (aux_lem_as_regularity_score_bridge_cutoff M hmL z eps' s g).1
      (aux_in_deterministic_good_scale_transfer_event M s eps g _ _ _ _ _ _
        hPS m z hZ eps' (le_max_left _ _) (max_le heps1.le hb1))
    have hE := (hC4 M L s ⟨h64, hs12⟩ htau eps' ⟨le_max_right _ _, max_le heps1.le hb1⟩
      m z g).1
    simp only [indicatorValue, if_pos hev] at hE
    have hacc := aux_in_deterministic_good_scale_transfer_accumulatedError_le M s eps g
      _ _ _ _ _ _ hPS m z hD
    have hacc' : accumulatedError M (some L) m z s g ≤ (Dsc m z).toReal := by
      rw [accumulatedError_some_eq_none_of_scale_le_cutoff M hmL z s g,
        ← accumulatedError_some_eq_none_of_scale_le_cutoff M (le_refl m) z s g]
      exact hacc
    have heps0 : 0 < eps := hPS.2.2.1
    have heps8 : eps' ^ 8 ≤ eps ^ 8 + s⁻¹ * M.delta ^ 2 := by
      have hpow : (s⁻¹ * M.delta ^ 2) ^ 8 ≤ s⁻¹ * M.delta ^ 2 :=
        pow_le_of_le_one hb0 hb1 (by norm_num)
      rcases le_total eps (s⁻¹ * M.delta ^ 2) with h | h
      · rw [heps', max_eq_right h]
        have : 0 ≤ eps ^ 8 := by positivity
        linarith
      · rw [heps', max_eq_left h]
        linarith
    refine hE.trans ((mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le).trans ?_)
    apply mul_le_mul_of_nonneg_left _ hC.le
    linarith

end Paper
