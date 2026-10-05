module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.AnnularSlotBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Transport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.AccumulatedErrorCovariance

@[expose] public section

/-!
# Conjunct (5) of `p.cutoff.regularity.good.scales`

The good-scale bound on the homogenization error, in the exact shape.

Two branches:

* `m ≤ L` — established verbatim in the shape at
  `Section6Cutoff.exists_indicator_section6HomogenizationError_le_cutoff_min_of_scale_le_cutoff`;
* `m > L` — composed here from the two established annular theorems,
  `AnnularLocalization.section6HomogenizationError_le_cutoff_slots_of_cutoff_lt_scale`
  (error ≤ constant times the four slots, at `z = 0`) and
  `AnnularRecombination.section6HomogenizationError_le_cutoff_min_of_slot_bound`
  (slots → the `min` bracket).  Neither had a call site before.

The recombination theorem takes an unsupplied `hepsilonCap`
(`section6HomogenizationError … ≤ C * epsilon`), and nothing in the repo proved
it for `some L` with `L < m`.  `section6HomogenizationError_le_cutoff_epsilon`
below supplies it, by bounding each of the four slots by `epsilon` using
`AnnularSlotBounds` and the interval hypothesis `s⁻¹ * delta ^ 2 ≤ epsilon`.

Both hypotheses of the recombination carry the *same* constant, so the slot bound
is inflated from `√cutoffAnnularSquareConstant` to `7 * √cutoffAnnularSquareConstant`
using slot nonnegativity.

The slots are hard-coded at the origin, so there is no slot-level covariance;
the `z`-generalization is done at the level of the homogenization error itself,
through `section6HomogenizationError_eq_translate_zero`,
`mem_goodEvent_iff_translate_zero` and `accumulatedError_translatePotentialSample`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open _root_.SubdiffusiveProcess.Model

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The missing `epsilon` cap on the annular branch.** -/
theorem section6HomogenizationError_le_cutoff_epsilon
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hLm : L < m)
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hD : s⁻¹ * M.delta ^ 2 ≤ epsilon)
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : PotentialSample d)
    (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s) :
    section6HomogenizationError M s L m omega 0 ≤
      Real.sqrt cutoffAnnularSquareConstant * 7 * epsilon := by
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (sq_pos_of_pos M.shellPrefix.delta_pos)).trans_le hsLower
  have hslots := section6HomogenizationError_le_cutoff_slots_of_cutoff_lt_scale
    M hLm hepsilon0 hepsilon1 hsLower hsUpper omega hgood
  have hA := cutoffGoodScaleResponseSlot_le M L hepsilon0 hs0.le hgood
  have hBs := goodScaleShellSlot_le m omega hgood.1
  have hBf := goodScaleFullSlot_le m omega hgood.1
  have hBg : goodScaleGradientSlot m omega ≤ 3 * epsilon := by
    rw [goodScaleGradientSlot_eq_longRatioGradientTail]
    exact longRatioGradientTail_le_three_mul_of_goodFieldOne m hepsilon0 hsUpper
      omega hgood.1
  have hroot : 0 ≤ Real.sqrt cutoffAnnularSquareConstant := Real.sqrt_nonneg _
  refine hslots.trans ?_
  have hsum : cutoffGoodScaleResponseSlot M L s m omega + s⁻¹ * M.delta ^ 2 +
      goodScaleShellSlot s m omega + goodScaleFullSlot s m omega +
      goodScaleGradientSlot m omega ≤ 7 * epsilon := by linarith
  calc Real.sqrt cutoffAnnularSquareConstant *
        (cutoffGoodScaleResponseSlot M L s m omega + s⁻¹ * M.delta ^ 2 +
          goodScaleShellSlot s m omega + goodScaleFullSlot s m omega +
          goodScaleGradientSlot m omega)
      ≤ Real.sqrt cutoffAnnularSquareConstant * (7 * epsilon) :=
        mul_le_mul_of_nonneg_left hsum hroot
    _ = Real.sqrt cutoffAnnularSquareConstant * 7 * epsilon := by ring

/-- The annular branch at the origin, in the `min` shape. -/
theorem section6HomogenizationError_le_cutoff_min_annular
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hLm : L < m)
    {epsilon s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (hepsilon : epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1)
    (omega : PotentialSample d)
    (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s) :
    section6HomogenizationError M s L m omega 0 ≤
        5 * (Real.sqrt cutoffAnnularSquareConstant * 7) *
          min epsilon (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M (some L) m 0 s omega) ∧
      section6HomogenizationError M s L m omega 0 ≤
        5 * (Real.sqrt cutoffAnnularSquareConstant * 7) * epsilon := by
  obtain ⟨hD, hepsilon1⟩ := hepsilon
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (sq_pos_of_pos M.shellPrefix.delta_pos)).trans_le hsLower
  have hD0 : (0 : ℝ) ≤ s⁻¹ * M.delta ^ 2 := by positivity
  have hepsilon0 : 0 ≤ epsilon := hD0.trans hD
  have hroot : 0 < Real.sqrt cutoffAnnularSquareConstant :=
    Real.sqrt_pos.mpr cutoffAnnularSquareConstant_pos
  have hCpos : 0 < Real.sqrt cutoffAnnularSquareConstant * 7 := by positivity
  have hslots := section6HomogenizationError_le_cutoff_slots_of_cutoff_lt_scale
    M hLm hepsilon0 hepsilon1 hsLower hsUpper omega hgood
  -- inflate the slot bound to the epsilon-cap constant
  have hsum0 : 0 ≤ cutoffGoodScaleResponseSlot M L s m omega + s⁻¹ * M.delta ^ 2 +
      goodScaleShellSlot s m omega + goodScaleFullSlot s m omega +
      goodScaleGradientSlot m omega := by
    have h1 := cutoffGoodScaleResponseSlot_nonneg M L s m omega
    have h2 := goodScaleShellSlot_nonneg s m omega
    have h3 := goodScaleFullSlot_nonneg s m omega
    have h4 := goodScaleGradientSlot_nonneg m omega
    linarith
  have hraw : section6HomogenizationError M s L m omega 0 ≤
      Real.sqrt cutoffAnnularSquareConstant * 7 *
        (cutoffGoodScaleResponseSlot M L s m omega + s⁻¹ * M.delta ^ 2 +
          goodScaleShellSlot s m omega + goodScaleFullSlot s m omega +
          goodScaleGradientSlot m omega) := by
    refine hslots.trans ?_
    have hle : Real.sqrt cutoffAnnularSquareConstant ≤
        Real.sqrt cutoffAnnularSquareConstant * 7 := by linarith [hroot.le]
    exact mul_le_mul_of_nonneg_right hle hsum0
  have hcap := section6HomogenizationError_le_cutoff_epsilon M hLm hepsilon0
    hepsilon1 hD hsLower hsUpper omega hgood
  exact section6HomogenizationError_le_cutoff_min_of_slot_bound M L m hCpos hs0.le
    ⟨hD, hepsilon1⟩ omega hgood hraw hcap

/-- **Conjunct (5) of the finite-cutoff good-scale proposition.** -/
theorem exists_cutoff_regularity_good_scale_clause (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, ∀ L : ℕ,
      (∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1, ∀ m : ℕ, ∀ z : Vec d,
          ∀ omega,
            indicatorValue (goodEvent M (some L) m z epsilon s)
                (fun omega' ↦ section6HomogenizationError M s L m omega' z) omega ≤
              C * min epsilon
                (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                  accumulatedError M (some L) m z s omega) ∧
            indicatorValue (goodEvent M (some L) m z epsilon s)
                (fun omega' ↦ section6HomogenizationError M s L m omega' z) omega ≤
              C * epsilon) := by
  obtain ⟨C0, hC0, hlow⟩ :=
    exists_indicator_section6HomogenizationError_le_cutoff_min_of_scale_le_cutoff d
  have hroot : 0 < Real.sqrt cutoffAnnularSquareConstant :=
    Real.sqrt_pos.mpr cutoffAnnularSquareConstant_pos
  refine ⟨C0 + 5 * (Real.sqrt cutoffAnnularSquareConstant * 7), by positivity, ?_⟩
  intro M L s hs epsilon hepsilon m z omega
  obtain ⟨hsLower, hsUpper⟩ := hs
  obtain ⟨hD, hepsilon1⟩ := hepsilon
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (sq_pos_of_pos M.shellPrefix.delta_pos)).trans_le hsLower
  have hD0 : (0 : ℝ) ≤ s⁻¹ * M.delta ^ 2 := by positivity
  have hepsilon0 : 0 ≤ epsilon := hD0.trans hD
  have hE0 : 0 ≤ accumulatedError M (some L) m z s omega :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.accumulatedError_nonneg
      M (some L) s m z omega
  have hmin0 : 0 ≤ min epsilon (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
      accumulatedError M (some L) m z s omega) :=
    le_min hepsilon0 (by positivity)
  have hann0 : (0 : ℝ) ≤ 5 * (Real.sqrt cutoffAnnularSquareConstant * 7) := by
    positivity
  rcases le_or_gt m L with hmL | hLm
  · obtain ⟨h1, h2⟩ := hlow M s ⟨hsLower, hsUpper⟩ L m hmL z omega epsilon
      ⟨hD, hepsilon1⟩
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (by linarith) hmin0
    · exact mul_le_mul_of_nonneg_right (by linarith) hepsilon0
  · unfold indicatorValue
    split_ifs with hmem
    · have hmem0 : translatePotentialSample z omega ∈
          goodEvent M (some L) m 0 epsilon s :=
        (mem_goodEvent_iff_translate_zero M (some L) m epsilon s z omega).mp hmem
      obtain ⟨h1, h2⟩ := section6HomogenizationError_le_cutoff_min_annular
        M hLm hsLower hsUpper ⟨hD, hepsilon1⟩ (translatePotentialSample z omega)
        hmem0
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.accumulatedError_translatePotentialSample
        M (some L) s m z omega] at h1
      rw [← section6HomogenizationError_eq_translate_zero] at h1 h2
      refine ⟨h1.trans ?_, h2.trans ?_⟩
      · exact mul_le_mul_of_nonneg_right (by linarith) hmin0
      · exact mul_le_mul_of_nonneg_right (by linarith) hepsilon0
    · exact ⟨mul_nonneg (by linarith) hmin0, mul_nonneg (by linarith) hepsilon0⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
