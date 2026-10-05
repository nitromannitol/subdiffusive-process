module

public import SubdiffusiveProcess.Paper.lem_as_regularity_rooted_iteration
public import SubdiffusiveProcess.Analysis.ScoreBudget
public import SubdiffusiveProcess.Analysis.ContinuousWeightedGradient

@[expose] public section

/-! The deterministic rooted estimate with all iteration constants chosen
before the coefficient. Two raw score budgets supply the good mask and its
error cap. Physical charts and the reference comparison are not asserted here.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A positive logarithmic budget smaller than one half follows from the prescribed loss. -/
theorem aux_lem_as_regularity_capped_iteration_lambda (w K : ℝ)
    (hw : 0 < w) (hw1 : w ≤ 1) (hK : 1 ≤ K) :
    0 < w / (K * 2) ∧ w / (K * 2) ≤ 1 / 2 := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith only [hw1, hK]

/-- Two small raw-score sums imply a rooted energy estimate for every continuous positive coefficient. -/
theorem lem_as_regularity_capped_iteration (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (D : deterministic_good_scale_input d) (Cg w : ℝ) (hCg : 0 < Cg)
    (hw : 0 < w) (hw1 : w ≤ 1) :
    ∃ lam tau C : ℝ, 0 < lam ∧ 0 < tau ∧ tau ≤ 1 ∧ 0 < C ∧
      ∀ base : ℝ, 0 ≤ base → base ≤ min (2 * lam) tau →
      ∀ (m n : ℕ), n + 26 ≤ m →
      ∀ (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
        (g : SpatialCoordinates d → Fin d → ℝ),
        MemHolder (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (1 / 2) g →
      ∀ a : Vec d → ℝ, Continuous a → (∀ y, 0 < a y) →
      ∀ data : ScalarTriadicCoeffData (fun y => a (y + 0)),
      ∀ u : H1Function (openCubeSet (originCube d (m : ℤ))),
        IsDivFormWeakSolutionOn a (cube d (m : ℤ)) u (fun y => g (y + z)) →
      ∀ ref Z score : ℕ → ℝ, (∀ j, 0 < ref j) → (∀ j, 0 ≤ Z j) → (∀ j, 0 ≤ score j) →
        (∑ j ∈ Finset.Icc n m, Z j) ≤ (lam * tau / 2) * ((m : ℝ) - n) →
        (∑ j ∈ Finset.Icc n m, score j) ≤ (lam * tau / 2) * ((m : ℝ) - n) →
        (∀ j : ℕ, j + 2 ≤ m → Z (j + 2) < 1 →
          paperHomogenizationError (originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2) (1 / 32)
            Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
            data.toTriadicCoeffFamily (ref j) ≤ ENNReal.ofReal (Cg * (base + score (j + 2)))) →
        (∀ j : ℕ, n ≤ j → j + 5 ≤ m →
          Real.exp (-(4 * (lam * ((m : ℝ) - n)))) ≤ ref j / ref (m - 2) ∧
          ref j / ref (m - 2) ≤ Real.exp (4 * (lam * ((m : ℝ) - n)))) →
        vectorNormalizedL2On (openCubeSet (originCube d (n : ℤ))) (fun y => Real.sqrt (a y) • u.grad y) ≤
          C * (3 : ℝ) ^ (w * ((m : ℝ) - n)) *
            (vectorNormalizedL2On (openCubeSet (originCube d (m : ℤ))) (fun y => Real.sqrt (a y) • u.grad y) +
              (Real.sqrt (ref (m - 2)))⁻¹ * ((3 : ℝ) ^ ((m : ℝ) / 2) *
                halfHolderSeminorm (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g)) := by
  classical
  obtain ⟨CH, CI, Cc, CP, hCH, hCI, hCc, hCP, hchain⟩ :=
    aux_prop_folded_iteration_translated_chain d hd D Cg hCg
  obtain ⟨h, hh, hth, hstep⟩ := aux_prop_folded_iteration_step_choice CH
  obtain ⟨eta, heta0, heta1, hthr⟩ := aux_prop_folded_iteration_eta_exists d CH h hCH hstep
  let cE := CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ)
  let K := max 1 ((d : ℝ) * Real.log 3 + (CI * (h + 1) + 3 * (cE * Cg) * CI) + 2 * 4)
  let C := max 1 (Real.exp (7 * (d : ℝ) / 2 * Real.log 3 + CI * (h + 1) * (h + 2)) * (4 : ℝ) ^ 2 *
    (Cc * (CP + (5 / 2 : ℝ) * (CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
      (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h)) * Section6ExcessDecay.fractionalHolderConst d *
        Real.sqrt (1 / 4) + Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8))))
  let lam := w / (K * 2)
  let tau := eta / 2
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  obtain ⟨hlam0, hlamh⟩ := aux_lem_as_regularity_capped_iteration_lambda w K hw hw1 hK1
  have htau : 0 < tau := half_pos heta0
  have htau1 : tau ≤ 1 := by dsimp only [tau]; linarith only [heta1]
  refine ⟨lam, tau, C, hlam0, htau, htau1, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro base hb0 hb m n hnm z hR g hg a ha hapos data u hu ref Z score hrf hZ hsc hZsum hscsum herr hrat
  have hlen : 0 ≤ (m : ℝ) - n := sub_nonneg.mpr (by exact_mod_cast (show n ≤ m by omega))
  obtain ⟨hscore, hcount⟩ := score_budget_rescale (Finset.Icc n m) Z score tau lam
    ((m : ℝ) - n) htau htau1 hlam0.le hlen (fun j _ => hZ j) (fun j _ => hsc j) hZsum hscsum
  apply lem_as_regularity_rooted_iteration d Cg CH CI Cc CP 4 eta K C w lam base h
    hCg hCH hCI hCc hCP (by norm_num) hK0 hw.le rfl hlamh hb0
    (hb.trans (min_le_left _ _)) hh hth heta0.le heta1 hthr hchain (le_max_right _ _) (le_max_right _ _)
    m n hnm z hR g hg a hapos data u hu ref score hrf hsc (fun j => Z j < 1 ∧ score j ≤ tau)
    hscore hcount ?_ ?_ (continuousWeightedGradient_window m a ha u)
  · intro j hj hgood
    have hmin : base + score (j + 2) ≤ eta := by
      have hbt := hb.trans (min_le_right _ _)
      dsimp only [tau] at hbt hgood
      linarith only [hbt, hgood.2]
    rw [min_eq_right hmin]
    exact herr j hj hgood.1
  · intro j hjn hjm
    obtain ⟨h1, h2⟩ := hrat j hjn hjm
    exact ⟨(mul_le_of_le_one_left (Real.exp_pos _).le (by norm_num : (4 : ℝ)⁻¹ ≤ 1)).trans h1,
      h2.trans (le_mul_of_one_le_left (Real.exp_pos _).le (by norm_num : (1 : ℝ) ≤ 4))⟩

end SubdiffusiveProcess.Paper
