import SubdiffusiveProcess.PrefixScores.Basic

/-! The extended accumulated error agrees almost surely with Section 6's real error. -/
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization hiding Vec
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.PrefixScores

lemma ofReal_sqrt (x : ℝ) : ENNReal.ofReal (Real.sqrt x) = ENNReal.ofReal x ^ (1 / 2 : ℝ) := by
  by_cases hx : 0 ≤ x
  · rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx), ENNReal.ofReal_zero,
      ENNReal.ofReal_of_nonpos (le_of_not_ge hx), ENNReal.zero_rpow_of_pos (by norm_num)]

private def responseValues {d : ℕ} (M : GMCModel d) (s : ℝ)
    (ω : PotentialSample d) (k : ℕ) (z : Vec d) : Set ℝ :=
  {r | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
    OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
    r = (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
      Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        t = section6Response M l l ω x e}) 1)}

private def blockValues {d : ℕ} (s : ℝ) (ω : PotentialSample d) (k : ℕ) (z : Vec d) : Set ℝ :=
  {r | ∃ j : ℕ, j ≤ k ∧ r = (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
    supNormOn (translatedCube d k z) (shellBlock k j ω)}

private lemma responseValues_nonneg {d : ℕ} (M : GMCModel d) (s : ℝ)
    (ω : PotentialSample d) (k : ℕ) (z : Vec d) :
    0 ≤ sSup (responseValues M s ω k z) := by
  apply Real.sSup_nonneg
  rintro r ⟨j, l, hj, hl, x, hgrid, hx, rfl⟩
  positivity

private lemma blockValues_nonneg {d : ℕ} (s : ℝ)
    (ω : PotentialSample d) (k : ℕ) (z : Vec d) :
    0 ≤ sSup (blockValues s ω k z) := by
  apply Real.sSup_nonneg
  rintro r ⟨j, hj, rfl⟩
  exact mul_nonneg (by positivity) (Section6CutoffRegularity.supNormOn_nonneg' _ _)

private lemma responseValues_bddAbove {d : ℕ} (M : GMCModel d) (s : ℝ)
    (ω : PotentialSample d) (k : ℕ) (z : Vec d) :
    BddAbove (responseValues M s ω k z) := by
  refine ⟨∑ l ∈ Finset.range (k + 1), (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - l)), ?_⟩
  rintro r ⟨j, l, hj, hl, x, hgrid, hx, rfl⟩
  have hroot : Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
      t = section6Response M l l ω x e}) 1) ≤ 1 := by
    exact (Real.sqrt_le_sqrt (min_le_right _ _)).trans_eq Real.sqrt_one
  calc
    _ ≤ (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - l)) * 1 :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ ≤ ∑ l ∈ Finset.range (k + 1), (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - l)) := by
      rw [mul_one]
      exact Finset.single_le_sum (f := fun l : ℕ => (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - l)))
        (fun i _ => by positivity) (Finset.mem_range.mpr (by omega : l < k + 1))

private lemma blockValues_bddAbove {d : ℕ} (s : ℝ)
    (ω : PotentialSample d) (k : ℕ) (z : Vec d) :
    BddAbove (blockValues s ω k z) := by
  refine ⟨∑ j ∈ Finset.range (k + 1), (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - j)) *
    supNormOn (translatedCube d k z) (shellBlock k j ω), ?_⟩
  rintro r ⟨j, hj, rfl⟩
  exact Finset.single_le_sum (f := fun j : ℕ => (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - j)) *
    supNormOn (translatedCube d k z) (shellBlock k j ω)) (fun i _ => mul_nonneg (by positivity)
    (Section6CutoffRegularity.supNormOn_nonneg' _ _)) (Finset.mem_range.mpr (by omega : j < k + 1))

private lemma responseTerm_eq {d : ℕ} [NeZero d] (M : GMCModel d) (s : ℝ)
    (ω : PotentialSample d) (k : ℕ) (z : Vec d) :
    (sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
      OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - l))) *
        (min (primitiveResponseDefect M ω l x) 1) ^ (1 / 2 : ℝ)}) =
      ENNReal.ofReal (sSup (responseValues M s ω k z)) := by
  have hpoint : ∀ l : ℕ, ∀ x : Vec d,
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - l))) *
        (min (primitiveResponseDefect M ω l x) 1) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - l)) *
        Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
          t = section6Response M l l ω x e}) 1)) := by
    intro l x
    rw [ENNReal.ofReal_mul (by positivity), ofReal_sqrt, ENNReal.ofReal_min,
      responseDefect_eq, ENNReal.ofReal_one]
  have heq : {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
      OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - l))) *
        (min (primitiveResponseDefect M ω l x) 1) ^ (1 / 2 : ℝ)} =
      ENNReal.ofReal '' responseValues M s ω k z := by
    ext v
    constructor
    · rintro ⟨j, l, hj, hlk, hl, x, hg, hx, rfl⟩
      exact ⟨_, ⟨j, l, hj, hl, x, hg, hx, rfl⟩, (hpoint l x).symm⟩
    · rintro ⟨r, ⟨j, l, hj, hl, x, hg, hx, rfl⟩, rfl⟩
      exact ⟨j, l, hj, by omega, hl, x, hg, hx, (hpoint l x).symm⟩
  rw [heq, ofReal_sSup_image _ (responseValues_bddAbove M s ω k z)]

private lemma blockTerm_eq {d : ℕ} (s : ℝ)
    (ω : PotentialSample d) (k : ℕ) (z : Vec d) :
    (sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - j))) *
        primitiveNormOn (translatedCube d k z) (shellBlock k j ω)}) =
      ENNReal.ofReal (sSup (blockValues s ω k z)) := by
  simp_rw [normOn_cube_eq _ _ _ (Section6CutoffRegularity.continuous_shellBlock _ _ _),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (_ : ℕ))))]
  have heq : {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - j)) *
        supNormOn (translatedCube d k z) (shellBlock k j ω))} =
      ENNReal.ofReal '' blockValues s ω k z := by
    ext v
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, hj, rfl⟩
  rw [heq, ofReal_sSup_image _ (blockValues_bddAbove s ω k z)]

lemma gradientNorm_eq {d : ℕ} (ω : PotentialSample d) (k : ℕ) (z : Vec d) (j : ℕ) :
    primitiveNormOn (translatedCube d k z) (fun x => euclideanNorm (shellGradient (ω j) x)) =
      ENNReal.ofReal (vectorSupNormOn (translatedCube d k z) (shellGradient (ω j))) := by
  have hc : Continuous (fun x : Vec d => euclideanNorm (shellGradient (ω j) x)) :=
    Section6CutoffRegularity.continuous_euclideanNorm.comp
      (Section6CutoffRegularity.continuous_shellGradient (ω j))
  rw [normOn_cube_eq (k : ℤ) z _ hc]
  unfold supNormOn vectorSupNormOn
  simp only [abs_of_nonneg (euclideanNorm_nonneg _)]

lemma ae_errorScore_eq {d : ℕ} [NeZero d] (M : GMCModel d) (s : ℝ) (k : ℕ) (z : Vec d) :
    ∀ᵐ ω ∂M.P.toMeasure,
      primitiveErrorScore M s ω k z = ENNReal.ofReal (accumulatedError M none k z s ω) := by
  filter_upwards [ae_summable_translatedCube_gradient_tail M k z] with ω hsum
  have htail : (∑' j : ℕ, if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k) *
      primitiveNormOn (translatedCube d k z) (fun x => euclideanNorm (shellGradient (ω j) x))
      else 0) = ENNReal.ofReal (∑' j : ℕ, if k ≤ j then (3 : ℝ) ^ k *
        vectorSupNormOn (translatedCube d k z) (shellGradient (ω j)) else 0) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by
      split_ifs with hj
      · exact mul_nonneg (by positivity) (vectorSupNormOn_shellGradient_nonneg j k hj z ω)
      · exact le_refl 0) hsum]
    apply tsum_congr
    intro j
    split_ifs with hj
    · rw [gradientNorm_eq, ENNReal.ofReal_mul (by positivity)]
    · exact ENNReal.ofReal_zero.symm
  have hzero := normOn_cube_eq (k : ℤ) z (ω 0) (PotentialField.contDiff_one (ω 0)).continuous
  have hzeroNN : 0 ≤ (3 : ℝ) ^ (-(s / 8) * (k : ℝ)) *
      supNormOn (translatedCube d k z) (ω 0) :=
    mul_nonneg (by positivity) (Section6CutoffRegularity.supNormOn_nonneg' _ _)
  have htailNN : 0 ≤ ∑' j : ℕ, if k ≤ j then (3 : ℝ) ^ k *
      vectorSupNormOn (translatedCube d k z) (shellGradient (ω j)) else 0 := by
    apply tsum_nonneg
    intro j
    split_ifs with hj
    · exact mul_nonneg (by positivity) (vectorSupNormOn_shellGradient_nonneg j k hj z ω)
    · exact le_refl 0
  unfold primitiveErrorScore
  rw [responseTerm_eq, blockTerm_eq, hzero, ← ENNReal.ofReal_mul (by positivity), htail,
    ← ENNReal.ofReal_add (responseValues_nonneg M s ω k z) (blockValues_nonneg s ω k z),
    ← ENNReal.ofReal_add (add_nonneg (responseValues_nonneg M s ω k z)
      (blockValues_nonneg s ω k z)) hzeroNN,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (responseValues_nonneg M s ω k z)
      (blockValues_nonneg s ω k z)) hzeroNN) htailNN]
  simp only [accumulatedError, responseValues, blockValues, Option.getD_none, min_self]

end SubdiffusiveProcess.PrefixScores
