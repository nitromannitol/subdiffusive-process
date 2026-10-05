module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.HolderScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorField
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows

@[expose] public section

/-!
# Hölder Step 3: deterministic reads from the accumulated error

The stopping argument controls the literal `accumulatedError`.  This file
records the two non-probabilistic projections used in the coefficient-ratio
display: a one-shell block and the stored long-gradient `tsum`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

private theorem shellBlock_continuous {d : ℕ} (m n : ℕ)
    (omega : Sample d) : Continuous (shellBlock m n omega) := by
  unfold shellBlock
  fun_prop

private theorem bddAbove_abs_values_translatedCube {d : ℕ} (m : ℤ) (z : Vec d)
    {f : Vec d → ℝ} (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ translatedCube d m z, a = |f x|} := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d228_bddAbove_abs_values_translatedCube (d := d) (r := m) (z := z) (f := f) (hf := hf)

/-- Point evaluation on a translated cube is bounded by the literal scalar
supremum norm for continuous fields. -/
theorem abs_apply_le_supNormOn_translatedCube {d : ℕ} {m : ℤ} {z : Vec d}
    {f : Vec d → ℝ} (hf : Continuous f) {x : Vec d}
    (hx : x ∈ translatedCube d m z) :
    |f x| ≤ supNormOn (translatedCube d m z) f := by
  unfold supNormOn
  exact le_csSup (bddAbove_abs_values_translatedCube m z hf) ⟨x, hx, rfl⟩

private theorem translatedShellSlot_bddAbove {d : ℕ}
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : Sample d) :
    BddAbove {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (translatedCube d (m : ℤ) z) (shellBlock m j omega)} := by
  let F : ℕ → ℝ := fun j ↦
    (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
      supNormOn (translatedCube d (m : ℤ) z) (shellBlock m j omega)
  refine ⟨Finset.sup' (Finset.range (m + 1))
      (Finset.nonempty_range_iff.mpr (by omega)) F, ?_⟩
  rintro r ⟨j, hj, rfl⟩
  exact Finset.le_sup' F (Finset.mem_range.mpr (by omega))

private theorem translatedShellSlot_nonneg {d : ℕ}
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : Sample d) :
    0 ≤ sSup {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (translatedCube d (m : ℤ) z) (shellBlock m j omega)} := by
  have hzero : supNormOn (translatedCube d (m : ℤ) z)
      (shellBlock m m omega) = 0 := by
    unfold supNormOn shellBlock
    have hset : {a : ℝ | ∃ x ∈ translatedCube d (m : ℤ) z,
        a = |∑ k ∈ Finset.Icc (m + 1) m, omega k x|} = {0} := by
      ext a
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp
      · intro ha
        rw [Set.mem_singleton_iff] at ha
        subst a
        refine ⟨z, ?_, by simp⟩
        exact ⟨0, Section6ExcessDecay.zero_mem_cube d (m : ℤ), by simp⟩
    rw [hset, csSup_singleton]
  apply le_csSup (translatedShellSlot_bddAbove s m z omega)
  exact ⟨m, le_rfl, by simp [hzero]⟩

private theorem responseSlot_nonneg {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : Sample d) :
    0 ≤ sSup {r : ℝ | ∃ j l : ℕ, j ≤ m ∧ l + 2 ≤ j ∧
      ∃ z' : Vec d, OnTriadicGrid l (z' - z) ∧
        z' - z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ))) *
          Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
            vecNormSq e = 1 ∧
            t = section6Response M l (min l (cutoff.getD l)) omega z' e}) 1)} := by
  let S : Set ℝ := {r : ℝ | ∃ j l : ℕ, j ≤ m ∧ l + 2 ≤ j ∧
      ∃ z' : Vec d, OnTriadicGrid l (z' - z) ∧
        z' - z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ))) *
          Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
            vecNormSq e = 1 ∧
            t = section6Response M l (min l (cutoff.getD l)) omega z' e}) 1)}
  change 0 ≤ sSup S
  by_cases hb : BddAbove S
  · by_cases hne : S.Nonempty
    · obtain ⟨r, hr⟩ := hne
      have hr0 : 0 ≤ r := by
        rcases hr with ⟨j, l, hj, hl, z', hzgrid, hzann, rfl⟩
        positivity
      exact le_trans hr0 (le_csSup hb hr)
    · have hS : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [hS]
      simp
  · rw [csSup_of_not_bddAbove hb]
    simp

private theorem shellZeroTerm_nonneg {d : ℕ}
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : Sample d) :
    0 ≤ (3 : ℝ) ^ (-(s / 8) * m) *
      supNormOn (translatedCube d (m : ℤ) z) (omega 0) := by
  have hsup : 0 ≤ supNormOn (translatedCube d (m : ℤ) z) (omega 0) := by
    unfold supNormOn
    have hb := bddAbove_abs_values_translatedCube (m : ℤ) z
      (omega 0).1.1.continuous
    have hz : z ∈ translatedCube d (m : ℤ) z :=
      ⟨0, Section6ExcessDecay.zero_mem_cube d (m : ℤ), by simp⟩
    exact (abs_nonneg (omega 0 z)).trans (le_csSup hb ⟨z, hz, rfl⟩)
  exact mul_nonneg (by positivity) hsup

/-- Every literal component of the accumulated error is nonnegative. -/
theorem accumulatedError_nonneg {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : Sample d) :
    0 ≤ accumulatedError M cutoff m z s omega := by
  rw [accumulatedError]
  have hresponse := responseSlot_nonneg M cutoff s m z omega
  have hblock := translatedShellSlot_nonneg s m z omega
  have hzero := shellZeroTerm_nonneg s m z omega
  have hgrad : 0 ≤ ∑' j : ℕ, if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
        (shellGradient (omega j)) else 0 := by
    exact tsum_nonneg fun j ↦ by
      split
      · exact mul_nonneg (by positivity)
          (vectorSupNormOn_shellGradient_nonneg j m (by omega) z omega)
      · exact le_rfl
  linarith

/-- The stored long-gradient `tsum` is a nonnegative summand of the literal
accumulated error.  Turning it into finite partial-sum bounds still requires a
summability certificate. -/
theorem gradientSuffix_le_accumulatedError {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : Sample d) :
    (∑' j : ℕ, if m ≤ j then
        (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
          (shellGradient (omega j)) else 0) ≤
      accumulatedError M cutoff m z s omega := by
  rw [accumulatedError]
  have hgrad : 0 ≤ ∑' j : ℕ, if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
        (shellGradient (omega j)) else 0 := by
    apply tsum_nonneg
    intro j
    split
    · exact mul_nonneg (by positivity)
        (vectorSupNormOn_shellGradient_nonneg j m (by omega) z omega)
    · exact le_rfl
  have hresponse := responseSlot_nonneg M cutoff s m z omega
  have hblock := translatedShellSlot_nonneg s m z omega
  have hzero := shellZeroTerm_nonneg s m z omega
  linarith

/-- The complete discounted shell-block supremum is a summand of the
accumulated error. -/
theorem shellSlot_le_accumulatedError {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : Sample d) :
    sSup {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (translatedCube d (m : ℤ) z) (shellBlock m j omega)} ≤
      accumulatedError M cutoff m z s omega := by
  rw [accumulatedError]
  have hresponse := responseSlot_nonneg M cutoff s m z omega
  have hblock := translatedShellSlot_nonneg s m z omega
  have hzero := shellZeroTerm_nonneg s m z omega
  have hgrad : 0 ≤ ∑' j : ℕ, if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
        (shellGradient (omega j)) else 0 := by
    exact tsum_nonneg fun j ↦ by
      split
      · exact mul_nonneg (by positivity)
          (vectorSupNormOn_shellGradient_nonneg j m (by omega) z omega)
      · exact le_rfl
  linarith

/-- The discounted zeroth shell is a summand of the accumulated error. -/
theorem shellZeroTerm_le_accumulatedError {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : Sample d) :
    (3 : ℝ) ^ (-(s / 8) * m) *
        supNormOn (translatedCube d (m : ℤ) z) (omega 0) ≤
      accumulatedError M cutoff m z s omega := by
  rw [accumulatedError]
  have hresponse := responseSlot_nonneg M cutoff s m z omega
  have hblock := translatedShellSlot_nonneg s m z omega
  have hzero := shellZeroTerm_nonneg s m z omega
  have hgrad : 0 ≤ ∑' j : ℕ, if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
        (shellGradient (omega j)) else 0 := by
    exact tsum_nonneg fun j ↦ by
      split
      · exact mul_nonneg (by positivity)
          (vectorSupNormOn_shellGradient_nonneg j m (by omega) z omega)
      · exact le_rfl
  linarith

/-- Every finite high-shell gradient block is bounded by the accumulated
error once a genuine summability certificate identifies the stored `tsum`
with its partial sums. -/
theorem finite_gradientSuffix_le_accumulatedError {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m L : ℕ) (z : Vec d) (omega : Sample d)
    (hsum : Summable (fun j : ℕ ↦ if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
        (shellGradient (omega j)) else 0)) :
    (∑ j ∈ Finset.Icc m L,
        (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
          (shellGradient (omega j))) ≤
      accumulatedError M cutoff m z s omega := by
  let F : ℕ → ℝ := fun j ↦ if m ≤ j then
    (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
      (shellGradient (omega j)) else 0
  have hpartial : (∑ j ∈ Finset.Icc m L,
        (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
          (shellGradient (omega j))) ≤ ∑' j, F j := by
    have heq : (∑ j ∈ Finset.Icc m L,
        (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
          (shellGradient (omega j))) = ∑ j ∈ Finset.Icc m L, F j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [F, ite_eq_left (Finset.mem_Icc.mp hj).1]
    rw [heq]
    apply hsum.sum_le_tsum
    intro j _hj
    change 0 ≤ if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
        (shellGradient (omega j)) else 0
    by_cases hmj : m ≤ j
    · rw [ite_eq_left hmj]
      exact mul_nonneg (by positivity)
        (vectorSupNormOn_shellGradient_nonneg j m hmj z omega)
    · rw [ite_eq_right hmj]
  exact hpartial.trans (gradientSuffix_le_accumulatedError M cutoff s m z omega)

/-- A one-step shell block, with exactly the manuscript's discount, is a
nonnegative summand of `accumulatedError`. -/
theorem weighted_shellBlock_le_accumulatedError {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m j : ℕ) (z : Vec d) (omega : Sample d) (hjm : j ≤ m) :
    (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (translatedCube d (m : ℤ) z) (shellBlock m j omega) ≤
      accumulatedError M cutoff m z s omega := by
  rw [accumulatedError]
  let blockSet : Set ℝ := {r : ℝ | ∃ i ≤ m,
    r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (i : ℝ))) *
      supNormOn (translatedCube d (m : ℤ) z) (shellBlock m i omega)}
  have hmem : (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
      supNormOn (translatedCube d (m : ℤ) z) (shellBlock m j omega) ∈ blockSet :=
    ⟨j, hjm, rfl⟩
  have hslot : (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
      supNormOn (translatedCube d (m : ℤ) z) (shellBlock m j omega) ≤
        sSup blockSet :=
    le_csSup (by simpa only [blockSet] using translatedShellSlot_bddAbove s m z omega) hmem
  have hresponse := responseSlot_nonneg M cutoff s m z omega
  have hzero := shellZeroTerm_nonneg s m z omega
  have hgrad : 0 ≤ ∑' i : ℕ, if m ≤ i then
      (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
        (shellGradient (omega i)) else 0 := by
    exact tsum_nonneg fun i ↦ by
      split
      · exact mul_nonneg (by positivity)
          (vectorSupNormOn_shellGradient_nonneg i m (by omega) z omega)
      · exact le_rfl
  change _ ≤ _ + sSup blockSet + _ + _
  linarith

/-- The truncated response supremum is itself a nonnegative summand of the
literal accumulated error.  This projection is used by the refined
good-scale error cap in the Hölder recurrence. -/
theorem responseSlot_le_accumulatedError {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : Sample d) :
    sSup {r : ℝ | ∃ j l : ℕ, j ≤ m ∧ l + 2 ≤ j ∧
        ∃ z' : Vec d, OnTriadicGrid l (z' - z) ∧
          z' - z ∈ cube d j \ cube d (j - 1) ∧
          r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ))) *
            Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
              vecNormSq e = 1 ∧
              t = section6Response M l (min l (cutoff.getD l)) omega z' e}) 1)} ≤
      accumulatedError M cutoff m z s omega := by
  rw [accumulatedError]
  have hresponse := responseSlot_nonneg M cutoff s m z omega
  have hblock := translatedShellSlot_nonneg s m z omega
  have hzero := shellZeroTerm_nonneg s m z omega
  have hgrad : 0 ≤ ∑' j : ℕ, if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d (m : ℤ) z)
        (shellGradient (omega j)) else 0 := by
    exact tsum_nonneg fun j ↦ by
      split
      · exact mul_nonneg (by positivity)
          (vectorSupNormOn_shellGradient_nonneg j m (by omega) z omega)
      · exact le_rfl
  linarith

/-- A specified truncated response atom is bounded by the accumulated error
whenever the response-slot supremum is genuinely bounded above. -/
theorem truncatedResponseAtom_le_accumulatedError {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : Sample d)
    (hbounded : BddAbove {r : ℝ | ∃ j l : ℕ, j ≤ m ∧ l + 2 ≤ j ∧
      ∃ z' : Vec d, OnTriadicGrid l (z' - z) ∧
        z' - z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ))) *
          Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
            vecNormSq e = 1 ∧
            t = section6Response M l (min l (cutoff.getD l)) omega z' e}) 1)})
    {j l : ℕ} (hj : j ≤ m) (hl : l + 2 ≤ j) {z' : Vec d}
    (hzgrid : OnTriadicGrid l (z' - z))
    (hzann : z' - z ∈ cube d j \ cube d (j - 1)) :
    (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ))) *
        Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
          vecNormSq e = 1 ∧
          t = section6Response M l (min l (cutoff.getD l)) omega z' e}) 1) ≤
      accumulatedError M cutoff m z s omega := by
  apply (le_csSup hbounded ⟨j, l, hj, hl, z', hzgrid, hzann, rfl⟩).trans
  exact responseSlot_le_accumulatedError M cutoff s m z omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
