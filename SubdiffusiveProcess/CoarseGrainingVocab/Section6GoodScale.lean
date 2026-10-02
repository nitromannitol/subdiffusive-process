import SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Support

/-!
# Deterministic support for the Section 6 good-scale error estimate

This file contains the pointwise event-reading layer used by
`p.good.scale.mathcal.E`.  In particular, it does not use the probabilistic
scale-concentration theorem: the proposition is a deterministic statement at
one sample once membership in the good event is known.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization Homogenization.Book
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The good event is monotone in its amplitude parameter on `[0,1]`. -/
theorem goodEvent_subset_one
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cutoff : Option ℕ)
    (m : ℕ) (y : Vec d) {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    goodEvent M cutoff m y epsilon s ⊆ goodEvent M cutoff m y 1 s := by
  intro omega homega
  rcases homega with ⟨hfieldOne, hfieldTwo, hresponse⟩
  refine ⟨?_, hfieldTwo, ?_⟩
  · intro j
    exact (hfieldOne j).trans <| by
      have hpow : 0 ≤ (3 : ℝ) ^ ((s * (j : ℝ)) / 8) :=
        Real.rpow_nonneg (by norm_num) _
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hepsilon1 hpow
  · intro j n hjm hnj z hzgrid hzann e he
    have hepsq : epsilon ^ 2 ≤ (1 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hepsilon0 hepsilon1 2
    have hpow : 0 ≤ (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) :=
      Real.rpow_nonneg (by norm_num) _
    exact (hresponse j n hjm hnj z hzgrid hzann e he).trans <| by
      exact mul_le_mul_of_nonneg_right hepsq hpow

/-- On the epsilon-good event, every atom in the printed response supremum is
at most `epsilon`.  The square root consumes the `epsilon^2` in
`GoodResponse`, while the stronger outer discount absorbs the remaining
`3^(s(m-n)/16)` factor. -/
theorem goodResponse_discounted_atom_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (homega : omega ∈ goodEvent M none m 0 epsilon s)
    {r : ℝ}
    (hr : r ∈ {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
        ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            t = section6Response M n n omega z e})}) :
    r ≤ epsilon := by
  rcases hr with ⟨j, n, hjm, hnj, z, hzgrid, hzann, rfl⟩
  have hnm : n ≤ m := by omega
  have hgap0 : 0 ≤ (m : ℝ) - (n : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hnm)
  let A : Set ℝ := {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
    t = section6Response M n n omega z e}
  have hAbdd : BddAbove A := by
    simpa only [A] using bddAbove_section6Response_unitSphere M n n omega z
  have hAne : A.Nonempty := by
    let i : Fin d := ⟨0, lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension⟩
    refine ⟨section6Response M n n omega z (Pi.single i 1), Pi.single i 1, ?_, rfl⟩
    rw [vecNormSq, vecDot, Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      simp [Pi.single_eq_of_ne hbi]
    · simp
  have hresp : sSup A ≤ epsilon ^ 2 *
      (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := by
    refine csSup_le hAne ?_
    intro t ht
    rcases ht with ⟨e, he, rfl⟩
    simpa using homega.2.2 j n hjm hnj z (by simpa using hzgrid)
      (by simpa using hzann) e he
  have hresp0 : 0 ≤ sSup A := by
    rcases hAne with ⟨t, ht⟩
    rcases ht with ⟨e, he, rfl⟩
    have hJ : 0 ≤ section6Response M n n omega z e := by
      unfold section6Response paperScalarProbe
      exact Ch02.responseJ_nonneg _ _ _ _
    exact hJ.trans (le_csSup hAbdd ⟨e, he, rfl⟩)
  have hepsq0 : 0 ≤ epsilon ^ 2 := sq_nonneg _
  have hsqrt : Real.sqrt (sSup A) ≤ epsilon *
      (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by
    have hright0 : 0 ≤ epsilon *
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) :=
      mul_nonneg hepsilon0 (Real.rpow_nonneg (by norm_num) _)
    rw [Real.sqrt_le_iff]
    refine ⟨hright0, ?_⟩
    calc
      sSup A ≤ epsilon ^ 2 *
          (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := hresp
      _ = (epsilon *
          (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) ^ 2 := by
        rw [mul_pow]
        congr 1
        calc
          (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) =
              (3 : ℝ) ^
                (((s * ((m : ℝ) - (n : ℝ))) / 16) * 2) := by ring_nf
          _ = ((3 : ℝ) ^
              ((s * ((m : ℝ) - (n : ℝ))) / 16)) ^ (2 : ℝ) := by
                rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
          _ = ((3 : ℝ) ^
              ((s * ((m : ℝ) - (n : ℝ))) / 16)) ^ (2 : ℕ) := by
                exact Real.rpow_natCast _ 2
  calc
    (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) * Real.sqrt (sSup A) ≤
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          (epsilon * (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) := by
      gcongr
    _ = epsilon * (3 : ℝ) ^
        (-(7 * s / 16) * ((m : ℝ) - (n : ℝ))) := by
      calc
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
            (epsilon * (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) =
          epsilon * ((3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) := by ring
        _ = epsilon * (3 : ℝ) ^
            (-(s / 2) * ((m : ℝ) - (n : ℝ)) +
              (s * ((m : ℝ) - (n : ℝ))) / 16) := by
                rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        _ = _ := by
          congr 1
          ring_nf
    _ ≤ epsilon * 1 := by
      gcongr
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) hgap0)
    _ = epsilon := mul_one _

/-- Supremum form of `goodResponse_discounted_atom_le`.  The empty-index
case (which occurs at the first two scales) is handled by the real `sSup`
convention. -/
theorem goodResponse_discounted_sSup_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d}
    (homega : omega ∈ goodEvent M none m 0 epsilon s) :
    sSup {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
        ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            t = section6Response M n n omega z e})} ≤ epsilon := by
  let S : Set ℝ := {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
        ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            t = section6Response M n n omega z e})}
  by_cases hS : S.Nonempty
  · change sSup S ≤ epsilon
    exact csSup_le hS fun r hr =>
      goodResponse_discounted_atom_le M hepsilon0 hs0 homega hr
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    change sSup S ≤ epsilon
    rw [hEmpty, Real.sSup_empty]
    exact hepsilon0

end

end SubdiffusiveProcess.CoarseGrainingVocab
