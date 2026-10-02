import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.RecurrenceBudget
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.SubunitTail
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.GoodEvent

/-!
# Hölder Step 3: refined local homogenization-error cap

The second clause of `p.good.scale.mathcal.E` gives the `epsilon` cap.  The
iteration also needs its first clause, with the untruncated response slot
replaced by the truncated response slot stored in `accumulatedError`.  The
only loss in that replacement is `epsilon^8`, exactly as in the manuscript.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

/-- Algebra behind the manuscript's response truncation: if `x` is above
one, the good-event bound forces the geometric weight below `epsilon`, and
the eight powers in the outer discount pay `epsilon^8`. -/
theorem pow_eight_mul_le_truncated_add_pow_eight
    {t epsilon x : ℝ} (ht0 : 0 < t)
    (hepsilon : 0 ≤ epsilon) (hx : 0 ≤ x)
    (hgood : x ≤ epsilon * t⁻¹) :
    t ^ 8 * x ≤ t ^ 8 * min x 1 + epsilon ^ 8 := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_left hx1]
    exact le_add_of_nonneg_right (pow_nonneg hepsilon 8)
  · have honeX : 1 < x := lt_of_not_ge hx1
    have htE : t < epsilon := by
      have hinv0 : 0 < t⁻¹ := inv_pos.mpr ht0
      have hmul := mul_lt_mul_of_pos_right (honeX.trans_le hgood) ht0
      rw [mul_assoc, inv_mul_cancel₀ ht0.ne', mul_one] at hmul
      nlinarith only [hmul]
    have htx : t ^ 8 * x ≤ epsilon * t ^ 7 := by
      calc
        t ^ 8 * x ≤ t ^ 8 * (epsilon * t⁻¹) :=
          mul_le_mul_of_nonneg_left hgood (pow_nonneg ht0.le 8)
        _ = epsilon * t ^ 7 := by
          field_simp [ht0.ne']
    have ht7 : t ^ 7 ≤ epsilon ^ 7 :=
      pow_le_pow_left₀ ht0.le htE.le 7
    have hmain : t ^ 8 * x ≤ epsilon ^ 8 := by
      calc
        t ^ 8 * x ≤ epsilon * t ^ 7 := htx
        _ ≤ epsilon * epsilon ^ 7 := mul_le_mul_of_nonneg_left ht7 hepsilon
        _ = epsilon ^ 8 := by ring
    exact hmain.trans (le_add_of_nonneg_left (mul_nonneg (pow_nonneg ht0.le 8)
      (le_min hx zero_le_one)))

private theorem truncatedResponseSet_bddAbove
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (omega : Sample d) :
    BddAbove {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n (z - 0) ∧
        z - 0 ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          Real.sqrt (min (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            q = section6Response M n (min n (none.getD n)) omega z e}) 1)} := by
  refine ⟨1, ?_⟩
  rintro r ⟨j, n, hjm, hnj, z, hzgrid, hzann, rfl⟩
  have hnm : n ≤ m := by omega
  have hgap : 0 ≤ (m : ℝ) - (n : ℝ) := by
    exact sub_nonneg.mpr (Nat.cast_le.2 hnm)
  have hw : (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hgap
  have hsqrt : Real.sqrt (min
      (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        q = section6Response M n (min n (none.getD n)) omega z e}) 1) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (min_le_right _ 1)
  exact (mul_le_mul hw hsqrt (Real.sqrt_nonneg _) (by positivity)).trans_eq (mul_one 1)

/-- The untruncated response slot in the proved good-scale display is bounded
by the truncated response slot in `accumulatedError`, plus `epsilon^8`. -/
theorem goodScaleResponseSlot_le_responseSlot_add_pow_eight
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m : ℕ} {epsilon s : ℝ}
    (hepsilon : 0 ≤ epsilon) (hs : 0 ≤ s) {omega : Sample d}
    (hgood : omega ∈ goodEvent M none m 0 epsilon s) :
    goodScaleResponseSlot M s m omega ≤
      accumulatedError M none m 0 s omega + epsilon ^ 8 := by
  unfold goodScaleResponseSlot
  let S : Set ℝ := {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
    r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
      Real.sqrt (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        q = section6Response M n n omega z e})}
  change sSup S ≤ _
  by_cases hS : S.Nonempty
  · apply csSup_le hS
    intro r hr
    rcases hr with ⟨j, n, hjm, hnj, z, hzgrid, hzann, rfl⟩
    let A : Set ℝ := {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
      q = section6Response M n (min n (none.getD n)) omega z e}
    have hAbdd : BddAbove A := by
      simpa only [A, Option.getD_none, min_self] using
        bddAbove_section6Response_unitSphere M n n omega z
    have hAne : A.Nonempty := by
      have hd : 2 ≤ d := M.shellPrefix.dimension
      let i : Fin d := ⟨0, by omega⟩
      let e : Vec d := Pi.single i 1
      refine ⟨section6Response M n (min n (none.getD n)) omega z e, e, ?_, rfl⟩
      rw [vecNormSq, vecDot, Finset.sum_eq_single i]
      · simp [e]
      · intro b _ hbi
        simp [e, Pi.single_eq_of_ne hbi]
      · simp
    have hA0 : 0 ≤ sSup A := by
      obtain ⟨q, hq⟩ := hAne
      rcases hq with ⟨e, he, rfl⟩
      have hJ : 0 ≤ section6Response M n (min n (none.getD n)) omega z e := by
        simp only [Option.getD_none, min_self]
        unfold section6Response paperScalarProbe
        exact Ch02.responseJ_nonneg _ _ _ _
      exact hJ.trans (le_csSup hAbdd ⟨e, he, rfl⟩)
    have hresp : sSup A ≤ epsilon ^ 2 *
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := by
      refine csSup_le hAne ?_
      intro q hq
      rcases hq with ⟨e, he, rfl⟩
      simpa only [A, sub_zero, Option.getD_none, min_self] using hgood.2.2 j n hjm hnj z
        (by simpa only [sub_zero] using hzgrid)
        (by simpa only [sub_zero] using hzann) e he
    have hsqrt : Real.sqrt (sSup A) ≤ epsilon *
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by
      have hright : 0 ≤ epsilon *
          (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by positivity
      rw [Real.sqrt_le_iff]
      refine ⟨hright, hresp.trans_eq ?_⟩
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    let t : ℝ := (3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ))) / 16)
    have ht0 : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
    have htinv : t⁻¹ =
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16) := by
      dsimp only [t]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    have htrunc := pow_eight_mul_le_truncated_add_pow_eight ht0 hepsilon
      (Real.sqrt_nonneg _) (by rwa [htinv])
    have hsqrtMin : min (Real.sqrt (sSup A)) 1 =
        Real.sqrt (min (sSup A) 1) := by
      have hmono : Monotone Real.sqrt := fun _ _ h ↦ Real.sqrt_le_sqrt h
      symm
      calc
        Real.sqrt (min (sSup A) 1) =
            min (Real.sqrt (sSup A)) (Real.sqrt 1) := hmono.map_min
        _ = min (Real.sqrt (sSup A)) 1 := by rw [Real.sqrt_one]
    have hweight : t ^ 8 =
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) := by
      dsimp only [t]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    rw [hweight, hsqrtMin] at htrunc
    have htruncated :
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
            Real.sqrt (min (sSup A) 1) ≤
          accumulatedError M none m 0 s omega := by
      apply truncatedResponseAtom_le_accumulatedError M none s m 0 omega
        (truncatedResponseSet_bddAbove M hs omega) hjm hnj
      · simpa only [sub_zero] using hzgrid
      · simpa only [sub_zero] using hzann
    have hadd := add_le_add htruncated (le_refl (epsilon ^ 8))
    simpa only [A, Option.getD_none, min_self] using htrunc.trans hadd
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [hEmpty, Real.sSup_empty]
    exact add_nonneg (accumulatedError_nonneg M none s m 0 omega)
      (pow_nonneg hepsilon 8)

private theorem cube_nonempty (d : ℕ) (m : ℤ) : (cube d m).Nonempty := by
  exact ⟨0, Section6ExcessDecay.zero_mem_cube d m⟩

private theorem bddAbove_abs_values_cube {d : ℕ} (m : ℤ)
    {f : Vec d → ℝ} (hf : Continuous f) :
    BddAbove {r : ℝ | ∃ x ∈ cube d m, r = |f x|} := by
  let Q := originCube d m
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      ((continuous_abs.comp hf).continuousOn)
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hC x hx'
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using
    h.trans (le_max_right _ _)

private theorem supNormOn_add_le_cube {d : ℕ} (m : ℤ)
    {f g : Vec d → ℝ} (hf : Continuous f) (hg : Continuous g) :
    supNormOn (cube d m) (fun x ↦ f x + g x) ≤
      supNormOn (cube d m) f + supNormOn (cube d m) g := by
  unfold supNormOn
  apply csSup_le
  · obtain ⟨x, hx⟩ := cube_nonempty d m
    exact ⟨|f x + g x|, x, hx, rfl⟩
  · rintro r ⟨x, hx, rfl⟩
    calc
      |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
      _ ≤ sSup {r : ℝ | ∃ y ∈ cube d m, r = |f y|} +
          sSup {r : ℝ | ∃ y ∈ cube d m, r = |g y|} :=
        add_le_add
          (le_csSup (bddAbove_abs_values_cube m hf) ⟨x, hx, rfl⟩)
          (le_csSup (bddAbove_abs_values_cube m hg) ⟨x, hx, rfl⟩)

private theorem fullShellBlock_eq_zero_add_shellBlock {d : ℕ}
    (m : ℕ) (omega : Sample d) (x : Vec d) :
    fullShellBlock m omega x = omega 0 x + shellBlock m 0 omega x := by
  unfold fullShellBlock shellBlock
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  apply Finset.sum_bij (fun k _ ↦ k + 1)
  · intro k hk
    simp only [Finset.mem_Icc]
    rw [Finset.mem_range] at hk
    omega
  · intro a ha b hb hab
    omega
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    refine ⟨i - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  · intro k hk
    rfl

theorem goodScaleShellSlot_le_accumulatedError
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) (m : ℕ)
    (omega : Sample d) :
    goodScaleShellSlot s m omega ≤ accumulatedError M none m 0 s omega := by
  unfold goodScaleShellSlot
  have h := shellSlot_le_accumulatedError M none s m 0 omega
  have hcube : translatedCube d (m : ℤ) 0 = cube d (m : ℤ) := by
    unfold translatedCube
    simp
  rw [hcube] at h
  exact h

theorem goodScaleGradientSlot_le_accumulatedError
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) (m : ℕ)
    (omega : Sample d) :
    goodScaleGradientSlot m omega ≤ accumulatedError M none m 0 s omega := by
  unfold goodScaleGradientSlot
  have h := gradientSuffix_le_accumulatedError M none s m 0 omega
  have hcube : translatedCube d (m : ℤ) 0 = cube d (m : ℤ) := by
    unfold translatedCube
    simp
  rw [hcube] at h
  exact h

theorem goodScaleFullSlot_le_two_mul_accumulatedError
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) (m : ℕ)
    (omega : Sample d) :
    goodScaleFullSlot s m omega ≤ 2 * accumulatedError M none m 0 s omega := by
  have hcontinuous0 : Continuous (omega 0 : Vec d → ℝ) := (omega 0).1.1.continuous
  have hcontinuousBlock : Continuous (shellBlock m 0 omega) := by
    unfold shellBlock
    fun_prop
  have hfun : fullShellBlock m omega = fun x ↦ omega 0 x + shellBlock m 0 omega x := by
    funext x
    exact fullShellBlock_eq_zero_add_shellBlock m omega x
  have hsup : supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) ≤
      supNormOn (cube d (m : ℤ)) (omega 0) +
        supNormOn (cube d (m : ℤ)) (shellBlock m 0 omega) := by
    rw [hfun]
    exact supNormOn_add_le_cube (m : ℤ) hcontinuous0 hcontinuousBlock
  let w : ℝ := (3 : ℝ) ^ (-(s / 8) * (m : ℝ))
  have hw : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
  have hweighted := mul_le_mul_of_nonneg_left hsup hw
  have hzero : w * supNormOn (cube d (m : ℤ)) (omega 0) ≤
      accumulatedError M none m 0 s omega := by
    have h := shellZeroTerm_le_accumulatedError M none s m 0 omega
    have hcube : translatedCube d (m : ℤ) 0 = cube d (m : ℤ) := by
      unfold translatedCube
      simp
    rw [hcube] at h
    simpa only [w] using h
  have hblock : w * supNormOn (cube d (m : ℤ)) (shellBlock m 0 omega) ≤
      accumulatedError M none m 0 s omega := by
    have h := weighted_shellBlock_le_accumulatedError M none s m 0 0 omega
      (Nat.zero_le m)
    have hcube : translatedCube d (m : ℤ) 0 = cube d (m : ℤ) := by
      unfold translatedCube
      simp
    rw [hcube] at h
    simpa only [w, Nat.cast_zero, sub_zero] using h
  unfold goodScaleFullSlot
  dsimp only [w] at hweighted hzero hblock
  nlinarith

/-- The first and second clauses of the proved good-scale proposition,
combined after the response truncation.  This is the origin-centred form of
`e.mathcalE.bound.applied`. -/
theorem exists_section6HomogenizationError_le_min_accumulatedError (d : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      ∀ L m : ℕ, m ≤ L → ∀ omega,
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
          omega ∈ goodEvent M none m 0 epsilon s →
            section6HomogenizationError M s L m omega 0 ≤
              K * min epsilon (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                accumulatedError M none m 0 s omega) := by
  obtain ⟨C, hC, hbase⟩ := SubdiffusiveProcess.Frozen.Section6.good_scale_mathcal_e d
  refine ⟨5 * C, by positivity, ?_⟩
  intro M s hs L m hmL omega epsilon hepsilon hgood
  have hs0 : 0 ≤ s :=
    (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hs.1
  have hD0 : 0 ≤ s⁻¹ * M.delta ^ 2 :=
    mul_nonneg (inv_nonneg.mpr hs0) (sq_nonneg _)
  have hepsilon0 : 0 ≤ epsilon := hD0.trans hepsilon.1
  have hgoodOne : omega ∈ goodEvent M none m 0 1 s :=
    goodEvent_subset_one M none m 0 hepsilon0 hepsilon.2 hgood
  have hraw := (hbase M s hs L m hmL omega).1
  rw [indicatorValue, if_pos hgoodOne] at hraw
  have hraw' : section6HomogenizationError M s L m omega 0 ≤
      C * goodScaleResponseSlot M s m omega + C * s⁻¹ * M.delta ^ 2 +
        C * goodScaleShellSlot s m omega + C * goodScaleFullSlot s m omega +
        C * goodScaleGradientSlot m omega := by
    simpa only [goodScaleResponseSlot, goodScaleShellSlot, goodScaleFullSlot,
      fullShellBlock, goodScaleGradientSlot, add_assoc, mul_assoc] using hraw
  let E := accumulatedError M none m 0 s omega
  let B := s⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E
  have hE0 : 0 ≤ E := accumulatedError_nonneg M none s m 0 omega
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hresp := goodScaleResponseSlot_le_responseSlot_add_pow_eight
    M hepsilon0 hs0 hgood
  have hshell := goodScaleShellSlot_le_accumulatedError M s m omega
  have hfull := goodScaleFullSlot_le_two_mul_accumulatedError M s m omega
  have hgrad := goodScaleGradientSlot_le_accumulatedError M s m omega
  have hrespC := mul_le_mul_of_nonneg_left hresp hC.le
  have hshellC := mul_le_mul_of_nonneg_left hshell hC.le
  have hfullC := mul_le_mul_of_nonneg_left hfull hC.le
  have hgradC := mul_le_mul_of_nonneg_left hgrad hC.le
  have hrefined : section6HomogenizationError M s L m omega 0 ≤ 5 * C * B := by
    dsimp only [E, B] at *
    nlinarith [hraw', hrespC, hshellC, hfullC, hgradC,
      mul_nonneg hC.le hD0, mul_nonneg hC.le (pow_nonneg hepsilon0 8)]
  have hepsilonCap := (hbase M s hs L m hmL omega).2 epsilon hepsilon hgood
  rcases le_total epsilon B with heB | hBe
  · rw [min_eq_left heB]
    exact hepsilonCap.trans <| by
      have : C * epsilon ≤ 5 * C * epsilon := by
        nlinarith [mul_nonneg hC.le hepsilon0]
      simpa only [mul_assoc] using this
  · rw [min_eq_right hBe]
    simpa only [mul_assoc] using hrefined

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
