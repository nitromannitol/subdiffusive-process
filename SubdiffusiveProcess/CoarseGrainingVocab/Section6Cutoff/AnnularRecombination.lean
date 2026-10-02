import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.RefinedLocalMathcalE
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ScaleSaturation
import SubdiffusiveProcess.Frozen.Section3.AnnealedMatrixBounds

/-!
# Finite-cutoff annular recombination

This module contains the part of the cutoff good-scale error argument that is
independent of the positive-scale localization estimate.  It replaces the
uncutoff response slot by the literal `min n L` slot, pays the manuscript's
`epsilon ^ 8` truncation residue, reads the unchanged field slots from
`accumulatedError M (some L)`, and performs the final `min` recombination.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

/-- The centered shell exponent in the cutoff identity
`a_(m ∧ L) / a_(n ∧ L)`. -/
def cutoffCenteredShellExponent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m n : ℕ)
    (omega : Sample d) (x : Vec d) : ℝ :=
  cutoffShellSum (min m L) ((min n L : ℕ) : ℤ) x omega -
    (((((min m L : ℕ) : ℤ) - ((min n L : ℕ) : ℤ)) : ℤ) : ℝ) *
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P

/-- Source display `e.cutoff.regularity.centered.ratio`, expressed through
the existing centered-shell carrier. -/
theorem aCutoff_min_ratio_eq_exp_cutoffCenteredShellExponent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {n m : ℕ} (hnm : n ≤ m) (omega : Sample d) (x : Vec d) :
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (min m L) omega x /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (min n L) omega x =
      Real.exp (cutoffCenteredShellExponent M L m n omega x) := by
  have hmin : min n L ≤ min m L := min_le_min_right L hnm
  rcases eq_or_lt_of_le hmin with heq | hlt
  · rw [heq, div_self (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos
      M (min m L) omega x).ne']
    unfold cutoffCenteredShellExponent cutoffShellSum cutoffShellIndices
    rw [heq]
    have hidx : ((((min m L : ℕ) : ℤ) + 1).toNat) = min m L + 1 := by
      omega
    rw [hidx]
    simp
  · have hrepr := cutoffRatioMinusOne_eq_exp_shell
      M (min m L) ((min n L : ℕ) : ℤ) omega x
        (by omega) (by exact_mod_cast hlt)
    unfold cutoffRatioMinusOne at hrepr
    have hnonneg : ¬ ((min n L : ℕ) : ℤ) < 0 := by omega
    simp only [aCutoffAtInt, hnonneg, if_false] at hrepr
    have htoNat : (((min n L : ℕ) : ℤ).toNat) = min n L := by omega
    rw [htoNat] at hrepr
    unfold cutoffCenteredShellExponent
    linarith

/-- Source display `e.cutoff.regularity.D.ordering`.  Truncating both scales
at `L` can only shorten the deterministic annealed-ordering exponent. -/
theorem cutoff_ahom_ratio_ordering
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {n m : ℕ} (hnm : n ≤ m) :
    1 ≤ ahom M (min n L) / ahom M (min m L) ∧
      ahom M (min n L) / ahom M (min m L) ≤
        Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
          ((m - n : ℕ) : ℝ)) := by
  have hmin : min n L ≤ min m L := min_le_min_right L hnm
  have hnpos : 0 < ahom M (min n L) := ahom_pos M _
  have hmpos : 0 < ahom M (min m L) := ahom_pos M _
  constructor
  · rw [one_le_div₀ hmpos]
    rcases eq_or_lt_of_le hmin with heq | hlt
    · rw [heq]
    · exact (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds.2
        M (min m L) (min n L) hlt).1
  · rcases eq_or_lt_of_le hmin with heq | hlt
    · rw [heq, div_self hmpos.ne']
      exact Real.one_le_exp <| mul_nonneg
        (mul_nonneg (by norm_num) M.G4.tauSq_pos.le) (by positivity)
    · have hraw := (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds.2
        M (min m L) (min n L) hlt).2
      have hratio : ahom M (min n L) / ahom M (min m L) ≤
          Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
            (((min m L) - (min n L) : ℕ) : ℝ)) := by
        exact (div_le_iff₀ hmpos).2 hraw
      refine hratio.trans (Real.exp_le_exp.mpr ?_)
      have hgap : min m L - min n L ≤ m - n := by omega
      have hgapReal : (((min m L) - (min n L) : ℕ) : ℝ) ≤
          ((m - n : ℕ) : ℝ) := by exact_mod_cast hgap
      exact mul_le_mul_of_nonneg_left hgapReal
        (mul_nonneg (by norm_num) M.G4.tauSq_pos.le)

/-- The response display slot with every local coefficient stopped at the
deterministic cutoff `L`. -/
def cutoffGoodScaleResponseSlot
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s : ℝ) (m : ℕ) (omega : Sample d) : ℝ :=
  sSup {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
    r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
      Real.sqrt (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        q = section6Response M n (min n L) omega z e})}

private theorem cutoffTruncatedResponseSet_bddAbove
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {m : ℕ} {s : ℝ} (hs : 0 ≤ s) (omega : Sample d) :
    BddAbove {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n (z - 0) ∧
        z - 0 ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          Real.sqrt (min (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            q = section6Response M n (min n L) omega z e}) 1)} := by
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
        q = section6Response M n (min n L) omega z e}) 1) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (min_le_right _ 1)
  exact (mul_le_mul hw hsqrt (Real.sqrt_nonneg _) (by positivity)).trans_eq
    (mul_one 1)

/-- The printed `x ≤ epsilon 3^(sD/16)` split on the literal finite-cutoff
response carrier. -/
theorem cutoffGoodScaleResponseSlot_le_accumulatedError_add_pow_eight
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {m : ℕ} {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon) (hs : 0 ≤ s)
    {omega : Sample d}
    (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s) :
    cutoffGoodScaleResponseSlot M L s m omega ≤
      accumulatedError M (some L) m 0 s omega + epsilon ^ 8 := by
  unfold cutoffGoodScaleResponseSlot
  let S : Set ℝ := {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
    r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
      Real.sqrt (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        q = section6Response M n (min n L) omega z e})}
  change sSup S ≤ _
  by_cases hS : S.Nonempty
  · apply csSup_le hS
    rintro _ ⟨j, n, hjm, hnj, z, hzgrid, hzann, rfl⟩
    let A : Set ℝ := {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
      q = section6Response M n (min n L) omega z e}
    have hAbdd : BddAbove A := by
      simpa only [A] using
        bddAbove_section6Response_unitSphere M n (min n L) omega z
    have hAne : A.Nonempty := by
      have hd : 2 ≤ d := M.shellPrefix.dimension
      let i : Fin d := ⟨0, by omega⟩
      let e : Vec d := Pi.single i 1
      refine ⟨section6Response M n (min n L) omega z e, e, ?_, rfl⟩
      rw [vecNormSq, vecDot, Finset.sum_eq_single i]
      · simp [e]
      · intro b _ hbi
        simp [e, Pi.single_eq_of_ne hbi]
      · simp
    have hA0 : 0 ≤ sSup A := by
      obtain ⟨q, e, he, rfl⟩ := hAne
      have hJ : 0 ≤ section6Response M n (min n L) omega z e := by
        unfold section6Response paperScalarProbe
        exact Ch02.responseJ_nonneg _ _ _ _
      exact hJ.trans (le_csSup hAbdd ⟨e, he, rfl⟩)
    have hresp : sSup A ≤ epsilon ^ 2 *
        (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8) := by
      refine csSup_le hAne ?_
      rintro _ ⟨e, he, rfl⟩
      simpa only [A, sub_zero, Option.getD_some] using
        hgood.2.2 j n hjm hnj z
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
          accumulatedError M (some L) m 0 s omega := by
      apply truncatedResponseAtom_le_accumulatedError M (some L) s m 0 omega
        (cutoffTruncatedResponseSet_bddAbove M L hs omega) hjm hnj
      · simpa only [sub_zero] using hzgrid
      · simpa only [sub_zero] using hzann
    have hadd := add_le_add htruncated (le_refl (epsilon ^ 8))
    simpa only [A, Option.getD_some] using htrunc.trans hadd
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [hEmpty, Real.sSup_empty]
    have hE := accumulatedError_nonneg M (some L) s m 0 omega
    positivity

/-- The shell-block slot is unchanged by the response cutoff. -/
theorem goodScaleShellSlot_le_cutoffAccumulatedError
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s : ℝ) (m : ℕ) (omega : Sample d) :
    goodScaleShellSlot s m omega ≤
      accumulatedError M (some L) m 0 s omega := by
  unfold goodScaleShellSlot
  have h := shellSlot_le_accumulatedError M (some L) s m 0 omega
  have hcube : translatedCube d (m : ℤ) 0 = cube d (m : ℤ) := by
    unfold translatedCube
    simp
  rw [hcube] at h
  exact h

/-- The gradient-tail slot is unchanged by the response cutoff. -/
theorem goodScaleGradientSlot_le_cutoffAccumulatedError
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s : ℝ) (m : ℕ) (omega : Sample d) :
    goodScaleGradientSlot m omega ≤
      accumulatedError M (some L) m 0 s omega := by
  unfold goodScaleGradientSlot
  have h := gradientSuffix_le_accumulatedError M (some L) s m 0 omega
  have hcube : translatedCube d (m : ℤ) 0 = cube d (m : ℤ) := by
    unfold translatedCube
    simp
  rw [hcube] at h
  exact h

private theorem cube_nonempty (d : ℕ) (m : ℤ) :
    (cube d m).Nonempty := by
  exact ⟨0, Section6ExcessDecay.zero_mem_cube d m⟩

private theorem bddAbove_abs_values_cube (m : ℤ)
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

private theorem supNormOn_add_le_cube (m : ℤ)
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

private theorem fullShellBlock_eq_zero_add_shellBlock
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

/-- The full low-frequency field slot costs two copies of the cutoff
accumulated error, exactly as in the infinite-cutoff recombination. -/
theorem goodScaleFullSlot_le_two_mul_cutoffAccumulatedError
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (s : ℝ) (m : ℕ) (omega : Sample d) :
    goodScaleFullSlot s m omega ≤
      2 * accumulatedError M (some L) m 0 s omega := by
  have hcontinuous0 : Continuous (omega 0 : Vec d → ℝ) :=
    (omega 0).1.1.continuous
  have hcontinuousBlock : Continuous (shellBlock m 0 omega) := by
    unfold shellBlock
    fun_prop
  have hfun : fullShellBlock m omega =
      fun x ↦ omega 0 x + shellBlock m 0 omega x := by
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
      accumulatedError M (some L) m 0 s omega := by
    have h := shellZeroTerm_le_accumulatedError M (some L) s m 0 omega
    have hcube : translatedCube d (m : ℤ) 0 = cube d (m : ℤ) := by
      unfold translatedCube
      simp
    rw [hcube] at h
    simpa only [w] using h
  have hblock : w * supNormOn (cube d (m : ℤ)) (shellBlock m 0 omega) ≤
      accumulatedError M (some L) m 0 s omega := by
    have h := weighted_shellBlock_le_accumulatedError
      M (some L) s m 0 0 omega (Nat.zero_le m)
    have hcube : translatedCube d (m : ℤ) 0 = cube d (m : ℤ) := by
      unfold translatedCube
      simp
    rw [hcube] at h
    simpa only [w, Nat.cast_zero, sub_zero] using h
  unfold goodScaleFullSlot
  dsimp only [w] at hweighted hzero hblock
  nlinarith

/-- Final deterministic annular recombination.  The input `hraw` is the one
remaining localization statement for the `m > L` branch; all conversion to
the literal frozen cutoff carrier is discharged here. -/
theorem section6HomogenizationError_le_cutoff_min_of_slot_bound
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    {s epsilon C : ℝ} (hC : 0 < C) (hs : 0 ≤ s)
    (hepsilon : epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1)
    (omega : Sample d)
    (hgood : omega ∈ goodEvent M (some L) m 0 epsilon s)
    (hraw : section6HomogenizationError M s L m omega 0 ≤
      C * (cutoffGoodScaleResponseSlot M L s m omega +
        s⁻¹ * M.delta ^ 2 + goodScaleShellSlot s m omega +
        goodScaleFullSlot s m omega + goodScaleGradientSlot m omega))
    (hepsilonCap : section6HomogenizationError M s L m omega 0 ≤
      C * epsilon) :
    section6HomogenizationError M s L m omega 0 ≤
        5 * C * min epsilon
          (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M (some L) m 0 s omega) ∧
      section6HomogenizationError M s L m omega 0 ≤ 5 * C * epsilon := by
  have hD0 : 0 ≤ s⁻¹ * M.delta ^ 2 :=
    mul_nonneg (inv_nonneg.mpr hs) (sq_nonneg _)
  have hepsilon0 : 0 ≤ epsilon := hD0.trans hepsilon.1
  let E := accumulatedError M (some L) m 0 s omega
  let B := s⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E
  have hE0 : 0 ≤ E := accumulatedError_nonneg M (some L) s m 0 omega
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hresp :=
    cutoffGoodScaleResponseSlot_le_accumulatedError_add_pow_eight
      M L hepsilon0 hs hgood
  have hshell := goodScaleShellSlot_le_cutoffAccumulatedError M L s m omega
  have hfull :=
    goodScaleFullSlot_le_two_mul_cutoffAccumulatedError M L s m omega
  have hgrad := goodScaleGradientSlot_le_cutoffAccumulatedError M L s m omega
  have hrefined : section6HomogenizationError M s L m omega 0 ≤
      5 * C * B := by
    dsimp only [E, B] at *
    have hC0 : 0 ≤ C := hC.le
    nlinarith [mul_le_mul_of_nonneg_left hresp hC0,
      mul_le_mul_of_nonneg_left hshell hC0,
      mul_le_mul_of_nonneg_left hfull hC0,
      mul_le_mul_of_nonneg_left hgrad hC0,
      mul_nonneg hC0 hD0,
      mul_nonneg hC0 (pow_nonneg hepsilon0 8)]
  constructor
  · rcases le_total epsilon B with heB | hBe
    · rw [min_eq_left heB]
      exact hepsilonCap.trans <| by
        have : C * epsilon ≤ 5 * C * epsilon := by
          nlinarith [mul_nonneg hC.le hepsilon0]
        simpa only [mul_assoc] using this
    · rw [min_eq_right hBe]
      simpa only [mul_assoc] using hrefined
  · exact hepsilonCap.trans <| by
      have : C * epsilon ≤ 5 * C * epsilon := by
        nlinarith [mul_nonneg hC.le hepsilon0]
      simpa only [mul_assoc] using this

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
