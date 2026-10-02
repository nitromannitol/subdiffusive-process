import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.RatioAssembly
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.GoodScaleSuffix
import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments

/-!
# Hölder Step 3: the stopped coefficient-ratio display

This is the deterministic content of `e.ratio.of.bs`.  The two stopped rows
at the translated centre and at the origin fund the finite shell block and
both parent suffixes.  A strict subunit bad-scale density supplies the genuine
summability certificates needed to read the `tsum` stored in
`accumulatedError`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem subinterval_error_sum_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) (omega : Sample d)
    {n q m : ℕ} (hnq : n ≤ q) (z : Vec d) :
    (∑ i ∈ Finset.Icc (q + 1) m, accumulatedError M none i z s omega) ≤
      ∑ i ∈ Finset.Icc n m, accumulatedError M none i z s omega := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  · intro i _hi _hout
    exact accumulatedError_nonneg M none s i z omega

private theorem one_error_le_sum {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) (omega : Sample d)
    {n m : ℕ} (hnm : n ≤ m) (z : Vec d) :
    accumulatedError M none m z s omega ≤
      ∑ i ∈ Finset.Icc n m, accumulatedError M none i z s omega := by
  exact Finset.single_le_sum
    (fun i _ => accumulatedError_nonneg M none s i z omega)
    (Finset.mem_Icc.mpr ⟨hnm, le_rfl⟩)

/-- The explicit parent/shell budget has the manuscript's linear exponential
form.  This elementary collapse is uniform in the window length. -/
theorem stopped_ratio_budget_le_exp {d : ℕ} {E s R : ℝ}
    (hE : 0 ≤ E) (hR : R ≤ E) :
    (1 + (d : ℝ) * E * Real.exp ((d : ℝ) * E)) ^ 2 *
        Real.exp (E / (3 : ℝ) ^ (-(s / 8)) + R) ≤
      Real.exp ((4 * (d : ℝ) + ((3 : ℝ) ^ (-(s / 8)))⁻¹ + 1) * E) := by
  let t := (d : ℝ) * E
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg d) hE
  have hone : 1 ≤ Real.exp t := Real.one_le_exp ht
  have htone : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have hparentOne : 1 + t * Real.exp t ≤ Real.exp (2 * t) := by
    calc
      1 + t * Real.exp t ≤ Real.exp t + t * Real.exp t :=
        by simpa only [add_comm] using add_le_add_right hone (t * Real.exp t)
      _ = Real.exp t * (t + 1) := by ring
      _ ≤ Real.exp t * Real.exp t :=
        mul_le_mul_of_nonneg_left htone (Real.exp_pos _).le
      _ = Real.exp (2 * t) := by rw [← Real.exp_add]; congr 1; ring
  have hparent : (1 + (d : ℝ) * E * Real.exp ((d : ℝ) * E)) ^ 2 ≤
      Real.exp (4 * (d : ℝ) * E) := by
    change (1 + t * Real.exp t) ^ 2 ≤ _
    calc
      (1 + t * Real.exp t) ^ 2 ≤ (Real.exp (2 * t)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hparentOne 2
      _ = Real.exp (4 * (d : ℝ) * E) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        dsimp [t]
        ring
  have hw : 0 < (3 : ℝ) ^ (-(s / 8)) := Real.rpow_pos_of_pos (by norm_num) _
  have hBR : E / (3 : ℝ) ^ (-(s / 8)) + R ≤
      (((3 : ℝ) ^ (-(s / 8)))⁻¹ + 1) * E := by
    rw [div_eq_inv_mul]
    nlinarith
  calc
    (1 + (d : ℝ) * E * Real.exp ((d : ℝ) * E)) ^ 2 *
          Real.exp (E / (3 : ℝ) ^ (-(s / 8)) + R)
        ≤ Real.exp (4 * (d : ℝ) * E) *
            Real.exp ((((3 : ℝ) ^ (-(s / 8)))⁻¹ + 1) * E) :=
      mul_le_mul hparent (Real.exp_le_exp.mpr hBR) (Real.exp_pos _).le
        (by positivity)
    _ = Real.exp ((4 * (d : ℝ) + ((3 : ℝ) ^ (-(s / 8)))⁻¹ + 1) * E) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The literal lower translated average is comparable to the parent cube
average, with every deterministic loss displayed explicitly. -/
theorem stopped_tailAverage_ratio_bounds {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L n q m : ℕ}
    (hnm : n < m) (hnq : n ≤ q) (hqm : q ≤ m) (hmL : m ≤ L)
    (epsilon s lambda E : ℝ) (hepsilon : 0 ≤ epsilon) (hs : s ≤ 1 / 2)
    (hlambda : lambda < 1) (omega : Sample d) (z : Vec d)
    (hz : z ∈ cube d m)
    (hsumZ : (∑ i ∈ Finset.Icc n m,
      accumulatedError M none i z s omega) ≤ E)
    (hsum0 : (∑ i ∈ Finset.Icc n m,
      accumulatedError M none i 0 s omega) ≤ E)
    (hbadZ : (∑ i ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M none i z epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ)))
    (hbad0 : (∑ i ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M none i 0 epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ))) :
    let P := (1 + (d : ℝ) * E * Real.exp ((d : ℝ) * E)) ^ 2
    let B := E / (3 : ℝ) ^ (-(s / 8))
    let R := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - q : ℕ) : ℝ)
    tailAverage M L q omega (translatedCube d (q : ℤ) z) /
        tailCoefficientCubeAverage M L m omega ≤ P * Real.exp (B + R) ∧
      tailCoefficientCubeAverage M L m omega /
        tailAverage M L q omega (translatedCube d (q : ℤ) z) ≤
          P * Real.exp (B + R) := by
  dsimp only
  obtain ⟨aZ, haZ, hgoodZ⟩ := exists_goodEvent_of_badCount_lt
    M epsilon s lambda hnm hlambda z omega hbadZ
  obtain ⟨a0, ha0, hgood0⟩ := exists_goodEvent_of_badCount_lt
    M epsilon s lambda hnm hlambda 0 omega hbad0
  have hgoodZT : GoodFieldOne aZ 0 epsilon s (translatePotentialSample z omega) :=
    (Section6Covariance.goodFieldOne_translatePotentialSample
      aZ 0 epsilon s z omega).2 (by simpa only [add_zero] using hgoodZ.1)
  have hsumTailZ : Summable (fun i : ℕ => if m ≤ i then
      (3 : ℝ) ^ m * vectorSupNormOn (cube d m)
        (shellGradient (translatePotentialSample z omega i)) else 0) :=
    summable_parentGradientTail_of_goodFieldOne
      (Finset.mem_Icc.mp haZ).2 hepsilon hs (translatePotentialSample z omega) hgoodZT
  have hsumTail0 : Summable (fun i : ℕ => if m ≤ i then
      (3 : ℝ) ^ m * vectorSupNormOn (cube d m)
        (shellGradient (omega i)) else 0) :=
    summable_parentGradientTail_of_goodFieldOne
      (Finset.mem_Icc.mp ha0).2 hepsilon hs omega hgood0.1
  have herrZ : accumulatedError M none m z s omega ≤ E :=
    (one_error_le_sum M s omega (le_of_lt hnm) z).trans hsumZ
  have herr0 : accumulatedError M none m 0 s omega ≤ E :=
    (one_error_le_sum M s omega (le_of_lt hnm) 0).trans hsum0
  have htailZ : longRatioGradientTail m (translatePotentialSample z omega) ≤ E :=
    (longRatioGradientTail_translate_le_accumulatedError M none s m z omega).trans herrZ
  have htail0 : longRatioGradientTail m omega ≤ E :=
    (longRatioGradientTail_le_accumulatedError_zero M none s m omega).trans herr0
  let AZ := (d : ℝ) * longRatioGradientTail m (translatePotentialSample z omega) *
    Real.exp ((d : ℝ) * longRatioGradientTail m (translatePotentialSample z omega))
  let A0 := (d : ℝ) * longRatioGradientTail m omega *
    Real.exp ((d : ℝ) * longRatioGradientTail m omega)
  let A := (d : ℝ) * E * Real.exp ((d : ℝ) * E)
  have hE0 : 0 ≤ E := (accumulatedError_nonneg M none s m z omega).trans herrZ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hAZ : AZ ≤ A := by
    dsimp only [AZ, A]
    have hde : (d : ℝ) * longRatioGradientTail m
        (translatePotentialSample z omega) ≤ (d : ℝ) * E :=
      mul_le_mul_of_nonneg_left htailZ hd0
    exact mul_le_mul hde (Real.exp_le_exp.mpr hde) (Real.exp_pos _).le
      (mul_nonneg hd0 hE0)
  have hA0 : A0 ≤ A := by
    dsimp only [A0, A]
    have hde : (d : ℝ) * longRatioGradientTail m omega ≤ (d : ℝ) * E :=
      mul_le_mul_of_nonneg_left htail0 hd0
    exact mul_le_mul hde (Real.exp_le_exp.mpr hde) (Real.exp_pos _).le
      (mul_nonneg hd0 hE0)
  have hAnonneg : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hAZ0 : 0 ≤ AZ := by
    dsimp only [AZ]
    exact mul_nonneg
      (mul_nonneg hd0 (longRatioGradientTail_nonneg m _)) (Real.exp_pos _).le
  have hA00 : 0 ≤ A0 := by
    dsimp only [A0]
    exact mul_nonneg
      (mul_nonneg hd0 (longRatioGradientTail_nonneg m _)) (Real.exp_pos _).le
  have hparentPoint : ∀ x ∈ cube d (q : ℤ),
      tailCoefficient M L m (translatePotentialSample z omega) x /
          tailCoefficientCubeAverage M L m omega ≤ (1 + A) ^ 2 ∧
        tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m (translatePotentialSample z omega) x ≤
            (1 + A) ^ 2 := by
    intro x hx
    have hp := parentTail_ratio_bounds M hqm hmL omega hz hx hsumTailZ hsumTail0
    dsimp only at hp
    have hfac : (1 + AZ) * (1 + A0) ≤ (1 + A) ^ 2 := by
      rw [pow_two]
      exact mul_le_mul (by linarith) (by linarith) (by linarith [hA00])
        (by linarith [hAnonneg])
    exact ⟨hp.1.trans hfac, hp.2.trans hfac⟩
  have hshellSum : (∑ i ∈ Finset.Icc (q + 1) m,
      accumulatedError M none i z s omega) ≤ E :=
    (subinterval_error_sum_le M s omega hnq z).trans hsumZ
  have hshellPoint : ∀ x ∈ cube d (q : ℤ),
      |shellBlock m q (translatePotentialSample z omega) x| ≤
        E / (3 : ℝ) ^ (-(s / 8)) := by
    intro x hx
    have hxtrans : z + x ∈ translatedCube d (q : ℤ) z := ⟨x, hx, rfl⟩
    rw [shellBlock_translatePotentialSample, add_comm]
    exact (abs_shellBlock_le_accumulatedError_sum M none s z omega hxtrans).trans
      (div_le_div_of_nonneg_right hshellSum (by positivity))
  have hrho := abs_normalizerLogError_le_of_le M hqm
  exact tailAverage_ratio_bounds_of_budgets M hqm hmL omega z
    (sq_nonneg (1 + A)) hparentPoint hshellPoint hrho

/-- `e.ratio.of.bs` in its final linear-in-window exponential form. -/
theorem stopped_tailAverage_ratio_bounds_exp {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L n q m : ℕ}
    (hnm : n < m) (hnq : n ≤ q) (hqm : q ≤ m) (hmL : m ≤ L)
    (epsilon s lambda : ℝ) (hepsilon : 0 ≤ epsilon) (hs : s ≤ 1 / 2)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (hdelta : M.delta ^ 2 ≤ lambda) (omega : Sample d) (z : Vec d)
    (hz : z ∈ cube d m)
    (hsumZ : (∑ i ∈ Finset.Icc n m,
      accumulatedError M none i z s omega) ≤
        lambda * ((m : ℝ) - (n : ℝ)))
    (hsum0 : (∑ i ∈ Finset.Icc n m,
      accumulatedError M none i 0 s omega) ≤
        lambda * ((m : ℝ) - (n : ℝ)))
    (hbadZ : (∑ i ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M none i z epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ)))
    (hbad0 : (∑ i ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M none i 0 epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ))) :
    let C := 4 * (d : ℝ) + ((3 : ℝ) ^ (-(s / 8)))⁻¹ + 1
    tailAverage M L q omega (translatedCube d (q : ℤ) z) /
        tailCoefficientCubeAverage M L m omega ≤
          Real.exp (C * lambda * ((m : ℝ) - (n : ℝ))) ∧
      tailCoefficientCubeAverage M L m omega /
        tailAverage M L q omega (translatedCube d (q : ℤ) z) ≤
          Real.exp (C * lambda * ((m : ℝ) - (n : ℝ))) := by
  dsimp only
  let E := lambda * ((m : ℝ) - (n : ℝ))
  have hgap0 : 0 ≤ (m : ℝ) - (n : ℝ) := by
    have hnmR : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 (le_of_lt hnm)
    linarith
  have hE0 : 0 ≤ E := mul_nonneg hlambda0 hgap0
  have hlog : Real.log 2 / 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have htau : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P ≤ lambda :=
    (tauSq_le_delta_sq M).trans <|
      (mul_le_of_le_one_left (sq_nonneg M.delta) hlog).trans hdelta
  have hgapQ : ((m - q : ℕ) : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    rw [Nat.cast_sub hqm]
    have hnqR : (n : ℝ) ≤ (q : ℝ) := Nat.cast_le.2 hnq
    linarith
  have hR : SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - q : ℕ) : ℝ) ≤ E := by
    dsimp only [E]
    exact mul_le_mul htau hgapQ (Nat.cast_nonneg _) hlambda0
  have hraw := stopped_tailAverage_ratio_bounds M hnm hnq hqm hmL
    epsilon s lambda E hepsilon hs hlambda1 omega z hz hsumZ hsum0 hbadZ hbad0
  dsimp only at hraw
  have hcollapse := stopped_ratio_budget_le_exp (d := d) (s := s)
    (R := SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * ((m - q : ℕ) : ℝ)) hE0 hR
  constructor
  · exact hraw.1.trans (by simpa only [E, mul_assoc] using hcollapse)
  · exact hraw.2.trans (by simpa only [E, mul_assoc] using hcollapse)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
