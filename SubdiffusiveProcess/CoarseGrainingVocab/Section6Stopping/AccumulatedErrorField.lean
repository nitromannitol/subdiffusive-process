module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ResponseRow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge
public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ExponentialFieldBlock

@[expose] public section

/-!
# Public field carriers for the fixed accumulated-error estimate

This module connects the exact pathwise gradient envelope proved in
`Section6Discharge` to the public Gamma-two shell machinery.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory ProbabilityTheory Homogenization.IndependentSums Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

noncomputable section

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem shellSigma_eq_singleton_stopping (d i : ℕ) :
    shellSigma d i = potentialShellIndexSigma (d := d) ({i} : Set ℕ) := by
  apply le_antisymm
  · exact le_iSup_of_le i (le_iSup_of_le (Set.mem_singleton i) le_rfl)
  · refine iSup_le fun k ↦ iSup_le fun hk ↦ ?_
    rw [Set.mem_singleton_iff] at hk
    subst k
    exact le_rfl

theorem section6TranslatedShellG2_eq_translatedShellG2 {d : ℕ}
    (j : ℕ) (z : Vec d) :
    section6TranslatedShellG2 j z = translatedShellG2 j z := by
  rfl

theorem section6SmallShellEnvelope_eq_translatedSmallShellEnvelope {d : ℕ}
    (j r : ℕ) (z : Vec d) :
    section6SmallShellEnvelope j r z =
      translatedSmallShellEnvelope j (r : ℤ) z := by
  rfl

/-- The `q`th public majorant of the gradient suffix at parent scale `k`. -/
def accumulatedGradientLayer {d : ℕ} (k q : ℕ) (z : Vec d) :
    Sample d → ℝ :=
  section6SmallShellEnvelope (k + q) k z

def accumulatedGradientLayerScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (q : ℕ) : ℝ :=
  (1 / 3 : ℝ) ^ q *
    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)

theorem accumulatedGradientLayer_nonneg {d : ℕ}
    (k q : ℕ) (z : Vec d) (omega : Sample d) :
    0 ≤ accumulatedGradientLayer k q z omega := by
  rw [accumulatedGradientLayer,
    section6SmallShellEnvelope_eq_translatedSmallShellEnvelope]
  exact translatedSmallShellEnvelope_nonneg _ _ _ _

theorem measurable_accumulatedGradientLayer {d : ℕ}
    (k q : ℕ) (z : Vec d) :
    Measurable (accumulatedGradientLayer (d := d) k q z) := by
  rw [accumulatedGradientLayer,
    section6SmallShellEnvelope_eq_translatedSmallShellEnvelope]
  exact measurable_translatedSmallShellEnvelope _ _ _

/-- A gradient layer reads only its actual shell coordinate. -/
theorem measurable_accumulatedGradientLayer_shellSigma {d : ℕ}
    (k q : ℕ) (z : Vec d) :
    Measurable[shellSigma d (k + q)]
      (accumulatedGradientLayer (d := d) k q z) := by
  rw [accumulatedGradientLayer,
    section6SmallShellEnvelope_eq_translatedSmallShellEnvelope,
    shellSigma_eq_singleton_stopping]
  letI : MeasurableSpace (Sample d) :=
    potentialShellIndexSigma ({k + q} : Set ℕ)
  unfold translatedSmallShellEnvelope
  exact measurable_const.mul
    (measurable_translatedShellG2_potentialShellIndexSigma
      (Set.mem_singleton (k + q)) _)

theorem accumulatedGradientLayerScale_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (q : ℕ) :
    0 < accumulatedGradientLayerScale M q := by
  unfold accumulatedGradientLayerScale
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  exact mul_pos (pow_pos (by norm_num) q)
    (mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos)

/-- Moving the observation scale down by `q` exposes exactly the geometric
weight in the manuscript's gradient-window rearrangement. -/
theorem accumulatedGradientLayer_eq_pow_mul_own {d : ℕ}
    (k q : ℕ) (z : Vec d) (omega : Sample d) :
    accumulatedGradientLayer k q z omega =
      (1 / 3 : ℝ) ^ q * accumulatedGradientLayer (k + q) 0 z omega := by
  unfold accumulatedGradientLayer
  rw [section6SmallShellEnvelope_eq_translatedSmallShellEnvelope,
    section6SmallShellEnvelope_eq_translatedSmallShellEnvelope]
  unfold translatedSmallShellEnvelope
  have hsub : (k : ℤ) - ((k + q : ℕ) : ℤ) = -(q : ℤ) := by omega
  rw [hsub]
  simp only [Nat.add_zero, sub_self, zpow_zero, one_mul]
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  norm_num

theorem isBigOWith_gammaTwo_accumulatedGradientLayer {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k q : ℕ) (z : Vec d) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (accumulatedGradientLayer k q z)
      (accumulatedGradientLayerScale M q) := by
  rw [accumulatedGradientLayer,
    section6SmallShellEnvelope_eq_translatedSmallShellEnvelope]
  have h := isBigOWith_gammaTwo_translatedSmallShellEnvelope
    M (k + q) (k : ℤ) z
  convert h using 1
  unfold accumulatedGradientLayerScale
  have hpow : (3 : ℝ) ^ ((k : ℤ) - ((k + q : ℕ) : ℤ)) =
      (1 / 3 : ℝ) ^ q := by
    rw [show (k : ℤ) - ((k + q : ℕ) : ℤ) = -(q : ℤ) by omega,
      zpow_neg, zpow_natCast, ← inv_pow]
    norm_num
  rw [hpow]

theorem summable_accumulatedGradientLayerScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    Summable (accumulatedGradientLayerScale M) := by
  unfold accumulatedGradientLayerScale
  exact (summable_geometric_of_norm_lt_one
    (show ‖(1 / 3 : ℝ)‖ < 1 by norm_num)).mul_right _

theorem tsum_accumulatedGradientLayerScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∑' q, accumulatedGradientLayerScale M q =
      (3 / 2 : ℝ) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
  unfold accumulatedGradientLayerScale
  rw [tsum_mul_right, tsum_geometric_of_norm_lt_one
    (show ‖(1 / 3 : ℝ)‖ < 1 by norm_num)]
  norm_num

def accumulatedGradientEnvelope {d : ℕ} (k : ℕ) (z : Vec d)
    (omega : Sample d) : ℝ :=
  (d : ℝ) * ∑' q, accumulatedGradientLayer k q z omega

def accumulatedGradientEnvelopeScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) : ℝ :=
  (d : ℝ) * gammaTriangleConst 2 * (3 / 2 : ℝ) *
    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)

theorem isBigOWith_gammaTwo_accumulatedGradientEnvelope
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : Vec d) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (accumulatedGradientEnvelope k z)
      (accumulatedGradientEnvelopeScale M) := by
  have hsum := isBigOWith_gammaSigma_tsum_nonneg
    (μ := M.P.toMeasure) (sigma := 2)
    (X := fun q => accumulatedGradientLayer (d := d) k q z)
    (a := accumulatedGradientLayerScale M) (by norm_num)
    (fun q omega => accumulatedGradientLayer_nonneg k q z omega)
    (fun q => measurable_accumulatedGradientLayer k q z)
    (accumulatedGradientLayerScale_pos M)
    (summable_accumulatedGradientLayerScale M)
    (fun q => isBigOWith_gammaTwo_accumulatedGradientLayer M k q z)
  rw [tsum_accumulatedGradientLayerScale] at hsum
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hscaled := hsum.const_mul hd
  simpa only [accumulatedGradientEnvelope, accumulatedGradientEnvelopeScale,
    mul_assoc] using! hscaled

theorem ae_summable_accumulatedGradientLayer {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      Summable (fun q => accumulatedGradientLayer k q z omega) := by
  apply ae_summable_of_isBigOWith_gammaSigma
    (X := fun q => accumulatedGradientLayer (d := d) k q z)
    (a := accumulatedGradientLayerScale M) (by norm_num : (0 : ℝ) < 2)
  · exact fun q omega => accumulatedGradientLayer_nonneg k q z omega
  · exact fun q => (measurable_accumulatedGradientLayer k q z).aemeasurable
  · exact accumulatedGradientLayerScale_pos M
  · exact summable_accumulatedGradientLayerScale M
  · exact fun q => isBigOWith_gammaTwo_accumulatedGradientLayer M k q z

theorem accumulatedGradientLayer_succ {d : ℕ}
    (k q : ℕ) (z : Vec d) (omega : Sample d) :
    accumulatedGradientLayer k (q + 1) z omega =
      (1 / 3 : ℝ) * accumulatedGradientLayer (k + 1) q z omega := by
  calc
    accumulatedGradientLayer k (q + 1) z omega =
        (1 / 3 : ℝ) ^ (q + 1) *
          accumulatedGradientLayer (k + (q + 1)) 0 z omega :=
      accumulatedGradientLayer_eq_pow_mul_own k (q + 1) z omega
    _ = (1 / 3 : ℝ) * ((1 / 3 : ℝ) ^ q *
          accumulatedGradientLayer ((k + 1) + q) 0 z omega) := by
      have hidx : k + (q + 1) = (k + 1) + q := by omega
      rw [hidx]
      rw [pow_succ]
      ring
    _ = (1 / 3 : ℝ) * accumulatedGradientLayer (k + 1) q z omega := by
      rw [accumulatedGradientLayer_eq_pow_mul_own (k + 1) q z omega]

/-- The literal gradient suffix is dominated termwise by the public envelope. -/
theorem accumulatedGradientTerm_le_layer {d : ℕ}
    (k q : ℕ) (z : Vec d) (omega : Sample d) :
    (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
        (shellGradient (omega (k + q))) ≤
      (d : ℝ) * accumulatedGradientLayer k q z omega := by
  exact scaled_vectorSupNormOn_shellGradient_le_envelope
    (j := k + q) (r := k) (by omega) z omega

/-- The literal infinite gradient suffix in `accumulatedError` is bounded,
almost surely, by the public Gamma-two envelope. -/
theorem ae_accumulatedGradientSuffix_le_envelope {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑' j : ℕ, if k ≤ j then
          (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
            (shellGradient (omega j)) else 0) ≤
        accumulatedGradientEnvelope k z omega := by
  filter_upwards [ae_summable_accumulatedGradientLayer M k z] with omega hlayer
  let F : ℕ → ℝ := fun j => if k ≤ j then
    (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
      (shellGradient (omega j)) else 0
  have htail : Summable (fun q : ℕ => F (q + k)) := by
    apply Summable.of_nonneg_of_le
      (fun q => by
        simp only [F, if_pos (by omega : k ≤ q + k)]
        exact mul_nonneg (by positivity)
          (vectorSupNormOn_shellGradient_nonneg
            (j := q + k) (r := k) (by omega) z omega))
      (fun q => by
        simp only [F, if_pos (by omega : k ≤ q + k)]
        simpa only [Nat.add_comm] using!
          accumulatedGradientTerm_le_layer k q z omega)
      (hlayer.mul_left (d : ℝ))
  have hF : Summable F := (summable_nat_add_iff k).mp htail
  have hsum := Summable.tsum_le_tsum
    (fun q => by
      dsimp only [F]
      rw [if_pos (by omega : k ≤ q + k)]
      simpa only [Nat.add_comm] using!
        accumulatedGradientTerm_le_layer k q z omega)
    htail (hlayer.mul_left (d : ℝ))
  have hprefix : ∑ j ∈ Finset.range k, F j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [F, show ¬k ≤ j by simpa using! Finset.mem_range.mp hj]
  have hfull : (∑' j, F j) = ∑' q, F (q + k) := by
    have hsplit := hF.sum_add_tsum_nat_add k
    rw [hprefix, zero_add] at hsplit
    exact hsplit.symm
  rw [← hfull] at hsum
  simpa only [F, accumulatedGradientEnvelope, tsum_mul_left] using! hsum

/-! ## Independent own-scale gradient rows -/

/-- The own-scale member of the gradient rearrangement. -/
def accumulatedGradientOwnRow {d : ℕ}
    (k : ℕ) (z : Vec d) (omega : Sample d) : ℝ :=
  (d : ℝ) * accumulatedGradientLayer k 0 z omega

def accumulatedGradientOwnRowScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) : ℝ :=
  (d : ℝ) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)

/-- One gradient suffix is its own-scale row plus one third of the next
suffix.  This recurrence is the algebraic form of the manuscript's
interchange of the `k,l` sums. -/
theorem accumulatedGradientEnvelope_eq_own_add_third {d : ℕ}
    (k : ℕ) (z : Vec d) (omega : Sample d)
    (hsum : Summable (fun q ↦ accumulatedGradientLayer k q z omega)) :
    accumulatedGradientEnvelope k z omega =
      accumulatedGradientOwnRow k z omega +
        (1 / 3 : ℝ) * accumulatedGradientEnvelope (k + 1) z omega := by
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have htail : (∑' q : ℕ, accumulatedGradientLayer k (q + 1) z omega) =
      (1 / 3 : ℝ) *
        ∑' q : ℕ, accumulatedGradientLayer (k + 1) q z omega := by
    simp_rw [accumulatedGradientLayer_succ]
    rw [tsum_mul_left]
  have hprefix : ∑ q ∈ Finset.range 1,
      accumulatedGradientLayer k q z omega =
        accumulatedGradientLayer k 0 z omega := by simp
  unfold accumulatedGradientEnvelope accumulatedGradientOwnRow
  rw [← hsplit, hprefix, htail]
  ring

theorem ae_forall_accumulatedGradientEnvelope_eq_own_add_third {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ k : ℕ,
      accumulatedGradientEnvelope k z omega =
        accumulatedGradientOwnRow k z omega +
          (1 / 3 : ℝ) * accumulatedGradientEnvelope (k + 1) z omega := by
  filter_upwards [ae_all_iff.2 fun k ↦
    ae_summable_accumulatedGradientLayer M k z] with omega hall
  intro k
  exact accumulatedGradientEnvelope_eq_own_add_third k z omega (hall k)

/-- Summing the suffix recurrence pays the geometric constant `3/2`. -/
theorem sum_accumulatedGradientEnvelope_le {d : ℕ}
    (z : Vec d) {n m : ℕ} (hnm : n ≤ m) (omega : Sample d)
    (hrec : ∀ k : ℕ, accumulatedGradientEnvelope k z omega =
      accumulatedGradientOwnRow k z omega +
        (1 / 3 : ℝ) * accumulatedGradientEnvelope (k + 1) z omega) :
    (∑ k ∈ Finset.Icc n m, accumulatedGradientEnvelope k z omega) ≤
      (3 / 2 : ℝ) *
        ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
          accumulatedGradientEnvelope m z omega) := by
  let E : ℕ → ℝ := fun k ↦ accumulatedGradientEnvelope k z omega
  let O : ℕ → ℝ := fun k ↦ accumulatedGradientOwnRow k z omega
  have hE0 : ∀ k, 0 ≤ E k := fun k ↦ by
    unfold E accumulatedGradientEnvelope
    exact mul_nonneg (Nat.cast_nonneg d) (tsum_nonneg fun q ↦
      accumulatedGradientLayer_nonneg k q z omega)
  have hO0 : ∀ k, 0 ≤ O k := fun k ↦ by
    unfold O accumulatedGradientOwnRow
    exact mul_nonneg (Nat.cast_nonneg d)
      (accumulatedGradientLayer_nonneg k 0 z omega)
  have hshift : (∑ k ∈ Finset.Icc n m, E (k + 1)) =
      ∑ l ∈ Finset.Icc (n + 1) (m + 1), E l := by
    refine Finset.sum_bij (fun k _ ↦ k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      change k + 1 ∈ Finset.Icc (n + 1) (m + 1)
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro a ha b hb hab
      change a + 1 = b + 1 at hab
      omega
    · intro l hl
      rw [Finset.mem_Icc] at hl
      refine ⟨l - 1, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · change l - 1 + 1 = l
        omega
    · intro k hk
      rfl
  have hleft : Finset.Icc n m = insert n (Finset.Icc (n + 1) m) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hright : Finset.Icc (n + 1) (m + 1) =
      insert (m + 1) (Finset.Icc (n + 1) m) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hshiftLe : (∑ k ∈ Finset.Icc n m, E (k + 1)) ≤
      (∑ k ∈ Finset.Icc n m, E k) + E (m + 1) := by
    rw [hshift, hleft, hright,
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    linarith [hE0 n]
  have hsumRec : (∑ k ∈ Finset.Icc n m, E k) =
      (∑ k ∈ Finset.Icc n m, O k) +
        (1 / 3 : ℝ) * ∑ k ∈ Finset.Icc n m, E (k + 1) := by
    calc
      _ = ∑ k ∈ Finset.Icc n m, (O k + (1 / 3 : ℝ) * E (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        simpa only [E, O] using! hrec k
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have htail : (1 / 3 : ℝ) * E (m + 1) ≤ E m := by
    change (1 / 3 : ℝ) * accumulatedGradientEnvelope (m + 1) z omega ≤
      accumulatedGradientEnvelope m z omega
    rw [hrec m]
    exact le_add_of_nonneg_left (hO0 m)
  have hS0 : 0 ≤ ∑ k ∈ Finset.Icc n m, E k :=
    Finset.sum_nonneg fun k _ ↦ hE0 k
  have hOsum0 : 0 ≤ ∑ k ∈ Finset.Icc n m, O k :=
    Finset.sum_nonneg fun k _ ↦ hO0 k
  change (∑ k ∈ Finset.Icc n m, E k) ≤ _
  change _ ≤ (3 / 2 : ℝ) * ((∑ k ∈ Finset.Icc n m, O k) + E m)
  rw [hsumRec]
  have hthirdShift := mul_le_mul_of_nonneg_left hshiftLe (by norm_num : (0 : ℝ) ≤ 1 / 3)
  nlinarith

theorem ae_sum_accumulatedGradientEnvelope_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m, accumulatedGradientEnvelope k z omega) ≤
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := by
  filter_upwards [ae_forall_accumulatedGradientEnvelope_eq_own_add_third M z]
    with omega hrec
  exact sum_accumulatedGradientEnvelope_le z hnm omega hrec

/-- Full gradient-suffix window rearrangement from Step 1 of
`l.sum.the.errors`. -/
theorem ae_sum_accumulatedGradientSuffix_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m, ∑' j : ℕ, if k ≤ j then
          (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
            (shellGradient (omega j)) else 0) ≤
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := by
  filter_upwards
    [ae_all_iff.2 fun k ↦ ae_accumulatedGradientSuffix_le_envelope M k z,
      ae_sum_accumulatedGradientEnvelope_le M z hnm]
      with omega hterm hwindow
  exact (Finset.sum_le_sum fun k _ ↦ hterm k).trans hwindow

theorem accumulatedGradientOwnRowScale_pos {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    0 < accumulatedGradientOwnRowScale M := by
  unfold accumulatedGradientOwnRowScale
  have hd : 0 < (d : ℝ) := by exact_mod_cast (NeZero.pos d)
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  exact mul_pos hd (mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos)

theorem accumulatedGradientOwnRow_nonneg {d : ℕ}
    (k : ℕ) (z : Vec d) (omega : Sample d) :
    0 ≤ accumulatedGradientOwnRow k z omega :=
  mul_nonneg (Nat.cast_nonneg d) (accumulatedGradientLayer_nonneg k 0 z omega)

theorem measurable_accumulatedGradientOwnRow_shellSigma {d : ℕ}
    (k : ℕ) (z : Vec d) :
    Measurable[shellSigma d k] (accumulatedGradientOwnRow k z) := by
  unfold accumulatedGradientOwnRow
  simpa only [Nat.add_zero] using!
    (measurable_accumulatedGradientLayer_shellSigma k 0 z).const_mul (d : ℝ)

theorem isBigOWith_gammaTwo_accumulatedGradientOwnRow
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (k : ℕ) (z : Vec d) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (accumulatedGradientOwnRow k z)
      (accumulatedGradientOwnRowScale M) := by
  have h := (isBigOWith_gammaTwo_accumulatedGradientLayer M k 0 z).const_mul
    (Nat.cast_nonneg d)
  simpa [accumulatedGradientOwnRow, accumulatedGradientOwnRowScale,
    accumulatedGradientLayerScale] using! h

/-- The own-scale gradient rows are mutually independent across shell
indices. -/
theorem iIndepFun_accumulatedGradientOwnRow {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d) :
    iIndepFun (fun k : ℕ ↦ accumulatedGradientOwnRow k z)
      M.P.toMeasure := by
  rw [iIndepFun_iff]
  intro s E hE
  have hshell : iIndep (shellSigma d) M.P.toMeasure :=
    M.shellPrefix.independent.iIndep
  exact hshell.meas_biInter fun k hk ↦
    (measurable_accumulatedGradientOwnRow_shellSigma k z).comap_le
      (E k) (hE k hk)

noncomputable def centeredAccumulatedGradientOwnRow {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : Vec d) :
    Sample d → ℝ :=
  fun omega ↦ accumulatedGradientOwnRow k z omega -
    ∫ eta, accumulatedGradientOwnRow k z eta ∂M.P.toMeasure

theorem measurable_centeredAccumulatedGradientOwnRow {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : Vec d) :
    Measurable (centeredAccumulatedGradientOwnRow M k z) := by
  unfold centeredAccumulatedGradientOwnRow
  exact ((measurable_accumulatedGradientOwnRow_shellSigma k z).mono
    (shellSigma_le k) le_rfl).sub measurable_const

theorem iIndepFun_centeredAccumulatedGradientOwnRow {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d) :
    iIndepFun (fun k : ℕ ↦ centeredAccumulatedGradientOwnRow M k z)
      M.P.toMeasure := by
  have hbase := iIndepFun_accumulatedGradientOwnRow M z
  have hcenter := hbase.comp
    (fun k : ℕ ↦ fun x : ℝ ↦ x -
      ∫ eta, accumulatedGradientOwnRow k z eta ∂M.P.toMeasure)
    (fun _ ↦ measurable_id.sub measurable_const)
  simpa only [centeredAccumulatedGradientOwnRow, Function.comp_apply] using! hcenter

theorem isBigO_centeredAccumulatedGradientOwnRow {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : Vec d) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (centeredAccumulatedGradientOwnRow M k z)
      ((1 + gammaMomentConst 2) * accumulatedGradientOwnRowScale M) := by
  have hA := accumulatedGradientOwnRowScale_pos M
  have hrow := isBigOWith_gammaTwo_accumulatedGradientOwnRow M k z
  have hraw := isBigO_gammaTwo_sub_const_of_isBigOWith_nonneg hA.le
    (integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo hA
      ((measurable_accumulatedGradientOwnRow_shellSigma k z).mono
        (shellSigma_le k) le_rfl)
      (accumulatedGradientOwnRow_nonneg k z) hrow).2.1
    (accumulatedGradientOwnRow_nonneg k z) hrow
  refine hraw.mono_scale ?_
  have hmean := (integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo
    hA ((measurable_accumulatedGradientOwnRow_shellSigma k z).mono
      (shellSigma_le k) le_rfl)
    (accumulatedGradientOwnRow_nonneg k z) hrow).2.2
  calc
    accumulatedGradientOwnRowScale M +
        ∫ eta, accumulatedGradientOwnRow k z eta ∂M.P.toMeasure ≤
      accumulatedGradientOwnRowScale M +
        gammaMomentConst 2 * accumulatedGradientOwnRowScale M := by gcongr
    _ = _ := by ring

theorem integral_centeredAccumulatedGradientOwnRow_eq_zero {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : Vec d) :
    ∫ omega, centeredAccumulatedGradientOwnRow M k z omega
      ∂M.P.toMeasure = 0 := by
  have hA := accumulatedGradientOwnRowScale_pos M
  have hint := (integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo
    hA ((measurable_accumulatedGradientOwnRow_shellSigma k z).mono
      (shellSigma_le k) le_rfl)
    (accumulatedGradientOwnRow_nonneg k z)
    (isBigOWith_gammaTwo_accumulatedGradientOwnRow M k z)).1
  unfold centeredAccumulatedGradientOwnRow
  rw [integral_sub hint (integrable_const _)]
  simp

noncomputable def centeredAccumulatedGradientWindow {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d) (n m : ℕ) :
    Sample d → ℝ :=
  fun omega ↦ ∑ k ∈ Finset.Icc n m,
    centeredAccumulatedGradientOwnRow M k z omega

theorem isBigO_centeredAccumulatedGradientWindow {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (centeredAccumulatedGradientWindow M z n m)
      (Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
          ((1 + gammaMomentConst 2) * accumulatedGradientOwnRowScale M)) := by
  let K := (1 + gammaMomentConst 2) * accumulatedGradientOwnRowScale M
  have hK : 0 < K := mul_pos
    (add_pos one_pos (gammaMomentConst_pos (by norm_num)))
    (accumulatedGradientOwnRowScale_pos M)
  have hsum := Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
    (μ := M.P.toMeasure)
    (X := fun k : ℕ ↦ centeredAccumulatedGradientOwnRow M k z)
    (s := Finset.Icc n m) (σ := 2) (K := K)
    (iIndepFun_centeredAccumulatedGradientOwnRow M z)
    (fun k ↦ measurable_centeredAccumulatedGradientOwnRow M k z)
    (Finset.nonempty_Icc.mpr hnm) (by norm_num) (by norm_num) hK
    (fun k _ ↦ by simpa only [K] using!
      isBigO_centeredAccumulatedGradientOwnRow M k z)
    (fun k _ ↦ integral_centeredAccumulatedGradientOwnRow_eq_zero M k z)
  rw [Nat.card_Icc] at hsum
  simpa only [centeredAccumulatedGradientWindow, K] using! hsum

theorem sum_accumulatedGradientOwnRow_le_centered_add_mean {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d)
    (n m : ℕ) (omega : Sample d) :
    (∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) ≤
      centeredAccumulatedGradientWindow M z n m omega +
        ((m + 1 - n : ℕ) : ℝ) *
          (gammaMomentConst 2 * accumulatedGradientOwnRowScale M) := by
  have hA := accumulatedGradientOwnRowScale_pos M
  have hmean : ∀ k,
      ∫ eta, accumulatedGradientOwnRow k z eta ∂M.P.toMeasure ≤
        gammaMomentConst 2 * accumulatedGradientOwnRowScale M := by
    intro k
    exact (integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo
      hA ((measurable_accumulatedGradientOwnRow_shellSigma k z).mono
        (shellSigma_le k) le_rfl)
      (accumulatedGradientOwnRow_nonneg k z)
      (isBigOWith_gammaTwo_accumulatedGradientOwnRow M k z)).2.2
  have hcard : (Finset.Icc n m).card = m + 1 - n := by rw [Nat.card_Icc]
  unfold centeredAccumulatedGradientWindow centeredAccumulatedGradientOwnRow
  calc
    (∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) =
        (∑ k ∈ Finset.Icc n m,
          (accumulatedGradientOwnRow k z omega -
            ∫ eta, accumulatedGradientOwnRow k z eta ∂M.P.toMeasure)) +
          ∑ k ∈ Finset.Icc n m,
            ∫ eta, accumulatedGradientOwnRow k z eta ∂M.P.toMeasure := by
      rw [Finset.sum_sub_distrib]
      ring
    _ ≤ (∑ k ∈ Finset.Icc n m,
          (accumulatedGradientOwnRow k z omega -
            ∫ eta, accumulatedGradientOwnRow k z eta ∂M.P.toMeasure)) +
          ∑ _k ∈ Finset.Icc n m,
            gammaMomentConst 2 * accumulatedGradientOwnRowScale M := by
      gcongr with k hk
      exact hmean k
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
