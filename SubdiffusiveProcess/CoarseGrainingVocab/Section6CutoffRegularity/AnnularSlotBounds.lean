module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.AccumulatedErrorMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.AnnularLocalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.AnnularRecombination
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodScaleSaturation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6GoodScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.LongRatioEvent

@[expose] public section

/-!
# Slot bounds on the good event, publicly

Conjunct (5) of `p.cutoff.regularity.good.scales` needs, for the `m > L`
(annular) branch, that each of the four good-scale slots is at most `epsilon` on
the good event.  Three of the four are proved in the repo already — but
`private`, inside `SubdiffusiveProcess/Providers/Section6/GoodScaleMathcalE.lean`, together with
a cascade of private helpers.  A vocabulary module may not reach into a provider,
so they are re-proved here, additively and publicly.

Two things make the port short:

* the helper cascade is largely subsumed by this collection's
  `LiteralSupMeasurability`: `bddAbove_abs_values_cube_int` becomes
  `bddAbove_image_of_isBounded` applied to `isBounded_cube`, and
  `shellControl_continuous` is assembled from the public `continuous_shellGradient`
  and `continuous_euclideanNorm` of `AccumulatedErrorMeasurability`;
* the shell, full and gradient slots do **not** mention the cutoff at all, and
  their bounds depend only on `GoodFieldOne m 0 epsilon s omega`, which is
  `hgood.1` for either cutoff.  So the `none`-case proofs transfer verbatim.

Only the **response** slot is cutoff-sensitive, and there the frozen
`GoodResponse` is already cutoff-generic — it bounds
`section6Response M n (min n (cutoff.getD n))`, which is exactly the carrier of
`cutoffGoodScaleResponseSlot` at `cutoff = some L`.  So
`Section6GoodScale.goodResponse_discounted_atom_le` is restated here for an
arbitrary cutoff, with the same proof.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open _root_.SubdiffusiveProcess.Model

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## The helper cascade, publicly -/

theorem abs_apply_le_supNormOn_cube {k : ℤ} {f : Vec d → ℝ}
    (hf : Continuous f) {x : Vec d} (hx : x ∈ cube d k) :
    |f x| ≤ supNormOn (cube d k) f :=
  le_csSup (bddAbove_image_of_isBounded (isBounded_cube d k) hf.abs) ⟨x, hx, rfl⟩

theorem cube_nonempty (k : ℤ) : (cube d k).Nonempty := by
  refine ⟨0, ?_⟩
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hp : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  constructor <;> simp only [Pi.zero_apply] <;> nlinarith

theorem translatedCube_zero_eq (k : ℤ) : translatedCube d k 0 = cube d k := by
  unfold translatedCube
  simp

theorem shellControl_continuous (g : PotentialField d) (i : ℕ) :
    Continuous (fun x ↦ |g x| + (3 : ℝ) ^ i *
      Homogenization.euclideanNorm (shellGradient g x)) :=
  (continuous_abs.comp (_root_.SubdiffusiveProcess.Model.PotentialField.contDiff_one g).continuous).add
    (continuous_const.mul
      (continuous_euclideanNorm.comp (continuous_shellGradient g)))

theorem euclideanNorm_nonneg' (v : Vec d) :
    0 ≤ Homogenization.euclideanNorm v := by
  unfold Homogenization.euclideanNorm
  exact Real.sqrt_nonneg _

/-! ## The field-one slot bounds -/

theorem sum_abs_le_of_goodFieldOne (m q : ℕ) {epsilon s : ℝ}
    (omega : PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega)
    {T : Finset ℕ} (hT : T ⊆ Finset.Icc (m - q) (m + q))
    {x : Vec d} (hx : x ∈ cube d (m : ℤ)) :
    ∑ i ∈ T, |omega i x| ≤ epsilon * (3 : ℝ) ^ ((s * (q : ℝ)) / 8) := by
  have hevent := hgood q
  rw [translatedCube_zero_eq] at hevent
  have hxlarge : x ∈ cube d ((m : ℤ) + 1 + (q : ℤ)) := by
    refine openCubeSet_originCube_subset_of_scale_le ?_ hx
    omega
  have hterm : ∀ i ∈ Finset.Icc (m - q) (m + q), |omega i x| ≤
      supNormOn (cube d ((m : ℤ) + 1 + (q : ℤ))) (fun y ↦
        |omega i y| + (3 : ℝ) ^ i *
          Homogenization.euclideanNorm (shellGradient (omega i) y)) := by
    intro i _
    have hcontrol := abs_apply_le_supNormOn_cube
      (shellControl_continuous (omega i) i) hxlarge
    have hnonneg : 0 ≤ |omega i x| + (3 : ℝ) ^ i *
        Homogenization.euclideanNorm (shellGradient (omega i) x) :=
      add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (euclideanNorm_nonneg' _))
    rw [abs_of_nonneg hnonneg] at hcontrol
    refine le_trans ?_ hcontrol
    have hg : 0 ≤ (3 : ℝ) ^ i *
        Homogenization.euclideanNorm (shellGradient (omega i) x) :=
      mul_nonneg (by positivity) (euclideanNorm_nonneg' _)
    linarith
  calc
    ∑ i ∈ T, |omega i x| ≤ ∑ i ∈ Finset.Icc (m - q) (m + q), |omega i x| :=
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun i _ _ ↦ abs_nonneg _)
    _ ≤ ∑ i ∈ Finset.Icc (m - q) (m + q),
        supNormOn (cube d ((m : ℤ) + 1 + (q : ℤ))) (fun y ↦
          |omega i y| + (3 : ℝ) ^ i *
            Homogenization.euclideanNorm (shellGradient (omega i) y)) :=
      Finset.sum_le_sum hterm
    _ ≤ epsilon * (3 : ℝ) ^ ((s * (q : ℝ)) / 8) := hevent

theorem supNormOn_shellBlock_le_of_goodFieldOne
    (m j : ℕ) (hj : j ≤ m) {epsilon s : ℝ}
    (omega : PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    supNormOn (cube d (m : ℤ)) (shellBlock m j omega) ≤
      epsilon * (3 : ℝ) ^ ((s * ((m - j : ℕ) : ℝ)) / 8) := by
  refine csSup_le ?_ ?_
  · obtain ⟨x, hx⟩ := cube_nonempty (d := d) (m : ℤ)
    exact ⟨|shellBlock m j omega x|, x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hsubset : Finset.Icc (j + 1) m ⊆
        Finset.Icc (m - (m - j)) (m + (m - j)) := by
      intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega
    have hsum := sum_abs_le_of_goodFieldOne m (m - j) omega hgood hsubset hx
    exact (Finset.abs_sum_le_sum_abs _ _).trans hsum

theorem supNormOn_fullShellBlock_le_of_goodFieldOne
    (m : ℕ) {epsilon s : ℝ}
    (omega : PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) ≤
      epsilon * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) := by
  refine csSup_le ?_ ?_
  · obtain ⟨x, hx⟩ := cube_nonempty (d := d) (m : ℤ)
    exact ⟨|fullShellBlock m omega x|, x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hsubset : Finset.range (m + 1) ⊆ Finset.Icc (m - m) (m + m) := by
      intro i hi
      simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
      omega
    have hsum := sum_abs_le_of_goodFieldOne m m omega hgood hsubset hx
    exact (Finset.abs_sum_le_sum_abs _ _).trans hsum

theorem goodScaleShellSlot_le (m : ℕ) {epsilon s : ℝ}
    (omega : PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    goodScaleShellSlot s m omega ≤ epsilon := by
  refine csSup_le ⟨_, m, le_rfl, rfl⟩ ?_
  rintro _ ⟨j, hj, rfl⟩
  have hgap : (m : ℝ) - (j : ℝ) = ((m - j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hj]
  have hsup := supNormOn_shellBlock_le_of_goodFieldOne m j hj omega hgood
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d (m : ℤ)) (shellBlock m j omega) ≤
        (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
          (epsilon * (3 : ℝ) ^ ((s * ((m - j : ℕ) : ℝ)) / 8)) :=
      mul_le_mul_of_nonneg_left hsup hw
    _ = epsilon := by
      rw [← hgap, ← mul_assoc, mul_comm _ epsilon, mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [show -(s / 8) * ((m : ℝ) - (j : ℝ)) + s * ((m : ℝ) - (j : ℝ)) / 8 = 0 by
        ring]
      rw [Real.rpow_zero, mul_one]

theorem goodScaleFullSlot_le (m : ℕ) {epsilon s : ℝ}
    (omega : PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    goodScaleFullSlot s m omega ≤ epsilon := by
  have hsup := supNormOn_fullShellBlock_le_of_goodFieldOne m omega hgood
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  unfold goodScaleFullSlot
  calc
    (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) *
        supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) ≤
        (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) *
          (epsilon * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) :=
      mul_le_mul_of_nonneg_left hsup hw
    _ = epsilon := by
      rw [← mul_assoc, mul_comm _ epsilon, mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [show -(s / 8) * (m : ℝ) + s * (m : ℝ) / 8 = 0 by ring]
      rw [Real.rpow_zero, mul_one]

/-! ## The response slot, cutoff-generically -/

theorem goodResponse_discounted_atom_le_cutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ) {m : ℕ}
    {epsilon s : ℝ} (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    {omega : PotentialSample d}
    (homega : omega ∈ goodEvent M cutoff m 0 epsilon s)
    {r : ℝ}
    (hr : r ∈ {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
        ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            t = section6Response M n (min n (cutoff.getD n)) omega z e})}) :
    r ≤ epsilon := by
  rcases hr with ⟨j, n, hjm, hnj, z, hzgrid, hzann, rfl⟩
  have hnm : n ≤ m := by omega
  have hgap0 : 0 ≤ (m : ℝ) - (n : ℝ) := sub_nonneg.mpr (by exact_mod_cast hnm)
  set A : Set ℝ := {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
    t = section6Response M n (min n (cutoff.getD n)) omega z e} with hAdef
  have hAbdd : BddAbove A := by
    rw [hAdef]
    exact bddAbove_section6Response_unitSphere M n (min n (cutoff.getD n)) omega z
  have hAne : A.Nonempty := by
    let i : Fin d := ⟨0, lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension⟩
    refine ⟨section6Response M n (min n (cutoff.getD n)) omega z (Pi.single i 1),
      Pi.single i 1, ?_, rfl⟩
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
              (3 : ℝ) ^ (((s * ((m : ℝ) - (n : ℝ))) / 16) * 2) := by ring_nf
          _ = ((3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) ^ (2 : ℝ) := by
                rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
          _ = ((3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) ^ (2 : ℕ) :=
                Real.rpow_natCast _ 2
  calc
    (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) * Real.sqrt (sSup A) ≤
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
          (epsilon * (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 16)) := by
      gcongr
    _ = epsilon * (3 : ℝ) ^ (-(7 * s / 16) * ((m : ℝ) - (n : ℝ))) := by
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

theorem cutoffGoodScaleResponseSlot_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {m : ℕ} {epsilon s : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hs0 : 0 ≤ s)
    {omega : PotentialSample d}
    (homega : omega ∈ goodEvent M (some L) m 0 epsilon s) :
    cutoffGoodScaleResponseSlot M L s m omega ≤ epsilon := by
  unfold cutoffGoodScaleResponseSlot
  set S : Set ℝ := {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
    r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
      Real.sqrt (sSup {q : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        q = section6Response M n (min n L) omega z e})} with hSdef
  by_cases hS : S.Nonempty
  · refine csSup_le hS fun r hr ↦ ?_
    exact goodResponse_discounted_atom_le_cutoff M (some L) hepsilon0 hs0 homega
      (by simpa only [hSdef, Option.getD_some] using hr)
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    rw [hEmpty, Real.sSup_empty]
    exact hepsilon0

/-! ## Slot nonnegativity

`Real.sSup_nonneg` needs no boundedness hypothesis: an unbounded or empty
`Real.sSup` is `0`, which is already nonnegative.  That makes each of these
three lines long, where the `private` originals in the provider went through
compactness. -/

theorem supNormOn_nonneg' (W : Set (Vec d)) (f : Vec d → ℝ) :
    0 ≤ supNormOn W f := by
  unfold supNormOn
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, _, rfl⟩
  exact abs_nonneg _

theorem vectorSupNormOn_nonneg' (W : Set (Vec d)) (f : Vec d → Vec d) :
    0 ≤ vectorSupNormOn W f := by
  unfold vectorSupNormOn
  refine Real.sSup_nonneg ?_
  rintro _ ⟨x, _, rfl⟩
  exact euclideanNorm_nonneg' _

theorem goodScaleShellSlot_nonneg (s : ℝ) (m : ℕ) (omega : PotentialSample d) :
    0 ≤ goodScaleShellSlot s m omega := by
  unfold goodScaleShellSlot
  refine Real.sSup_nonneg ?_
  rintro _ ⟨j, _, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (supNormOn_nonneg' _ _)

theorem goodScaleFullSlot_nonneg (s : ℝ) (m : ℕ) (omega : PotentialSample d) :
    0 ≤ goodScaleFullSlot s m omega := by
  unfold goodScaleFullSlot
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (supNormOn_nonneg' _ _)

theorem goodScaleGradientSlot_nonneg (m : ℕ) (omega : PotentialSample d) :
    0 ≤ goodScaleGradientSlot m omega := by
  rw [goodScaleGradientSlot_eq_longRatioGradientTail]
  unfold longRatioGradientTail
  refine tsum_nonneg fun j ↦ ?_
  by_cases h : m ≤ j
  · simp only [ite_eq_left h]
    exact mul_nonneg (by positivity) (vectorSupNormOn_nonneg' _ _)
  · simp only [ite_eq_right h]
    exact le_rfl

theorem cutoffGoodScaleResponseSlot_nonneg
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ) (m : ℕ)
    (omega : PotentialSample d) :
    0 ≤ cutoffGoodScaleResponseSlot M L s m omega := by
  unfold cutoffGoodScaleResponseSlot
  refine Real.sSup_nonneg ?_
  rintro _ ⟨j, n, _, _, z, _, _, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
