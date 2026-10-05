module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.ResponseBudgetPointwise
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6AnnularResummation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridStabilityCap

@[expose] public section

/-!
# Aggregating the Section 6 localization budget

This file converts the pointwise one-cube sensitivity estimate into the four
non-subunit slots of the printed good-scale display.  It follows the
`DisplaySlots` / `RepresentativeTransfer` split of
`Algsuperdiff/Section4/Provider/Annular`: first name the literal display slots,
then prove domination of each annular atom.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open Homogenization Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The first supremum in the frozen good-scale display. -/
def goodScaleResponseSlot (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  sSup {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
    r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
      Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        t = section6Response M n n omega z e})}

/-- The shell-block supremum in the frozen good-scale display. -/
def goodScaleShellSlot (s : ℝ) (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  sSup {r : ℝ | ∃ j ≤ m,
    r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
      supNormOn (cube d m) (shellBlock m j omega)}

/-- The final gradient-tail slot in the frozen display. -/
def goodScaleGradientSlot (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  ∑' j : ℕ, if m ≤ j then
    (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega j)) else 0

theorem goodScaleGradientSlot_eq_longRatioGradientTail (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    goodScaleGradientSlot m omega = longRatioGradientTail m omega := rfl

private theorem shellBlock_continuous (m n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Continuous (shellBlock m n omega) := by
  unfold shellBlock
  fun_prop

private theorem bddAbove_abs_values_cube (m : ℕ) {f : Vec d → ℝ}
    (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ cube d m, a = |f x|} := by
  let Q := originCube d (m : ℤ)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      ((continuous_abs.comp hf).continuousOn)
  refine ⟨max 0 C, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hC x hx'
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using!
    h.trans (le_max_right _ _)

private theorem supNormOn_mono_cube {n m : ℕ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) :
    supNormOn (cube d n)
        (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) ≤
      supNormOn (cube d m) (shellBlock m n omega) := by
  unfold supNormOn
  apply csSup_le
  · refine ⟨|shellBlock m n (translatePotentialSample (triadicCubeShift R) omega) 0|,
      0, ?_, rfl⟩
    rw [cube, mem_openCubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
    constructor <;> simp only [Pi.zero_apply] <;> nlinarith
  · rintro _ ⟨x, hx, rfl⟩
    have hscale : R.scale = (n : ℤ) := scale_eq_of_mem_descendantsAtScale hR
    have hxR : triadicCubeShift R + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simpa only [hscale, add_sub_cancel_left] using! hx
    have hxM : triadicCubeShift R + x ∈ cube d m :=
      openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hR) hR hxR
    have hle : |shellBlock m n omega (triadicCubeShift R + x)| ≤
        sSup {a : ℝ | ∃ y ∈ cube d m, a = |shellBlock m n omega y|} :=
      le_csSup (bddAbove_abs_values_cube m (shellBlock_continuous m n omega))
        ⟨triadicCubeShift R + x, hxM, rfl⟩
    simpa only [shellBlock_translatePotentialSample, add_comm] using! hle

private theorem responseSlot_bddAbove_of_goodEvent
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ} {m : ℕ}
    {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}
    (hs0 : 0 ≤ s) (hgood : omega ∈ goodEvent M none m 0 1 s) :
    BddAbove {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
        Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
          t = section6Response M n n omega z e})} := by
  refine ⟨1, ?_⟩
  intro r hr
  exact goodResponse_discounted_atom_le M zero_le_one hs0 hgood hr

private theorem shellSlot_bddAbove
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    BddAbove {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d m) (shellBlock m j omega)} := by
  let F : ℕ → ℝ := fun j =>
    (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
      supNormOn (cube d m) (shellBlock m j omega)
  refine ⟨Finset.sup' (Finset.range (m + 1))
      (Finset.nonempty_range_iff.mpr (by omega)) F, ?_⟩
  rintro r ⟨j, hj, rfl⟩
  exact Finset.le_sup' F (Finset.mem_range.mpr (by omega))

private theorem response_weight_le_slot_sq
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m n j : ℕ}
    (hnm : n ≤ m) {s : ℝ} (hs0 : 0 ≤ s)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : omega ∈ goodEvent M none m 0 1 s)
    (hj : j ≤ m) (hnj : n + 2 ≤ j) {z : Vec d}
    (hzgrid : OnTriadicGrid n z) (hzann : z ∈ cube d j \ cube d (j - 1))
    {e : Vec d} (he : vecNormSq e = 1) :
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        section6Response M n n omega z e ≤
      goodScaleResponseSlot M s m omega ^ 2 := by
  let A : Set ℝ := {t : ℝ | ∃ u : Vec d, vecNormSq u = 1 ∧
    t = section6Response M n n omega z u}
  have hAbdd : BddAbove A := by
    simpa only [A] using! bddAbove_section6Response_unitSphere M n n omega z
  have hJle : section6Response M n n omega z e ≤ sSup A :=
    le_csSup hAbdd ⟨e, he, rfl⟩
  have hA0 : 0 ≤ sSup A := by
    exact (by
      have hJ0 : 0 ≤ section6Response M n n omega z e := by
        unfold section6Response paperScalarProbe
        exact Ch02.responseJ_nonneg _ _ _ _
      exact hJ0.trans hJle)
  let atom := (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) * Real.sqrt (sSup A)
  have hatomMem : atom ∈ {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
      ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
        Real.sqrt (sSup {t : ℝ | ∃ u : Vec d, vecNormSq u = 1 ∧
          t = section6Response M n n omega z u})} := by
    exact ⟨j, n, hj, hnj, z, hzgrid, hzann, by simp only [atom, A]⟩
  have hatomLe : atom ≤ goodScaleResponseSlot M s m omega := by
    unfold goodScaleResponseSlot
    exact le_csSup (responseSlot_bddAbove_of_goodEvent M hs0 hgood) hatomMem
  have hatom0 : 0 ≤ atom := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.sqrt_nonneg _)
  have hslot0 : 0 ≤ goodScaleResponseSlot M s m omega := hatom0.trans hatomLe
  have hgap : (m : ℝ) - (n : ℝ) = ((m - n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hnm]
  calc
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        section6Response M n n omega z e ≤
      (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) * sSup A := by gcongr
    _ = atom ^ 2 := by
      dsimp [atom]
      rw [mul_pow, Real.sq_sqrt hA0]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 2
      rw [hgap]
      ring
    _ ≤ goodScaleResponseSlot M s m omega ^ 2 :=
      pow_le_pow_left₀ hatom0 hatomLe 2

private theorem shell_weight_le_slot_sq
    {m n : ℕ} (hnm : n ≤ m) {s : ℝ} (hs0 : 0 ≤ s)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) :
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        supNormOn (cube d n)
          (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 ≤
      goodScaleShellSlot s m omega ^ 2 := by
  let G := supNormOn (cube d m) (shellBlock m n omega)
  let atom := (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (n : ℝ))) * G
  have hGlocal := supNormOn_mono_cube omega hR
  have hG0 : 0 ≤ G := by
    unfold G supNormOn
    obtain ⟨x, hx⟩ : (cube d m).Nonempty := by
      refine ⟨0, ?_⟩
      rw [cube, mem_openCubeSet_originCube_iff]
      intro i
      have hp : 0 < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
      constructor <;> simp only [Pi.zero_apply] <;> nlinarith
    exact (abs_nonneg (shellBlock m n omega x)).trans
      (le_csSup (bddAbove_abs_values_cube m (shellBlock_continuous m n omega))
        ⟨x, hx, rfl⟩)
  have hatomMem : atom ∈ {r : ℝ | ∃ j ≤ m,
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d m) (shellBlock m j omega)} :=
    ⟨n, hnm, by simp only [atom, G]⟩
  have hatomLe : atom ≤ goodScaleShellSlot s m omega := by
    unfold goodScaleShellSlot
    exact le_csSup (shellSlot_bddAbove s m omega) hatomMem
  have hatom0 : 0 ≤ atom := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hG0
  have hslot0 : 0 ≤ goodScaleShellSlot s m omega := hatom0.trans hatomLe
  have hgap : 0 ≤ ((m - n : ℕ) : ℝ) := by positivity
  have hgap' : 0 ≤ (m : ℝ) - (n : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hnm)
  have hw : (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) ≤
      ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (n : ℝ)))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Nat.cast_ofNat, Nat.cast_sub hnm]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hlocal0 : 0 ≤ supNormOn (cube d n)
      (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) := by
    unfold supNormOn
    have hzero : (0 : Vec d) ∈ cube d n := by
      rw [cube, mem_openCubeSet_originCube_iff]
      intro i
      have hp : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
      constructor <;> simp only [Pi.zero_apply] <;> nlinarith
    exact (abs_nonneg _).trans
      (le_csSup (bddAbove_abs_values_cube n
        (shellBlock_continuous m n (translatePotentialSample (triadicCubeShift R) omega)))
        ⟨0, hzero, rfl⟩)
  calc
    (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
        supNormOn (cube d n)
          (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 ≤
      (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) * G ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hlocal0 hGlocal 2)
          (Real.rpow_nonneg (by norm_num) _)
    _ ≤ ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (n : ℝ)))) ^ 2 * G ^ 2 := by
        gcongr
    _ = atom ^ 2 := by simp only [atom]; ring
    _ ≤ goodScaleShellSlot s m omega ^ 2 :=
      pow_le_pow_left₀ hatom0 hatomLe 2

/-- Every nonnegative-scale annular atom is controlled by the response,
gradient-tail, shell-block, and deterministic-drift display slots. -/
theorem weightedLocalProbe_le_goodScaleSlots
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n j : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (hj : j ≤ m) (hnj : n + 2 ≤ j)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ))
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    {e : Vec d} (he : vecNormSq e = 1)
    (hgood : omega ∈ goodEvent M none m 0 1 s) :
    (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) *
        paperScalarProbe (originCube d (n : ℤ))
          (aCutoffFamily M L (translatePotentialSample (triadicCubeShift R) omega))
          (tailCoefficientCubeAverage M L m omega) e ≤
      2 * goodScaleResponseSlot M s m omega ^ 2 +
        36 * ratioCollapseConstant d ^ 2 *
          (goodScaleGradientSlot m omega ^ 2 +
            goodScaleShellSlot s m omega ^ 2 +
            2 * (s⁻¹ * M.delta ^ 2) ^ 2) := by
  have hs0 : 0 ≤ s := le_trans (mul_nonneg (by norm_num) (sq_nonneg M.delta)) hsLower
  have hraw := weightedPaperScalarProbe_tailAverage_le_split_of_mem_goodEvent
    M hnm hmL hsLower hsUpper hj hnj omega hR hann he hgood
  have hresp := response_weight_le_slot_sq M hnm hs0 omega hgood hj hnj
    (onTriadicGrid_triadicCubeShift_of_scale
      (scale_eq_of_mem_descendantsAtScale hR)) hann he
  have hshell := shell_weight_le_slot_sq hnm hs0 omega hR
  have hv : (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (mul_nonneg hs0 (by positivity)))
  have hgrad0 : 0 ≤ goodScaleGradientSlot m omega := by
    rw [goodScaleGradientSlot_eq_longRatioGradientTail]
    exact longRatioGradientTail_nonneg m omega
  have hgrad : (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
      longRatioGradientTail m omega ^ 2 ≤ goodScaleGradientSlot m omega ^ 2 := by
    rw [← goodScaleGradientSlot_eq_longRatioGradientTail]
    nlinarith [sq_nonneg (goodScaleGradientSlot m omega)]
  have hdrift : 2 * (s⁻¹) ^ 2 * M.delta ^ 4 =
      2 * (s⁻¹ * M.delta ^ 2) ^ 2 := by ring
  have hresp2 : 2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
      section6Response M n n omega (triadicCubeShift R) e ≤
      2 * goodScaleResponseSlot M s m omega ^ 2 := by
    nlinarith only [hresp]
  have hbudget :
      (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
            longRatioGradientTail m omega ^ 2 +
          (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
            supNormOn (cube d n)
              (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 +
          2 * (s⁻¹) ^ 2 * M.delta ^ 4 ≤
        goodScaleGradientSlot m omega ^ 2 +
          goodScaleShellSlot s m omega ^ 2 +
          2 * (s⁻¹ * M.delta ^ 2) ^ 2 := by
    rw [hdrift]
    exact add_le_add (add_le_add hgrad hshell) le_rfl
  have hcoef : 0 ≤ 36 * ratioCollapseConstant d ^ 2 := by positivity
  calc
    _ ≤ 2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n n omega (triadicCubeShift R) e +
        36 * ratioCollapseConstant d ^ 2 *
          ((3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
              longRatioGradientTail m omega ^ 2 +
            (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
              supNormOn (cube d n)
                (shellBlock m n (translatePotentialSample (triadicCubeShift R) omega)) ^ 2 +
            2 * (s⁻¹) ^ 2 * M.delta ^ 4) := hraw
    _ ≤ 2 * goodScaleResponseSlot M s m omega ^ 2 +
        36 * ratioCollapseConstant d ^ 2 *
          (goodScaleGradientSlot m omega ^ 2 +
            goodScaleShellSlot s m omega ^ 2 +
            2 * (s⁻¹ * M.delta ^ 2) ^ 2) := by
      exact add_le_add hresp2 (mul_le_mul_of_nonneg_left hbudget hcoef)

/-! ## Passage to the positive-scale annular supremum -/

/-- The common square budget for every nonnegative-scale annular atom. -/
def goodScalePositiveBudget (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  2 * goodScaleResponseSlot M s m omega ^ 2 +
    36 * ratioCollapseConstant d ^ 2 *
      (goodScaleGradientSlot m omega ^ 2 +
        goodScaleShellSlot s m omega ^ 2 +
        2 * (s⁻¹ * M.delta ^ 2) ^ 2)

/-- An annular cube of scale at most `j - 2` with `j ≤ m` is a descendant of
`□_m` at its own scale. -/
theorem annularCube_mem_descendantsAtScale
    {m : ℕ} {R : TriadicCube d} {j : ℤ}
    (hj : j ≤ (m : ℤ)) (hscale : R.scale ≤ j - 2)
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1)) :
    R ∈ descendantsAtScale (originCube d (m : ℤ)) R.scale := by
  have hRm : R.scale ≤ (m : ℤ) := by omega
  have hjm : cube d j ⊆ cube d (m : ℤ) :=
    openCubeSet_originCube_subset_of_scale_le hj
  have hzOpen : triadicCubeShift R ∈ cube d (m : ℤ) := hjm hann.1
  have hzHalf : triadicCubeShift R ∈ cubeSet (originCube d (m : ℤ)) :=
    openCubeSet_subset_cubeSet _ hzOpen
  have hcover := cubeSet_subset_iUnion_descendantsAtScale
    (originCube d (m : ℤ)) hRm hzHalf
  obtain ⟨Q, hQrest⟩ := Set.mem_iUnion.1 hcover
  obtain ⟨hQ, hzQ⟩ := Set.mem_iUnion.1 hQrest
  have hQscale : Q.scale = R.scale := scale_eq_of_mem_descendantsAtScale hQ
  have hzR : triadicCubeShift R ∈ cubeSet R := by
    simpa only [cubeCenter, triadicCubeShift] using!
      SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.cubeCenter_mem_cubeSet R
  have hRQ : R = Q :=
    SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.eq_of_scale_eq_of_mem_of_mem
      hQscale.symm hzR hzQ
  rw [hRQ, hQscale]
  exact hQ

/-- Every nonnegative-scale annular atom is bounded by the positive-scale
budget. -/
theorem positive_annular_atom_le_budget
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    {s : ℝ} (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : omega ∈ goodEvent M none m 0 1 s)
    (p : AnnularPairTwo d (m : ℤ)) (hscale0 : 0 ≤ p.1.1.scale) :
    ENNReal.ofReal
          ((3 : ℝ) ^ (-(3 * s / 2) *
            ((m : ℝ) - (p.1.1.scale : ℝ)))) *
        section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega) p.1.1 ≤
      ENNReal.ofReal (goodScalePositiveBudget M s m omega) := by
  obtain ⟨hj, hscale, hann⟩ := p.2
  let n : ℕ := p.1.1.scale.toNat
  let jn : ℕ := p.1.2.toNat
  have hncast : (n : ℤ) = p.1.1.scale := by
    exact Int.toNat_of_nonneg hscale0
  have hj0 : 0 ≤ p.1.2 := by omega
  have hjcast : (jn : ℤ) = p.1.2 := Int.toNat_of_nonneg hj0
  have hnmZ : (n : ℤ) ≤ (m : ℤ) := by rw [hncast]; omega
  have hjmZ : (jn : ℤ) ≤ (m : ℤ) := by rw [hjcast]; exact hj
  have hnjZ : (n : ℤ) + 2 ≤ (jn : ℤ) := by rw [hncast, hjcast]; omega
  have hnm : n ≤ m := by exact_mod_cast hnmZ
  have hjm : jn ≤ m := by exact_mod_cast hjmZ
  have hnj : n + 2 ≤ jn := by exact_mod_cast hnjZ
  have hR : p.1.1 ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ) := by
    rw [hncast]
    exact annularCube_mem_descendantsAtScale hj hscale hann
  have hweight :
      (3 : ℝ) ^ (-(3 * s / 2) * ((m : ℝ) - (p.1.1.scale : ℝ))) =
        (3 : ℝ) ^ (-(3 / 2) * (s * ((m - n : ℕ) : ℝ))) := by
    congr 1
    have hgap : (m : ℝ) - (n : ℝ) = ((m - n : ℕ) : ℝ) := by
      rw [Nat.cast_sub hnm]
    have hnreal : (n : ℝ) = (p.1.1.scale : ℝ) := by exact_mod_cast hncast
    rw [← hnreal, hgap]
    ring
  unfold section6LocalProbeMax
  rw [ENNReal.mul_iSup]
  refine iSup_le fun e => ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), hweight]
  apply ENNReal.ofReal_le_ofReal
  simpa [goodScalePositiveBudget, hncast,
    Section6Covariance.translatePotentialSample_zero] using!
    weightedLocalProbe_le_goodScaleSlots M hnm hmL hsLower hsUpper
      hjm hnj omega hR (by simpa only [hjcast] using! hann) e.2 hgood

/-- The nonnegative-scale part of `annularSupTwo` is bounded by the four
positive-scale display slots. -/
theorem annularSupTwo_positive_le_goodScaleBudget
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    {s : ℝ} (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : omega ∈ goodEvent M none m 0 1 s) :
    (⨆ p : {p : AnnularPairTwo d (m : ℤ) // 0 ≤ p.1.1.scale},
      ENNReal.ofReal ((3 : ℝ) ^ (-(3 * s / 2) *
          ((m : ℝ) - (p.1.1.1.scale : ℝ)))) *
        section6LocalProbeMax M L omega 0
          (tailCoefficientCubeAverage M L m omega) p.1.1.1) ≤
      ENNReal.ofReal (goodScalePositiveBudget M s m omega) := by
  refine iSup_le fun p => ?_
  exact positive_annular_atom_le_budget M hmL hsLower hsUpper omega hgood p.1 p.2

theorem goodScalePositiveBudget_nonneg
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ goodScalePositiveBudget M s m omega := by
  unfold goodScalePositiveBudget
  positivity

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
