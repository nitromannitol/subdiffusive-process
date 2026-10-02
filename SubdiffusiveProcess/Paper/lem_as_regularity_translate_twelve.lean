import SubdiffusiveProcess.Paper.product_threshold_good_scale
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.GoodEvent
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables

/-! Translation covariance of the threshold-`B` product good event. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open Homogenization hiding Vec
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

theorem aux_lem_as_regularity_translate_twelve_mem_translatedCube {d : ℕ} (z y : Vec d) (k : ℤ)
    (x : Vec d) :
    x ∈ translatedCube d k y ↔ x + z ∈ translatedCube d k (z + y) := by
  rw [← image_add_left_translatedCube z k y]
  constructor
  · intro hx
    exact ⟨x, hx, add_comm z x⟩
  · rintro ⟨p, hp, hpx⟩
    have : p = x := by
      have h2 : z + p = x + z := hpx
      have h3 : p + z = x + z := by rw [add_comm p z]; exact h2
      exact add_right_cancel h3
    rw [← this]; exact hp

/-- The product good event is exactly translation covariant. -/
theorem lem_as_regularity_translate_twelve {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (B : ℝ) (cutoff : Option ℕ) (m : ℕ) (y : Vec d) (e s : ℝ) (z : Vec d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    translatePotentialSample z ω ∈ Paper.product_threshold_good_scale d M B cutoff m y e s ↔
      ω ∈ Paper.product_threshold_good_scale d M B cutoff m (z + y) e s := by
  unfold Paper.product_threshold_good_scale
  simp only [Set.mem_setOf_eq]
  rw [goodFieldOne_translatePotentialSample, goodResponse_translatePotentialSample]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr Iff.rfl (and_congr Iff.rfl (and_congr (forall_congr' fun j => ?_) Iff.rfl))))))
  set g : Vec d → ℝ := fun p =>
    (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |ω i p|) +
      ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i p - ω i (z + y)|) else 1 with hg
  have hfun : (fun x : Vec d =>
        (∏ i ∈ Finset.Icc (m - j) (m + j),
          Real.exp |translatePotentialSample z ω i x|) +
        ∏' i : ℕ, if m + j ≤ i then
          Real.exp (4 * |translatePotentialSample z ω i x -
            translatePotentialSample z ω i y|) else 1) =
      fun x : Vec d => g (x + z) := by
    funext x
    simp only [hg, translatePotentialSample_apply]
    rw [add_comm y z]
  have hmul : (∀ x ∈ translatedCube d ((m : ℤ) + 1 + (j : ℤ)) y,
        Multipliable (fun i : ℕ => if m + j ≤ i then
          Real.exp (4 * |translatePotentialSample z ω i x - translatePotentialSample z ω i y|)
          else 1)) ↔
      (∀ x ∈ translatedCube d ((m : ℤ) + 1 + (j : ℤ)) (z + y),
        Multipliable (fun i : ℕ => if m + j ≤ i then
          Real.exp (4 * |ω i x - ω i (z + y)|) else 1)) := by
    constructor
    · intro h x' hx'
      have hx : x' - z ∈ translatedCube d ((m : ℤ) + 1 + (j : ℤ)) y := by
        rw [aux_lem_as_regularity_translate_twelve_mem_translatedCube z y]
        simpa only [sub_add_cancel] using hx'
      have := h (x' - z) hx
      simpa only [translatePotentialSample_apply, sub_add_cancel, add_comm y z] using this
    · intro h x hx
      have hx' := (aux_lem_as_regularity_translate_twelve_mem_translatedCube z y _ x).1 hx
      have := h (x + z) hx'
      simpa only [translatePotentialSample_apply, add_comm y z] using this
  have hbdd : BddAbove ((fun x : Vec d => |(∏ i ∈ Finset.Icc (m - j) (m + j),
          Real.exp |translatePotentialSample z ω i x|) +
        ∏' i : ℕ, if m + j ≤ i then
          Real.exp (4 * |translatePotentialSample z ω i x -
            translatePotentialSample z ω i y|) else 1|) ''
        translatedCube d ((m : ℤ) + 1 + (j : ℤ)) y) ↔
      BddAbove ((fun x : Vec d => |g x|) ''
        translatedCube d ((m : ℤ) + 1 + (j : ℤ)) (z + y)) := by
    have himg : ((fun x : Vec d => |(∏ i ∈ Finset.Icc (m - j) (m + j),
          Real.exp |translatePotentialSample z ω i x|) +
        ∏' i : ℕ, if m + j ≤ i then
          Real.exp (4 * |translatePotentialSample z ω i x -
            translatePotentialSample z ω i y|) else 1|) ''
        translatedCube d ((m : ℤ) + 1 + (j : ℤ)) y) =
        ((fun x : Vec d => |g x|) ''
        translatedCube d ((m : ℤ) + 1 + (j : ℤ)) (z + y)) := by
      have hf' : (fun x : Vec d => |(∏ i ∈ Finset.Icc (m - j) (m + j),
          Real.exp |translatePotentialSample z ω i x|) +
        ∏' i : ℕ, if m + j ≤ i then
          Real.exp (4 * |translatePotentialSample z ω i x -
            translatePotentialSample z ω i y|) else 1|) = fun x => |g (x + z)| := by
        funext x
        exact congrArg (fun t => |t|) (congrFun hfun x)
      rw [hf']
      ext r
      simp only [Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x + z, (aux_lem_as_regularity_translate_twelve_mem_translatedCube z y _ x).1 hx, rfl⟩
      · rintro ⟨x', hx', rfl⟩
        refine ⟨x' - z, ?_, by simp only [sub_add_cancel]⟩
        rw [aux_lem_as_regularity_translate_twelve_mem_translatedCube z y]
        simpa only [sub_add_cancel] using hx'
    rw [himg]
  have hsup : supNormOn (translatedCube d ((m : ℤ) + 1 + (j : ℤ)) y) (fun x =>
        (∏ i ∈ Finset.Icc (m - j) (m + j),
          Real.exp |translatePotentialSample z ω i x|) +
        ∏' i : ℕ, if m + j ≤ i then
          Real.exp (4 * |translatePotentialSample z ω i x -
            translatePotentialSample z ω i y|) else 1) =
      supNormOn (translatedCube d ((m : ℤ) + 1 + (j : ℤ)) (z + y)) g := by
    rw [hfun]
    exact supNormOn_translatedCube_comp_add z y _ g
  rw [hsup]
  exact and_congr hmul (and_congr hbdd Iff.rfl)

end Paper
