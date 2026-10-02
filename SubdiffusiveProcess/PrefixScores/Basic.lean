import SubdiffusiveProcess.Main.PrimitiveErrorFiniteness
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.GoodEvent
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

/-! Bridges from extended primitive scores to the real tests in Section 6. -/

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization hiding Vec
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.PrefixScores

lemma ofReal_sSup_image (S : Set ℝ) (hS : BddAbove S) :
    sSup (ENNReal.ofReal '' S) = ENNReal.ofReal (sSup S) := by
  classical
  by_cases hne : S.Nonempty
  · have gc : GaloisConnection Real.toNNReal ((↑) : ℝ≥0 → ℝ) :=
      fun r p => Real.toNNReal_le_iff_le_coe
    have hmono : Monotone Real.toNNReal := fun a b h => Real.toNNReal_mono h
    have hbdd := hmono.map_bddAbove hS
    have hkey := gc.l_csSup' hne hS
    have heq : ENNReal.ofReal '' S =
        ((↑) : ℝ≥0 → ENNReal) '' (Real.toNNReal '' S) := by
      rw [Set.image_image]; rfl
    rw [heq, sSup_image, ← ENNReal.coe_sSup hbdd, ← hkey]
    rfl
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp

lemma bddAbove_values_cube {d : ℕ} (k : ℤ) (z : Vec d)
    (f : Vec d → ℝ) (hf : Continuous f) :
    BddAbove {r : ℝ | ∃ x ∈ translatedCube d k z, r = f x} := by
  have hc := (Section6TheoremC.isCompact_closure_cube d k).image
    (continuous_const.add continuous_id : Continuous (fun x : Vec d => z + x))
  refine (hc.image hf).bddAbove.mono ?_
  rintro r ⟨x, hx, rfl⟩
  exact ⟨x, Set.image_mono subset_closure hx, rfl⟩

lemma normOn_cube_eq {d : ℕ} (k : ℤ) (z : Vec d)
    (f : Vec d → ℝ) (hf : Continuous f) :
    primitiveNormOn (translatedCube d k z) f =
      ENNReal.ofReal (supNormOn (translatedCube d k z) f) := by
  have heq : {v : ENNReal | ∃ x ∈ translatedCube d k z,
      v = ENNReal.ofReal |f x|} =
      ENNReal.ofReal '' {r : ℝ | ∃ x ∈ translatedCube d k z, r = |f x|} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨|f x|, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  unfold primitiveNormOn supNormOn
  rw [heq, ofReal_sSup_image _ (bddAbove_values_cube k z _ hf.abs)]

lemma responseDefect_eq {d : ℕ} [NeZero d] (M : GMCModel d)
    (ω : PotentialSample d) (l : ℕ) (x : Vec d) :
    primitiveResponseDefect M ω l x = ENNReal.ofReal
      (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        t = section6Response M l l ω x e}) := by
  have heq : {v : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
      v = ENNReal.ofReal (section6Response M l l ω x e)} =
      ENNReal.ofReal '' {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        t = section6Response M l l ω x e} := by
    ext v
    constructor
    · rintro ⟨e, he, rfl⟩; exact ⟨_, ⟨e, he, rfl⟩, rfl⟩
    · rintro ⟨t, ⟨e, he, rfl⟩, rfl⟩; exact ⟨e, he, rfl⟩
  unfold primitiveResponseDefect
  rw [heq, ofReal_sSup_image _ (bddAbove_section6Response_unitSphere M l l ω x)]

lemma discount_cancel (a : ℝ) :
    (3 : ℝ) ^ (-a) * (3 : ℝ) ^ a = 1 := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), neg_add_cancel, Real.rpow_zero]

lemma goodFieldOne_bound {d : ℕ} (s eps : ℝ) (ω : PotentialSample d)
    (m : ℕ) (z : Vec d) (_heps : 0 ≤ eps)
    (hgood : GoodFieldOne m z eps s ω) :
    primitiveFieldScore s ω m z ≤ ENNReal.ofReal eps := by
  refine sSup_le ?_
  rintro v ⟨j, rfl⟩
  have hcont : ∀ i : ℕ, Continuous (fun x : Vec d =>
      |ω i x| + (3 : ℝ) ^ (i : ℝ) * euclideanNorm (shellGradient (ω i) x)) := by
    intro i
    exact (PotentialField.contDiff_one (ω i)).continuous.abs.add
      (continuous_const.mul (Section6CutoffRegularity.continuous_euclideanNorm.comp
        (Section6CutoffRegularity.continuous_shellGradient (ω i))))
  simp_rw [normOn_cube_eq _ _ _ (hcont _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    Section6CutoffRegularity.supNormOn_nonneg' _ _), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left (hgood j)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-(s * (j : ℝ) / 8)))
  simpa only [Real.rpow_natCast, Nat.cast_add, Nat.cast_one, mul_left_comm,
    discount_cancel, mul_one] using h

lemma goodResponse_bound {d : ℕ} [NeZero d] (M : GMCModel d) (s eps : ℝ)
    (ω : PotentialSample d) (m : ℕ) (z : Vec d)
    (hgood : GoodResponse M none m z eps s ω) :
    primitiveResponseScore M s ω m z ≤ ENNReal.ofReal (eps ^ 2) := by
  refine sSup_le ?_
  rintro v ⟨j, l, hj, hl, x, hgrid, hx, rfl⟩
  have hJ : primitiveResponseDefect M ω l x ≤
      ENNReal.ofReal (eps ^ 2 * (3 : ℝ) ^ (s * ((m : ℝ) - l) / 8)) := by
    refine sSup_le ?_
    rintro v ⟨e, he, rfl⟩
    exact ENNReal.ofReal_le_ofReal (by simpa only [Option.getD_none, min_self]
      using (hgood j l hj hl x hgrid hx e he))
  calc
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - l) / 8))) *
        ENNReal.ofReal (eps ^ 2 * (3 : ℝ) ^ (s * ((m : ℝ) - l) / 8)) :=
      mul_le_mul_right hJ _
    _ = ENNReal.ofReal (eps ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity), mul_left_comm, discount_cancel, mul_one]

lemma ramp_le_badIndicator (a b : ℝ) (X : ENNReal) :
    extendedPrimitiveRamp a b X ≤ if ENNReal.ofReal a < X then (1 : ℝ) else 0 := by
  classical
  split_ifs with h
  · exact (extendedPrimitiveRamp_bounds a b X).2
  · have hx : X ≤ ENNReal.ofReal a := le_of_not_gt h
    simp only [extendedPrimitiveRamp, tsub_eq_zero_of_le hx, ENNReal.zero_div,
      min_eq_right (zero_le _), ENNReal.toReal_zero, le_refl]

lemma partialProduct_le_tprod (f : ℕ → ℝ) (start K : ℕ)
    (hf : Multipliable (fun i => if start ≤ i then f i else 1))
    (hone : ∀ i, 1 ≤ f i) :
    (∏ i ∈ Finset.Icc start (start + K), ENNReal.ofReal (f i)) ≤
      ENNReal.ofReal (∏' i : ℕ, if start ≤ i then f i else 1) := by
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (zero_le_one.trans (hone i)))]
  apply ENNReal.ofReal_le_ofReal
  let g : ℕ → ℝ := fun i => if start ≤ i then f i else 1
  have hg : ∀ i, 1 ≤ g i := fun i => by dsimp [g]; split_ifs <;> simp_all
  have hs : (∏ i ∈ Finset.Icc start (start + K), f i) =
      ∏ i ∈ Finset.Icc start (start + K), g i := by
    apply Finset.prod_congr rfl
    intro i hi
    exact (if_pos (Finset.mem_Icc.mp hi).1).symm
  rw [hs]
  apply ge_of_tendsto hf.hasProd
  filter_upwards [Filter.eventually_ge_atTop (Finset.Icc start (start + K))] with t ht
  rw [← Finset.prod_sdiff ht]
  have htail : 1 ≤ ∏ i ∈ t \ Finset.Icc start (start + K), g i := by
    simpa using (Finset.prod_le_prod (f := fun _ : ℕ => (1 : ℝ))
      (fun _ _ => zero_le_one) (fun i _ => hg i))
  have hpos : 0 ≤ ∏ i ∈ Finset.Icc start (start + K), g i :=
    Finset.prod_nonneg (fun i _ => zero_le_one.trans (hg i))
  exact le_mul_of_one_le_left hpos htail

lemma ae_goodFieldTwo_bound {d : ℕ} (M : GMCModel d) (s : ℝ) (m : ℕ) (z : Vec d) :
    ∀ᵐ ω ∂M.P.toMeasure, GoodFieldTwo m z s ω → primitiveProductScore s ω m z ≤ 6 := by
  have hprod : ∀ᵐ ω ∂M.P.toMeasure, ∀ j : ℕ, ∀ x ∈ translatedCube d (m + 1 + j) z,
      Multipliable (fun i : ℕ => if m + j ≤ i then
        Real.exp (4 * |ω i x - ω i z|) else 1) := by
    exact ae_all_iff.mpr (fun j => ae_multipliable_goodFieldTwo_tail_on_translatedCube M m j z)
  have hbdd : ∀ᵐ ω ∂M.P.toMeasure, ∀ j : ℕ,
      BddAbove {a : ℝ | ∃ x ∈ translatedCube d (m + 1 + j) z,
        a = |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |ω i x|) +
          ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i x - ω i z|) else 1|} :=
    ae_all_iff.mpr (fun j => ae_bddAbove_goodFieldTwo_values_on_translatedCube M m j z)
  filter_upwards [hprod, hbdd] with ω hp hb
  intro hg
  refine sSup_le ?_
  rintro v ⟨j, rfl⟩
  have hinter : (sSup {w : ENNReal | ∃ x ∈ translatedCube d (m + 1 + j) z,
      w = (∏ i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal (Real.exp |ω i x|)) +
        sSup {u : ENNReal | ∃ K : ℕ, u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
          ENNReal.ofReal (Real.exp (4 * |ω i x - ω i z|))}}) ≤
      ENNReal.ofReal (supNormOn (translatedCube d (m + 1 + j) z) (fun x =>
        (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |ω i x|) +
          ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i x - ω i z|) else 1)) := by
    refine sSup_le ?_
    rintro w ⟨x, hx, rfl⟩
    have ht : (sSup {u : ENNReal | ∃ K : ℕ, u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
        ENNReal.ofReal (Real.exp (4 * |ω i x - ω i z|))}) ≤
        ENNReal.ofReal (∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i x - ω i z|) else 1) := by
      refine sSup_le ?_
      rintro u ⟨K, rfl⟩
      exact partialProduct_le_tprod _ _ _ (hp j x hx) (fun i =>
        Real.one_le_exp (by positivity))
    calc
      _ ≤ ENNReal.ofReal (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |ω i x|) +
          ENNReal.ofReal (∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i x - ω i z|) else 1) := by
        rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
        exact add_le_add_right ht _
      _ = ENNReal.ofReal ((∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |ω i x|) +
          ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i x - ω i z|) else 1) :=
        (ENNReal.ofReal_add (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))
          (zero_le_one.trans (by
            apply ge_of_tendsto (hp j x hx).hasProd
            exact Filter.Eventually.of_forall (fun t => by
              simpa using (Finset.prod_le_prod (f := fun _ : ℕ => (1 : ℝ))
                (fun _ _ => zero_le_one) (fun i _ => by
                  split_ifs <;> simp only [le_refl, Real.one_le_exp_iff]; positivity)))))).symm
      _ ≤ ENNReal.ofReal (supNormOn _ _) := ENNReal.ofReal_le_ofReal
        ((le_abs_self _).trans (le_csSup (hb j) ⟨x, hx, rfl⟩))
  calc
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        ENNReal.ofReal (supNormOn _ _) := mul_le_mul_right hinter _
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        ENNReal.ofReal (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8)) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal (hg j)) _
    _ = 6 := by
      rw [← ENNReal.ofReal_mul (by positivity), mul_left_comm, discount_cancel, mul_one]
      norm_num

end SubdiffusiveProcess.PrefixScores
