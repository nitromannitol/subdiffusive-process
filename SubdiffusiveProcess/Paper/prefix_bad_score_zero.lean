module

public import SubdiffusiveProcess.Paper.prefix_tail_score_bridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.PointwiseBoundedness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.RatioCollapse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_prefix_bad_score_zero_discount (s0 s x c : ℝ)
    (hss : s0 ≤ s) (hx : 0 ≤ x) (hc : 0 ≤ c) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * x / 8))) *
      ENNReal.ofReal (c * (3 : ℝ) ^ (s0 * x / 8)) ≤ ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hex : -(s * x / 8) + s0 * x / 8 ≤ 0 := by
    have := mul_le_mul_of_nonneg_right hss hx
    linarith
  calc
    (3 : ℝ) ^ (-(s * x / 8)) * (c * (3 : ℝ) ^ (s0 * x / 8)) =
        c * (3 : ℝ) ^ (-(s * x / 8) + s0 * x / 8) := by
      rw [Real.rpow_add (by norm_num)]
      ring
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hex) hc
    _ = c := mul_one c

theorem aux_prefix_bad_score_zero_product_bound {d : ℕ}
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d) (m j : ℕ) (z : Vec d)
    (eps s : ℝ) (heps : 0 ≤ eps) (hs : s ≤ 1 / 2)
    (hF : GoodFieldOne m z eps s g) (hP : GoodFieldTwo m z s g)
    (x : Vec d) (hx : x ∈ translatedCube d ((m + 1 + j : ℕ) : ℤ) z) :
    (∏ i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal (Real.exp |g i x|)) +
      sSup {u : ENNReal | ∃ K : ℕ,
        u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
          ENNReal.ofReal (Real.exp (4 * |g i x - g i z|))} ≤
      ENNReal.ofReal (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8)) := by
  let gt := translatePotentialSample z g
  have hFt : GoodFieldOne m 0 eps s gt := by
    apply (goodFieldOne_translatePotentialSample m 0 eps s z g).mpr
    simpa only [add_zero] using hF
  have hPt : GoodFieldTwo m 0 s gt := by
    apply (goodFieldTwo_translatePotentialSample m 0 s z g).mpr
    simpa only [add_zero] using hP
  have hx0 : x - z ∈ cube d ((m + 1 + j : ℕ) : ℤ) := by
    rcases hx with ⟨y, hy, hxy⟩
    have hyx : x - z = y := by
      change z + y = x at hxy
      rw [← hxy, add_sub_cancel_left]
    rwa [hyx]
  let pointTerm : ℕ → ℝ := fun i => if m + j ≤ i then 4 * |g i x - g i z| else 0
  have hpoint : Summable pointTerm := by
    have hsum := Section6Localization.summable_goodFieldTwo_tail_supNorm_of_goodFieldOne
      m j heps hs gt hFt
    apply Summable.of_nonneg_of_le (g := pointTerm) _ _ hsum
    · intro i
      dsimp only [pointTerm]
      split_ifs <;> positivity
    · intro i
      dsimp only [pointTerm]
      split_ifs with hi
      · have h := Section6Localization.abs_apply_le_supNormOn_cube_of_continuous
          ((gt i).1.1.continuous.sub (continuous_const : Continuous (fun _ : Vec d => gt i 0))) hx0
        have heval : gt i (x - z) - gt i 0 = g i x - g i z := by
          simp only [gt, translatePotentialSample_apply, sub_add_cancel, zero_add]
        change |gt i (x - z) - gt i 0| ≤ _ at h
        rw [heval] at h
        exact mul_le_mul_of_nonneg_left h (by norm_num)
      · exact le_rfl
  let T : ℝ := ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |g i x - g i z|) else 1
  have hTeq : T = Real.exp (∑' i, pointTerm i) := by
    have heq : (fun i : ℕ => if m + j ≤ i then Real.exp (4 * |g i x - g i z|) else 1) =
        fun i => Real.exp (pointTerm i) := by
      funext i
      dsimp only [pointTerm]
      split_ifs <;> simp only [Real.exp_zero]
    dsimp only [T]
    rw [heq]
    exact hpoint.hasSum.rexp.tprod_eq
  have hT0 : 0 ≤ T := by rw [hTeq]; positivity
  have hpartial : sSup {u : ENNReal | ∃ K : ℕ,
      u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
        ENNReal.ofReal (Real.exp (4 * |g i x - g i z|))} ≤ ENNReal.ofReal T := by
    apply sSup_le
    rintro v ⟨K, rfl⟩
    rw [aux_psf_prod_ofReal_exp, hTeq]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have heq : (∑ i ∈ Finset.Icc (m + j) (m + j + K), 4 * |g i x - g i z|) =
        ∑ i ∈ Finset.Icc (m + j) (m + j + K), pointTerm i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [pointTerm, ite_eq_left (Finset.mem_Icc.mp hi).1]
    rw [heq]
    exact hpoint.sum_le_tsum _ (fun i _ => by dsimp only [pointTerm]; split_ifs <;> positivity)
  have hvalue : (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |g i x|) + T ≤
      6 * (3 : ℝ) ^ (s * (j : ℝ) / 8) := by
    have hb := Section6Localization.bddAbove_goodFieldTwo_values_of_goodFieldOne
      m j heps hs gt hFt
    have hx0' : x - z ∈ translatedCube d ((m + 1 + j : ℕ) : ℤ) 0 := by
      exact ⟨x - z, hx0, zero_add _⟩
    have hle := le_csSup hb ⟨x - z, hx0', rfl⟩
    have hgood := hPt j
    have hkey := hle.trans hgood
    simp only [gt, translatePotentialSample_apply, sub_add_cancel, zero_add] at hkey
    exact (le_abs_self _).trans hkey
  calc
    _ ≤ (∏ i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal (Real.exp |g i x|)) +
        ENNReal.ofReal T := add_le_add le_rfl hpartial
    _ = ENNReal.ofReal ((∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |g i x|) + T) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
        ← ENNReal.ofReal_add (by positivity) hT0]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hvalue

theorem aux_prefix_bad_score_zero_field_norm {d : ℕ}
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d) (i n : ℕ) (z : Vec d) :
    sSup {v : ENNReal | ∃ x ∈ translatedCube d (n : ℤ) z,
      v = ENNReal.ofReal |(|g i x| + (3 : ℝ) ^ (i : ℝ) *
        Homogenization.euclideanNorm (shellGradient (g i) x))|} =
      ENNReal.ofReal (supNormOn (translatedCube d (n : ℤ) z)
        (fun x => |g i x| + (3 : ℝ) ^ i * Homogenization.euclideanNorm (shellGradient (g i) x))) := by
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (aux_psf_normOn_le i n z g)
  rw [← ENNReal.ofReal_toReal hfin, aux_prefix_score_accumulated_error_norm]
  simp only [Real.rpow_natCast]

theorem prefix_bad_score_zero {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s s0 eps : ℝ)
    (hs0 : s0 ≤ 1 / 2) (hss : s0 ≤ s)
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt)
    (m : ℕ) (z : Vec d)
    (hgood : g ∈ goodEvent M none m z (eps / 2) s0) : Zsc m z = 0 := by
  obtain ⟨_, _, heps, _, hF, hP, hR, _, _, hZ, _⟩ := hPS
  have hFbound : Fsc m z ≤ ENNReal.ofReal (eps / 2) := by
    rw [hF m z]
    apply sSup_le
    rintro v ⟨j, rfl⟩
    have hn : ∀ i : ℕ,
        sSup {v : ENNReal | ∃ x ∈ translatedCube d ((m : ℤ) + 1 + (j : ℤ)) z,
          v = ENNReal.ofReal |(|g i x| + (3 : ℝ) ^ (i : ℝ) *
            Homogenization.euclideanNorm (shellGradient (g i) x))|} =
        ENNReal.ofReal (supNormOn (translatedCube d ((m : ℤ) + 1 + (j : ℤ)) z)
          (fun x => |g i x| + (3 : ℝ) ^ i * Homogenization.euclideanNorm (shellGradient (g i) x))) := by
      intro i
      simpa only [Nat.cast_add, Nat.cast_one] using
        aux_prefix_bad_score_zero_field_norm g i (m + 1 + j) z
    dsimp only
    simp_rw [hn]
    have hnonneg : ∀ i : ℕ, 0 ≤ supNormOn
        (translatedCube d ((m : ℤ) + 1 + (j : ℤ)) z)
        (fun x => |g i x| + (3 : ℝ) ^ i * Homogenization.euclideanNorm (shellGradient (g i) x)) := by
      intro i
      rw [← aux_prefix_score_accumulated_error_norm]
      exact ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i)]
    exact (mul_le_mul_right (ENNReal.ofReal_le_ofReal (hgood.1 j)) _).trans
      (aux_prefix_bad_score_zero_discount s0 s j (eps / 2) hss (Nat.cast_nonneg _) (by positivity))
  have hPbound : Psc m z ≤ ENNReal.ofReal 6 := by
    rw [hP m z]
    apply sSup_le
    rintro v ⟨j, rfl⟩
    refine le_trans ?_
      (aux_prefix_bad_score_zero_discount s0 s j 6 hss (Nat.cast_nonneg _) (by norm_num))
    apply mul_le_mul_right
    apply sSup_le
    rintro v ⟨x, hx, rfl⟩
    apply aux_prefix_bad_score_zero_product_bound g m j z (eps / 2) s0
      (by positivity) hs0 hgood.1 hgood.2.1 x
    simpa only [Nat.cast_add, Nat.cast_one] using hx
  have hRbound : Rsc m z ≤ ENNReal.ofReal (eps ^ 2 / 4) := by
    rw [hR m z]
    apply sSup_le
    rintro v ⟨j, n, hjm, hnj, x, hgrid, hann, rfl⟩
    have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show n ≤ m by omega)
    refine le_trans ?_
      (aux_prefix_bad_score_zero_discount s0 s ((m : ℝ) - (n : ℝ))
        (eps ^ 2 / 4) hss (sub_nonneg.mpr hnm) (by positivity))
    apply mul_le_mul_right
    apply sSup_le
    rintro v ⟨e, he, rfl⟩
    have hg := hgood.2.2 j n hjm hnj x hgrid hann e he
    simp only [Option.getD_none, min_self] at hg
    have hepssq : (eps / 2) ^ 2 = eps ^ 2 / 4 := by ring
    rw [hepssq] at hg
    exact ENNReal.ofReal_le_ofReal hg
  rw [(hZ m z).1]
  dsimp only
  rw [tsub_eq_zero_of_le hFbound, tsub_eq_zero_of_le hPbound,
    tsub_eq_zero_of_le hRbound]
  norm_num

end SubdiffusiveProcess.Paper

