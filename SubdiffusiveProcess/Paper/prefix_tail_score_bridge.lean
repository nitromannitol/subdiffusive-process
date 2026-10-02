import SubdiffusiveProcess.Paper.primitive_scores_finite
import SubdiffusiveProcess.Main.BilateralField
import Mathlib.Tactic

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book SubdiffusiveProcess
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_prefix_score_accumulated_error_sup_ofReal {ι : Type*}
    (p : ι → Prop) (f : ι → ℝ) (hf : ∀ i, p i → 0 ≤ f i) :
    (sSup {v : ENNReal | ∃ i, p i ∧ v = ENNReal.ofReal (f i)}).toReal =
      sSup {v : ℝ | ∃ i, p i ∧ v = f i} := by
  rw [ENNReal.toReal_sSup _ (by
    rintro v ⟨i, hi, rfl⟩
    exact ENNReal.ofReal_ne_top)]
  congr 1
  ext r
  constructor
  · rintro ⟨v, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, ENNReal.toReal_ofReal (hf i hi)⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨ENNReal.ofReal (f i), ⟨i, hi, rfl⟩,
      ENNReal.toReal_ofReal (hf i hi)⟩

theorem aux_prefix_score_accumulated_error_norm {d : ℕ}
    (W : Set (Vec d)) (f : Vec d → ℝ) :
    (sSup {v : ENNReal | ∃ x ∈ W, v = ENNReal.ofReal |f x|}).toReal =
      supNormOn W f :=
  aux_prefix_score_accumulated_error_sup_ofReal (fun x => x ∈ W)
    (fun x => |f x|) (fun _ _ => abs_nonneg _)

theorem aux_prefix_score_accumulated_error_response {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (l : ℕ) (z : Vec d) :
    (sSup {v : ENNReal | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
      v = ENNReal.ofReal (section6Response M l l g z e)}).toReal =
      sSup {v : ℝ | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
        v = section6Response M l l g z e} := by
  apply aux_prefix_score_accumulated_error_sup_ofReal
  intro e _
  unfold section6Response paperScalarProbe
  exact Ch02.responseJ_nonneg _ _ _ _

def aux_prefix_score_accumulated_error_raw {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (k : ℕ) (z : Vec d) : ENNReal :=
  sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
    OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
      (min (aux_psf_Jval M l g x) 1) ^ (1 / 2 : ℝ)} +
  sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
      sSup {v : ENNReal | ∃ x ∈ translatedCube d k z,
        v = ENNReal.ofReal |shellBlock k j g x|}} +
  ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
    sSup {v : ENNReal | ∃ x ∈ translatedCube d k z, v = ENNReal.ofReal |g 0 x|} +
  ∑' j : ℕ, if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k) *
    sSup {v : ENNReal | ∃ x ∈ translatedCube d k z,
      v = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (g j) x)|} else 0

theorem aux_prefix_score_accumulated_error_raw_eq {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (m : ℕ) (z : Vec d)
    (hD : aux_prefix_score_accumulated_error_raw M s g m z ≠ ⊤) :
    (aux_prefix_score_accumulated_error_raw M s g m z).toReal =
      accumulatedError M none m z s g := by
  let Dsc := aux_prefix_score_accumulated_error_raw M s g
  let J : ℕ → Vec d → ENNReal := fun l x =>
    sSup {v : ENNReal | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
      v = ENNReal.ofReal (section6Response M l l g x e)}
  let normOn : Set (Vec d) → (Vec d → ℝ) → ENNReal := fun W f =>
    sSup {v : ENNReal | ∃ x ∈ W, v = ENNReal.ofReal |f x|}
  let A : ENNReal := sSup {v : ENNReal | ∃ j l : ℕ,
    j ≤ m ∧ l ≤ m ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
    OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ)))) *
      (min (J l x) 1) ^ (1 / 2 : ℝ)}
  let B : ENNReal := sSup {v : ENNReal | ∃ j : ℕ, j ≤ m ∧
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ)))) *
      normOn (translatedCube d m z) (shellBlock m j g)}
  let C : ENNReal := ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (m : ℝ))) *
    normOn (translatedCube d m z) (g 0)
  let t : ℕ → ENNReal := fun j => if m ≤ j then
    ENNReal.ofReal ((3 : ℝ) ^ m) * normOn (translatedCube d m z)
      (fun x => Homogenization.euclideanNorm (shellGradient (g j) x)) else 0
  have hsum : Dsc m z = A + B + C + ∑' j, t j := rfl
  have hf : Dsc m z ≠ ⊤ := hD
  rw [hsum] at hf
  simp only [ENNReal.add_ne_top] at hf
  have hJ : ∀ l x, J l x ≠ ⊤ := fun l x => aux_psf_Jval_ne_top M l g x
  have hJn : ∀ l x, (J l x).toReal = sSup {v : ℝ | ∃ e : Vec d,
      Homogenization.vecNormSq e = 1 ∧ v = section6Response M l l g x e} :=
    fun l x => aux_prefix_score_accumulated_error_response M g l x
  have hnorm : ∀ W f, (normOn W f).toReal = supNormOn W f :=
    aux_prefix_score_accumulated_error_norm
  have hAt : A.toReal = sSup {r : ℝ | ∃ j l : ℕ, j ≤ m ∧ l + 2 ≤ j ∧
      ∃ x : Vec d, OnTriadicGrid l (x - z) ∧
        x - z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ))) *
          Real.sqrt (min (sSup {v : ℝ | ∃ e : Vec d,
            Homogenization.vecNormSq e = 1 ∧ v = section6Response M l l g x e}) 1)} := by
    have hterm : ∀ (l : ℕ) (x : Vec d),
        (ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ)))) *
          (min (J l x) 1) ^ (1 / 2 : ℝ)).toReal =
        (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ))) *
          Real.sqrt (min (sSup {v : ℝ | ∃ e : Vec d,
            Homogenization.vecNormSq e = 1 ∧ v = section6Response M l l g x e}) 1) := by
      intro l x
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
        ← ENNReal.toReal_rpow, ENNReal.toReal_min (hJ l x) ENNReal.one_ne_top,
        ENNReal.toReal_one, hJn, ← Real.sqrt_eq_rpow]
    dsimp only [A]
    rw [ENNReal.toReal_sSup _ (fun v hv =>
      ne_top_of_le_ne_top hf.1.1.1 (le_sSup hv))]
    congr 1
    ext r
    constructor
    · rintro ⟨v, ⟨j, l, hjm, _, hlj, x, hx, hann, rfl⟩, rfl⟩
      exact ⟨j, l, hjm, hlj, x, hx, hann, hterm l x⟩
    · rintro ⟨j, l, hjm, hlj, x, hx, hann, rfl⟩
      refine ⟨_, ⟨j, l, hjm, by omega, hlj, x, hx, hann, rfl⟩, hterm l x⟩
  have hBt : B.toReal = sSup {r : ℝ | ∃ j : ℕ, j ≤ m ∧
      r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (translatedCube d m z) (shellBlock m j g)} := by
    dsimp only [B]
    rw [ENNReal.toReal_sSup _ (fun v hv =>
      ne_top_of_le_ne_top hf.1.1.2 (le_sSup hv))]
    congr 1
    ext r
    constructor
    · rintro ⟨v, ⟨j, hjm, rfl⟩, rfl⟩
      refine ⟨j, hjm, ?_⟩
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hnorm]
    · rintro ⟨j, hjm, rfl⟩
      refine ⟨_, ⟨j, hjm, rfl⟩, ?_⟩
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hnorm]
  have hCt : C.toReal = (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) *
      supNormOn (translatedCube d m z) (g 0) := by
    dsimp only [C]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hnorm]
  have htt : (∑' j, t j).toReal = ∑' j : ℕ, if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (translatedCube d m z) (shellGradient (g j))
      else 0 := by
    rw [ENNReal.tsum_toReal_eq (fun j => ne_top_of_le_ne_top hf.2 (ENNReal.le_tsum j))]
    apply tsum_congr
    intro j
    dsimp only [t]
    split_ifs
    · rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hnorm]
      congr 1
      unfold supNormOn vectorSupNormOn
      simp only [abs_of_nonneg (Homogenization.euclideanNorm_nonneg _)]
    · exact ENNReal.toReal_zero
  change (Dsc m z).toReal = _
  rw [hsum, ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr hf.1.1, hf.1.2⟩) hf.2,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr hf.1.1) hf.1.2,
    ENNReal.toReal_add hf.1.1.1 hf.1.1.2, hAt, hBt, hCt, htt]
  unfold accumulatedError
  simp only [Option.getD_none, min_self]

theorem aux_prefix_score_accumulated_error_discount {s0 s t x : ℝ}
    (hss : s0 ≤ s) (ht : 0 < t) (hx : 0 ≤ x) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s / t) * x)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s0 / t) * x)) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hdiv := div_le_div_of_nonneg_right hss ht.le
  nlinarith [mul_le_mul_of_nonneg_right hdiv hx]

theorem aux_prefix_score_accumulated_error_raw_antitone {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s0 s : ℝ} (hss : s0 ≤ s)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (k : ℕ) (z : Vec d) :
    aux_prefix_score_accumulated_error_raw M s g k z ≤
      aux_prefix_score_accumulated_error_raw M s0 g k z := by
  unfold aux_prefix_score_accumulated_error_raw
  refine add_le_add ?_ le_rfl
  apply add_le_add
  · apply add_le_add
    · apply sSup_le
      rintro v ⟨j, l, hj, hl, hlj, x, hx, hann, rfl⟩
      exact (mul_le_mul_left (aux_prefix_score_accumulated_error_discount hss
        (by norm_num : (0 : ℝ) < 2) (sub_nonneg.mpr (by exact_mod_cast hl))) _).trans
        (le_sSup ⟨j, l, hj, hl, hlj, x, hx, hann, rfl⟩)
    · apply sSup_le
      rintro v ⟨j, hj, rfl⟩
      exact (mul_le_mul_left (aux_prefix_score_accumulated_error_discount hss
        (by norm_num : (0 : ℝ) < 8) (sub_nonneg.mpr (by exact_mod_cast hj))) _).trans
        (le_sSup ⟨j, hj, rfl⟩)
  · exact mul_le_mul_left (aux_prefix_score_accumulated_error_discount hss
      (by norm_num : (0 : ℝ) < 8) (Nat.cast_nonneg k)) _

def aux_prefix_physical_tail_sum {d : ℕ}
    (N k buffer D e : ℕ) (w : SpatialCoordinates d)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (useD : Bool) (om : BilateralField d) : ℝ :=
  ∑ j ∈ Finset.Icc ((k : ℤ) - (e : ℤ) - (buffer : ℤ))
      (min (N : ℤ) ((k : ℤ) - (e : ℤ) + (D : ℤ) + (buffer : ℤ))),
    if 0 ≤ (N : ℤ) - j then
      if useD then (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om).toReal
      else Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om
    else 0



theorem prefix_tail_score_bridge {s0 s t x : ℝ}
    (hss : s0 ≤ s) (ht : 0 < t) (hx : 0 ≤ x) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s / t) * x)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s0 / t) * x)) :=
  aux_prefix_score_accumulated_error_discount hss ht hx

end Paper
