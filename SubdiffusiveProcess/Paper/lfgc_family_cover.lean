module

public import SubdiffusiveProcess.Paper.lfgc_single_cover1

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory Filter Topology SubdiffusiveProcess
open scoped ENNReal

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]



@[instance_reducible]
def aux_lfgc_family_cover_nodeWin (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] (k : ℕ) (h : ℕ+) :
    MeasurableSpace (BilateralField d) :=
  layerWindow C(SpatialCoordinates d, ℝ) (Set.Icc (-(k : ℤ) - 2 * (h : ℤ)) (-(k : ℤ) + (h : ℤ)))

theorem aux_lfgc_family_cover_measurableSet_cellEvent (T : ℕ) (offset : Fin T → ℤ) (n : ℤ) (ε : ℝ) (i : Fin T) (l : ℕ)
    (y : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) (s : Set ℤ) (hs : ((l + 1 : ℕ) : ℤ) ∈ s) :
    MeasurableSet[layerWindow C(SpatialCoordinates d, ℝ) s] (aux_lfgc_single_cover1_cellEvent T offset n ε i l y) := by
  have hm : Measurable (fun omega : BilateralField d =>
      _root_.SubdiffusiveProcess.Paper.aux_psf_cellObs (l + 1) y (aux_lfgc_layer_tail_canonEta 0 omega)) :=
    (_root_.SubdiffusiveProcess.Paper.aux_psf_cellObs_measurable (l + 1) y).comp (aux_lfgc_layer_tail_measurable_canonEta 0)
  refine measurableSet_layerWindow_of_depends (measurableSet_lt measurable_const hm) fun ω ω' h => ?_
  have hl : ω ((l + 1 : ℕ) : ℤ) = ω' ((l + 1 : ℕ) : ℤ) := h _ hs
  have hc : aux_lfgc_layer_tail_canonEta 0 ω (l + 1) = aux_lfgc_layer_tail_canonEta 0 ω' (l + 1) := by
    unfold aux_lfgc_layer_tail_canonEta
    have e : (((l + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) = ((l + 1 : ℕ) : ℤ) := by simp
    rw [e, hl]
  have : _root_.SubdiffusiveProcess.Paper.aux_psf_cellObs (l + 1) y (aux_lfgc_layer_tail_canonEta 0 ω) =
      _root_.SubdiffusiveProcess.Paper.aux_psf_cellObs (l + 1) y (aux_lfgc_layer_tail_canonEta 0 ω') := by
    unfold _root_.SubdiffusiveProcess.Paper.aux_psf_cellObs; rw [hc]
  simp only [aux_lfgc_single_cover1_cellEvent, Set.mem_ofPred_eq, this]

/-- Bernoulli-type lower bound used for the super-exponential tails. -/
theorem aux_lfgc_family_cover_one_add_le_pow_mul_pow (a b : ℕ) :
    (1 : ℝ) + a + b ≤ ((3 : ℝ) / 2) ^ (2 * a) * (3 : ℝ) ^ (2 * b) := by
  have h1 : (1 : ℝ) + a ≤ ((3 : ℝ) / 2) ^ (2 * a) := by
    rw [pow_mul]
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 5 / 4 by norm_num) a
    norm_num at this ⊢
    linarith
  have h2 : (1 : ℝ) + b ≤ (3 : ℝ) ^ (2 * b) := by
    rw [pow_mul]
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 8 by norm_num) b
    norm_num at this ⊢
    linarith
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  nlinarith

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- Lower bound for the cell-event threshold. -/
theorem aux_lfgc_family_cover_cellEvent_threshold_ge {T : ℕ} (offset : Fin T → ℤ) (k : ℕ) (hoff : ∀ i, -3 ≤ offset i)
    {ε : ℝ} (hε : 0 ≤ ε) (i : Fin T) (l : ℕ) :
    2 * ε * d / 27 * ((3 : ℝ) / 2) ^ (l + 1) * (3 : ℝ) ^ k ≤
      2 * (ε / 2 ^ (l + 1)) / (3 : ℝ) ^ (-((k : ℤ) + offset i)) * ((3 : ℝ) ^ (l + 1) * d) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-((k : ℤ) + offset i)) := by positivity
  have hinv : ((3 : ℝ) ^ (-((k : ℤ) + offset i)))⁻¹ = (3 : ℝ) ^ ((k : ℤ) + offset i) := by
    rw [zpow_neg, inv_inv]
  have hge : (3 : ℝ) ^ k / 27 ≤ (3 : ℝ) ^ ((k : ℤ) + offset i) := by
    have : (3 : ℝ) ^ ((k : ℤ) - 3) ≤ (3 : ℝ) ^ ((k : ℤ) + offset i) :=
      zpow_le_zpow_right₀ (by norm_num) (by have := hoff i; omega)
    refine le_trans (le_of_eq ?_) this
    rw [zpow_sub₀ (by norm_num), zpow_natCast]; norm_num
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have e : 2 * (ε / 2 ^ (l + 1)) / (3 : ℝ) ^ (-((k : ℤ) + offset i)) * ((3 : ℝ) ^ (l + 1) * d) =
      2 * ε * d * ((3 : ℝ) / 2) ^ (l + 1) * ((3 : ℝ) ^ (-((k : ℤ) + offset i)))⁻¹ := by
    rw [div_pow]; field_simp
  rw [e, hinv]
  have hpow : 0 ≤ 2 * ε * d * ((3 : ℝ) / 2) ^ (l + 1) := by positivity
  calc 2 * ε * d / 27 * ((3 : ℝ) / 2) ^ (l + 1) * (3 : ℝ) ^ k
      = 2 * ε * d * ((3 : ℝ) / 2) ^ (l + 1) * ((3 : ℝ) ^ k / 27) := by ring
    _ ≤ 2 * ε * d * ((3 : ℝ) / 2) ^ (l + 1) * (3 : ℝ) ^ ((k : ℤ) + offset i) :=
        mul_le_mul_of_nonneg_left hge hpow

/-- Super-exponential decay of a single cell event. -/
theorem aux_lfgc_family_cover_cellEvent_prob (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {T : ℕ} (offset : Fin T → ℤ)
    (k : ℕ) (hoff : ∀ i, -3 ≤ offset i) {ε R : ℝ} (hε : 0 ≤ ε)
    (hC1 : R ≤ (2 * ε * d / 27 / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M) ^ 2) (i : Fin T) (l : ℕ)
    (y : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) :
    (chaosSampleLaw M).toMeasure (aux_lfgc_single_cover1_cellEvent T offset k ε i l y) ≤
      2 * ENNReal.ofReal (Real.exp (-(2 * ε * d / 27 / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M) ^ 2) *
        Real.exp (-R * ((l + 1 + k : ℕ) : ℝ))) := by
  have hσ := _root_.SubdiffusiveProcess.Paper.aux_psf_sigma_pos M
  set C := 2 * ε * d / 27 / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M
  set t := 2 * (ε / 2 ^ (l + 1)) / (3 : ℝ) ^ (-((k : ℤ) + offset i)) * ((3 : ℝ) ^ (l + 1) * d)
  have ht0 : 0 ≤ t := by positivity
  refine (lfgc_layer_tail M 0 (l + 1) y ht0).trans ?_
  gcongr
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hge := aux_lfgc_family_cover_cellEvent_threshold_ge (d := d) offset k hoff hε i l
  have hC0 : 0 ≤ C := by positivity
  have hq : C * (((3 : ℝ) / 2) ^ (l + 1) * (3 : ℝ) ^ k) ≤ t / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M := by
    rw [le_div_iff₀ hσ]
    calc C * (((3 : ℝ) / 2) ^ (l + 1) * (3 : ℝ) ^ k) * _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M
        = 2 * ε * d / 27 * ((3 : ℝ) / 2) ^ (l + 1) * (3 : ℝ) ^ k := by
          simp only [C]; field_simp
      _ ≤ t := hge
  have hsq : C ^ 2 * (1 + (l + 1 : ℕ) + k) ≤ (t / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M) ^ 2 := by
    have hb := aux_lfgc_family_cover_one_add_le_pow_mul_pow (l + 1) k
    have hpp : 0 ≤ C * (((3 : ℝ) / 2) ^ (l + 1) * (3 : ℝ) ^ k) := by positivity
    have h2 : (C * (((3 : ℝ) / 2) ^ (l + 1) * (3 : ℝ) ^ k)) ^ 2 ≤ (t / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M) ^ 2 :=
      pow_le_pow_left₀ hpp hq 2
    have h3 : C ^ 2 * (1 + (l + 1 : ℕ) + k) ≤ (C * (((3 : ℝ) / 2) ^ (l + 1) * (3 : ℝ) ^ k)) ^ 2 := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
      rw [mul_comm (l + 1) 2, mul_comm k 2]
      push_cast at hb ⊢
      linarith
    linarith
  push_cast at hsq ⊢
  nlinarith [hsq, hC1, sq_nonneg C]

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_family_cover_card_cellCenters_le_nat [_instPreserved0 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_instPreserved1 : BorelSpace C(SpatialCoordinates d, ℝ)] (w : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) : (aux_lfgc_layer_osc_cells_cellCenters w).card ≤ 57 ^ d := by
  have := aux_lfgc_layer_osc_cells_card_cellCenters_le w
  exact_mod_cast this

/-- Interval cover of the cell events of all infrared layers `l ≥ L₀`. -/
theorem lfgc_family_cover (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {T : ℕ} (offset : Fin T → ℤ)
    (shift : Fin T → SpatialCoordinates d) (k : ℕ) (z : SpatialCoordinates d)
    (hoff : ∀ i, -3 ≤ offset i) {ε R : ℝ} (hε : 0 ≤ ε) (L₀ : ℕ)
    (hC1 : R ≤ (2 * ε * d / 27 / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M) ^ 2)
    (hC2 : 16 * T * 57 ^ d * Real.exp (-(2 * ε * d / 27 / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M) ^ 2) ≤ 1) :
    IsTailCover (chaosSampleLaw M).toMeasure (aux_lfgc_family_cover_nodeWin d k)
      (⋃ (i : Fin T) (l : ℕ) (_ : L₀ ≤ l)
        (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
        aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y)
      (fun h => ENNReal.ofReal (Real.exp (-R * (h : ℝ)) / 8)) := by
  classical
  set C := 2 * ε * d / 27 / _root_.SubdiffusiveProcess.Paper.aux_psf_sigma M
  let A : ℕ → Set (BilateralField d) := fun l => if L₀ ≤ l then
    ⋃ (i : Fin T) (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
      aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y else ∅
  have hEq : (⋃ (i : Fin T) (l : ℕ) (_ : L₀ ≤ l)
      (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
      aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y) = ⋃ l, A l := by
    ext omega
    simp only [Set.mem_iUnion, A]
    constructor
    · rintro ⟨i, l, hl, y, hy, h⟩
      exact ⟨l, by simp only [hl, ite_true, Set.mem_iUnion]; exact ⟨i, y, hy, h⟩⟩
    · rintro ⟨l, h⟩
      by_cases hl : L₀ ≤ l
      · simp only [hl, ite_true, Set.mem_iUnion] at h
        obtain ⟨i, y, hy, h⟩ := h
        exact ⟨i, l, hl, y, hy, h⟩
      · simp only [hl, ite_false, Set.mem_empty_iff_false] at h
  rw [hEq]
  let hj : ℕ → ℕ+ := fun l => ⟨l + 1 + k, by omega⟩
  have hinj : Function.Injective hj := by
    intro a b h
    have := congrArg PNat.val h
    simp only [hj, PNat.mk_coe] at this
    omega
  refine isTailCover_iUnion_injective (P := (chaosSampleLaw M).toMeasure) (B := aux_lfgc_family_cover_nodeWin d k)
    A hj hinj (fun l => ?_) _ (fun l => ?_)
  · by_cases hl : L₀ ≤ l
    · simp only [A, hl, ite_true]
      refine MeasurableSet.iUnion fun i => Finset.measurableSet_biUnion _ fun y _ => ?_
      refine aux_lfgc_family_cover_measurableSet_cellEvent T offset (k : ℤ) ε i l y _ ⟨?_, ?_⟩
      · simp only [hj, PNat.mk_coe]; push_cast; omega
      · simp only [hj, PNat.mk_coe]; push_cast; omega
    · simp only [A, hl, ite_false]; exact @MeasurableSet.empty _ (aux_lfgc_family_cover_nodeWin d k (hj l))
  · by_cases hl : L₀ ≤ l
    · simp only [A, hl, ite_true]
      have hc : ∀ (i : Fin T) (y : SubdiffusiveProcess.CoarseGrainingVocab.Vec d),
          (chaosSampleLaw M).toMeasure (aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y) ≤
            2 * ENNReal.ofReal (Real.exp (-C ^ 2) * Real.exp (-R * ((l + 1 + k : ℕ) : ℝ))) :=
        fun i y => aux_lfgc_family_cover_cellEvent_prob M offset k hoff hε hC1 i l y
      set b := 2 * ENNReal.ofReal (Real.exp (-C ^ 2) * Real.exp (-R * ((l + 1 + k : ℕ) : ℝ)))
      calc (chaosSampleLaw M).toMeasure (⋃ (i : Fin T) (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
            aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y)
          ≤ ∑ i : Fin T, (chaosSampleLaw M).toMeasure (⋃ (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
            aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y) := measure_iUnion_fintype_le _ _
        _ ≤ ∑ _i : Fin T, (57 ^ d : ℝ≥0∞) * b := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine (measure_biUnion_finset_le _ _).trans ?_
            refine (Finset.sum_le_sum fun y _ => hc i y).trans ?_
            rw [Finset.sum_const, nsmul_eq_mul]
            gcongr
            exact_mod_cast aux_lfgc_family_cover_card_cellCenters_le_nat _
        _ = (T : ℝ≥0∞) * (57 ^ d : ℝ≥0∞) * b := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
        _ ≤ ENNReal.ofReal (Real.exp (-R * ((hj l : ℕ) : ℝ)) / 8) := by
            simp only [b, hj, PNat.mk_coe]
            set x := Real.exp (-C ^ 2) * Real.exp (-R * ((l + 1 + k : ℕ) : ℝ))
            have hx : 0 ≤ x := by positivity
            have hxle : 2 * ((T : ℝ) * 57 ^ d * x) ≤ Real.exp (-R * ((l + 1 + k : ℕ) : ℝ)) / 8 := by
              have he := Real.exp_pos (-R * ((l + 1 + k : ℕ) : ℝ))
              have : 2 * ((T : ℝ) * 57 ^ d * Real.exp (-C ^ 2)) ≤ 1 / 8 := by linarith
              simp only [x]
              nlinarith [he, this]
            clear_value x
            have key : (T : ℝ≥0∞) * (57 : ℝ≥0∞) ^ d * (2 * ENNReal.ofReal x) =
                ENNReal.ofReal ((T : ℝ) * 57 ^ d * (2 * x)) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num),
                ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
            rw [key]
            refine ENNReal.ofReal_le_ofReal ?_
            linarith
    · simp only [A, hl, ite_false, measure_empty, zero_le]

end SubdiffusiveProcess.Paper
