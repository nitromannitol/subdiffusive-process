module

public import Mathlib
public import SubdiffusiveProcess.Paper.lem_finite_trace_smooth_net
public import SubdiffusiveProcess.FiniteStopping.TraceRescaling
public import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison
public import SubdiffusiveProcess.Analysis.HolderDilationToolkit

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal ContDiff Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ}

theorem aux_conv_represented_catalogue_holder_family_ratio_mul (β : ℝ) (S : Set (SpatialCoordinates d)) (c : ℝ)
    (f : SpatialCoordinates d → ℝ) :
    holderRatioSet β S (fun x => c * f x) = |c| • holderRatioSet β S f := by
  ext v
  simp only [holderRatioSet, Set.mem_smul_set, Set.mem_setOf_eq, smul_eq_mul]
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    refine ⟨_, ⟨x, hx, y, hy, hxy, rfl⟩, ?_⟩
    rw [← mul_sub, abs_mul, mul_div_assoc]
  · rintro ⟨w, ⟨x, hx, y, hy, hxy, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, hxy, by rw [← mul_sub, abs_mul, mul_div_assoc]⟩

theorem aux_conv_represented_catalogue_holder_family_abs_mul (S : Set (SpatialCoordinates d)) (c : ℝ) (f : SpatialCoordinates d → ℝ) :
    {v : ℝ | ∃ x ∈ S, v = |c * f x|} = |c| • {v : ℝ | ∃ x ∈ S, v = |f x|} := by
  ext v
  simp only [Set.mem_smul_set, Set.mem_setOf_eq, smul_eq_mul]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by rw [abs_mul]⟩
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by rw [abs_mul]⟩

theorem aux_conv_represented_catalogue_holder_family_holderSeminorm_nonneg (β : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : 0 ≤ holderSeminorm β S f := by
  unfold holderSeminorm
  apply Real.sSup_nonneg
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  positivity

theorem aux_conv_represented_catalogue_holder_family_cAlpha_mul (β : ℝ) (S : Set (SpatialCoordinates d)) (c : ℝ)
    (f : SpatialCoordinates d → ℝ) :
    cAlphaNorm β S (fun x => c * f x) = |c| * cAlphaNorm β S f := by
  unfold cAlphaNorm holderSeminorm
  rw [aux_conv_represented_catalogue_holder_family_abs_mul, aux_conv_represented_catalogue_holder_family_ratio_mul, Real.sSup_smul_of_nonneg (abs_nonneg c),
    Real.sSup_smul_of_nonneg (abs_nonneg c)]
  simp only [smul_eq_mul]
  ring

theorem aux_conv_represented_catalogue_holder_family_isHolder_mul (β : ℝ) (S : Set (SpatialCoordinates d)) (c : ℝ)
    (f : SpatialCoordinates d → ℝ) (h : IsHolderOn β S f) :
    IsHolderOn β S (fun x => c * f x) := by
  unfold IsHolderOn at h ⊢
  rw [aux_conv_represented_catalogue_holder_family_ratio_mul]
  obtain ⟨A, hA⟩ := h
  refine ⟨|c| * A, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact mul_le_mul_of_nonneg_left (hA hw) (abs_nonneg c)

theorem aux_conv_represented_catalogue_holder_family_bdd_mul (S : Set (SpatialCoordinates d)) (c : ℝ)
    (f : SpatialCoordinates d → ℝ) (h : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|}) :
    BddAbove {v : ℝ | ∃ x ∈ S, v = |c * f x|} := by
  rw [aux_conv_represented_catalogue_holder_family_abs_mul]
  obtain ⟨A, hA⟩ := h
  refine ⟨|c| * A, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact mul_le_mul_of_nonneg_left (hA hw) (abs_nonneg c)

theorem aux_conv_represented_catalogue_holder_family_isHolder_sub (β : ℝ) (S : Set (SpatialCoordinates d))
    (f g : SpatialCoordinates d → ℝ) (hf : IsHolderOn β S f) (hg : IsHolderOn β S g) :
    IsHolderOn β S (fun x => f x - g x) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨A + B, ?_⟩
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  have h1 : |f x - f y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ β ≤ A :=
    hA ⟨x, hx, y, hy, hxy, rfl⟩
  have h2 : |g x - g y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ β ≤ B :=
    hB ⟨x, hx, y, hy, hxy, rfl⟩
  have hden : 0 ≤ (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ β :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  calc |(f x - g x) - (f y - g y)| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ β
      ≤ (|f x - f y| + |g x - g y|) / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ β := by
        apply div_le_div_of_nonneg_right _ hden
        have : (f x - g x) - (f y - g y) = (f x - f y) - (g x - g y) := by ring
        rw [this]; exact abs_sub _ _
    _ ≤ A + B := by rw [add_div]; exact add_le_add h1 h2

theorem aux_conv_represented_catalogue_holder_family_bdd_sub (S : Set (SpatialCoordinates d)) (f g : SpatialCoordinates d → ℝ)
    (hf : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|}) (hg : BddAbove {v : ℝ | ∃ x ∈ S, v = |g x|}) :
    BddAbove {v : ℝ | ∃ x ∈ S, v = |f x - g x|} := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨A + B, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (abs_sub _ _).trans (add_le_add (hA ⟨x, hx, rfl⟩) (hB ⟨x, hx, rfl⟩))

theorem aux_conv_represented_catalogue_holder_family_sup_nonneg (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
    0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} :=
  Real.sSup_nonneg (by rintro _ ⟨x, hx, rfl⟩; exact abs_nonneg _)

theorem aux_conv_represented_catalogue_holder_family_cAlpha_nonneg (β : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : 0 ≤ cAlphaNorm β S f :=
  add_nonneg (aux_conv_represented_catalogue_holder_family_sup_nonneg S f) (aux_conv_represented_catalogue_holder_family_holderSeminorm_nonneg β S f)

theorem aux_conv_represented_catalogue_holder_family_quot_nonneg (β : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : 0 ≤ quotientCBetaNorm β S f := by
  unfold quotientCBetaNorm
  exact Real.sInf_nonneg (by rintro _ ⟨c, rfl⟩; exact aux_conv_represented_catalogue_holder_family_cAlpha_nonneg _ _ _)

theorem aux_conv_represented_catalogue_holder_family_quot_mul (β : ℝ) (S : Set (SpatialCoordinates d)) (c : ℝ) (hc : 0 < c)
    (f : SpatialCoordinates d → ℝ) :
    quotientCBetaNorm β S (fun x => c * f x) = c * quotientCBetaNorm β S f := by
  unfold quotientCBetaNorm
  have hset : {v : ℝ | ∃ c', v = cAlphaNorm β S (fun x => c * f x - c')} =
      c • {v : ℝ | ∃ c', v = cAlphaNorm β S (fun x => f x - c')} := by
    ext v
    simp only [Set.mem_smul_set, Set.mem_setOf_eq, smul_eq_mul]
    constructor
    · rintro ⟨c', rfl⟩
      refine ⟨cAlphaNorm β S (fun x => f x - c' / c), ⟨c' / c, rfl⟩, ?_⟩
      have : (fun x => c * f x - c') = fun x => c * (f x - c' / c) := by
        funext x; field_simp
      rw [this, aux_conv_represented_catalogue_holder_family_cAlpha_mul, abs_of_pos hc]
    · rintro ⟨w, ⟨c', rfl⟩, rfl⟩
      refine ⟨c * c', ?_⟩
      have : (fun x => c * f x - c * c') = fun x => c * (f x - c') := by
        funext x; ring
      rw [this, aux_conv_represented_catalogue_holder_family_cAlpha_mul, abs_of_pos hc]
  rw [hset, Real.sInf_smul_of_nonneg hc.le]
  rfl

theorem aux_conv_represented_catalogue_holder_family_quot_le_cAlpha (β : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : quotientCBetaNorm β S f ≤ cAlphaNorm β S f := by
  unfold quotientCBetaNorm
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨c, rfl⟩; exact aux_conv_represented_catalogue_holder_family_cAlpha_nonneg _ _ _⟩
  · exact ⟨0, by simp only [sub_zero]⟩

theorem aux_conv_represented_catalogue_holder_family_exists_const (β : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) (t : ℝ) (ht : quotientCBetaNorm β S f < t) :
    ∃ c : ℝ, cAlphaNorm β S (fun x => f x - c) < t := by
  unfold quotientCBetaNorm at ht
  have hne : Set.Nonempty {v : ℝ | ∃ c : ℝ, v = cAlphaNorm β S (fun x => f x - c)} :=
    ⟨cAlphaNorm β S (fun x => f x - 0), 0, rfl⟩
  obtain ⟨v, ⟨c, rfl⟩, hv⟩ := exists_lt_of_csInf_lt hne ht
  exact ⟨c, hv⟩

theorem aux_conv_represented_catalogue_holder_family_cAlpha_sub_const_le (β : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) (hb : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|}) (t : ℝ) :
    cAlphaNorm β S (fun x => f x - t) ≤ cAlphaNorm β S f + |t| := by
  unfold cAlphaNorm
  have hseq : holderSeminorm β S (fun x => f x - t) = holderSeminorm β S f := by
    unfold holderSeminorm
    rw [FiniteStopping.holderRatioSet_sub_const]
  rw [hseq]
  have hsup : sSup {v : ℝ | ∃ x ∈ S, v = |f x - t|} ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} + |t| := by
    apply Real.sSup_le
    · rintro _ ⟨x, hx, rfl⟩
      have h1 : |f x| ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} := le_csSup hb ⟨x, hx, rfl⟩
      calc |f x - t| ≤ |f x| + |t| := abs_sub _ _
        _ ≤ _ := by linarith
    · have := aux_conv_represented_catalogue_holder_family_sup_nonneg S f
      positivity
  linarith

theorem aux_conv_represented_catalogue_holder_family_abs_le_cAlpha (β : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) (hb : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|})
    (x : SpatialCoordinates d) (hx : x ∈ S) : |f x| ≤ cAlphaNorm β S f := by
  unfold cAlphaNorm
  have := le_csSup hb ⟨x, hx, rfl⟩
  linarith [aux_conv_represented_catalogue_holder_family_holderSeminorm_nonneg β S f]

theorem aux_conv_represented_catalogue_holder_family_cAlpha_neg (β : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : cAlphaNorm β S (fun x => -f x) = cAlphaNorm β S f := by
  have := aux_conv_represented_catalogue_holder_family_cAlpha_mul β S (-1) f
  simpa using this

theorem aux_conv_represented_catalogue_holder_family_frontier_dil (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (y : SpatialCoordinates d) :
    y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) ↔
      cubeDilation z 0 r y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  change y ∈ frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) ↔
    cubeDilation z 0 r y ∈ frontier (Metric.ball z (r / 2))
  rw [frontier_ball _ (by norm_num), frontier_ball _ (by positivity), Metric.mem_sphere,
    Metric.mem_sphere]
  have hd : dist (cubeDilation z 0 r y) z = r * dist y 0 := by
    rw [dist_eq_norm, dist_eq_norm]
    have : cubeDilation z 0 r y - z = r • (y - 0) := by
      funext i; simp [cubeDilation]
    rw [this, norm_smul, Real.norm_of_nonneg hr.le]
  rw [hd]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have : r * dist y 0 = r * (1 / 2) := by rw [h]; ring
    exact mul_left_cancel₀ hr.ne' this

theorem aux_conv_represented_catalogue_holder_family_rescaled_eq (z : SpatialCoordinates d) (r : ℝ) (f : SpatialCoordinates d → ℝ) :
    rescaledDatum z r f = fun y => f (cubeDilation z 0 r y) := by
  funext y
  unfold rescaledDatum
  congr 1
  funext i
  simp [cubeDilation]

/-- The frontier of the unit cube. -/
abbrev aux_conv_represented_catalogue_holder_family_Sfr (d : ℕ) : Set (SpatialCoordinates d) :=
  frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))

theorem aux_conv_represented_catalogue_holder_family_class_unit (β : ℝ) (f : SpatialCoordinates d → ℝ) :
    IsCellBoundaryClass β 0 1 f ↔
      (IsHolderOn β (aux_conv_represented_catalogue_holder_family_Sfr d) f ∧ BddAbove {v : ℝ | ∃ x ∈ aux_conv_represented_catalogue_holder_family_Sfr d, v = |f x|}) := by
  unfold IsCellBoundaryClass
  rw [FiniteStopping.rescaledDatum_unit]

theorem aux_conv_represented_catalogue_holder_family_cbqn_unit (β : ℝ) (f : SpatialCoordinates d → ℝ) :
    cellBoundaryQuotientNorm β 0 1 f = quotientCBetaNorm β (aux_conv_represented_catalogue_holder_family_Sfr d) f := by
  unfold cellBoundaryQuotientNorm
  rw [FiniteStopping.rescaledDatum_unit]

theorem aux_conv_represented_catalogue_holder_family_isHolder_add_const (β : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) (q : ℝ) (h : IsHolderOn β S f) :
    IsHolderOn β S (fun x => f x + q) := by
  have : (fun x => f x + q) = fun x => f x - (-q) := by funext x; ring
  rw [this, FiniteStopping.isHolderOn_sub_const]
  exact h

theorem aux_conv_represented_catalogue_holder_family_bdd_add_const (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ)
    (q : ℝ) (h : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|}) :
    BddAbove {v : ℝ | ∃ x ∈ S, v = |f x + q|} := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A + |q|, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (abs_add_le _ _).trans (add_le_add (hA ⟨x, hx, rfl⟩) le_rfl)

/-- Unit-frame approximation: countably many finite smooth nets, integer scale and rational shift. -/
theorem aux_conv_represented_catalogue_holder_family_core (hd : 2 ≤ d) (β α : ℝ) (hb : 1 / 2 < β) (hba : β < α) (ha1 : α < 1) :
    ∃ Hs : ℕ → ℕ → Finset (SpatialCoordinates d → ℝ),
      (∀ m n, ∀ h ∈ Hs m n, ContDiff ℝ ∞ h ∧ IsCellBoundaryClass β 0 1 h) ∧
      ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass α 0 1 g → IsCellBoundaryClass β 0 1 g →
        ∃ n : ℕ, ∀ m : ℕ, ∃ h ∈ Hs m n, ∃ q : ℚ,
          cAlphaNorm β (aux_conv_represented_catalogue_holder_family_Sfr d) (fun y => g y - (((n : ℝ) + 1) * h y + (q : ℝ))) <
            3 * (1 / ((m : ℝ) + 1)) := by
  obtain ⟨C, hC, hbnd, hnet⟩ := lem_finite_trace_smooth_net d hd β α hb hba ha1
  have hε : ∀ m n : ℕ, (0 : ℝ) < 1 / (((m : ℝ) + 1) * ((n : ℝ) + 1)) := fun m n => by positivity
  choose Hs hHs hHnet using fun m n => hnet _ (hε m n)
  refine ⟨Hs, fun m n h hh => ⟨(hHs m n h hh).1, (hHs m n h hh).2.1⟩, ?_⟩
  intro g hgα hgβ
  set N := cellBoundaryQuotientNorm α 0 1 g with hN
  set n : ℕ := ⌈N⌉₊ with hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hgα' := (aux_conv_represented_catalogue_holder_family_class_unit α g).1 hgα
  have hgβ' := (aux_conv_represented_catalogue_holder_family_class_unit β g).1 hgβ
  have hclass' : IsCellBoundaryClass α 0 1 (fun x => ((n : ℝ) + 1)⁻¹ * g x) :=
    (aux_conv_represented_catalogue_holder_family_class_unit α _).2 ⟨aux_conv_represented_catalogue_holder_family_isHolder_mul _ _ _ _ hgα'.1, aux_conv_represented_catalogue_holder_family_bdd_mul _ _ _ hgα'.2⟩
  have hnorm' : cellBoundaryQuotientNorm α 0 1 (fun x => ((n : ℝ) + 1)⁻¹ * g x) ≤ 1 := by
    rw [aux_conv_represented_catalogue_holder_family_cbqn_unit, aux_conv_represented_catalogue_holder_family_quot_mul _ _ _ (inv_pos.2 hn1), ← aux_conv_represented_catalogue_holder_family_cbqn_unit,
      inv_mul_le_iff₀ hn1]
    have := Nat.le_ceil N
    linarith
  refine ⟨n, fun m => ?_⟩
  obtain ⟨h, hhmem, hhnorm⟩ := hHnet m n _ hclass' hnorm'
  have hhβ := (aux_conv_represented_catalogue_holder_family_class_unit β h).1 (hHs m n h hhmem).2.1
  have hhnorm' : quotientCBetaNorm β (aux_conv_represented_catalogue_holder_family_Sfr d) (fun x => ((n : ℝ) + 1)⁻¹ * g x - h x) ≤
      1 / (((m : ℝ) + 1) * ((n : ℝ) + 1)) := by
    rw [← aux_conv_represented_catalogue_holder_family_cbqn_unit]; exact hhnorm
  have hq : quotientCBetaNorm β (aux_conv_represented_catalogue_holder_family_Sfr d) (fun y => g y - ((n : ℝ) + 1) * h y) ≤
      1 / ((m : ℝ) + 1) := by
    have hfun : (fun y => g y - ((n : ℝ) + 1) * h y) =
        fun y => ((n : ℝ) + 1) * (((n : ℝ) + 1)⁻¹ * g y - h y) := by
      funext y; field_simp
    rw [hfun, aux_conv_represented_catalogue_holder_family_quot_mul _ _ _ hn1]
    calc ((n : ℝ) + 1) * quotientCBetaNorm β (aux_conv_represented_catalogue_holder_family_Sfr d)
          (fun x => ((n : ℝ) + 1)⁻¹ * g x - h x)
        ≤ ((n : ℝ) + 1) * (1 / (((m : ℝ) + 1) * ((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hhnorm' hn1.le
      _ = 1 / ((m : ℝ) + 1) := by field_simp
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlt : quotientCBetaNorm β (aux_conv_represented_catalogue_holder_family_Sfr d) (fun y => g y - ((n : ℝ) + 1) * h y) <
      2 * (1 / ((m : ℝ) + 1)) := by
    refine lt_of_le_of_lt hq ?_
    have : 0 < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  obtain ⟨c, hc⟩ := aux_conv_represented_catalogue_holder_family_exists_const β _ _ _ hlt
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show c - 1 / ((m : ℝ) + 1) < c + 1 / ((m : ℝ) + 1) by
    have : 0 < 1 / ((m : ℝ) + 1) := by positivity
    linarith)
  refine ⟨h, hhmem, q, ?_⟩
  have hbddF : BddAbove {v : ℝ | ∃ x ∈ aux_conv_represented_catalogue_holder_family_Sfr d, v = |g x - ((n : ℝ) + 1) * h x|} :=
    aux_conv_represented_catalogue_holder_family_bdd_sub _ g (fun y => ((n : ℝ) + 1) * h y) hgβ'.2 (aux_conv_represented_catalogue_holder_family_bdd_mul _ _ h hhβ.2)
  have hbddu : BddAbove {v : ℝ | ∃ x ∈ aux_conv_represented_catalogue_holder_family_Sfr d,
      v = |(g x - ((n : ℝ) + 1) * h x) - c|} :=
    aux_conv_represented_catalogue_holder_family_bdd_sub _ (fun y => g y - ((n : ℝ) + 1) * h y) (fun _ => c) hbddF
      ⟨|c|, by rintro _ ⟨x, hx, rfl⟩; exact le_rfl⟩
  have hshift := aux_conv_represented_catalogue_holder_family_cAlpha_sub_const_le β (aux_conv_represented_catalogue_holder_family_Sfr d)
    (fun y => (g y - ((n : ℝ) + 1) * h y) - c) hbddu ((q : ℝ) - c)
  have hfun2 : (fun y => g y - (((n : ℝ) + 1) * h y + (q : ℝ))) =
      fun y => ((g y - ((n : ℝ) + 1) * h y) - c) - ((q : ℝ) - c) := by
    funext y; ring
  rw [hfun2]
  have hqc : |(q : ℝ) - c| < 1 / ((m : ℝ) + 1) := by
    rw [abs_lt]; constructor <;> linarith
  linarith

theorem aux_conv_represented_catalogue_holder_family_dil_roundtrip (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (y : SpatialCoordinates d) : cubeDilation 0 z r⁻¹ (cubeDilation z 0 r y) = y :=
  (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne').left_inv y

theorem aux_conv_represented_catalogue_holder_family_dil_roundtrip' (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (x : SpatialCoordinates d) : cubeDilation z 0 r (cubeDilation 0 z r⁻¹ x) = x :=
  (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne').right_inv x

theorem aux_conv_represented_catalogue_holder_family_contDiff_dil (z z' : SpatialCoordinates d) (r : ℝ) :
    ContDiff ℝ ∞ (cubeDilation z z' r) := by
  refine contDiff_pi.2 fun i => ?_
  simp only [cubeDilation]
  exact contDiff_const.add (contDiff_const.mul ((contDiff_apply ℝ ℝ i).sub contDiff_const))

/-- **Countable smooth traces approximating Hölder boundary data (clause D8), one cube.** -/
theorem conv_represented_catalogue_holder_family (d : ℕ) (hd : 2 ≤ d) (beta alpha : ℝ)
    (hb : 1 / 2 < beta) (hba : beta < alpha) (ha1 : alpha < 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ (ι : Type) (_ : Countable ι) (theta : ι → SpatialCoordinates d → ℝ),
      (∀ i, ContDiff ℝ ∞ (theta i)) ∧
      ∀ b : SpatialCoordinates d → ℝ,
        IsHolderOn alpha (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b →
        IsCellBoundaryClass beta z r b →
        ∃ h : ℕ → ι,
          (∀ k : ℕ, IsCellBoundaryClass beta z r (theta (h k) - b)) ∧
          Tendsto (fun k : ℕ => cellBoundaryQuotientNorm beta z r (theta (h k) - b))
            atTop (𝓝 0) ∧
          TendstoUniformlyOn (fun k : ℕ => theta (h k)) b atTop
            (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  classical
  obtain ⟨Hs, hHs, hcore⟩ := aux_conv_represented_catalogue_holder_family_core hd beta alpha hb hba ha1
  let ι : Type := Σ m : ℕ, Σ n : ℕ, {h // h ∈ Hs m n} × ℚ
  let theta : ι → SpatialCoordinates d → ℝ := fun i x =>
    ((i.2.1 : ℝ) + 1) * i.2.2.1.1 (cubeDilation 0 z r⁻¹ x) + ((i.2.2.2 : ℚ) : ℝ)
  have hres : ∀ i : ι, rescaledDatum z r (theta i) =
      fun y => ((i.2.1 : ℝ) + 1) * i.2.2.1.1 y + ((i.2.2.2 : ℚ) : ℝ) := by
    intro i
    rw [aux_conv_represented_catalogue_holder_family_rescaled_eq]
    funext y
    simp only [theta, aux_conv_represented_catalogue_holder_family_dil_roundtrip z r hr]
  refine ⟨ι, inferInstance, theta, ?_, ?_⟩
  · intro i
    exact ((contDiff_const.mul ((hHs i.1 i.2.1 i.2.2.1.1 i.2.2.1.2).1.comp
      (aux_conv_represented_catalogue_holder_family_contDiff_dil 0 z r⁻¹)))).add contDiff_const
  intro b hbH hbC
  have hmem : ∀ y, y ∈ aux_conv_represented_catalogue_holder_family_Sfr d ↔
      cubeDilation z 0 r y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    fun y => aux_conv_represented_catalogue_holder_family_frontier_dil z r hr y
  set g := rescaledDatum z r b with hg
  have hgH : IsHolderOn alpha (aux_conv_represented_catalogue_holder_family_Sfr d) g := by
    rw [hg, aux_conv_represented_catalogue_holder_family_rescaled_eq]
    exact aux_hDet_isHolderOn_dilation z r hr alpha b _ _ hmem hbH
  have hgα : IsCellBoundaryClass alpha 0 1 g :=
    (FiniteStopping.IsCellBoundaryClass_rescale alpha z r b).1 ⟨hgH, hbC.2⟩
  have hgβ : IsCellBoundaryClass beta 0 1 g :=
    (FiniteStopping.IsCellBoundaryClass_rescale beta z r b).1 hbC
  obtain ⟨n, hn⟩ := hcore g hgα hgβ
  choose hh hhmem q hq using hn
  let idx : ℕ → ι := fun k => ⟨k, n, ⟨hh k, hhmem k⟩, q k⟩
  have hgβ' := (aux_conv_represented_catalogue_holder_family_class_unit beta g).1 hgβ
  -- the rescaled error functions
  let F : ℕ → SpatialCoordinates d → ℝ := fun k y =>
    (((n : ℝ) + 1) * hh k y + (q k : ℝ)) - g y
  have hFclass : ∀ k, IsCellBoundaryClass beta 0 1 (F k) := by
    intro k
    have hhβ := (aux_conv_represented_catalogue_holder_family_class_unit beta (hh k)).1 (hHs k n (hh k) (hhmem k)).2
    refine (aux_conv_represented_catalogue_holder_family_class_unit beta _).2 ⟨?_, ?_⟩
    · exact aux_conv_represented_catalogue_holder_family_isHolder_sub _ _ _ _
        (aux_conv_represented_catalogue_holder_family_isHolder_add_const _ _ _ _ (aux_conv_represented_catalogue_holder_family_isHolder_mul _ _ _ _ hhβ.1)) hgβ'.1
    · exact aux_conv_represented_catalogue_holder_family_bdd_sub _ _ _
        (aux_conv_represented_catalogue_holder_family_bdd_add_const _ _ _ (aux_conv_represented_catalogue_holder_family_bdd_mul _ _ _ hhβ.2)) hgβ'.2
  have hFres : ∀ k, rescaledDatum z r (theta (idx k) - b) = F k := by
    intro k
    funext y
    have := congrFun (hres (idx k)) y
    change rescaledDatum z r (theta (idx k)) y - rescaledDatum z r b y = F k y
    rw [this]
  have hFbound : ∀ k, cAlphaNorm beta (aux_conv_represented_catalogue_holder_family_Sfr d) (F k) < 3 * (1 / ((k : ℝ) + 1)) := by
    intro k
    have h1 := hq k
    have hneg : F k = fun y => -(g y - (((n : ℝ) + 1) * hh k y + (q k : ℝ))) := by
      funext y; simp only [F]; ring
    rw [hneg, aux_conv_represented_catalogue_holder_family_cAlpha_neg]
    exact h1
  refine ⟨idx, ?_, ?_, ?_⟩
  · intro k
    rw [FiniteStopping.IsCellBoundaryClass_rescale, hFres]
    exact hFclass k
  · have hsq : ∀ k, cellBoundaryQuotientNorm beta z r (theta (idx k) - b) ≤
        3 * (1 / ((k : ℝ) + 1)) := by
      intro k
      rw [FiniteStopping.cellBoundaryQuotientNorm_rescale, hFres, aux_conv_represented_catalogue_holder_family_cbqn_unit]
      exact (aux_conv_represented_catalogue_holder_family_quot_le_cAlpha _ _ _).trans (hFbound k).le
    refine squeeze_zero (fun k => ?_) hsq ?_
    · rw [FiniteStopping.cellBoundaryQuotientNorm_rescale, hFres, aux_conv_represented_catalogue_holder_family_cbqn_unit]
      exact aux_conv_represented_catalogue_holder_family_quot_nonneg _ _ _
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 3
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun k : ℕ => 3 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 3
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with k hk
    intro x hx
    set y := cubeDilation 0 z r⁻¹ x with hy
    have hxy : cubeDilation z 0 r y = x := aux_conv_represented_catalogue_holder_family_dil_roundtrip' z r hr x
    have hyS : y ∈ aux_conv_represented_catalogue_holder_family_Sfr d := (hmem y).2 (by rw [hxy]; exact hx)
    have hbd := (aux_conv_represented_catalogue_holder_family_class_unit beta (F k)).1 (hFclass k)
    have habs := aux_conv_represented_catalogue_holder_family_abs_le_cAlpha beta (aux_conv_represented_catalogue_holder_family_Sfr d) (F k) hbd.2 y hyS
    have hgy : g y = b x := by
      rw [hg, aux_conv_represented_catalogue_holder_family_rescaled_eq]
      show b (cubeDilation z 0 r y) = b x
      rw [hxy]
    have hval : F k y = theta (idx k) x - b x := by
      rw [← hgy]
    rw [Real.dist_eq, abs_sub_comm, ← hval]
    exact lt_of_le_of_lt habs (lt_of_lt_of_le (hFbound k) hk.le)

end Paper
