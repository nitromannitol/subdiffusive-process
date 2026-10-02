import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Paper.lem_finite_trace_holder_precompact
import SubdiffusiveProcess.Paper.lem_finite_trace_smooth_density

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess
open scoped ContDiff

namespace Paper



lemma aux_lem_finite_trace_smooth_net_holderRatioSet_nonneg_mem
    {d : ℕ} {beta : ℝ} {S : Set (SpatialCoordinates d)}
    {F : SpatialCoordinates d → ℝ} {v : ℝ}
    (hv : v ∈ SubdiffusiveProcess.Lane4.holderRatioSet beta S F) : 0 ≤ v := by
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := hv
  exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) beta)

lemma aux_lem_finite_trace_smooth_net_holderRatioSet_congr_absdiff
    {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    {f g : SpatialCoordinates d → ℝ}
    (h : ∀ x y, |f x - f y| = |g x - g y|) :
    SubdiffusiveProcess.Lane4.holderRatioSet beta S f =
      SubdiffusiveProcess.Lane4.holderRatioSet beta S g := by
  ext v
  simp only [SubdiffusiveProcess.Lane4.holderRatioSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hv⟩
    exact ⟨x, hx, y, hy, hxy, by rw [hv, h x y]⟩
  · rintro ⟨x, hx, y, hy, hxy, hv⟩
    exact ⟨x, hx, y, hy, hxy, by rw [hv, ← h x y]⟩

lemma aux_lem_finite_trace_smooth_net_holderRatioSet_sub_const
    {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (F : SpatialCoordinates d → ℝ) (c : ℝ) :
    SubdiffusiveProcess.Lane4.holderRatioSet beta S (fun x => F x - c) =
      SubdiffusiveProcess.Lane4.holderRatioSet beta S F :=
  aux_lem_finite_trace_smooth_net_holderRatioSet_congr_absdiff beta S (fun x y => by
    congr 1
    change F x - c - (F y - c) = F x - F y
    ring)

lemma aux_lem_finite_trace_smooth_net_holderRatioSet_neg
    {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (F : SpatialCoordinates d → ℝ) :
    SubdiffusiveProcess.Lane4.holderRatioSet beta S (fun x => -F x) =
      SubdiffusiveProcess.Lane4.holderRatioSet beta S F :=
  aux_lem_finite_trace_smooth_net_holderRatioSet_congr_absdiff beta S (fun x y => by
    rw [show -F x - -F y = -(F x - F y) by ring, abs_neg])

lemma aux_lem_finite_trace_smooth_net_absSet_neg
    {d : ℕ} {S : Set (SpatialCoordinates d)} {F : SpatialCoordinates d → ℝ} :
    {v : ℝ | ∃ x ∈ S, v = |(fun x => -F x) x|} =
      {v : ℝ | ∃ x ∈ S, v = |F x|} := by
  ext v
  constructor
  · rintro ⟨x, hx, hv⟩
    exact ⟨x, hx, by rw [hv]; change |-F x| = |F x|; rw [abs_neg]⟩
  · rintro ⟨x, hx, hv⟩
    exact ⟨x, hx, by rw [hv]; change |F x| = |-F x|; rw [abs_neg]⟩

lemma aux_lem_finite_trace_smooth_net_absBddAbove_neg
    {d : ℕ} {S : Set (SpatialCoordinates d)} {F : SpatialCoordinates d → ℝ}
    (hb : BddAbove {v : ℝ | ∃ x ∈ S, v = |F x|}) :
    BddAbove {v : ℝ | ∃ x ∈ S, v = |(fun x => -F x) x|} := by
  rwa [aux_lem_finite_trace_smooth_net_absSet_neg]

lemma aux_lem_finite_trace_smooth_net_absBddAbove_sub_const
    {d : ℕ} {S : Set (SpatialCoordinates d)}
    {F : SpatialCoordinates d → ℝ} (c : ℝ)
    (hb : BddAbove {v : ℝ | ∃ x ∈ S, v = |F x|}) :
    BddAbove {v : ℝ | ∃ x ∈ S, v = |F x - c|} := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨M + |c|, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  have step : |F x - c| ≤ |F x| + |c| := by
    rw [sub_eq_add_neg]
    calc
      |F x + -c| ≤ |F x| + |-c| := abs_add_le (F x) (-c)
      _ = |F x| + |c| := by rw [abs_neg]
  calc
    |F x - c| ≤ M + |c| :=
      le_trans step (add_le_add (hM ⟨x, hx, rfl⟩) (le_refl _))

lemma aux_lem_finite_trace_smooth_net_cAlphaNorm_add_le
    {d : ℕ} {beta : ℝ} {S : Set (SpatialCoordinates d)}
    {F G : SpatialCoordinates d → ℝ}
    (hFa : BddAbove {v : ℝ | ∃ x ∈ S, v = |F x|})
    (hFr : BddAbove (SubdiffusiveProcess.Lane4.holderRatioSet beta S F))
    (hGa : BddAbove {v : ℝ | ∃ x ∈ S, v = |G x|})
    (hGr : BddAbove (SubdiffusiveProcess.Lane4.holderRatioSet beta S G)) :
    SubdiffusiveProcess.Lane4.cAlphaNorm beta S (fun x => F x + G x) ≤
      SubdiffusiveProcess.Lane4.cAlphaNorm beta S F +
        SubdiffusiveProcess.Lane4.cAlphaNorm beta S G := by
  have hD : ∀ x y : SpatialCoordinates d,
      0 ≤ (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta :=
    fun x y => Real.rpow_nonneg (Real.sqrt_nonneg _) beta
  have h1 : sSup {v : ℝ | ∃ x ∈ S, v = |F x + G x|} ≤
      sSup {v : ℝ | ∃ x ∈ S, v = |F x|} +
        sSup {v : ℝ | ∃ x ∈ S, v = |G x|} := by
    apply Real.sSup_le
    · rintro v ⟨x, hx, rfl⟩
      exact le_trans (abs_add_le (F x) (G x))
        (add_le_add (le_csSup hFa ⟨x, hx, rfl⟩)
          (le_csSup hGa ⟨x, hx, rfl⟩))
    · exact add_nonneg
        (Real.sSup_nonneg (fun v hv => by
          obtain ⟨x, hx, rfl⟩ := hv
          exact abs_nonneg _))
        (Real.sSup_nonneg (fun v hv => by
          obtain ⟨x, hx, rfl⟩ := hv
          exact abs_nonneg _))
  have h2 : sSup (SubdiffusiveProcess.Lane4.holderRatioSet beta S
      (fun x => F x + G x)) ≤
      sSup (SubdiffusiveProcess.Lane4.holderRatioSet beta S F) +
        sSup (SubdiffusiveProcess.Lane4.holderRatioSet beta S G) := by
    apply Real.sSup_le
    · rintro v ⟨x, hx, y, hy, hxy, rfl⟩
      calc
        |F x + G x - (F y + G y)| /
              (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta
            = |(F x - F y) + (G x - G y)| /
                (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta := by
                rw [show F x + G x - (F y + G y) =
                    (F x - F y) + (G x - G y) by ring]
        _ ≤ (|F x - F y| + |G x - G y|) /
              (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta :=
          div_le_div_of_nonneg_right (abs_add_le (F x - F y) (G x - G y))
            (hD x y)
        _ = |F x - F y| /
              (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta +
            |G x - G y| /
              (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta := by ring
        _ ≤ sSup (SubdiffusiveProcess.Lane4.holderRatioSet beta S F) +
              sSup (SubdiffusiveProcess.Lane4.holderRatioSet beta S G) :=
          add_le_add
            (le_csSup hFr ⟨x, hx, y, hy, hxy, rfl⟩)
            (le_csSup hGr ⟨x, hx, y, hy, hxy, rfl⟩)
    · exact add_nonneg
        (Real.sSup_nonneg (fun v hv =>
          aux_lem_finite_trace_smooth_net_holderRatioSet_nonneg_mem hv))
        (Real.sSup_nonneg (fun v hv =>
          aux_lem_finite_trace_smooth_net_holderRatioSet_nonneg_mem hv))
  have h3 : SubdiffusiveProcess.Lane4.cAlphaNorm beta S (fun x => F x + G x) =
      sSup {v : ℝ | ∃ x ∈ S, v = |F x + G x|} +
        sSup (SubdiffusiveProcess.Lane4.holderRatioSet beta S
          (fun x => F x + G x)) := rfl
  have h4 : SubdiffusiveProcess.Lane4.cAlphaNorm beta S F =
      sSup {v : ℝ | ∃ x ∈ S, v = |F x|} +
        sSup (SubdiffusiveProcess.Lane4.holderRatioSet beta S F) := rfl
  have h5 : SubdiffusiveProcess.Lane4.cAlphaNorm beta S G =
      sSup {v : ℝ | ∃ x ∈ S, v = |G x|} +
        sSup (SubdiffusiveProcess.Lane4.holderRatioSet beta S G) := rfl
  rw [h3, h4, h5]
  linarith

lemma aux_lem_finite_trace_smooth_net_cAlphaNorm_neg
    {d : ℕ} {beta : ℝ} {S : Set (SpatialCoordinates d)}
    {F : SpatialCoordinates d → ℝ} :
    SubdiffusiveProcess.Lane4.cAlphaNorm beta S (fun x => -F x) =
      SubdiffusiveProcess.Lane4.cAlphaNorm beta S F := by
  have h3 : SubdiffusiveProcess.Lane4.cAlphaNorm beta S (fun x => -F x) =
      sSup {v : ℝ | ∃ x ∈ S, v = |(fun x => -F x) x|} +
        sSup (SubdiffusiveProcess.Lane4.holderRatioSet beta S (fun x => -F x)) := rfl
  have h4 : SubdiffusiveProcess.Lane4.cAlphaNorm beta S F =
      sSup {v : ℝ | ∃ x ∈ S, v = |F x|} +
        sSup (SubdiffusiveProcess.Lane4.holderRatioSet beta S F) := rfl
  rw [h3, h4, aux_lem_finite_trace_smooth_net_holderRatioSet_neg,
    aux_lem_finite_trace_smooth_net_absSet_neg]

lemma aux_lem_finite_trace_smooth_net_quotientCBetaNorm_add_le
    {d : ℕ} {beta : ℝ} {S : Set (SpatialCoordinates d)}
    {F G : SpatialCoordinates d → ℝ}
    (hFh : BddAbove (SubdiffusiveProcess.Lane4.holderRatioSet beta S F))
    (hFa : BddAbove {v : ℝ | ∃ x ∈ S, v = |F x|})
    (hGh : BddAbove (SubdiffusiveProcess.Lane4.holderRatioSet beta S G))
    (hGa : BddAbove {v : ℝ | ∃ x ∈ S, v = |G x|}) :
    SubdiffusiveProcess.quotientCBetaNorm beta S (fun x => F x + G x) ≤
      SubdiffusiveProcess.quotientCBetaNorm beta S F +
        SubdiffusiveProcess.quotientCBetaNorm beta S G := by
  have hAFne :
      ({v : ℝ | ∃ c, v = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
        (fun x => F x - c)} : Set ℝ).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hAGne :
      ({v : ℝ | ∃ c, v = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
        (fun x => G x - c)} : Set ℝ).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hBdd : BddBelow
      ({u : ℝ | ∃ c, u = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
        (fun x => F x + G x - c)} : Set ℝ) := by
    refine ⟨0, ?_⟩
    rintro v ⟨c, rfl⟩
    unfold SubdiffusiveProcess.Lane4.cAlphaNorm
      SubdiffusiveProcess.Lane4.holderSeminorm
    apply add_nonneg
    · exact Real.sSup_nonneg (fun v hv => by
        obtain ⟨x, hx, rfl⟩ := hv
        exact abs_nonneg _)
    · exact Real.sSup_nonneg (fun v hv =>
        aux_lem_finite_trace_smooth_net_holderRatioSet_nonneg_mem hv)
  have key : ∀ v ∈ {v : ℝ | ∃ c, v = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
        (fun x => F x - c)},
      ∀ w ∈ {w : ℝ | ∃ c, w = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
        (fun x => G x - c)},
      sInf {u : ℝ | ∃ c, u = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
        (fun x => F x + G x - c)} ≤ v + w := by
    rintro v ⟨c1, rfl⟩ w ⟨c2, rfl⟩
    have hmem : SubdiffusiveProcess.Lane4.cAlphaNorm beta S
        (fun x => F x + G x - (c1 + c2)) ∈
        {u : ℝ | ∃ c, u = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
          (fun x => F x + G x - c)} := ⟨c1 + c2, rfl⟩
    refine le_trans (csInf_le hBdd hmem) ?_
    have hend : (fun x => F x + G x - (c1 + c2)) =
        (fun x => (F x - c1) + (G x - c2)) := by
      funext x
      ring
    rw [hend]
    refine aux_lem_finite_trace_smooth_net_cAlphaNorm_add_le ?_ ?_ ?_ ?_
    · exact aux_lem_finite_trace_smooth_net_absBddAbove_sub_const c1 hFa
    · rw [aux_lem_finite_trace_smooth_net_holderRatioSet_sub_const]
      exact hFh
    · exact aux_lem_finite_trace_smooth_net_absBddAbove_sub_const c2 hGa
    · rw [aux_lem_finite_trace_smooth_net_holderRatioSet_sub_const]
      exact hGh
  have hfin :
      sInf {u : ℝ | ∃ c, u = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
        (fun x => F x + G x - c)} ≤
      sInf {v : ℝ | ∃ c, v = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
        (fun x => F x - c)} +
        sInf {v : ℝ | ∃ c, v = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
        (fun x => G x - c)} := by
    have step1 : ∀ w ∈ {w : ℝ | ∃ c, w = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
        (fun x => G x - c)},
        sInf {u : ℝ | ∃ c, u = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
          (fun x => F x + G x - c)} - w ≤
          sInf {v : ℝ | ∃ c, v = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
            (fun x => F x - c)} := by
      intro w hw
      refine le_csInf hAFne ?_
      intro v hv
      linarith [key v hv w hw]
    have step2 :
        sInf {u : ℝ | ∃ c, u = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
          (fun x => F x + G x - c)} -
          sInf {v : ℝ | ∃ c, v = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
            (fun x => F x - c)} ≤
        sInf {v : ℝ | ∃ c, v = SubdiffusiveProcess.Lane4.cAlphaNorm beta S
          (fun x => G x - c)} := by
      refine le_csInf hAGne ?_
      intro w hw
      linarith [step1 w hw]
    linarith
  unfold SubdiffusiveProcess.quotientCBetaNorm
  exact hfin

lemma aux_lem_finite_trace_smooth_net_quotientCBetaNorm_neg
    {d : ℕ} {beta : ℝ} {S : Set (SpatialCoordinates d)}
    {F : SpatialCoordinates d → ℝ} :
    SubdiffusiveProcess.quotientCBetaNorm beta S (fun x => -F x) =
      SubdiffusiveProcess.quotientCBetaNorm beta S F := by
  unfold SubdiffusiveProcess.quotientCBetaNorm
  congr 1
  ext v
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨-c, ?_⟩
    rw [show (fun x => -F x - c) = (fun x => -(F x + c)) by
      funext x; ring]
    rw [aux_lem_finite_trace_smooth_net_cAlphaNorm_neg]
    rw [show (fun x => F x + c) = (fun x => F x - (-c)) by
      funext x; ring]
  · rintro ⟨c, rfl⟩
    refine ⟨-c, ?_⟩
    rw [show (fun x => F x - c) = (fun x => -(-F x + c)) by
      funext x; ring]
    rw [aux_lem_finite_trace_smooth_net_cAlphaNorm_neg]
    rw [show (fun x => -F x + c) = (fun x => -F x - (-c)) by
      funext x; ring]

lemma aux_lem_finite_trace_smooth_net_IsCellBoundaryClass_neg
    {d : ℕ} (beta : ℝ) (z : SpatialCoordinates d) (r : ℝ)
    {f : SpatialCoordinates d → ℝ}
    (hf : SubdiffusiveProcess.IsCellBoundaryClass beta z r f) :
    SubdiffusiveProcess.IsCellBoundaryClass beta z r (fun x => -f x) := by
  obtain ⟨hh, ha⟩ := hf
  have hres : SubdiffusiveProcess.rescaledDatum z r (fun x => -f x) =
      (fun x => -(SubdiffusiveProcess.rescaledDatum z r f) x) := by
    funext y
    simp only [SubdiffusiveProcess.rescaledDatum]
  refine ⟨?_, ?_⟩
  · rw [hres]
    change BddAbove (SubdiffusiveProcess.Lane4.holderRatioSet beta _
      (fun x => -(SubdiffusiveProcess.rescaledDatum z r f) x))
    rw [aux_lem_finite_trace_smooth_net_holderRatioSet_neg]
    exact hh
  · rw [hres]
    exact aux_lem_finite_trace_smooth_net_absBddAbove_neg ha

lemma aux_lem_finite_trace_smooth_net_cellBoundaryQuotientNorm_add_le
    {d : ℕ} (beta : ℝ) (z : SpatialCoordinates d) (r : ℝ)
    {f g : SpatialCoordinates d → ℝ}
    (hf : SubdiffusiveProcess.IsCellBoundaryClass beta z r f)
    (hg : SubdiffusiveProcess.IsCellBoundaryClass beta z r g) :
    SubdiffusiveProcess.cellBoundaryQuotientNorm beta z r (fun x => f x + g x) ≤
      SubdiffusiveProcess.cellBoundaryQuotientNorm beta z r f +
        SubdiffusiveProcess.cellBoundaryQuotientNorm beta z r g := by
  obtain ⟨hfh, hfa⟩ := hf
  obtain ⟨hgh, hga⟩ := hg
  have key : SubdiffusiveProcess.rescaledDatum z r (fun x => f x + g x) =
      (fun y => SubdiffusiveProcess.rescaledDatum z r f y +
        SubdiffusiveProcess.rescaledDatum z r g y) := by
    funext y
    simp only [SubdiffusiveProcess.rescaledDatum]
  unfold SubdiffusiveProcess.cellBoundaryQuotientNorm
  rw [key]
  exact aux_lem_finite_trace_smooth_net_quotientCBetaNorm_add_le hfh hfa hgh hga

lemma aux_lem_finite_trace_smooth_net_cellBoundaryQuotientNorm_neg
    {d : ℕ} (beta : ℝ) (z : SpatialCoordinates d) (r : ℝ)
    {f : SpatialCoordinates d → ℝ} :
    SubdiffusiveProcess.cellBoundaryQuotientNorm beta z r (fun x => -f x) =
      SubdiffusiveProcess.cellBoundaryQuotientNorm beta z r f := by
  have key : SubdiffusiveProcess.rescaledDatum z r (fun x => -f x) =
      (fun x => -(SubdiffusiveProcess.rescaledDatum z r f) x) := by
    funext y
    simp only [SubdiffusiveProcess.rescaledDatum]
  unfold SubdiffusiveProcess.cellBoundaryQuotientNorm
  rw [key, aux_lem_finite_trace_smooth_net_quotientCBetaNorm_neg]

theorem lem_finite_trace_smooth_net
    (d : ℕ) (hd : 2 ≤ d)
    (beta alpha : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧
      (∀ g : SpatialCoordinates d → ℝ,
        IsCellBoundaryClass alpha 0 1 g → cellBoundaryQuotientNorm alpha 0 1 g ≤ 1 →
          IsCellBoundaryClass beta 0 1 g ∧ cellBoundaryQuotientNorm beta 0 1 g ≤ C) ∧
      (∀ epsilon : ℝ, 0 < epsilon →
        ∃ Hs : Finset (SpatialCoordinates d → ℝ),
          (∀ h ∈ Hs, ContDiff ℝ ∞ h ∧ IsCellBoundaryClass beta 0 1 h ∧
            cellBoundaryQuotientNorm beta 0 1 h ≤ C) ∧
          (∀ g : SpatialCoordinates d → ℝ,
            IsCellBoundaryClass alpha 0 1 g → cellBoundaryQuotientNorm alpha 0 1 g ≤ 1 →
              ∃ h ∈ Hs,
              cellBoundaryQuotientNorm beta 0 1 (fun x => g x - h x) ≤ epsilon)) := by
  obtain ⟨C0, hC0, hBnd, hNet⟩ :=
    lem_finite_trace_holder_precompact d hd beta alpha hbeta hba halpha
  have hBnd' : ∀ g : SpatialCoordinates d → ℝ,
      IsCellBoundaryClass alpha 0 1 g → cellBoundaryQuotientNorm alpha 0 1 g ≤ 1 →
        IsCellBoundaryClass beta 0 1 g ∧ cellBoundaryQuotientNorm beta 0 1 g ≤ C0 + 1 := by
    intro g hg hunit
    obtain ⟨hclass, hnorm⟩ := hBnd g hg hunit
    exact ⟨hclass, by linarith⟩
  classical
  refine ⟨C0 + 1, by linarith, hBnd', ?_⟩
  intro epsilon hepsilon
  let delta : ℝ := min (epsilon / 2) 1
  have hdelta_le_half : delta ≤ epsilon / 2 := by
    rw [show delta = min (epsilon / 2) 1 by rfl]
    exact min_le_left _ _
  have hdelta_le_one : delta ≤ 1 := by
    rw [show delta = min (epsilon / 2) 1 by rfl]
    exact min_le_right _ _
  have hdelta_pos : 0 < delta := by
    rw [show delta = min (epsilon / 2) 1 by rfl]
    exact lt_min (by linarith) one_pos
  obtain ⟨Gs, hGs_bdd, hGs_cover⟩ := hNet delta hdelta_pos
  have key : ∀ c ∈ Gs, ∃ φ : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ φ ∧ IsCellBoundaryClass beta 0 1 φ ∧
      IsCellBoundaryClass beta 0 1 (fun x => c x - φ x) ∧
      cellBoundaryQuotientNorm beta 0 1 (fun x => c x - φ x) ≤ delta :=
    fun c hc => lem_finite_trace_smooth_density d hd beta alpha hbeta hba halpha c
      (hGs_bdd c hc).1 (hGs_bdd c hc).2 delta hdelta_pos
  let φ : {c // c ∈ Gs} → (SpatialCoordinates d → ℝ) :=
    fun x => Classical.choose (key x.1 x.2)
  have hφspec : ∀ x : {c // c ∈ Gs},
      ContDiff ℝ ∞ (φ x) ∧ IsCellBoundaryClass beta 0 1 (φ x) ∧
      IsCellBoundaryClass beta 0 1 (fun y => x.1 y - φ x y) ∧
      cellBoundaryQuotientNorm beta 0 1 (fun y => x.1 y - φ x y) ≤ delta :=
    fun x => Classical.choose_spec (key x.1 x.2)
  refine ⟨Gs.attach.image φ, ?_, ?_⟩
  · intro h hh
    rw [Finset.mem_image] at hh
    obtain ⟨x, hx, rfl⟩ := hh
    obtain ⟨hsmooth, hclass, hdiffclass, hdiffnorm⟩ := hφspec x
    obtain ⟨hxclass, hxnorm⟩ := hBnd x.1 (hGs_bdd x.1 x.2).1 (hGs_bdd x.1 x.2).2
    refine ⟨hsmooth, hclass, ?_⟩
    have hneg : IsCellBoundaryClass beta 0 1 (fun y => -(x.1 y - φ x y)) :=
      aux_lem_finite_trace_smooth_net_IsCellBoundaryClass_neg beta 0 1 hdiffclass
    have htri := aux_lem_finite_trace_smooth_net_cellBoundaryQuotientNorm_add_le
      beta 0 1 hxclass hneg
    have hφeq : φ x = (fun y => x.1 y + -(x.1 y - φ x y)) := by
      funext y
      ring
    rw [hφeq]
    calc
      cellBoundaryQuotientNorm beta 0 1
          (fun y => x.1 y + -(x.1 y - φ x y)) ≤
          cellBoundaryQuotientNorm beta 0 1 x.1 +
            cellBoundaryQuotientNorm beta 0 1
              (fun y => -(x.1 y - φ x y)) := htri
      _ = cellBoundaryQuotientNorm beta 0 1 x.1 +
            cellBoundaryQuotientNorm beta 0 1
              (fun y => x.1 y - φ x y) := by
            rw [aux_lem_finite_trace_smooth_net_cellBoundaryQuotientNorm_neg]
      _ ≤ C0 + delta := add_le_add hxnorm hdiffnorm
      _ ≤ C0 + 1 := by linarith
  · intro g hg hunit
    obtain ⟨c, hc, hgcclass, hgcnorm⟩ := hGs_cover g hg hunit
    obtain ⟨hsmooth, hclass, hdiffclass, hdiffnorm⟩ := hφspec ⟨c, hc⟩
    refine ⟨φ ⟨c, hc⟩, ?_, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨⟨c, hc⟩, Finset.mem_attach Gs ⟨c, hc⟩, rfl⟩
    · have htri := aux_lem_finite_trace_smooth_net_cellBoundaryQuotientNorm_add_le
        beta 0 1 hgcclass hdiffclass
      have heq : (fun y => g y - φ ⟨c, hc⟩ y) =
          (fun y => (g y - c y) + (c y - φ ⟨c, hc⟩ y)) := by
        funext y
        ring
      rw [heq]
      calc
        cellBoundaryQuotientNorm beta 0 1
            (fun y => (g y - c y) + (c y - φ ⟨c, hc⟩ y)) ≤
            cellBoundaryQuotientNorm beta 0 1 (fun y => g y - c y) +
              cellBoundaryQuotientNorm beta 0 1
                (fun y => c y - φ ⟨c, hc⟩ y) := htri
        _ ≤ delta + delta := add_le_add hgcnorm hdiffnorm
        _ ≤ epsilon := by linarith

end Paper
