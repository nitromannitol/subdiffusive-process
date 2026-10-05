module

public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess

namespace SubdiffusiveProcess.Paper



theorem lem_finite_trace_response_continuity
    (d : ℕ) (_hd : 2 ≤ d)
    (beta : ℝ) (_hbeta : 1 / 2 < beta) (_hbeta_one : beta < 1)
    (A : ℝ) (hA : 0 ≤ A)
    (R : Seminorm ℝ (SpatialCoordinates d → ℝ))
    (hR : ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
      (R g) ^ 2 ≤ A * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2) :
    ∀ g h : SpatialCoordinates d → ℝ,
      IsCellBoundaryClass beta 0 1 g → IsCellBoundaryClass beta 0 1 h →
        |(R g) ^ 2 - (R h) ^ 2| ≤
          A * cellBoundaryQuotientNorm beta 0 1 (fun x => g x - h x) *
            (cellBoundaryQuotientNorm beta 0 1 g +
              cellBoundaryQuotientNorm beta 0 1 h) := by
  intro g h hg hh
  have hca : ∀ (F : SpatialCoordinates d → ℝ) (c : ℝ),
      0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)))
        (fun x => F x - c) := by
    intro F c
    unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
    apply add_nonneg
    · apply Real.sSup_nonneg
      intro w hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact abs_nonneg _
    · apply Real.sSup_nonneg
      intro w hw
      unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet at hw
      obtain ⟨x, hx, y, hy, hxy, rfl⟩ := hw
      exact div_nonneg (abs_nonneg _)
        (Real.rpow_nonneg (Real.sqrt_nonneg _) beta)
  have quotient_nonneg : ∀ (F : SpatialCoordinates d → ℝ),
      0 ≤ cellBoundaryQuotientNorm beta 0 1 F := by
    intro F
    unfold cellBoundaryQuotientNorm quotientCBetaNorm
    apply le_csInf
    · exact ⟨_, ⟨0, rfl⟩⟩
    · intro v hv
      obtain ⟨c, rfl⟩ := hv
      exact hca (rescaledDatum 0 1 F) c
  have holder_sub : ∀ (S : Set (SpatialCoordinates d))
      (G1 G2 : SpatialCoordinates d → ℝ),
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S G1 → _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S G2 →
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S (G1 - G2) := by
    intro S G1 G2 h1 h2
    unfold _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn at h1 h2 ⊢
    obtain ⟨b1, hb1⟩ := h1
    obtain ⟨b2, hb2⟩ := h2
    refine ⟨b1 + b2, fun v hv => ?_⟩
    unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet at hv
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := hv
    have hD : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta := by
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra hcon
        push Not at hcon
        exact hxy (funext hcon)
      have hle : (x i - y i) ^ 2 ≤ ∑ j : Fin d, (x j - y j) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j - y j))
          (Finset.mem_univ i)
      have hpos : 0 < (x i - y i) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hi)
      have hsum_pos : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by linarith
      exact Real.rpow_pos_of_pos (Real.sqrt_pos_of_pos hsum_pos) beta
    have hnum : |(G1 - G2) x - (G1 - G2) y| ≤
        |G1 x - G1 y| + |G2 x - G2 y| := by
      have hkey : (G1 - G2) x - (G1 - G2) y =
          (G1 x - G1 y) - (G2 x - G2 y) := by
        simp only [Pi.sub_apply]
        ring
      rw [hkey]
      exact (abs_add_le (G1 x - G1 y) (-(G2 x - G2 y))).trans_eq
        (by rw [abs_neg])
    have e1 : |G1 x - G1 y| /
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta ≤ b1 :=
      hb1 ⟨x, hx, y, hy, hxy, rfl⟩
    have e2 : |G2 x - G2 y| /
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta ≤ b2 :=
      hb2 ⟨x, hx, y, hy, hxy, rfl⟩
    calc
      |(G1 - G2) x - (G1 - G2) y| /
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta
          ≤ (|G1 x - G1 y| + |G2 x - G2 y|) /
              (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta := by
            exact div_le_div_of_nonneg_right hnum (le_of_lt hD)
      _ = |G1 x - G1 y| /
            (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta +
          |G2 x - G2 y| /
            (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta := by
              rw [add_div]
      _ ≤ b1 + b2 := add_le_add e1 e2
  have absBdd_sub : ∀ (S : Set (SpatialCoordinates d))
      (G1 G2 : SpatialCoordinates d → ℝ),
      BddAbove {v | ∃ x ∈ S, v = |G1 x|} →
      BddAbove {v | ∃ x ∈ S, v = |G2 x|} →
        BddAbove {v | ∃ x ∈ S, v = |G1 x - G2 x|} := by
    intro S G1 G2 h1 h2
    obtain ⟨b1, hb1⟩ := h1
    obtain ⟨b2, hb2⟩ := h2
    refine ⟨b1 + b2, fun v hv => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hv
    have e1 : |G1 x| ≤ b1 := hb1 ⟨x, hx, rfl⟩
    have e2 : |G2 x| ≤ b2 := hb2 ⟨x, hx, rfl⟩
    calc
      |G1 x - G2 x| ≤ |G1 x| + |G2 x| := by
        exact (abs_add_le (G1 x) (-(G2 x))).trans_eq
          (by rw [abs_neg])
      _ ≤ b1 + b2 := add_le_add e1 e2
  have hres_sub : rescaledDatum (0 : SpatialCoordinates d) 1 (g - h) =
      rescaledDatum (0 : SpatialCoordinates d) 1 g -
        rescaledDatum (0 : SpatialCoordinates d) 1 h := by
    funext y
    simp only [rescaledDatum, Pi.sub_apply]
  have hgh_class : IsCellBoundaryClass beta 0 1 (g - h) := by
    obtain ⟨hgH, hgB⟩ := hg
    obtain ⟨hhH, hhB⟩ := hh
    refine ⟨?_, ?_⟩
    · have h := holder_sub
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)))
        (rescaledDatum 0 1 g) (rescaledDatum 0 1 h) hgH hhH
      simpa only [hres_sub] using! h
    · have h := absBdd_sub
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d)))
        (rescaledDatum 0 1 g) (rescaledDatum 0 1 h) hgB hhB
      simpa only [hres_sub] using! h
  have hNg0 : 0 ≤ cellBoundaryQuotientNorm beta 0 1 g := quotient_nonneg g
  have hNh0 : 0 ≤ cellBoundaryQuotientNorm beta 0 1 h := quotient_nonneg h
  have hNd0 : 0 ≤ cellBoundaryQuotientNorm beta 0 1 (g - h) :=
    quotient_nonneg (g - h)
  have hRg := hR g hg
  have hRh := hR h hh
  have hRd := hR (g - h) hgh_class
  have hRg_le : R g ≤ Real.sqrt A * cellBoundaryQuotientNorm beta 0 1 g := by
    have h := Real.sqrt_le_sqrt hRg
    rw [Real.sqrt_sq (apply_nonneg R g), Real.sqrt_mul hA,
      Real.sqrt_sq hNg0] at h
    exact h
  have hRh_le : R h ≤ Real.sqrt A * cellBoundaryQuotientNorm beta 0 1 h := by
    have hsqrt := Real.sqrt_le_sqrt hRh
    rw [Real.sqrt_sq (apply_nonneg R h), Real.sqrt_mul hA,
      Real.sqrt_sq hNh0] at hsqrt
    exact hsqrt
  have hRd_le : R (g - h) ≤
      Real.sqrt A * cellBoundaryQuotientNorm beta 0 1 (g - h) := by
    have hsqrt := Real.sqrt_le_sqrt hRd
    rw [Real.sqrt_sq (apply_nonneg R (g - h)), Real.sqrt_mul hA,
      Real.sqrt_sq hNd0] at hsqrt
    exact hsqrt
  have htri : |R g - R h| ≤ R (g - h) := by
    rw [abs_sub_le_iff]
    constructor
    · have h1 := map_add_le_add R (g - h) h
      have e : (g - h) + h = g := by abel
      rw [e] at h1
      linarith
    · have h1 := map_add_le_add R g (h - g)
      have e : g + (h - g) = h := by abel
      rw [e] at h1
      have e2 : h - g = -(g - h) := by abel
      rw [e2, map_neg_eq_map R] at h1
      linarith
  have hsum_le : R g + R h ≤ Real.sqrt A *
      (cellBoundaryQuotientNorm beta 0 1 g +
        cellBoundaryQuotientNorm beta 0 1 h) := by
    calc
      R g + R h ≤ Real.sqrt A * cellBoundaryQuotientNorm beta 0 1 g +
          Real.sqrt A * cellBoundaryQuotientNorm beta 0 1 h :=
            add_le_add hRg_le hRh_le
      _ = Real.sqrt A * (cellBoundaryQuotientNorm beta 0 1 g +
          cellBoundaryQuotientNorm beta 0 1 h) := by ring
  have hfinal : R (g - h) * (R g + R h) ≤
      A * cellBoundaryQuotientNorm beta 0 1 (g - h) *
        (cellBoundaryQuotientNorm beta 0 1 g +
          cellBoundaryQuotientNorm beta 0 1 h) := by
    have hc1 : 0 ≤ Real.sqrt A * cellBoundaryQuotientNorm beta 0 1 (g - h) :=
      mul_nonneg (Real.sqrt_nonneg A) hNd0
    calc
      R (g - h) * (R g + R h) ≤
          (Real.sqrt A * cellBoundaryQuotientNorm beta 0 1 (g - h)) *
            (Real.sqrt A * (cellBoundaryQuotientNorm beta 0 1 g +
              cellBoundaryQuotientNorm beta 0 1 h)) :=
        mul_le_mul hRd_le hsum_le
          (add_nonneg (apply_nonneg R g) (apply_nonneg R h)) hc1
      _ = A * cellBoundaryQuotientNorm beta 0 1 (g - h) *
          (cellBoundaryQuotientNorm beta 0 1 g +
            cellBoundaryQuotientNorm beta 0 1 h) := by
        have hs := Real.sq_sqrt hA
        calc
          (Real.sqrt A * cellBoundaryQuotientNorm beta 0 1 (g - h)) *
              (Real.sqrt A * (cellBoundaryQuotientNorm beta 0 1 g +
                cellBoundaryQuotientNorm beta 0 1 h)) =
              (Real.sqrt A) ^ 2 *
                (cellBoundaryQuotientNorm beta 0 1 (g - h) *
                  (cellBoundaryQuotientNorm beta 0 1 g +
                    cellBoundaryQuotientNorm beta 0 1 h)) := by ring
          _ = A * cellBoundaryQuotientNorm beta 0 1 (g - h) *
                (cellBoundaryQuotientNorm beta 0 1 g +
                cellBoundaryQuotientNorm beta 0 1 h) := by
            rw [hs]
            ring
  have key : |(R g) ^ 2 - (R h) ^ 2| ≤ R (g - h) * (R g + R h) := by
    have hsum_nonneg : 0 ≤ R g + R h :=
      add_nonneg (apply_nonneg R g) (apply_nonneg R h)
    have hsq : |(R g) ^ 2 - (R h) ^ 2| = |R g - R h| * (R g + R h) := by
      rw [show (R g) ^ 2 - (R h) ^ 2 = (R g - R h) * (R g + R h) by ring]
      rw [abs_mul, abs_of_nonneg hsum_nonneg]
    rw [hsq]
    exact mul_le_mul_of_nonneg_right htri hsum_nonneg
  exact key.trans hfinal

end SubdiffusiveProcess.Paper
