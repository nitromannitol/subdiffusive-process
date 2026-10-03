module

public import SubdiffusiveProcess.Paper.lem_interp_averaging
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open SubdiffusiveProcess
open scoped ENNReal

noncomputable section
namespace Paper



theorem lem_interp_scale_bound (d : ℕ) (hd : 1 ≤ d) (alpha beta : ℝ)
    (hb : 0 < beta) (hba : beta < alpha) (ha : alpha ≤ 1) :
    let Q0 := centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num)
    let S := closure (Q0 : Set (SpatialCoordinates d))
    ∃ C : ℝ, 0 < C ∧
      ∀ v : SpatialCoordinates d → ℝ, Lane4.IsHolderOn alpha S v →
        Lane4.IsHolderOn beta S v ∧
          ∀ h : ℝ, 0 < h → h ≤ 1 →
            let B := C * (Lane4.holderSeminorm alpha S v * h ^ (alpha - beta) +
              h ^ (-(d : ℝ) / 2 - beta) *
                (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal)
            Lane4.holderSeminorm beta S v ≤ B ∧
              Lane4.cAlphaNorm beta S v ≤ B := by
  dsimp only
  let Q0 :=
    centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num)
  let S : Set (SpatialCoordinates d) := closure (Q0 : Set (SpatialCoordinates d))
  change ∃ C : ℝ, 0 < C ∧
    ∀ v : SpatialCoordinates d → ℝ, Lane4.IsHolderOn alpha S v →
      Lane4.IsHolderOn beta S v ∧
        ∀ h : ℝ, 0 < h → h ≤ 1 →
          Lane4.holderSeminorm beta S v ≤
              C * (Lane4.holderSeminorm alpha S v * h ^ (alpha - beta) +
                h ^ (-(d : ℝ) / 2 - beta) *
                  (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal) ∧
            Lane4.cAlphaNorm beta S v ≤
              C * (Lane4.holderSeminorm alpha S v * h ^ (alpha - beta) +
                h ^ (-(d : ℝ) / 2 - beta) *
                  (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal)
  have ha0 : 0 < alpha := by linarith
  obtain ⟨C0, hC0, havg⟩ := lem_interp_averaging d hd alpha ha0 ha
  let C : ℝ := 3 * (C0 + 2)
  have hC : 0 < C := by
    dsimp [C]
    nlinarith
  have hC1 : 1 ≤ C := by
    dsimp [C]
    nlinarith
  have hC2 : 2 ≤ C := by
    dsimp [C]
    nlinarith
  have hC3 : 3 ≤ C := by
    dsimp [C]
    nlinarith
  have hC0le : C0 ≤ C := by
    dsimp [C]
    nlinarith
  have hC2C0 : 2 * C0 ≤ C := by
    dsimp [C]
    nlinarith
  have hC3C0 : 3 * C0 ≤ C := by
    dsimp [C]
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro v hv
  have hvBdd : BddAbove (Lane4.holderRatioSet alpha S v) := by
    simpa [Lane4.IsHolderOn] using hv
  have hK : 0 ≤ Lane4.holderSeminorm alpha S v := by
    unfold Lane4.holderSeminorm
    by_cases hne : (Lane4.holderRatioSet alpha S v).Nonempty
    · rcases hne with ⟨r, hr⟩
      have hr0 : 0 ≤ r := by
        rcases hr with ⟨x, hx, y, hy, hxy, rfl⟩
        exact div_nonneg (abs_nonneg _)
          (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      exact hr0.trans (le_csSup hvBdd hr)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simp
  have hL : 0 ≤
      (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal :=
    ENNReal.toReal_nonneg
  have hscale : ∀ h : ℝ, 0 < h → h ≤ 1 →
      Lane4.IsHolderOn beta S v ∧
        Lane4.holderSeminorm beta S v ≤
            C * (Lane4.holderSeminorm alpha S v * h ^ (alpha - beta) +
              h ^ (-(d : ℝ) / 2 - beta) *
                (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal) ∧
          Lane4.cAlphaNorm beta S v ≤
            C * (Lane4.holderSeminorm alpha S v * h ^ (alpha - beta) +
              h ^ (-(d : ℝ) / 2 - beta) *
                (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal) := by
    intro h hh hh1
    let A : ℝ := Lane4.holderSeminorm alpha S v * h ^ (alpha - beta)
    let D : ℝ := h ^ (-(d : ℝ) / 2 - beta) *
      (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal
    let T : ℝ := 2 * C0 * D + 2 * A
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg hK (Real.rpow_nonneg (le_of_lt hh) _)
    have hD : 0 ≤ D := by
      dsimp [D]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hh) _) hL
    have hC0D : 0 ≤ C0 * D := mul_nonneg hC0.le hD
    have hpowA : h ^ alpha ≤ h ^ (alpha - beta) := by
      apply Real.rpow_le_rpow_of_exponent_ge hh hh1
      linarith
    have hpowD : h ^ (-(d : ℝ) / 2) ≤ h ^ (-(d : ℝ) / 2 - beta) := by
      apply Real.rpow_le_rpow_of_exponent_ge hh hh1
      linarith
    have hpoint : ∀ x ∈ S,
        |v x| ≤ C0 * h ^ (-(d : ℝ) / 2) *
            (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
          Lane4.holderSeminorm alpha S v * h ^ alpha := by
      intro x hx
      exact (havg v hv).2 h hh hh1 x hx
    have hpoint' : ∀ x ∈ S, |v x| ≤ C0 * D + A := by
      intro x hx
      have hx0 := hpoint x hx
      calc
        |v x| ≤ C0 * h ^ (-(d : ℝ) / 2) *
              (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
            Lane4.holderSeminorm alpha S v * h ^ alpha := hx0
        _ ≤ C0 * h ^ (-(d : ℝ) / 2 - beta) *
              (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
            Lane4.holderSeminorm alpha S v * h ^ (alpha - beta) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpowD hC0.le) hL)
            (mul_le_mul_of_nonneg_left hpowA hK)
        _ = C0 * D + A := by
          simp [A, D, mul_assoc]
    have hdist_pos : ∀ x y : SpatialCoordinates d, x ≠ y →
        0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      intro x y hxy
      obtain ⟨j, hj⟩ : ∃ j : Fin d, x j ≠ y j := by
        by_contra h
        push_neg at h
        exact hxy (funext h)
      have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
        exact Finset.sum_pos' (fun i _ => sq_nonneg (x i - y i))
          ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
      exact Real.sqrt_pos.2 hsum
    have hratio : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
        |v x - v y| /
            (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta ≤ T := by
      intro x hx y hy hxy
      let δ : ℝ := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)
      have hδ : 0 < δ := by
        dsimp [δ]
        exact hdist_pos x y hxy
      have hα := aux_lem_interp_averaging_holder_bound ha0 hv x hx y hy
      by_cases hnear : δ ≤ h
      · have hnear' : |v x - v y| / δ ^ beta ≤ A := by
          calc
            |v x - v y| / δ ^ beta ≤
                Lane4.holderSeminorm alpha S v * δ ^ alpha / δ ^ beta := by
              exact div_le_div_of_nonneg_right hα
                (Real.rpow_nonneg hδ.le _)
            _ = Lane4.holderSeminorm alpha S v * δ ^ (alpha - beta) := by
              rw [mul_div_assoc, ← Real.rpow_sub hδ]
            _ ≤ A := by
              dsimp [A]
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow hδ.le hnear (sub_pos.mpr hba).le) hK
        have hAT : A ≤ T := by
          dsimp [T]
          nlinarith
        simpa [δ] using hnear'.trans hAT
      · have hfar : h < δ := lt_of_not_ge hnear
        have hβδ : 0 < δ ^ beta := Real.rpow_pos_of_pos hδ beta
        have hβh : h ^ beta ≤ δ ^ beta :=
          Real.rpow_le_rpow (le_of_lt hh) (le_of_lt hfar) hb.le
        have hnum : |v x - v y| ≤
            2 * (C0 * h ^ (-(d : ℝ) / 2) *
              (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
              Lane4.holderSeminorm alpha S v * h ^ alpha) := by
          calc
            |v x - v y| ≤ |v x| + |v y| := by
              have heq : v x - v y = v x + (-v y) := by ring
              rw [heq]
              simpa [abs_neg] using abs_add_le (v x) (-v y)
            _ ≤ (C0 * h ^ (-(d : ℝ) / 2) *
                  (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
                Lane4.holderSeminorm alpha S v * h ^ alpha) +
                (C0 * h ^ (-(d : ℝ) / 2) *
                  (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
                Lane4.holderSeminorm alpha S v * h ^ alpha) :=
              add_le_add (hpoint x hx) (hpoint y hy)
            _ = _ := by ring
        have hdiv : |v x - v y| / δ ^ beta ≤
            (2 * (C0 * h ^ (-(d : ℝ) / 2) *
              (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
              Lane4.holderSeminorm alpha S v * h ^ alpha)) / h ^ beta := by
          calc
            |v x - v y| / δ ^ beta ≤
                (2 * (C0 * h ^ (-(d : ℝ) / 2) *
                  (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
                  Lane4.holderSeminorm alpha S v * h ^ alpha)) / δ ^ beta :=
              div_le_div_of_nonneg_right hnum hβδ.le
            _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
              (Real.rpow_pos_of_pos hh beta) hβh
        have hdiv' : |v x - v y| / δ ^ beta ≤ T := by
          have heq :
              (2 * (C0 * h ^ (-(d : ℝ) / 2) *
                (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
                Lane4.holderSeminorm alpha S v * h ^ alpha)) / h ^ beta = T := by
            dsimp [T, D, A]
            calc
              (2 * (C0 * h ^ (-(d : ℝ) / 2) *
                (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
                Lane4.holderSeminorm alpha S v * h ^ alpha)) / h ^ beta =
                  2 * C0 * (h ^ (-(d : ℝ) / 2) / h ^ beta) *
                    (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
                    2 * Lane4.holderSeminorm alpha S v *
                      (h ^ alpha / h ^ beta) := by ring
              _ = 2 * C0 * h ^ (-(d : ℝ) / 2 - beta) *
                    (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
                    2 * Lane4.holderSeminorm alpha S v * h ^ (alpha - beta) := by
                rw [← Real.rpow_sub hh, ← Real.rpow_sub hh]
              _ = 2 * C0 * (h ^ (-(d : ℝ) / 2 - beta) *
                    (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal) +
                    2 * (Lane4.holderSeminorm alpha S v * h ^ (alpha - beta)) := by ring
          exact hdiv.trans_eq heq
        exact hdiv'
    have hT : T ≤ C * (A + D) := by
      calc
        T = 2 * C0 * D + 2 * A := by rfl
        _ ≤ C * D + C * A := add_le_add
          (mul_le_mul_of_nonneg_right hC2C0 hD)
          (mul_le_mul_of_nonneg_right hC2 hA)
        _ = C * (A + D) := by ring
    have hsemiT : Lane4.holderSeminorm beta S v ≤ T := by
      unfold Lane4.holderSeminorm
      have hTnonneg : 0 ≤ T := by
        dsimp [T]
        nlinarith
      refine Real.sSup_le ?_ hTnonneg
      intro r hr
      rcases hr with ⟨x, hx, y, hy, hxy, rfl⟩
      exact hratio x hx y hy hxy
    have hsemiB : Lane4.holderSeminorm beta S v ≤ C * (A + D) :=
      hsemiT.trans hT
    have hmem : Lane4.IsHolderOn beta S v := by
      exact ⟨T, fun r hr => by
        rcases hr with ⟨x, hx, y, hy, hxy, rfl⟩
        exact hratio x hx y hy hxy⟩
    have habs0 : sSup {r : ℝ | ∃ x ∈ S, r = |v x|} ≤ C0 * D + A := by
      have hsupnonneg : 0 ≤ C0 * D + A := by
        exact add_nonneg (mul_nonneg hC0.le hD) hA
      refine Real.sSup_le ?_ hsupnonneg
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      exact hpoint' x hx
    have hca : Lane4.cAlphaNorm beta S v ≤ C * (A + D) := by
      unfold Lane4.cAlphaNorm
      calc
        sSup {r : ℝ | ∃ x ∈ S, r = |v x|} +
            Lane4.holderSeminorm beta S v ≤ (C0 * D + A) + T :=
          add_le_add habs0 hsemiT
        _ ≤ 3 * C0 * D + 3 * A := by
          dsimp [T]
          ring_nf
          rfl
        _ ≤ C * D + C * A := add_le_add
          (mul_le_mul_of_nonneg_right hC3C0 hD)
          (mul_le_mul_of_nonneg_right hC3 hA)
        _ = C * (A + D) := by ring
    refine ⟨hmem, ?_, ?_⟩
    · simpa [A, D] using hsemiB
    · simpa [A, D] using hca
  have hmem := (hscale 1 one_pos (by norm_num)).1
  refine ⟨hmem, ?_⟩
  intro h hh hh1
  exact (hscale h hh hh1).2

end Paper
