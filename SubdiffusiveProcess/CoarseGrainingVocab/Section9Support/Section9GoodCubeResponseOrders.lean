import SubdiffusiveProcess.CoarseGrainingVocab.HomogenizationErrorDefault
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
import Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.GeometricOne
set_option autoImplicit false
open Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

private lemma rpow_three_neg_le_one {x : ℝ} (hx : 0 ≤ x) : ((3 : ℝ) ^ (-x)) ≤ 1 := by
  rw [← Real.rpow_zero (3:ℝ)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) (by linarith)

private lemma disc_val (s q : ℝ) :
    Ch02.geometricDiscount s q = 1 - ((3 : ℝ) ^ (-(s * q))) := by
  unfold Ch02.geometricDiscount
  congr 2
  ring

private lemma disc_pos {s q : ℝ} (hsq : 0 < s * q) :
    0 < Ch02.geometricDiscount s q := by
  rw [disc_val]
  have hneg : -(s * q) < 0 := by linarith
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg)

private lemma disc_nonneg {s q : ℝ} (hsq : 0 ≤ s * q) :
    0 ≤ Ch02.geometricDiscount s q := by
  rw [disc_val]
  have h1 := rpow_three_neg_le_one (x := s * q) hsq
  have h2 : 0 ≤ ((3 : ℝ) ^ (-(s * q))) := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _
  linarith

private lemma disc_le_one (s q : ℝ) : Ch02.geometricDiscount s q ≤ 1 := by
  rw [disc_val]
  have h2 : 0 ≤ ((3 : ℝ) ^ (-(s * q))) := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _
  linarith

private lemma tsum_sq_le {f : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ l, f l ≤ c) (hsum : ∑' l : ℕ, f l = c) :
    ∑' l : ℕ, f l ^ (2:ℝ) ≤ c ^ (2:ℝ) := by
  have h1 : ∀ l : ℕ, f l ^ (2:ℝ) ≤ f l * c := by
    intro l
    rw [ENNReal.rpow_two, pow_two]
    exact mul_le_mul_right (h l) _
  calc ∑' l : ℕ, f l ^ (2:ℝ) ≤ ∑' l : ℕ, f l * c := ENNReal.tsum_le_tsum h1
    _ = (∑' l : ℕ, f l) * c := ENNReal.tsum_mul_right
    _ = c * c := by rw [hsum]
    _ = c ^ (2:ℝ) := (pow_two c).symm.trans (ENNReal.rpow_two c).symm

private lemma aux_one {d : ℕ} (Q : TriadicCube d) (n : ℤ) (p : Ch02.MultiscaleExponent)
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) (s : ℝ) (hs : 0 ≤ s) :
    paperHomogenizationErrorFinite Q n s p 1 a alpha
      = ENNReal.ofReal (Ch02.geometricDiscount s 1) *
          ∑' l : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s * (l:ℝ))))) *
            paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha := by
  unfold paperHomogenizationErrorFinite
  rw [show ((1:ℝ) / 1) = 1 from by norm_num]
  simp only [ENNReal.rpow_one]
  have hD : 0 ≤ Ch02.geometricDiscount s 1 :=
    disc_nonneg (mul_nonneg hs (by norm_num : (0:ℝ) ≤ 1))
  have hterm : ∀ l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 1 l) *
      paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha
      = ENNReal.ofReal (Ch02.geometricDiscount s 1) *
        (ENNReal.ofReal (((3 : ℝ) ^ (-(s * (l:ℝ))))) *
          paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha) := by
    intro l
    have hw1 : Ch02.geometricWeight s 1 l
        = Ch02.geometricDiscount s 1 * (3 : ℝ) ^ ((-s) * 1 * (l : ℝ)) := rfl
    have hw : 0 ≤ ((3 : ℝ) ^ (-(s * (l:ℝ)))) := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _
    have hexp : ((3 : ℝ) ^ ((-s) * 1 * (l:ℝ))) = ((3 : ℝ) ^ (-(s * (l:ℝ)))) := by
      rw [show (-s) * 1 * (l:ℝ) = -(s * (l:ℝ)) from by ring]
    rw [hw1, hexp, ENNReal.ofReal_mul hD, mul_assoc]
  have hsum_eq : ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 1 l) *
      paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha
      = ENNReal.ofReal (Ch02.geometricDiscount s 1) *
        ∑' l : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s * (l:ℝ))))) *
          paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha := by
    rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  exact hsum_eq

private lemma aux_two {d : ℕ} (Q : TriadicCube d) (n : ℤ) (p : Ch02.MultiscaleExponent)
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) {s0 : ℝ} (hs0 : 0 < s0) :
    paperHomogenizationErrorFinite Q n s0 p 2 a alpha
      ≤ ∑' l : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
          paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha := by
  unfold paperHomogenizationErrorFinite
  set T : ℝ≥0∞ := ∑' l : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
    paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha with hTdef
  have hD2pos : 0 < Ch02.geometricDiscount s0 2 :=
    disc_pos (mul_pos hs0 (by norm_num : (0:ℝ) < 2))
  have hD2le : 0 ≤ Ch02.geometricDiscount s0 2 := le_of_lt hD2pos
  have hterm : ∀ l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s0 2 l) *
      (paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha) ^ (2:ℝ)
      = ENNReal.ofReal (Ch02.geometricDiscount s0 2) *
        ((ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
          paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha) ^ (2:ℝ)) := by
    intro l
    have hw1 : Ch02.geometricWeight s0 2 l
        = Ch02.geometricDiscount s0 2 * (3 : ℝ) ^ ((-s0) * 2 * (l : ℝ)) := rfl
    have hw : 0 ≤ ((3 : ℝ) ^ (-(s0 * (l:ℝ)))) := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _
    have hw2 : 0 ≤ (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) ^ (2:ℝ) := by positivity
    have hexp : ((3 : ℝ) ^ ((-s0) * 2 * (l:ℝ)))
        = (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) ^ (2:ℝ) := by
      rw [show (-s0) * 2 * (l:ℝ) = -(s0 * (l:ℝ)) * 2 from by ring,
        Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    have hof : ENNReal.ofReal ((((3 : ℝ) ^ (-(s0 * (l:ℝ))))) ^ (2:ℝ))
        = (ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ)))))) ^ (2:ℝ) := by
      have e1 : (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) ^ (2:ℝ)
          = ((3 : ℝ) ^ (-(s0 * (l:ℝ)))) * ((3 : ℝ) ^ (-(s0 * (l:ℝ)))) := by
        rw [Real.rpow_two, pow_two]
      have e2 : (ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ)))))) ^ (2:ℝ)
          = ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
            ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) := by
        rw [ENNReal.rpow_two, pow_two]
      rw [e1, ENNReal.ofReal_mul hw, e2]
    rw [hw1, hexp, ENNReal.ofReal_mul hD2le, hof, mul_assoc,
      ← ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))))
        (paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha) (by norm_num : (0:ℝ) ≤ 2)]
  simp only [hterm]
  have hb : ∀ l : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
      paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha ≤ T := by
    intro l
    rw [hTdef]
    first
      | exact ENNReal.le_tsum _ l
      | exact ENNReal.le_tsum l
  have hsum : ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricDiscount s0 2) *
      ((ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
        paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha) ^ (2:ℝ))
      ≤ T ^ (2:ℝ) := by
    calc ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricDiscount s0 2) *
          ((ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
            paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha) ^ (2:ℝ))
        = ENNReal.ofReal (Ch02.geometricDiscount s0 2) *
            ∑' l : ℕ, (ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
              paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha) ^ (2:ℝ) :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (Ch02.geometricDiscount s0 2) * T ^ (2:ℝ) :=
          mul_le_mul_right (tsum_sq_le hb hTdef.symm) _
      _ ≤ ENNReal.ofReal (1:ℝ) * T ^ (2:ℝ) :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (disc_le_one s0 2)) _
      _ = T ^ (2:ℝ) := by rw [ENNReal.ofReal_one, one_mul]
  have hTsq : (T ^ (2:ℝ)) ^ ((1:ℝ) / 2) = T := by
    rw [← ENNReal.rpow_mul, show (2:ℝ) * ((1:ℝ) / 2) = 1 from by norm_num, ENNReal.rpow_one]
  rw [← hTsq]
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ) < (1:ℝ) / 2)).mpr hsum

/-- A positive first-order scale sum controls both stronger decay and the square scale sum. -/
theorem goodCube_response_orders_le_one
    {d : ℕ} (Q : TriadicCube d) (n : ℤ) (a : Ch02.TriadicCoeffFamily d)
    (alpha : ℝ) (p : Ch02.MultiscaleExponent)
    {s0 s : ℝ} (hs0 : 0 < s0) (horder : s0 ≤ s) :
    paperHomogenizationError Q n s p (.finite 1) a alpha ≤
        ENNReal.ofReal ((Ch02.geometricDiscount s0 1)⁻¹) *
          paperHomogenizationError Q n s0 p (.finite 1) a alpha ∧
      paperHomogenizationError Q n s0 p (.finite 2) a alpha ≤
        ENNReal.ofReal ((Ch02.geometricDiscount s0 1)⁻¹) *
          paperHomogenizationError Q n s0 p (.finite 1) a alpha := by
  show paperHomogenizationErrorFinite Q n s p 1 a alpha ≤
      ENNReal.ofReal ((Ch02.geometricDiscount s0 1)⁻¹) *
        paperHomogenizationErrorFinite Q n s0 p 1 a alpha ∧
    paperHomogenizationErrorFinite Q n s0 p 2 a alpha ≤
      ENNReal.ofReal ((Ch02.geometricDiscount s0 1)⁻¹) *
        paperHomogenizationErrorFinite Q n s0 p 1 a alpha
  rw [aux_one Q n p a alpha s (hs0.le.trans horder), aux_one Q n p a alpha s0 hs0.le]
  have hD0 : 0 < Ch02.geometricDiscount s0 1 :=
    disc_pos (mul_pos hs0 (by norm_num : (0:ℝ) < 1))
  have hscale : ENNReal.ofReal ((Ch02.geometricDiscount s0 1)⁻¹) *
      ENNReal.ofReal (Ch02.geometricDiscount s0 1) = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hD0.le),
      inv_mul_cancel₀ (ne_of_gt hD0), ENNReal.ofReal_one]
  have hRHS : ENNReal.ofReal ((Ch02.geometricDiscount s0 1)⁻¹) *
      (ENNReal.ofReal (Ch02.geometricDiscount s0 1) *
        ∑' l : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
          paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha)
      = ∑' l : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
          paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha := by
    rw [← mul_assoc, hscale, one_mul]
  refine ⟨?_, ?_⟩
  · calc ENNReal.ofReal (Ch02.geometricDiscount s 1) *
        ∑' l : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s * (l:ℝ))))) *
          paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha
      ≤ ENNReal.ofReal (Ch02.geometricDiscount s 1) *
          ∑' l : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
            paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha :=
          mul_le_mul_right (ENNReal.tsum_le_tsum (fun (l : ℕ) => mul_le_mul_left
            (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1:ℝ) ≤ 3)
              (by
                have hle : s0 * (l:ℝ) ≤ s * (l:ℝ) :=
                  mul_le_mul_of_nonneg_right horder (Nat.cast_nonneg l)
                linarith)))
            (paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha))) _
    _ ≤ ENNReal.ofReal (1:ℝ) *
          (∑' l : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
            paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha) :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (disc_le_one s 1)) _
    _ = ∑' l : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
          paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha := by
      rw [ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal ((Ch02.geometricDiscount s0 1)⁻¹) *
          (ENNReal.ofReal (Ch02.geometricDiscount s0 1) *
            ∑' l : ℕ, ENNReal.ofReal (((3 : ℝ) ^ (-(s0 * (l:ℝ))))) *
              paperScaleResponseAtScale Q (n - (l:ℤ)) p a alpha) := hRHS.symm
  · rw [hRHS]
    exact aux_two Q n p a alpha hs0

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
