module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/-- Existing finite averaging step, at one fixed horizon.
Carried inputs and suppliers:
- hbad is the integrated all-chain budget from cor_integrate.
- hpadding is averaged jointly over shifts and levels, as supplied by lem_shifts.
- hparent and hcover are the parent/child counting and covering premises of
  this conditional finite-measure substep; their verification remains in lem_mass.
- hcollar is the omitted collar budget; prop_growth supplies the boundary-null
  property that permits collars of arbitrarily small mass in lem_mass.
The selected levels and their actual cardinality are explicit. No all-horizon
lower-density assertion or convergence of the deficit is assumed. Cofinal
favourable horizons remain part of the principal lem_mass conclusion.
 for the scope of this existing lemma. -/
theorem lem_mass_average
    (X : Type) [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    (Q : Set X) (_hQmeas : MeasurableSet Q)
    (Shift : Type) [Fintype Shift] [Nonempty Shift]
    (J : ℕ) (hJ : 0 < J)
    (levels : Finset ℕ)
    (hlevels : levels ⊆ Finset.Icc 1 J)
    (deficit : ℝ)
    (hdeficit : (J : ℝ) / 2 - deficit ≤ (levels.card : ℝ))
    (Good Bad ParentLoss PaddingLoss CollarLoss : ℕ → Shift → Set X)
    (_hGood : ∀ n : ℕ, ∀ σ : Shift, MeasurableSet (Good n σ))
    (_hBad : ∀ n : ℕ, ∀ σ : Shift, MeasurableSet (Bad n σ))
    (_hParentLoss : ∀ n : ℕ, ∀ σ : Shift, MeasurableSet (ParentLoss n σ))
    (_hPaddingLoss : ∀ n : ℕ, ∀ σ : Shift, MeasurableSet (PaddingLoss n σ))
    (_hCollarLoss : ∀ n : ℕ, ∀ σ : Shift, MeasurableSet (CollarLoss n σ))
    (hcover : ∀ n ∈ levels, ∀ σ : Shift,
      Q ⊆ Good n σ ∪ Bad n σ ∪ ParentLoss n σ ∪ PaddingLoss n σ ∪ CollarLoss n σ)
    (theta parentRate paddingRate collarRate Bbar : ℝ)
    (_htheta : 0 ≤ theta)
    (hparentRate : 0 ≤ parentRate)
    (hpaddingRate : 0 ≤ paddingRate)
    (hcollarRate : 0 ≤ collarRate)
    (_hBbar : 0 ≤ Bbar)
    (hbad : ∀ σ : Shift,
      ∑ n ∈ levels, (mu (Bad n σ)).toReal ≤
        (theta * (J : ℝ) + Bbar) * (mu Q).toReal)
    (hparent : ∀ σ : Shift,
      ∑ n ∈ levels, (mu (ParentLoss n σ)).toReal ≤
        (levels.card : ℝ) * parentRate * (mu Q).toReal)
    (hpadding :
      ∑ σ : Shift, ∑ n ∈ levels, (mu (PaddingLoss n σ)).toReal ≤
        (Fintype.card Shift : ℝ) * (levels.card : ℝ) * paddingRate * (mu Q).toReal)
    (hcollar : ∀ σ : Shift,
      ∑ n ∈ levels, (mu (CollarLoss n σ)).toReal ≤
        (levels.card : ℝ) * collarRate * (mu Q).toReal) :
    (1 / 2 - theta - parentRate - paddingRate - collarRate
        - Bbar / (J : ℝ) - deficit / (J : ℝ)) * (mu Q).toReal ≤
      (∑ σ : Shift, ∑ n ∈ levels, (mu (Good n σ)).toReal) /
        ((J : ℝ) * (Fintype.card Shift : ℝ)) := by
  have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hSpos : (0 : ℝ) < (Fintype.card Shift : ℝ) := by
    have h : 0 < Fintype.card Shift := Fintype.card_pos
    exact_mod_cast h
  have hq : 0 ≤ (mu Q).toReal := ENNReal.toReal_nonneg
  have hLle : (levels.card : ℝ) ≤ (J : ℝ) := by
    have hcard_le : levels.card ≤ (Finset.Icc 1 J).card := Finset.card_le_card hlevels
    have hIcc : (Finset.Icc 1 J).card = J := by
      have hset : Finset.Icc 1 J = (Finset.range (J + 1)).erase 0 := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]; omega
      rw [hset, Finset.card_erase_of_mem (by simp), Finset.card_range]
      omega
    have h : levels.card ≤ J := hIcc ▸ hcard_le
    exact_mod_cast h
  have hu2 : ∀ A B : Set X, (mu (A ∪ B)).toReal ≤ (mu A).toReal + (mu B).toReal := by
    intro A B
    have hfin : mu A + mu B ≠ ⊤ := by
      rw [ENNReal.add_ne_top]
      exact ⟨measure_ne_top mu A, measure_ne_top mu B⟩
    rw [← ENNReal.toReal_add (measure_ne_top mu A) (measure_ne_top mu B)]
    exact ENNReal.toReal_mono hfin (measure_union_le A B)
  have hu5 : ∀ A B C D E : Set X,
      (mu (A ∪ B ∪ C ∪ D ∪ E)).toReal ≤
        (mu A).toReal + (mu B).toReal + (mu C).toReal + (mu D).toReal + (mu E).toReal := by
    intro A B C D E
    have h1 := hu2 (A ∪ B ∪ C ∪ D) E
    have h2 := hu2 (A ∪ B ∪ C) D
    have h3 := hu2 (A ∪ B) C
    have h4 := hu2 A B
    linarith
  have hQle : ∀ n ∈ levels, ∀ σ : Shift,
      (mu Q).toReal ≤ (mu (Good n σ)).toReal + (mu (Bad n σ)).toReal + (mu (ParentLoss n σ)).toReal + (mu (PaddingLoss n σ)).toReal + (mu (CollarLoss n σ)).toReal := by
    intro n hn σ
    have h1 : (mu Q).toReal ≤
        (mu (Good n σ ∪ Bad n σ ∪ ParentLoss n σ ∪ PaddingLoss n σ ∪ CollarLoss n σ)).toReal :=
      ENNReal.toReal_mono (measure_ne_top mu _) (measure_mono (hcover n hn σ))
    have h2 := hu5 (Good n σ) (Bad n σ) (ParentLoss n σ) (PaddingLoss n σ) (CollarLoss n σ)
    linarith
  have hA : (Fintype.card Shift : ℝ) * (levels.card : ℝ) * (mu Q).toReal ≤
      (∑ σ : Shift, ∑ n ∈ levels, (mu (Good n σ)).toReal) +
      (∑ σ : Shift, ∑ n ∈ levels, (mu (Bad n σ)).toReal) +
      (∑ σ : Shift, ∑ n ∈ levels, (mu (ParentLoss n σ)).toReal) +
      (∑ σ : Shift, ∑ n ∈ levels, (mu (PaddingLoss n σ)).toReal) +
      (∑ σ : Shift, ∑ n ∈ levels, (mu (CollarLoss n σ)).toReal) := by
    have h1 : (∑ σ : Shift, ∑ n ∈ levels, (mu Q).toReal) ≤
        ∑ σ : Shift, ∑ n ∈ levels,
          ((mu (Good n σ)).toReal + (mu (Bad n σ)).toReal + (mu (ParentLoss n σ)).toReal + (mu (PaddingLoss n σ)).toReal + (mu (CollarLoss n σ)).toReal) :=
      Finset.sum_le_sum (fun σ _ => Finset.sum_le_sum (fun n hn => hQle n hn σ))
    have hL : (∑ σ : Shift, ∑ n ∈ levels, (mu Q).toReal) =
        (Fintype.card Shift : ℝ) * (levels.card : ℝ) * (mu Q).toReal := by
      have hin : (∑ n ∈ levels, (mu Q).toReal) = (levels.card : ℝ) * (mu Q).toReal := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    have hR : (∑ σ : Shift, ∑ n ∈ levels,
          ((mu (Good n σ)).toReal + (mu (Bad n σ)).toReal + (mu (ParentLoss n σ)).toReal + (mu (PaddingLoss n σ)).toReal + (mu (CollarLoss n σ)).toReal)) =
        (∑ σ : Shift, ∑ n ∈ levels, (mu (Good n σ)).toReal) +
        (∑ σ : Shift, ∑ n ∈ levels, (mu (Bad n σ)).toReal) +
        (∑ σ : Shift, ∑ n ∈ levels, (mu (ParentLoss n σ)).toReal) +
        (∑ σ : Shift, ∑ n ∈ levels, (mu (PaddingLoss n σ)).toReal) +
        (∑ σ : Shift, ∑ n ∈ levels, (mu (CollarLoss n σ)).toReal) := by
      simp only [Finset.sum_add_distrib, add_assoc]
    rw [hL, hR] at h1
    exact h1
  have hB : (∑ σ : Shift, ∑ n ∈ levels, (mu (Bad n σ)).toReal) ≤
      (Fintype.card Shift : ℝ) * (theta * (J : ℝ) + Bbar) * (mu Q).toReal := by
    have h1 : (∑ σ : Shift, ∑ n ∈ levels, (mu (Bad n σ)).toReal) ≤
        ∑ σ : Shift, (theta * (J : ℝ) + Bbar) * (mu Q).toReal :=
      Finset.sum_le_sum (fun σ _ => hbad σ)
    have h2 : (∑ σ : Shift, (theta * (J : ℝ) + Bbar) * (mu Q).toReal)
        = (Fintype.card Shift : ℝ) * (theta * (J : ℝ) + Bbar) * (mu Q).toReal := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    linarith [h1, h2]
  have hPr : (∑ σ : Shift, ∑ n ∈ levels, (mu (ParentLoss n σ)).toReal) ≤
      (Fintype.card Shift : ℝ) * (levels.card : ℝ) * parentRate * (mu Q).toReal := by
    have h1 : (∑ σ : Shift, ∑ n ∈ levels, (mu (ParentLoss n σ)).toReal) ≤
        ∑ σ : Shift, (levels.card : ℝ) * parentRate * (mu Q).toReal :=
      Finset.sum_le_sum (fun σ _ => hparent σ)
    have h2 : (∑ σ : Shift, (levels.card : ℝ) * parentRate * (mu Q).toReal)
        = (Fintype.card Shift : ℝ) * (levels.card : ℝ) * parentRate * (mu Q).toReal := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    linarith [h1, h2]
  have hPd : (∑ σ : Shift, ∑ n ∈ levels, (mu (PaddingLoss n σ)).toReal) ≤
      (Fintype.card Shift : ℝ) * (levels.card : ℝ) * paddingRate * (mu Q).toReal := hpadding
  have hCl : (∑ σ : Shift, ∑ n ∈ levels, (mu (CollarLoss n σ)).toReal) ≤
      (Fintype.card Shift : ℝ) * (levels.card : ℝ) * collarRate * (mu Q).toReal := by
    have h1 : (∑ σ : Shift, ∑ n ∈ levels, (mu (CollarLoss n σ)).toReal) ≤
        ∑ σ : Shift, (levels.card : ℝ) * collarRate * (mu Q).toReal :=
      Finset.sum_le_sum (fun σ _ => hcollar σ)
    have h2 : (∑ σ : Shift, (levels.card : ℝ) * collarRate * (mu Q).toReal)
        = (Fintype.card Shift : ℝ) * (levels.card : ℝ) * collarRate * (mu Q).toReal := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    linarith [h1, h2]
  have hG : (Fintype.card Shift : ℝ) * (mu Q).toReal *
      ((levels.card : ℝ) - theta * (J : ℝ) - Bbar - (levels.card : ℝ) * (parentRate + paddingRate + collarRate)) ≤
      ∑ σ : Shift, ∑ n ∈ levels, (mu (Good n σ)).toReal := by
    nlinarith [hA, hB, hPr, hPd, hCl]
  have hkey2 : (J : ℝ) / 2 - deficit - (parentRate + paddingRate + collarRate) * (J : ℝ) ≤
      (levels.card : ℝ) - (levels.card : ℝ) * (parentRate + paddingRate + collarRate) := by
    have hpr : 0 ≤ parentRate + paddingRate + collarRate := by linarith
    have hJc : 0 ≤ (J : ℝ) - (levels.card : ℝ) := by linarith
    have hprod : 0 ≤ (parentRate + paddingRate + collarRate) * ((J : ℝ) - (levels.card : ℝ)) :=
      mul_nonneg hpr hJc
    have hc : 0 ≤ (levels.card : ℝ) - ((J : ℝ) / 2 - deficit) := by linarith
    linarith [hprod, hc]
  have hmul : (Fintype.card Shift : ℝ) * (mu Q).toReal *
      ((J : ℝ) / 2 - deficit - (parentRate + paddingRate + collarRate) * (J : ℝ)) ≤
      (Fintype.card Shift : ℝ) * (mu Q).toReal *
        ((levels.card : ℝ) - (levels.card : ℝ) * (parentRate + paddingRate + collarRate)) :=
    mul_le_mul_of_nonneg_left hkey2 (mul_nonneg (le_of_lt hSpos) hq)
  have hmain : (Fintype.card Shift : ℝ) * (mu Q).toReal *
      ((J : ℝ) / 2 - theta * (J : ℝ) - (parentRate + paddingRate + collarRate) * (J : ℝ) - Bbar - deficit) ≤
      ∑ σ : Shift, ∑ n ∈ levels, (mu (Good n σ)).toReal := by
    linarith [hG, hmul]
  have key : (1 / 2 - theta - parentRate - paddingRate - collarRate - Bbar / (J : ℝ) - deficit / (J : ℝ)) * (mu Q).toReal * ((J : ℝ) * (Fintype.card Shift : ℝ))
      = (Fintype.card Shift : ℝ) * (mu Q).toReal *
        ((J : ℝ) / 2 - theta * (J : ℝ) - (parentRate + paddingRate + collarRate) * (J : ℝ) - Bbar - deficit) := by
    field_simp
    ring
  have hposX : 0 < (J : ℝ) * (Fintype.card Shift : ℝ) := mul_pos hJpos hSpos
  have hmain2 : (1 / 2 - theta - parentRate - paddingRate - collarRate - Bbar / (J : ℝ) - deficit / (J : ℝ)) * (mu Q).toReal * ((J : ℝ) * (Fintype.card Shift : ℝ)) ≤
      ∑ σ : Shift, ∑ n ∈ levels, (mu (Good n σ)).toReal := by
    rw [key]
    exact hmain
  have hsimp : (1 / 2 - theta - parentRate - paddingRate - collarRate - Bbar / (J : ℝ) - deficit / (J : ℝ)) * (mu Q).toReal * ((J : ℝ) * (Fintype.card Shift : ℝ)) * ((J : ℝ) * (Fintype.card Shift : ℝ))⁻¹
      = (1 / 2 - theta - parentRate - paddingRate - collarRate - Bbar / (J : ℝ) - deficit / (J : ℝ)) * (mu Q).toReal := by
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hposX), mul_one]
  have hmul2 := mul_le_mul_of_nonneg_right hmain2 (inv_nonneg.mpr (le_of_lt hposX))
  have hdiv : (∑ σ : Shift, ∑ n ∈ levels, (mu (Good n σ)).toReal) / ((J : ℝ) * (Fintype.card Shift : ℝ))
      = (∑ σ : Shift, ∑ n ∈ levels, (mu (Good n σ)).toReal) * ((J : ℝ) * (Fintype.card Shift : ℝ))⁻¹ :=
    div_eq_mul_inv _ _
  rw [hdiv, ← hsimp]
  exact hmul2


end SubdiffusiveProcess.Paper
