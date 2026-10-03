module

public import SubdiffusiveProcess.Paper.cor_neumann_source

@[expose] public section

/-! The root coarse ellipticity at exponent two controls the cellwise inverse ellipticity.
This deterministic identity supplies no probabilistic bound by itself. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- The second-moment inverse ellipticity is its literal weighted descendant series. -/
theorem aux_lem_as_regularity_cell_coercivity_series {d : ℕ} (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (e : ℝ) (he : 0 < e) (he2 : e ≤ 2) :
    let Y := fun n : ℕ => Homogenization.Book.Ch02.geometricWeight e 1 n *
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ)) (E.chart z r hr a z r)
    Summable Y ∧ (∑' n, Y n) = (E.lam z r hr a z r (e / 2) 2)⁻¹ := by
  intro Y
  have heI : e / 2 ∈ Ioc (0 : ℝ) 1 := ⟨by linarith only [he], by linarith only [he2]⟩
  have hq : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h := E.lam_eq z r hr a z r hr (le_refl _) (e / 2) heI 2 hq
  have hw (n : ℕ) : Homogenization.Book.Ch02.geometricWeight (e / 2) 2 n =
      Homogenization.Book.Ch02.geometricWeight e 1 n := by
    unfold Homogenization.Book.Ch02.geometricWeight Homogenization.Book.Ch02.geometricDiscount
    rw [show -(e / 2) * 2 = -e by ring, mul_one]
  have hscale (n : ℕ) : (Homogenization.originCube d 0).scale - (n : ℤ) = -(n : ℤ) := by
    change (0 : ℤ) - (n : ℤ) = -(n : ℤ)
    ring
  norm_num only [if_neg (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat,
    Homogenization.Book.Ch02.lambdaSq_finite, Homogenization.Book.Ch02.lambdaSqFinite,
    show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one, neg_one_mul] at h
  norm_num only [hw, hscale] at h
  have heq : (∑' n, Y n) = (E.lam z r hr a z r (e / 2) 2)⁻¹ := by
    rw [h]
    have h1 (x : ℝ) : Real.rpow x 1 = x := Real.rpow_one x
    have hn (x : ℝ) : Real.rpow x (-1) = x⁻¹ := Real.rpow_neg_one x
    simp only [h1, hn, inv_inv]
    rfl
  refine ⟨?_, heq⟩
  by_contra hns
  have hz := tsum_eq_zero_of_not_summable hns
  have hp := inv_pos.mpr (E.lam_pos z r hr a z r (e / 2) 2)
  rw [← heq, hz] at hp
  exact (lt_irrefl 0) hp

/-- Cell inverse ellipticity grows at most by a power of the cell side, paid by the root. -/
theorem lem_as_regularity_cell_coercivity {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) (j : ℕ) (k : Fin d → ℤ)
    (hk : aux_prop_growth_holder_macro_campanato_Adm j k) :
    aux_prop_growth_holder_macro_campanato_side j ^ e *
      (E.lam (aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j k)
        (aux_prop_growth_holder_macro_campanato_side j)
        (aux_prop_growth_holder_macro_campanato_side_pos j)
        (cutoffPositiveCoefficient M H om N
          (aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j k)
          (aux_prop_growth_holder_macro_campanato_side_pos j))
        (aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j k)
        (aux_prop_growth_holder_macro_campanato_side j) 1 1)⁻¹ ≤
      ((1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e))) *
        (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
          (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
          (fun _ => (1 / 2 : ℝ)) 1 (e / 2) 2)⁻¹ := by
  obtain ⟨hs, heq⟩ := aux_lem_as_regularity_cell_coercivity_series E
    (fun _ => (1 / 2 : ℝ)) 1 one_pos
    (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
    e he (he1.trans (by norm_num))
  simpa only [heq] using aux_cor_neumann_source_lam_cell E M H om N j k hk e e he le_rfl he1 hs

end Paper
