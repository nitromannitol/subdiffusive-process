module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.lem_extension_cell_moment

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper




/-! ### Pure-real discounted-series lemmas -/

section DiscountedSeries
open Homogenization.Book.Ch02

/-- The geometric weight in closed form. -/
theorem aux_lem_cell_ellipticity_gw_eq (s q : ℝ) (n : ℕ) :
    geometricWeight s q n = (1 - (3 : ℝ) ^ (-s * q)) * ((3 : ℝ) ^ (-s * q)) ^ n := by
  unfold geometricWeight geometricDiscount
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm (-s * q)]

theorem aux_lem_cell_ellipticity_base_pos (s q : ℝ) : 0 < (3 : ℝ) ^ (-s * q) := Real.rpow_pos_of_pos (by norm_num) _

theorem aux_lem_cell_ellipticity_base_lt_one {s q : ℝ} (h : 0 < s * q) : (3 : ℝ) ^ (-s * q) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [h])

theorem aux_lem_cell_ellipticity_base_le_of_le {s q s0 q0 : ℝ} (h : s0 * q0 ≤ s * q) :
    (3 : ℝ) ^ (-s * q) ≤ (3 : ℝ) ^ (-s0 * q0) :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [h])

theorem aux_lem_cell_ellipticity_gw_nonneg {s q : ℝ} (h : 0 ≤ s * q) (n : ℕ) :
    0 ≤ geometricWeight s q n := by
  rw [aux_lem_cell_ellipticity_gw_eq]
  have h1 : (3 : ℝ) ^ (-s * q) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [h])
  exact mul_nonneg (by linarith only [h1]) (pow_nonneg (aux_lem_cell_ellipticity_base_pos s q).le n)

theorem aux_lem_cell_ellipticity_gw_le {s q s0 q0 : ℝ} (h0 : 0 < s0 * q0) (h : s0 * q0 ≤ s * q) (n : ℕ) :
    geometricWeight s q n ≤ (1 - (3 : ℝ) ^ (-s0 * q0))⁻¹ * geometricWeight s0 q0 n := by
  have hpos : 0 < 1 - (3 : ℝ) ^ (-s0 * q0) := by linarith only [aux_lem_cell_ellipticity_base_lt_one h0]
  rw [aux_lem_cell_ellipticity_gw_eq, aux_lem_cell_ellipticity_gw_eq, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  have ha := aux_lem_cell_ellipticity_base_le_of_le h
  have hp := aux_lem_cell_ellipticity_base_pos s q
  have h1 : (3 : ℝ) ^ (-s * q) ≤ 1 := by
    have := aux_lem_cell_ellipticity_base_lt_one (lt_of_lt_of_le h0 h)
    linarith only [this]
  calc (1 - (3 : ℝ) ^ (-s * q)) * ((3 : ℝ) ^ (-s * q)) ^ n
      ≤ 1 * ((3 : ℝ) ^ (-s * q)) ^ n :=
        mul_le_mul_of_nonneg_right (by linarith only [hp]) (pow_nonneg hp.le n)
    _ ≤ ((3 : ℝ) ^ (-s0 * q0)) ^ n := by
        rw [one_mul]; exact pow_le_pow_left₀ hp.le ha n

theorem aux_lem_cell_ellipticity_hasSum_gw {s q : ℝ} (h : 0 < s * q) :
    HasSum (fun n : ℕ => geometricWeight s q n) 1 := by
  have hlt := aux_lem_cell_ellipticity_base_lt_one h
  have hg := (hasSum_geometric_of_lt_one (aux_lem_cell_ellipticity_base_pos s q).le hlt).mul_left
    (1 - (3 : ℝ) ^ (-s * q))
  have hpos : (1 - (3 : ℝ) ^ (-s * q)) ≠ 0 := by linarith only [hlt]
  simp only [aux_lem_cell_ellipticity_gw_eq]
  convert hg using 1
  exact (mul_inv_cancel₀ hpos).symm

/-- Comparison of the `q = 2` discounted series at exponents `s0 ≤ s`. -/
theorem aux_lem_cell_ellipticity_tsum_two_le {s s0 : ℝ} (hs0 : 0 < s0) (h : s0 ≤ s) (T : ℕ → ℝ) (hT : ∀ n, 0 ≤ T n)
    (hV : Summable fun n => geometricWeight s0 2 n * T n) :
    ∑' n, geometricWeight s 2 n * T n ≤
      (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹ * ∑' n, geometricWeight s0 2 n * T n := by
  have h0 : 0 < s0 * 2 := by linarith only [hs0]
  have hle : ∀ n, geometricWeight s 2 n * T n ≤
      (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹ * (geometricWeight s0 2 n * T n) := fun n => by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (aux_lem_cell_ellipticity_gw_le h0 (by linarith only [h]) n) (hT n)
  have hsum := hV.mul_left (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hle
    (Summable.of_nonneg_of_le
      (fun n => mul_nonneg (aux_lem_cell_ellipticity_gw_nonneg (by linarith only [hs0, h]) n) (hT n)) hle hsum) hsum

/-- Comparison of the `q = 1` discounted series at exponent `s` with the `q = 2` series at
`s0 ≤ s / 2` (weighted Cauchy--Schwarz; the `q = 1` weights sum to one). -/
theorem aux_lem_cell_ellipticity_tsum_one_sq_le {s s0 : ℝ} (hs0 : 0 < s0) (h : 2 * s0 ≤ s) (T : ℕ → ℝ) (hT : ∀ n, 0 ≤ T n)
    (hV : Summable fun n => geometricWeight s0 2 n * T n) :
    (∑' n, geometricWeight s 1 n * (T n) ^ (1 / 2 : ℝ)) ^ 2 ≤
      (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹ * ∑' n, geometricWeight s0 2 n * T n := by
  have h0 : 0 < s0 * 2 := by linarith only [hs0]
  have hs1 : 0 < s * 1 := by linarith only [hs0, h]
  have hw : ∀ n, 0 ≤ geometricWeight s 1 n := fun n => aux_lem_cell_ellipticity_gw_nonneg hs1.le n
  have hle : ∀ n, geometricWeight s 1 n * T n ≤
      (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹ * (geometricWeight s0 2 n * T n) := fun n => by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (aux_lem_cell_ellipticity_gw_le h0 (by linarith only [h]) n) (hT n)
  have hsum := hV.mul_left (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹
  have hsum1 : Summable fun n => geometricWeight s 1 n * T n :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (hT n)) hle hsum
  have hV1 : ∑' n, geometricWeight s 1 n * T n ≤
      (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹ * ∑' n, geometricWeight s0 2 n * T n := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hle hsum1 hsum
  refine le_trans ?_ hV1
  set V1 := ∑' n, geometricWeight s 1 n * T n with hV1def
  have hV1nn : 0 ≤ V1 := tsum_nonneg fun n => mul_nonneg (hw n) (hT n)
  have hx : ∀ n, 0 ≤ (T n) ^ (1 / 2 : ℝ) := fun n => Real.rpow_nonneg (hT n) _
  have hxx : ∀ n, ((T n) ^ (1 / 2 : ℝ)) ^ 2 = T n := fun n => by
    rw [← Real.sqrt_eq_rpow]; exact Real.sq_sqrt (hT n)
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, geometricWeight s 1 n * (T n) ^ (1 / 2 : ℝ) ≤
      Real.sqrt V1 := by
    intro N
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
      (fun n => Real.sqrt (geometricWeight s 1 n))
      (fun n => Real.sqrt (geometricWeight s 1 n) * (T n) ^ (1 / 2 : ℝ))
    have e1 : ∀ n, Real.sqrt (geometricWeight s 1 n) *
        (Real.sqrt (geometricWeight s 1 n) * (T n) ^ (1 / 2 : ℝ)) =
        geometricWeight s 1 n * (T n) ^ (1 / 2 : ℝ) := fun n => by
      rw [← mul_assoc, Real.mul_self_sqrt (hw n)]
    have e2 : ∀ n, Real.sqrt (geometricWeight s 1 n) ^ 2 = geometricWeight s 1 n := fun n =>
      Real.sq_sqrt (hw n)
    have e3 : ∀ n, (Real.sqrt (geometricWeight s 1 n) * (T n) ^ (1 / 2 : ℝ)) ^ 2 =
        geometricWeight s 1 n * T n := fun n => by
      rw [mul_pow, e2, hxx]
    simp only [e1, e2, e3] at hcs
    have hwsum : ∑ n ∈ Finset.range N, geometricWeight s 1 n ≤ 1 :=
      sum_le_hasSum _ (fun n _ => hw n) (aux_lem_cell_ellipticity_hasSum_gw hs1)
    have hwV : ∑ n ∈ Finset.range N, geometricWeight s 1 n * T n ≤ V1 :=
      sum_le_hasSum _ (fun n _ => mul_nonneg (hw n) (hT n)) hsum1.hasSum
    have hsq : (∑ n ∈ Finset.range N, geometricWeight s 1 n * (T n) ^ (1 / 2 : ℝ)) ^ 2 ≤ V1 := by
      refine hcs.trans ?_
      calc _ ≤ 1 * ∑ n ∈ Finset.range N, geometricWeight s 1 n * T n :=
            mul_le_mul hwsum le_rfl (Finset.sum_nonneg fun n _ => mul_nonneg (hw n) (hT n))
              zero_le_one
        _ ≤ V1 := by rw [one_mul]; exact hwV
    exact Real.le_sqrt_of_sq_le hsq
  have hU : ∑' n, geometricWeight s 1 n * (T n) ^ (1 / 2 : ℝ) ≤ Real.sqrt V1 :=
    Real.tsum_le_of_sum_range_le (fun n => mul_nonneg (hw n) (hx n)) hpart
  have hUnn : 0 ≤ ∑' n, geometricWeight s 1 n * (T n) ^ (1 / 2 : ℝ) :=
    tsum_nonneg fun n => mul_nonneg (hw n) (hx n)
  calc _ ≤ Real.sqrt V1 ^ 2 := pow_le_pow_left₀ hUnn hU 2
    _ = V1 := Real.sq_sqrt hV1nn

end DiscountedSeries

section
open Homogenization Homogenization.Book.Ch02

/-- Scalar matrices compare in the Loewner order as their scalars do. -/
theorem aux_lem_cell_ellipticity_scalar_loewner {d : ℕ} {u v c : ℝ} (h : u ≤ c * v) :
    MatLoewnerLE (scalarMatrix (d := d) u) (c • scalarMatrix (d := d) v) := by
  intro e
  rw [matVecMul_scalarMatrix, smul_matVecMul, matVecMul_scalarMatrix, vecDot_smul_right,
    vecDot_smul_right, vecDot_smul_right]
  have h0 : 0 ≤ vecDot e e := by
    have := vecNormSq_nonneg e
    exact this
  linarith only [mul_le_mul_of_nonneg_right h h0]


/-- Per-cube comparison of `|b|` and `|σ_*⁻¹|` for two chart families which are a.e. scalar
matrices of comparable functions. -/
theorem aux_lem_cell_ellipticity_coarse_le {d : ℕ}
    (a b : TriadicCoeffFamily d) (f g : SpatialCoordinates d → ℝ) (c : ℝ) (hc : 0 < c)
    (Q : TriadicCube d)
    (hf : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      (a.coeffOn Q).toCoeffField x = scalarMatrix (f x))
    (hg : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      (b.coeffOn Q).toCoeffField x = scalarMatrix (g x))
    (hfg : ∀ x ∈ openCubeSet Q, f x ≤ c * g x) (hgf : ∀ x ∈ openCubeSet Q, g x ≤ c * f x) :
    coarseBMatrixNorm Q a ≤ c * coarseBMatrixNorm Q b ∧
      coarseSigmaStarInvMatrixNorm Q a ≤ c * coarseSigmaStarInvMatrixNorm Q b := by
  have hasym : CoeffOn.IsSymmetric (a.coeffOn Q) := hf.mono fun x hx => by
    rw [hx]; exact scalarMatrix_isSymm _
  have hbsym : CoeffOn.IsSymmetric (b.coeffOn Q) := hg.mono fun x hx => by
    rw [hx]; exact scalarMatrix_isSymm _
  constructor
  · refine aux_lem_extension_cell_moment_b_norm_le_mul (cubeDomain Q) (a.coeffOn Q) (b.coeffOn Q)
      hasym hbsym c hc ?_
    filter_upwards [hf, hg, ae_restrict_mem (measurableSet_openCubeSet Q)] with x hfx hgx hxQ
    rw [hfx, hgx]
    exact aux_lem_cell_ellipticity_scalar_loewner (hfg x hxQ)
  · refine aux_lem_extension_cell_moment_sigmaStarInv_norm_le_mul (cubeDomain Q) (a.coeffOn Q)
      (b.coeffOn Q) hasym hbsym c hc ?_
    filter_upwards [hf, hg, ae_restrict_mem (measurableSet_openCubeSet Q)] with x hfx hgx hxQ
    rw [hfx, hgx]
    exact aux_lem_cell_ellipticity_scalar_loewner (hgf x hxQ)

/-- A finite supremum of nonnegative reals compared termwise with a multiple of another. -/
theorem aux_lem_cell_ellipticity_finsetSup_le {α : Type*} (S : Finset α) (f g : α → ℝ)
    (hg : ∀ x, 0 ≤ g x) {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ S, f x ≤ c * g x) :
    finsetSupReal S f ≤ c * finsetSupReal S g := by
  unfold finsetSupReal
  refine Real.sSup_le ?_ (mul_nonneg hc (Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact hg x)))
  rintro _ ⟨x, hx, rfl⟩
  exact (h x hx).trans (mul_le_mul_of_nonneg_left
    (le_csSup (((S : Set α).toFinite).image g).bddAbove ⟨x, hx, rfl⟩) hc)


theorem aux_lem_cell_ellipticity_summable_of_ne_zero {f : ℕ → ℝ} (h : ∑' n, f n ≠ 0) :
    Summable f := by
  by_contra hns
  exact h (tsum_eq_zero_of_not_summable hns)

/-- **Deterministic comparison of the target ellipticities** (`q = 2`): if two charts are a.e.
scalar matrices of functions `f, g` on the unit root with `f ≤ c g` and `g ≤ c f`, then
`Λ_{s,2}` and `λ_{s,2}⁻¹` compare with the factor `c`. -/
theorem aux_lem_cell_ellipticity_compare {d : ℕ} (E : in_J d)
    (za : SpatialCoordinates d) (Ra : ℝ) (hRa : 0 < Ra)
    (a : PositiveCoefficient (centeredCube za Ra hRa))
    (wa : SpatialCoordinates d) (ra : ℝ) (hra : 0 < ra)
    (hsuba : (centeredCube wa ra hra : Set (SpatialCoordinates d)) ⊆
      (centeredCube za Ra hRa : Set (SpatialCoordinates d)))
    (zb : SpatialCoordinates d) (Rb : ℝ) (hRb : 0 < Rb)
    (b : PositiveCoefficient (centeredCube zb Rb hRb))
    (wb : SpatialCoordinates d) (rb : ℝ) (hrb : 0 < rb)
    (hsubb : (centeredCube wb rb hrb : Set (SpatialCoordinates d)) ⊆
      (centeredCube zb Rb hRb : Set (SpatialCoordinates d)))
    (f g : SpatialCoordinates d → ℝ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ Q : TriadicCube d, openCubeSet Q ⊆ openCubeSet (originCube d 0) →
      ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
        ((E.chart za Ra hRa a wa ra).coeffOn Q).toCoeffField x = scalarMatrix (f x))
    (hg : ∀ Q : TriadicCube d, openCubeSet Q ⊆ openCubeSet (originCube d 0) →
      ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
        ((E.chart zb Rb hRb b wb rb).coeffOn Q).toCoeffField x = scalarMatrix (g x))
    (hfg : ∀ x ∈ openCubeSet (originCube d 0), f x ≤ c * g x)
    (hgf : ∀ x ∈ openCubeSet (originCube d 0), g x ≤ c * f x)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    E.Lam za Ra hRa a wa ra s 2 ≤ c * E.Lam zb Rb hRb b wb rb s 2 ∧
      (E.lam za Ra hRa a wa ra s 2)⁻¹ ≤ c * (E.lam zb Rb hRb b wb rb s 2)⁻¹ := by
  have hk : ∀ n : ℕ, (originCube d 0).scale - (n : ℤ) ≤ (originCube d 0).scale :=
    fun n => sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hcoarse : ∀ (n : ℕ) (Q : TriadicCube d),
      Q ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)) →
      coarseBMatrixNorm Q (E.chart za Ra hRa a wa ra) ≤
          c * coarseBMatrixNorm Q (E.chart zb Rb hRb b wb rb) ∧
        coarseSigmaStarInvMatrixNorm Q (E.chart za Ra hRa a wa ra) ≤
          c * coarseSigmaStarInvMatrixNorm Q (E.chart zb Rb hRb b wb rb) := by
    intro n Q hQ
    have hQs := openCubeSet_subset_of_mem_descendantsAtScale (hk n) hQ
    exact aux_lem_cell_ellipticity_coarse_le _ _ f g c hc Q (hf Q hQs) (hg Q hQs)
      (fun x hx => hfg x (hQs hx)) (fun x hx => hgf x (hQs hx))
  have hnnB : ∀ (n : ℕ) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
      (u : PositiveCoefficient (centeredCube z R hR)) (w : SpatialCoordinates d) (r : ℝ),
      0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 n * maxDescendantBMatrixNormAtScale (originCube d 0)
        ((originCube d 0).scale - (n : ℤ)) (E.chart z R hR u w r) := fun n z R hR u w r =>
    mul_nonneg (aux_lem_extension_cell_moment_weight_nonneg hs.1.le n)
      (aux_lem_extension_cell_moment_finsetSupReal_nonneg _ _ fun _ => norm_nonneg _)
  have hnnS : ∀ (n : ℕ) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
      (u : PositiveCoefficient (centeredCube z R hR)) (w : SpatialCoordinates d) (r : ℝ),
      0 ≤ Homogenization.Book.Ch02.geometricWeight s 2 n * maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0)
        ((originCube d 0).scale - (n : ℤ)) (E.chart z R hR u w r) := fun n z R hR u w r =>
    mul_nonneg (aux_lem_extension_cell_moment_weight_nonneg hs.1.le n)
      (aux_lem_extension_cell_moment_finsetSupReal_nonneg _ _ fun _ => norm_nonneg _)
  constructor
  · rw [aux_lem_extension_cell_moment_Lam_eq_tsum E za Ra hRa a wa ra hra hsuba s hs,
      aux_lem_extension_cell_moment_Lam_eq_tsum E zb Rb hRb b wb rb hrb hsubb s hs,
      ← tsum_mul_left]
    have hsumB : Summable fun n : ℕ => Homogenization.Book.Ch02.geometricWeight s 2 n *
        maxDescendantBMatrixNormAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ))
          (E.chart zb Rb hRb b wb rb) := by
      refine aux_lem_cell_ellipticity_summable_of_ne_zero ?_
      rw [← aux_lem_extension_cell_moment_Lam_eq_tsum E zb Rb hRb b wb rb hrb hsubb s hs]
      exact (E.Lam_pos _ _ _ _ _ _ _ _).ne'
    have hle : ∀ n : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 n * maxDescendantBMatrixNormAtScale (originCube d 0)
        ((originCube d 0).scale - (n : ℤ)) (E.chart za Ra hRa a wa ra) ≤
        c * (Homogenization.Book.Ch02.geometricWeight s 2 n * maxDescendantBMatrixNormAtScale (originCube d 0)
          ((originCube d 0).scale - (n : ℤ)) (E.chart zb Rb hRb b wb rb)) := fun n => by
      rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (aux_lem_extension_cell_moment_weight_nonneg hs.1.le n)
      exact aux_lem_cell_ellipticity_finsetSup_le _ _ _ (fun _ => norm_nonneg _) hc.le
        (fun Q hQ => (hcoarse n Q hQ).1)
    exact Summable.tsum_le_tsum hle
      (Summable.of_nonneg_of_le (fun n => hnnB n za Ra hRa a wa ra) hle (hsumB.mul_left c))
      (hsumB.mul_left c)
  · rw [aux_lem_extension_cell_moment_lam_inv_eq_tsum E za Ra hRa a wa ra hra hsuba s hs,
      aux_lem_extension_cell_moment_lam_inv_eq_tsum E zb Rb hRb b wb rb hrb hsubb s hs,
      ← tsum_mul_left]
    have hsumS : Summable fun n : ℕ => Homogenization.Book.Ch02.geometricWeight s 2 n *
        maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0)
          ((originCube d 0).scale - (n : ℤ)) (E.chart zb Rb hRb b wb rb) := by
      refine aux_lem_cell_ellipticity_summable_of_ne_zero ?_
      rw [← aux_lem_extension_cell_moment_lam_inv_eq_tsum E zb Rb hRb b wb rb hrb hsubb s hs]
      exact (inv_pos.2 (E.lam_pos _ _ _ _ _ _ _ _)).ne'
    have hle : ∀ n : ℕ, Homogenization.Book.Ch02.geometricWeight s 2 n *
        maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0)
          ((originCube d 0).scale - (n : ℤ)) (E.chart za Ra hRa a wa ra) ≤
        c * (Homogenization.Book.Ch02.geometricWeight s 2 n * maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0)
          ((originCube d 0).scale - (n : ℤ)) (E.chart zb Rb hRb b wb rb)) := fun n => by
      rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (aux_lem_extension_cell_moment_weight_nonneg hs.1.le n)
      exact aux_lem_cell_ellipticity_finsetSup_le _ _ _ (fun _ => norm_nonneg _) hc.le
        (fun Q hQ => (hcoarse n Q hQ).2)
    exact Summable.tsum_le_tsum hle
      (Summable.of_nonneg_of_le (fun n => hnnS n za Ra hRa a wa ra) hle (hsumS.mul_left c))
      (hsumS.mul_left c)

end

section
open Homogenization Homogenization.Book.Ch02

/-- `in_J`'s `Λ_{s,1}` is the square of the discounted `q = 1` series of `|b|` maxima. -/
theorem aux_lem_cell_ellipticity_Lam_eq_one {d : ℕ} (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    E.Lam z r hr a w r' s 1 =
      (∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n *
        (maxDescendantBMatrixNormAtScale (originCube d 0)
          ((originCube d 0).scale - (n : ℤ)) (E.chart z r hr a w r')) ^ (1 / 2 : ℝ)) ^ 2 := by
  rw [E.Lam_eq z r hr a w r' hr' hsub s hs 1 le_rfl]
  simp only [Homogenization.Book.Ch02.LambdaSq, Homogenization.Book.Ch02.LambdaSqFinite, ENNReal.one_ne_top, ite_false, ENNReal.toReal_one]
  norm_num


/-- `in_J`'s `λ_{s,1}⁻¹` is the square of the discounted `q = 1` series of `|σ_*⁻¹|` maxima. -/
theorem aux_lem_cell_ellipticity_lam_inv_eq_one {d : ℕ} (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    (E.lam z r hr a w r' s 1)⁻¹ =
      (∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight s 1 n *
        (maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0)
          ((originCube d 0).scale - (n : ℤ)) (E.chart z r hr a w r')) ^ (1 / 2 : ℝ)) ^ 2 := by
  rw [E.lam_eq z r hr a w r' hr' hsub s hs 1 le_rfl]
  simp only [Homogenization.Book.Ch02.lambdaSq, Homogenization.Book.Ch02.lambdaSqFinite,
    ENNReal.one_ne_top, ite_false, ENNReal.toReal_one]
  norm_num


/-- **Reduction of the target ellipticities to a small order and exponent two.**  For
`q ∈ {1,2}`, `s ∈ (0,1]` and `0 < s0` with `2 s0 ≤ s`, the weighted sums compare
(Cauchy--Schwarz for `q = 1`, the discount for `q = 2`). -/
theorem aux_lem_cell_ellipticity_reduce {d : ℕ} (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s s0 : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hs0 : 0 < s0) (h2 : 2 * s0 ≤ s)
    (qn : ℝ≥0∞) (hq : qn = 1 ∨ qn = 2) :
    E.Lam z r hr a w r' s qn + (E.lam z r hr a w r' s qn)⁻¹ ≤
      (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹ *
        (E.Lam z r hr a w r' s0 2 + (E.lam z r hr a w r' s0 2)⁻¹) := by
  have hs0' : s0 ∈ Set.Ioc (0 : ℝ) 1 := ⟨hs0, by linarith only [hs.2, h2, hs0]⟩
  have hsB : Summable fun n : ℕ => Homogenization.Book.Ch02.geometricWeight s0 2 n *
      maxDescendantBMatrixNormAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ))
        (E.chart z r hr a w r') := by
    refine aux_lem_cell_ellipticity_summable_of_ne_zero ?_
    rw [← aux_lem_extension_cell_moment_Lam_eq_tsum E z r hr a w r' hr' hsub s0 hs0']
    exact (E.Lam_pos _ _ _ _ _ _ _ _).ne'
  have hsS : Summable fun n : ℕ => Homogenization.Book.Ch02.geometricWeight s0 2 n *
      maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0)
        ((originCube d 0).scale - (n : ℤ)) (E.chart z r hr a w r') := by
    refine aux_lem_cell_ellipticity_summable_of_ne_zero ?_
    rw [← aux_lem_extension_cell_moment_lam_inv_eq_tsum E z r hr a w r' hr' hsub s0 hs0']
    exact (inv_pos.2 (E.lam_pos _ _ _ _ _ _ _ _)).ne'
  have hTB : ∀ n : ℕ, 0 ≤ maxDescendantBMatrixNormAtScale (originCube d 0)
      ((originCube d 0).scale - (n : ℤ)) (E.chart z r hr a w r') := fun n =>
    aux_lem_extension_cell_moment_finsetSupReal_nonneg _ _ fun _ => norm_nonneg _
  have hTS : ∀ n : ℕ, 0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0)
      ((originCube d 0).scale - (n : ℤ)) (E.chart z r hr a w r') := fun n =>
    aux_lem_extension_cell_moment_finsetSupReal_nonneg _ _ fun _ => norm_nonneg _
  have hL0 := aux_lem_extension_cell_moment_Lam_eq_tsum E z r hr a w r' hr' hsub s0 hs0'
  have hl0 := aux_lem_extension_cell_moment_lam_inv_eq_tsum E z r hr a w r' hr' hsub s0 hs0'
  rcases hq with rfl | rfl
  · rw [aux_lem_cell_ellipticity_Lam_eq_one E z r hr a w r' hr' hsub s hs,
      aux_lem_cell_ellipticity_lam_inv_eq_one E z r hr a w r' hr' hsub s hs, hL0, hl0,
      mul_add]
    exact add_le_add
      (aux_lem_cell_ellipticity_tsum_one_sq_le hs0 h2 _ hTB hsB)
      (aux_lem_cell_ellipticity_tsum_one_sq_le hs0 h2 _ hTS hsS)
  · rw [aux_lem_extension_cell_moment_Lam_eq_tsum E z r hr a w r' hr' hsub s hs,
      aux_lem_extension_cell_moment_lam_inv_eq_tsum E z r hr a w r' hr' hsub s hs, hL0, hl0,
      mul_add]
    exact add_le_add
      (aux_lem_cell_ellipticity_tsum_two_le hs0 (by linarith only [h2, hs0]) _ hTB hsB)
      (aux_lem_cell_ellipticity_tsum_two_le hs0 (by linarith only [h2, hs0]) _ hTS hsS)

end

theorem aux_lem_cell_ellipticity_aemeasurable_tsum {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → α → ℝ} (hg : ∀ n, AEMeasurable (g n) μ)
    (hnn : ∀ n x, 0 ≤ g n x) : AEMeasurable (fun x => ∑' n, g n x) μ := by
  have h : (fun x => ∑' n, g n x) = fun x => (∑' n, ENNReal.ofReal (g n x)).toReal := by
    funext x
    rw [ENNReal.tsum_toReal_eq (fun n => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun n => (ENNReal.toReal_ofReal (hnn n x)).symm
  rw [h]
  exact (AEMeasurable.tsum fun n => (hg n).ennreal_ofReal).ennreal_toReal


/-- **Measurability clause for general `(s, q)`.** -/
theorem aux_lem_cell_ellipticity_aestronglyMeasurable {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hcell : centeredCube w r' hr' ≤ centeredCube z0 R hR)
    (qn : ℝ≥0∞) (hq : qn = 1 ∨ qn = 2) :
    AEStronglyMeasurable (fun om =>
      E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r' s qn +
        (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r' s qn)⁻¹)
      (chaosSampleLaw M).toMeasure := by
  have hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d)) := hcell
  rcases hq with rfl | rfl
  · have hB : ∀ n : ℕ, AEMeasurable (fun om =>
        Homogenization.Book.Ch02.geometricWeight s 1 n *
          (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
            (Homogenization.originCube d 0)
            ((Homogenization.originCube d 0).scale - (n : ℤ))
            (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r')) ^ (1 / 2 : ℝ))
        (chaosSampleLaw M).toMeasure := fun n =>
      (((aux_lem_extension_cell_moment_aesm_maxB_chart hd E M H hH.1 N z0 R hR w r' hr'
        hsub n).aemeasurable).pow_const _).const_mul _
    have hS : ∀ n : ℕ, AEMeasurable (fun om =>
        Homogenization.Book.Ch02.geometricWeight s 1 n *
          (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
            (Homogenization.originCube d 0)
            ((Homogenization.originCube d 0).scale - (n : ℤ))
            (E.chart z0 R hR (cutoffPositiveCoefficient M H om N z0 hR) w r')) ^ (1 / 2 : ℝ))
        (chaosSampleLaw M).toMeasure := fun n =>
      (((aux_lem_extension_cell_moment_aesm_maxS_chart hd E M H hH.1 N z0 R hR w r' hr'
        hsub n).aemeasurable).pow_const _).const_mul _
    have hw : ∀ n : ℕ, 0 ≤ Homogenization.Book.Ch02.geometricWeight s 1 n := fun n =>
      aux_lem_cell_ellipticity_gw_nonneg (by linarith only [hs.1]) n
    refine (((aux_lem_cell_ellipticity_aemeasurable_tsum hB fun n om =>
        mul_nonneg (hw n) (Real.rpow_nonneg
          (aux_lem_extension_cell_moment_finsetSupReal_nonneg _ _ fun _ => norm_nonneg _) _)
        ).pow_const 2).add
      ((aux_lem_cell_ellipticity_aemeasurable_tsum hS fun n om =>
        mul_nonneg (hw n) (Real.rpow_nonneg
          (aux_lem_extension_cell_moment_finsetSupReal_nonneg _ _ fun _ => norm_nonneg _) _)
        ).pow_const 2)).aestronglyMeasurable.congr (Filter.Eventually.of_forall fun om => ?_)
    simp only [Pi.add_apply, aux_lem_cell_ellipticity_Lam_eq_one E z0 R hR _ w r' hr' hsub s hs,
      aux_lem_cell_ellipticity_lam_inv_eq_one E z0 R hR _ w r' hr' hsub s hs]
  · exact aux_lem_extension_cell_moment_aestronglyMeasurable hd E M H hH s hs z0 R hR N w r' hr'
      hcell

/-- **Deterministic comparison of the target ellipticities** (the monotonicity/homogeneity step of
paper `mfd:lem-cell-ellipticity`, combined with the comparison of the weighted sums at
exponents `s0 ≤ s/2` and `s`).

If the charts of the two cells are a.e. on every triadic sub-cube of the unit root the scalar
matrices of comparable functions `f, g` (`f ≤ c g` and `g ≤ c f` on the unit root), then for every
`s ∈ (0,1]`, `q ∈ {1,2}` and `0 < s0 ≤ s/2`,
`Λ_{s,q}(a) + λ_{s,q}(a)⁻¹ ≤ (1 - 3^{-2 s0})⁻¹ · c · (Λ_{s0,2}(b) + λ_{s0,2}(b)⁻¹)`. -/
theorem lem_cell_ellipticity_compare :
  ∀ (d : ℕ) (E : in_J d)
    (za : SpatialCoordinates d) (Ra : ℝ) (hRa : 0 < Ra)
    (a : PositiveCoefficient (centeredCube za Ra hRa))
    (wa : SpatialCoordinates d) (ra : ℝ) (hra : 0 < ra),
    (centeredCube wa ra hra : Set (SpatialCoordinates d)) ⊆
      (centeredCube za Ra hRa : Set (SpatialCoordinates d)) →
  ∀ (zb : SpatialCoordinates d) (Rb : ℝ) (hRb : 0 < Rb)
    (b : PositiveCoefficient (centeredCube zb Rb hRb))
    (wb : SpatialCoordinates d) (rb : ℝ) (hrb : 0 < rb),
    (centeredCube wb rb hrb : Set (SpatialCoordinates d)) ⊆
      (centeredCube zb Rb hRb : Set (SpatialCoordinates d)) →
  ∀ (f g : SpatialCoordinates d → ℝ) (c : ℝ), 0 < c →
    (∀ Q : Homogenization.TriadicCube d,
      Homogenization.openCubeSet Q ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∀ᵐ x ∂Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q),
        ((E.chart za Ra hRa a wa ra).coeffOn Q).toCoeffField x =
          Homogenization.scalarMatrix (f x)) →
    (∀ Q : Homogenization.TriadicCube d,
      Homogenization.openCubeSet Q ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0) →
      ∀ᵐ x ∂Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q),
        ((E.chart zb Rb hRb b wb rb).coeffOn Q).toCoeffField x =
          Homogenization.scalarMatrix (g x)) →
    (∀ x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0), f x ≤ c * g x) →
    (∀ x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0), g x ≤ c * f x) →
  ∀ (s s0 : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 → 0 < s0 → 2 * s0 ≤ s →
  ∀ (qn : ℝ≥0∞), (qn = 1 ∨ qn = 2) →
    E.Lam za Ra hRa a wa ra s qn + (E.lam za Ra hRa a wa ra s qn)⁻¹ ≤
      (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹ *
        (c * (E.Lam zb Rb hRb b wb rb s0 2 + (E.lam zb Rb hRb b wb rb s0 2)⁻¹)) := by
  intro d E za Ra hRa a wa ra hra hsuba zb Rb hRb b wb rb hrb hsubb f g c hc hf hg hfg hgf
    s s0 hs hs0 h2 qn hq
  have hs0' : s0 ∈ Set.Ioc (0 : ℝ) 1 := ⟨hs0, by linarith only [hs.2, h2, hs0]⟩
  have hred := aux_lem_cell_ellipticity_reduce E za Ra hRa a wa ra hra hsuba s s0 hs hs0 h2 qn hq
  have hcmp := aux_lem_cell_ellipticity_compare E za Ra hRa a wa ra hra hsuba zb Rb hRb b wb rb
    hrb hsubb f g c hc hf hg hfg hgf s0 hs0'
  have hC : 0 ≤ (1 - (3 : ℝ) ^ (-s0 * 2))⁻¹ := by
    have := aux_lem_cell_ellipticity_base_lt_one (s := s0) (q := 2) (by linarith only [hs0])
    exact inv_nonneg.2 (by linarith only [this])
  refine hred.trans (mul_le_mul_of_nonneg_left ?_ hC)
  calc _ ≤ c * E.Lam zb Rb hRb b wb rb s0 2 + c * (E.lam zb Rb hRb b wb rb s0 2)⁻¹ :=
        add_le_add hcmp.1 hcmp.2
    _ = _ := (mul_add _ _ _).symm

end SubdiffusiveProcess.Paper
