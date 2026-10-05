module

public import Mathlib
public import SubdiffusiveProcess.Bank.CoarseEllipticityTransfer
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Paper.in_J

@[expose] public section

/-!
# Order transfer and deep-grid cell geometry

Order transfer for the coarse ellipticity charts and exact arithmetic relating
triadic deep cells to the grid supplied by the extension estimate.
-/

open scoped BigOperators ENNReal NNReal
open Homogenization Homogenization.Book.Ch02
open SubdiffusiveProcess

noncomputable section
namespace SubdiffusiveProcess.Paper

section InJOrderTransfer




open SubdiffusiveProcess

variable {d : ℕ}

/-- `in_J`'s `Λ_{s,q}` at a finite exponent is the upstream `LambdaSqFinite` of the
rescaled chart family on the unit root. -/
lemma w20_Lam_eq_finite (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (q : ℝ≥0∞) (hq : 1 ≤ q) (hqt : q ≠ ⊤) :
    Jc.Lam z r hr a w r' s q =
      LambdaSqFinite (Homogenization.originCube d 0) s q.toReal
        (Jc.chart z r hr a w r') := by
  rw [Jc.Lam_eq z r hr a w r' hr' hsub s hs q hq, ite_eq_right hqt]
  rfl

/-- `in_J`'s `λ_{s,q}` at a finite exponent is the upstream `lambdaSqFinite`. -/
lemma w20_lam_eq_finite (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (q : ℝ≥0∞) (hq : 1 ≤ q) (hqt : q ≠ ⊤) :
    Jc.lam z r hr a w r' s q =
      lambdaSqFinite (Homogenization.originCube d 0) s q.toReal
        (Jc.chart z r hr a w r') := by
  rw [Jc.lam_eq z r hr a w r' hr' hsub s hs q hq, ite_eq_right hqt]
  rfl

/-- Summability of the `Λ` series at any legal order, from `in_J.Lam_pos`. -/
lemma w20_summable_Lam (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    Summable (fun n : ℕ => Book.Ch02.geometricWeight sigma 2 n *
      (maxDescendantBMatrixNormAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (n : ℤ))
        (Jc.chart z r hr a w r')) ^ ((2 : ℝ) / 2)) := by
  refine w19_summable_of_LambdaSqFinite_pos _ sigma 2 two_pos _ ?_
  have hpos := Jc.Lam_pos z r hr a w r' sigma 2
  rw [w20_Lam_eq_finite Jc z r hr a w r' hr' hsub sigma hsigma 2 one_le_two
    (by simp)] at hpos
  simpa using hpos

/-- Summability of the `λ` series at any legal order, from `in_J.lam_pos`. -/
lemma w20_summable_lam (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    Summable (fun n : ℕ => Book.Ch02.geometricWeight sigma 2 n *
      (maxDescendantSigmaStarInvMatrixNormAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (n : ℤ))
        (Jc.chart z r hr a w r')) ^ ((2 : ℝ) / 2)) := by
  refine w19_summable_of_lambdaSqFinite_pos _ sigma 2 two_pos _ ?_
  have hpos := Jc.lam_pos z r hr a w r' sigma 2
  rw [w20_lam_eq_finite Jc z r hr a w r' hr' hsub sigma hsigma 2 one_le_two
    (by simp)] at hpos
  simpa using hpos



theorem w20_in_J_order_transfer (Jc : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s s0 : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hs0 : s0 ∈ Set.Ioc (0 : ℝ) 1)
    (hle : s0 ≤ s / 2) (qe : ℝ≥0∞) (hqe : qe = 1 ∨ qe = 2) :
    Jc.Lam z r hr a w r' s qe + (Jc.lam z r hr a w r' s qe)⁻¹ ≤
      (Book.Ch02.geometricDiscount s0 2)⁻¹ *
        (Jc.Lam z r hr a w r' s0 2 + (Jc.lam z r hr a w r' s0 2)⁻¹) := by
  have hspos : 0 < s := hs.1
  have hs0pos : 0 < s0 := hs0.1
  have hs0s : s0 ≤ s := le_trans hle (by linarith)
  have hhalf : s / 2 ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith [hs.2]⟩
  have hc0 : 0 < Book.Ch02.geometricDiscount s0 2 := w19_geometricDiscount_pos s0 2 hs0pos two_pos
  have hconst : ((Book.Ch02.geometricDiscount s0 2)⁻¹) ^ ((2 : ℝ) / 2) =
      (Book.Ch02.geometricDiscount s0 2)⁻¹ := by
    rw [show ((2 : ℝ) / 2) = (1 : ℝ) by norm_num, Real.rpow_one]
  have hqt : qe ≠ ⊤ := by rcases hqe with h | h <;> subst h <;> simp
  have hq1 : 1 ≤ qe := by rcases hqe with h | h <;> subst h <;> simp
  have hqR : qe.toReal = 1 ∨ qe.toReal = 2 := by
    rcases hqe with h | h <;> subst h <;> simp
  have h2R : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by simp
  set Q : Homogenization.TriadicCube d := Homogenization.originCube d 0 with hQ
  set ch : Homogenization.Book.Ch02.TriadicCoeffFamily d := Jc.chart z r hr a w r' with hch
  have hsumL0 := w20_summable_Lam Jc z r hr a w r' hr' hsub s0 hs0
  have hsuml0 := w20_summable_lam Jc z r hr a w r' hr' hsub s0 hs0
  have hsumLh := w20_summable_Lam Jc z r hr a w r' hr' hsub (s / 2) hhalf
  have hsumlh := w20_summable_lam Jc z r hr a w r' hr' hsub (s / 2) hhalf
  have hLam : LambdaSqFinite Q s qe.toReal ch ≤
      (Book.Ch02.geometricDiscount s0 2)⁻¹ * LambdaSqFinite Q s0 2 ch := by
    rcases hqR with h | h <;> rw [h]
    · have h1 : LambdaSqFinite Q s 1 ch ≤ LambdaSqFinite Q (s / 2) 2 ch :=
        w19_LambdaSqFinite_one_le_two Q s hspos ch hsumLh
      have h2 : LambdaSqFinite Q (s / 2) 2 ch ≤
          ((Book.Ch02.geometricDiscount s0 2)⁻¹) ^ ((2 : ℝ) / 2) * LambdaSqFinite Q s0 2 ch :=
        w19_LambdaSqFinite_transfer_order Q s0 (s / 2) 2 hs0pos two_pos hle ch hsumL0
      rw [hconst] at h2
      exact le_trans h1 h2
    · have h2 : LambdaSqFinite Q s 2 ch ≤
          ((Book.Ch02.geometricDiscount s0 2)⁻¹) ^ ((2 : ℝ) / 2) * LambdaSqFinite Q s0 2 ch :=
        w19_LambdaSqFinite_transfer_order Q s0 s 2 hs0pos two_pos hs0s ch hsumL0
      rw [hconst] at h2
      exact h2
  have hlam : (lambdaSqFinite Q s qe.toReal ch)⁻¹ ≤
      (Book.Ch02.geometricDiscount s0 2)⁻¹ * (lambdaSqFinite Q s0 2 ch)⁻¹ := by
    rcases hqR with h | h <;> rw [h]
    · have h1 : (lambdaSqFinite Q s 1 ch)⁻¹ ≤ (lambdaSqFinite Q (s / 2) 2 ch)⁻¹ :=
        w19_lambdaSqFinite_inv_one_le_two Q s hspos ch hsumlh
      have h2 : (lambdaSqFinite Q (s / 2) 2 ch)⁻¹ ≤
          ((Book.Ch02.geometricDiscount s0 2)⁻¹) ^ ((2 : ℝ) / 2) * (lambdaSqFinite Q s0 2 ch)⁻¹ :=
        w19_lambdaSqFinite_inv_transfer_order Q s0 (s / 2) 2 hs0pos two_pos hle ch hsuml0
      rw [hconst] at h2
      exact le_trans h1 h2
    · have h2 : (lambdaSqFinite Q s 2 ch)⁻¹ ≤
          ((Book.Ch02.geometricDiscount s0 2)⁻¹) ^ ((2 : ℝ) / 2) * (lambdaSqFinite Q s0 2 ch)⁻¹ :=
        w19_lambdaSqFinite_inv_transfer_order Q s0 s 2 hs0pos two_pos hs0s ch hsuml0
      rw [hconst] at h2
      exact h2
  rw [w20_Lam_eq_finite Jc z r hr a w r' hr' hsub s hs qe hq1 hqt,
    w20_lam_eq_finite Jc z r hr a w r' hr' hsub s hs qe hq1 hqt,
    w20_Lam_eq_finite Jc z r hr a w r' hr' hsub s0 hs0 2 one_le_two (by simp),
    w20_lam_eq_finite Jc z r hr a w r' hr' hsub s0 hs0 2 one_le_two (by simp),
    h2R, mul_add]
  exact add_le_add hLam hlam

/-- The admissible `β` for a given order `s`: `β = min (3/4) (1/2 + 2 s)` lies in
`(1/2, 1)`, and `lem_extension`'s order `s0 = (β - 1/2)/4` satisfies `0 < s0 ≤ 1` and
`s0 ≤ s/2`, which is exactly what `w20_in_J_order_transfer` requires. -/
lemma w20_beta_of_order (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    min (3 / 4 : ℝ) (1 / 2 + 2 * s) ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
      (min (3 / 4 : ℝ) (1 / 2 + 2 * s) - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 ∧
      (min (3 / 4 : ℝ) (1 / 2 + 2 * s) - 1 / 2) / 4 ≤ s / 2 := by
  obtain ⟨hpos, -⟩ := hs
  rcases le_total (3 / 4 : ℝ) (1 / 2 + 2 * s) with h | h
  · rw [min_eq_left h]
    exact ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, by linarith⟩
  · rw [min_eq_right h]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith⟩

end InJOrderTransfer

variable {d : ℕ}



def w21_matchedDepth (j : ℤ) (k : ℕ) : ℕ := ((k : ℤ) - j).toNat



lemma w21_radius_match (j : ℤ) (k : ℕ) (hjk : j ≤ (k : ℤ)) :
    ((3 : ℝ) ^ j) * (3 : ℝ) ^ (-(k : ℤ)) =
      (3 : ℝ) ^ (-((w21_matchedDepth j k : ℕ) : ℤ)) := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  rw [← zpow_add₀ h3]
  congr 1
  simp only [w21_matchedDepth]
  omega

/-- Cubes depend on their centre and radius only, so equal radii give equal cells. -/
lemma w21_cell_congr (z : SpatialCoordinates d) (n : Fin d → ℤ) (t t' : ℝ)
    (ht : 0 < t) (ht' : 0 < t') (h : t = t') :
    centeredCube (fun i => z i + t * (n i : ℝ)) t ht =
      centeredCube (fun i => z i + t' * (n i : ℝ)) t' ht' := by
  subst h; rfl



lemma w21_deep_cell_is_grid_cell (z : SpatialCoordinates d) (j : ℤ) (k : ℕ)
    (hjk : j ≤ (k : ℤ)) (n : Fin d → ℤ)
    (ht : (0 : ℝ) < (3 : ℝ) ^ j * (3 : ℝ) ^ (-(k : ℤ)))
    (ht' : (0 : ℝ) < (3 : ℝ) ^ (-((w21_matchedDepth j k : ℕ) : ℤ))) :
    centeredCube (fun i => z i + (3 : ℝ) ^ j * (3 : ℝ) ^ (-(k : ℤ)) * (n i : ℝ))
        ((3 : ℝ) ^ j * (3 : ℝ) ^ (-(k : ℤ))) ht =
      centeredCube
        (fun i => z i + (3 : ℝ) ^ (-((w21_matchedDepth j k : ℕ) : ℤ)) * (n i : ℝ))
        ((3 : ℝ) ^ (-((w21_matchedDepth j k : ℕ) : ℤ))) ht' :=
  w21_cell_congr z n _ _ ht ht' (w21_radius_match j k hjk)



lemma w21_depth_le_of_nonneg (j : ℤ) (hj : 0 ≤ j) (k N : ℕ) (hk : k ≤ N) :
    w21_matchedDepth j k ≤ N := by
  simp only [w21_matchedDepth]
  omega

/-- For a root of radius `3^j` with `j < 0` the deep range `theta*N < k ≤ N` always
contains a cell whose matched depth exceeds `N`, so `eq:mfd-3` does not reach it: take
`k = N`. -/
lemma w21_deep_range_escapes_of_neg (j : ℤ) (hj : j < 0) (N : ℕ) (hN : 1 ≤ N)
    (theta : ℝ) (htheta1 : theta < 1) :
    theta * (N : ℝ) < (N : ℝ) ∧ N ≤ N ∧ N < w21_matchedDepth j N := by
  refine ⟨?_, le_rfl, ?_⟩
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    calc theta * (N : ℝ) < 1 * (N : ℝ) := by
          exact mul_lt_mul_of_pos_right htheta1 hNpos
      _ = (N : ℝ) := one_mul _
  · simp only [w21_matchedDepth]
    omega

/-- When the root exponent is below the cell depth, the natural matched depth
casts back to the expected integer offset. -/
lemma w22_matchedDepth_cast (j : ℤ) (k : ℕ) (hjk : j ≤ (k : ℤ)) :
    ((w21_matchedDepth j k : ℕ) : ℤ) = (k : ℤ) - j := by
  simp only [w21_matchedDepth]
  exact Int.toNat_of_nonneg (by omega)

/-- For an arbitrary root exponent, a cell of depth at most `N` needs no more
than `N + (-j).toNat` matched grid levels. This is bookkeeping only; it does
not assert that the extension estimate supplies those extra levels. -/
lemma w22_matchedDepth_le_offset (j : ℤ) (k N : ℕ) (hk : k ≤ N) :
    w21_matchedDepth j k ≤ N + (-j).toNat := by
  simp only [w21_matchedDepth]
  rw [Int.toNat_le]
  have hk' : (k : ℤ) ≤ (N : ℤ) := by exact_mod_cast hk
  have h : -j ≤ ((-j).toNat : ℤ) := Int.self_le_toNat _
  push_cast
  omega

end SubdiffusiveProcess.Paper
