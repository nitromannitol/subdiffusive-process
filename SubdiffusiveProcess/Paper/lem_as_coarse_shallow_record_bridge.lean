module

public import SubdiffusiveProcess.Paper.lem_as_coarse_first_clause_assembly
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid
public import Homogenization.Sobolev.Fractional.PairCapture

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess SubdiffusiveProcess.Lane4

namespace Paper

private theorem aux_lem_as_coarse_shallow_record_bridge_index_descendant {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (k : ℕ) (nidx : Fin d → ℤ)
    (hsub : (centeredCube
        (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
        (r * (3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d))) :
    ({ scale := -(k : ℤ), index := nidx } : TriadicCube d) ∈
      descendantsAtScale (originCube d 0) (-(k : ℤ)) := by
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d 0) (by simp [originCube])]
  have hdepth : Int.toNat ((originCube d 0).scale - -(k : ℤ)) = k := by
    simp [originCube]
  rw [hdepth]
  apply Gagliardo.mem_descendantsAtDepth_of_index_range
  · simp [originCube]
  · intro i
    have hcenter : (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ∈
        (centeredCube
          (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
          (r * (3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) := by
      rw [centeredCube_eq_pi]
      intro j _
      constructor <;> dsimp <;> nlinarith [show 0 < r * (3 : ℝ) ^ (-(k : ℤ)) by positivity]
    have hroot := hsub hcenter
    rw [centeredCube_eq_pi] at hroot
    have hi := hroot i (Set.mem_univ i)
    have hp : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := by positivity
    have hpow : (3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ (k : ℤ) = 1 := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      simp
    have hcast : ((3 : ℤ) ^ k : ℝ) = (3 : ℝ) ^ (k : ℤ) := by
      norm_cast
    have hh := Gagliardo.two_mul_halfRange k
    simp only [originCube, Pi.zero_apply, mul_zero, zero_sub, zero_add] at hh ⊢
    have hleft : -(1 / 2 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ) := by
      by_contra hn
      have hbad := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hr.le
      dsimp at hi
      nlinarith [hi.1, hbad]
    have hright : (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ) < (1 / 2 : ℝ) := by
      by_contra hn
      have hbad := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hr.le
      dsimp at hi
      nlinarith [hi.2, hbad]
    constructor
    · have hreal : -((3 : ℝ) ^ (k : ℤ)) / 2 < (nidx i : ℝ) := by
        have h := mul_lt_mul_of_pos_left hleft hp
        nlinarith [hpow]
      have hint : -((3 : ℤ) ^ k) < 2 * nidx i := by
        exact_mod_cast (by nlinarith [hreal] : -(((3 : ℤ) ^ k : ℝ)) < 2 * (nidx i : ℝ))
      omega
    · have hreal : (nidx i : ℝ) < ((3 : ℝ) ^ (k : ℤ)) / 2 := by
        have h := mul_lt_mul_of_pos_left hright hp
        nlinarith [hpow]
      have hint : 2 * nidx i < (3 : ℤ) ^ k := by
        exact_mod_cast (by nlinarith [hreal] : 2 * (nidx i : ℝ) < (((3 : ℤ) ^ k : ℝ)))
      omega

/-- A root-chart retained-grid sum bound supplies exactly the shallow grid-cell input
    used by `aux_lem_as_coarse_ms_Inputs`, including arbitrary root offset `m`. -/
theorem lem_as_coarse_shallow_record_bridge {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (rho theta : ℝ) (m N0 : ℕ) (K : ℝ)
    (hgrid : ∀ N, N0 ≤ N → ∀ k : ℕ, (k : ℝ) ≤ theta * N →
      maxDescendantBMatrixNormAtScale (originCube d 0) (-(k : ℤ))
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) +
      maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0) (-(k : ℤ))
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤
        K * (3 : ℝ) ^ (rho * (k : ℝ))) :
    ∀ N, N0 ≤ N → ∀ k : ℕ, (k : ℝ) ≤ theta * N → ∀ nidx : Fin d → ℤ,
      (centeredCube (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
          (r * (3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      coarseBMatrixNorm (originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)) ∧
      coarseSigmaStarInvMatrixNorm (originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ K * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  haveI : NeZero d := ⟨by omega⟩
  intro N hN k hk nidx hsub
  let R : TriadicCube d := ⟨-(k : ℤ), nidx⟩
  have hR : R ∈ descendantsAtScale (originCube d 0) (-(k : ℤ)) :=
    aux_lem_as_coarse_shallow_record_bridge_index_descendant z r hr k nidx hsub
  let a := Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r
  have hsum := hgrid N hN k hk
  have hb : coarseBMatrixNorm R a ≤
      maxDescendantBMatrixNormAtScale (originCube d 0) (-(k : ℤ)) a :=
    coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale_of_mem_descendantsAtScale a hR
  have hs : coarseSigmaStarInvMatrixNorm R a ≤
      maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0) (-(k : ℤ)) a :=
    coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale_of_mem_descendantsAtScale a hR
  have hbn : 0 ≤ maxDescendantBMatrixNormAtScale (originCube d 0) (-(k : ℤ)) a :=
    maxDescendantBMatrixNormAtScale_nonneg (originCube d 0) (by simp [originCube]) a
  have hsn : 0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0) (-(k : ℤ)) a :=
    maxDescendantSigmaStarInvMatrixNormAtScale_nonneg (originCube d 0) (by simp [originCube]) a
  have hR' : R ∈ descendantsAtScale (originCube d 0)
      ((originCube d 0).scale - (k : ℤ)) := by
    simpa [originCube] using hR
  obtain ⟨hbt, hst⟩ := aux_lem_as_coarse_ms_chart_transport Jc M H om N z r hr k hR'
  change coarseBMatrixNorm R a = coarseBMatrixNorm (originCube d 0)
    (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
      (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
      (r * (3 : ℝ) ^ (-(k : ℤ)))) at hbt
  change coarseSigmaStarInvMatrixNorm R a = coarseSigmaStarInvMatrixNorm (originCube d 0)
    (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
      (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
      (r * (3 : ℝ) ^ (-(k : ℤ)))) at hst
  constructor
  · rw [← hbt]
    linarith
  · rw [← hst]
    linarith

end Paper
