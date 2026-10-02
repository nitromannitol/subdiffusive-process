import SubdiffusiveProcess.Paper.lem_as_coarse_first_clause_assembly
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.SmallTail
import Homogenization.Sobolev.Fractional.PairCapture

open Homogenization.Book.Ch02
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open Set

noncomputable section
namespace Paper

/-- An integer-indexed cell of relative depth `k` contained in the root is
exactly a triadic descendant cell. -/
theorem aux_lem_as_coarse_deep_record_bridge_index_descendant {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (k : ℕ)
    (v : Fin d → ℤ)
    (hsub : (centeredCube (aux_lem_as_coarse_ms_cellCenter z r k v)
        (r * (3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d))) :
    ({scale := -(k : ℤ), index := v} : Homogenization.TriadicCube d) ∈
      Homogenization.descendantsAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (k : ℤ)) := by
  have hk0 : (Homogenization.originCube d 0).scale - (k : ℤ) ≤
      (Homogenization.originCube d 0).scale := by
    simp [Homogenization.originCube]
  rw [Homogenization.mem_descendantsAtScale_iff hk0]
  have htn : Int.toNat ((Homogenization.originCube d 0).scale -
      ((Homogenization.originCube d 0).scale - (k : ℤ))) = k := by simp
  rw [htn]
  apply Homogenization.Gagliardo.mem_descendantsAtDepth_of_index_range
  · simp [Homogenization.originCube]
  · intro i
    simp only [Homogenization.originCube, Pi.zero_apply, mul_zero, zero_sub, zero_add]
    let t : ℝ := (3 : ℝ) ^ (-(k : ℤ))
    let p : ℝ := (3 : ℝ) ^ k
    have ht : 0 < t := by dsimp [t]; positivity
    have hp : 0 < p := by dsimp [p]; positivity
    have htp : t * p = 1 := by
      dsimp [t, p]
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      simp
    let w : SpatialCoordinates d := aux_lem_as_coarse_ms_cellCenter z r k v
    have hcoord : Set.Ioo (w i - r * t / 2) (w i + r * t / 2) ⊆
        Set.Ioo (z i - r / 2) (z i + r / 2) := by
      intro x hx
      let y : SpatialCoordinates d := fun j => if j = i then x else w j
      have hy : y ∈ (centeredCube w (r * t) (by positivity) : Set (SpatialCoordinates d)) := by
        rw [centeredCube_eq_pi w (by positivity)]
        intro j _
        by_cases hji : j = i
        · simpa [y, hji] using hx
        · have hrt : 0 < r * t := mul_pos hr ht
          simp [y, hji, Set.mem_Ioo, hrt]
      have hy' := hsub hy
      rw [centeredCube_eq_pi z hr] at hy'
      simpa [y] using hy' i (Set.mem_univ i)
    obtain ⟨hl, hu⟩ := (Set.Ioo_subset_Ioo_iff (by linarith [mul_pos hr ht])).mp hcoord
    have hw : w i = z i + r * t * (v i : ℝ) := rfl
    rw [hw] at hl hu
    have hlo : -(p - 1) / 2 ≤ (v i : ℝ) := by
      nlinarith [mul_pos hr ht]
    have hhi : (v i : ℝ) ≤ (p - 1) / 2 := by
      nlinarith [mul_pos hr ht]
    have hhalf := Homogenization.Gagliardo.two_mul_halfRange k
    have hpow : p = ((3 : ℤ) ^ k : ℝ) := by simp [p]
    rw [hpow] at hlo hhi
    have hhalfR : (2 : ℝ) * (Homogenization.Gagliardo.halfRange k : ℝ) =
        ((3 : ℤ) ^ k : ℝ) - 1 := by exact_mod_cast hhalf
    constructor
    · have hv : -(Homogenization.Gagliardo.halfRange k : ℝ) ≤ (v i : ℝ) := by
        linarith
      exact_mod_cast hv
    · have hv : (v i : ℝ) ≤ (Homogenization.Gagliardo.halfRange k : ℝ) := by
        linarith
      exact_mod_cast hv

/-- A deep-grid bound controls both chart matrices at every descendant cell,
with the root depth offset accounted for by `k + m ≤ N`. -/
theorem aux_lem_as_coarse_deep_record_bridge_cell {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (theta rho : ℝ) (m N0 : ℕ) (Kdeep : ℕ → ℝ)
    (hgrid : ∀ N, N0 ≤ N → ∀ k : ℕ,
      theta * (N : ℝ) < (k : ℝ) → k ≤ N →
      maxDescendantBMatrixNormAtScale (Homogenization.originCube d 0) (-(k : ℤ))
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) +
        maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(k : ℤ))
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤
        Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ))) :
    ∀ N, N0 ≤ N → ∀ k : ℕ, theta * (N : ℝ) < (k : ℝ) → k + m ≤ N →
      ∀ R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (k : ℤ)),
      coarseBMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (aux_lem_as_coarse_ms_cellCenter z r k R.index)
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤
          Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ)) ∧
      coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (aux_lem_as_coarse_ms_cellCenter z r k R.index)
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤
          Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  haveI : NeZero d := ⟨by omega⟩
  intro N hN k hk hkN R hR
  let A := Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r
  have hR' : R ∈ Homogenization.descendantsAtScale
      (Homogenization.originCube d 0) (-(k : ℤ)) := by
    simpa [Homogenization.originCube] using hR
  have hB := coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale_of_mem_descendantsAtScale
    A hR'
  have hS := coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale_of_mem_descendantsAtScale
    A hR'
  have hk0 : -(k : ℤ) ≤ (Homogenization.originCube d 0).scale := by
    simp [Homogenization.originCube]
  have hB0 := maxDescendantBMatrixNormAtScale_nonneg
    (Homogenization.originCube d 0) hk0 A
  have hS0 := maxDescendantSigmaStarInvMatrixNormAtScale_nonneg
    (Homogenization.originCube d 0) hk0 A
  have hsum := hgrid N hN k hk (by omega)
  obtain ⟨htB, htS⟩ := aux_lem_as_coarse_ms_chart_transport Jc M H om N z r hr k hR
  constructor
  · rw [← htB]
    linarith
  · rw [← htS]
    linarith

/-- The deep-grid child supplies the exact deep-cell field of
`aux_lem_as_coarse_ms_Inputs` for an arbitrary triadic root depth `m`. -/
theorem lem_as_coarse_deep_record_bridge {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (theta rho : ℝ) (m N0 : ℕ) (Kdeep : ℕ → ℝ)
    (hgrid : ∀ N, N0 ≤ N → ∀ k : ℕ,
      theta * (N : ℝ) < (k : ℝ) → k ≤ N →
      maxDescendantBMatrixNormAtScale (Homogenization.originCube d 0) (-(k : ℤ))
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) +
        maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(k : ℤ))
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤
        Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ))) :
    ∀ N, N0 ≤ N → ∀ k : ℕ, theta * (N : ℝ) < (k : ℝ) → k + m ≤ N →
      ∀ nidx : Fin d → ℤ,
      (centeredCube (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
          (r * (3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      coarseBMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ)) ∧
      coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (fun i => z i + r * (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            (r * (3 : ℝ) ^ (-(k : ℤ)))) ≤ Kdeep N * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  intro N hN k hk hkN nidx hsub
  let R : Homogenization.TriadicCube d := {scale := -(k : ℤ), index := nidx}
  have hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (k : ℤ)) :=
    aux_lem_as_coarse_deep_record_bridge_index_descendant z r hr k nidx hsub
  simpa only [R, aux_lem_as_coarse_ms_cellCenter] using
    aux_lem_as_coarse_deep_record_bridge_cell hd Jc M H om z r hr theta rho m N0 Kdeep
      hgrid N hN k hk hkN R hR

end Paper
