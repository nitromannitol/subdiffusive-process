module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_translated_cell_bridge
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_descendant_rechart
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_center_carrier

@[expose] public section

open MeasureTheory Set Filter Metric
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-! ## H. The physical centre family of a triadic root and the parent assembly -/

/-- Physical centres at physical depth `n` of the root `(z, r)` with `r = 3^j`:
the centres `z + r c_R` of the root-chart descendants `R` of scale `-(n + j)`. -/
def aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (j : ℤ) (n : ℕ) :
    Finset (SpatialCoordinates d) :=
  (descendantsAtScale (originCube d 0) (-((n : ℤ) + j))).image
    (fun R => (fun i => z i + r * cubeCenter R i : SpatialCoordinates d))

theorem aux_lem_as_coarse_shallow_grid_parent_local_fraction_nat_pow_cast (d m : ℕ) :
    (((3 ^ d) ^ m : ℕ) : ℝ) = (3 : ℝ) ^ ((d : ℝ) * (m : ℝ)) := by
  calc
    (((3 ^ d) ^ m : ℕ) : ℝ) = ((3 : ℝ) ^ d) ^ m := by norm_cast
    _ = ((3 : ℝ) ^ (d : ℝ)) ^ (m : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    _ = (3 : ℝ) ^ ((d : ℝ) * (m : ℝ)) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- At most `3^{d j⁺} 3^{dn}` physical centres at physical depth `n`. -/
theorem aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters_card {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (j : ℤ)
    (n : ℕ) :
    ((aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters z r j n).card : ℝ) ≤
      (3 : ℝ) ^ ((d : ℝ) * (j.toNat : ℝ)) * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)) := by
  have hle : (aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters z r j n).card ≤
      (descendantsAtScale (originCube d 0) (-((n : ℤ) + j))).card :=
    Finset.card_image_le
  have hpos : (0 : ℝ) ≤ (3 : ℝ) ^ ((d : ℝ) * (j.toNat : ℝ)) * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)) :=
    by positivity
  by_cases hs : -((n : ℤ) + j) ≤ (originCube d 0).scale
  · rw [descendantsAtScale_eq_descendantsAtDepth _ hs, descendantsAtDepth_card] at hle
    have hm : Int.toNat ((originCube d 0).scale - -((n : ℤ) + j)) ≤ j.toNat + n := by
      change Int.toNat (0 - -((n : ℤ) + j)) ≤ j.toNat + n
      omega
    have hle' : (aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters z r j n).card ≤ (3 ^ d) ^ (j.toNat + n) :=
      hle.trans (Nat.pow_le_pow_right (by positivity) hm)
    calc ((aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters z r j n).card : ℝ) ≤ (((3 ^ d) ^ (j.toNat + n) : ℕ) : ℝ) := by
          exact_mod_cast hle'
      _ = (3 : ℝ) ^ ((d : ℝ) * (j.toNat : ℝ)) * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)) := by
          rw [aux_lem_as_coarse_shallow_grid_parent_local_fraction_nat_pow_cast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          congr 1
          push_cast
          ring
  · rw [descendantsAtScale_eq_empty _ (lt_of_not_ge hs)] at hle
    have : (aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters z r j n).card = 0 := Nat.le_zero.mp (by simpa using hle)
    rw [this, Nat.cast_zero]
    exact hpos

/-- Every physical centre lies within `r` of the root point. -/
theorem aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters_dist {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 ≤ r)
    (j : ℤ) (n : ℕ) : ∀ y ∈ aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters z r j n, dist y z ≤ r := by
  intro y hy
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hy
  have hs : -((n : ℤ) + j) ≤ (originCube d 0).scale := by
    by_contra hs
    rw [descendantsAtScale_eq_empty _ (lt_of_not_ge hs)] at hR
    simp at hR
  have hk : -((n : ℤ) + j) = -((Int.toNat ((n : ℤ) + j) : ℕ) : ℤ) := by
    change -((n : ℤ) + j) ≤ 0 at hs
    omega
  rw [hk] at hR
  have hc := lem_as_coarse_shallow_grid_center_carrier hR
  rw [dist_pi_le_iff hr]
  intro i
  rw [Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_nonneg hr]
  have := hc i
  nlinarith

/-- The unit-chart norm pair at a physical centre and physical depth. -/
def aux_lem_as_coarse_shallow_grid_parent_local_fraction_cellNorm {d : ℕ} (Jc : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hc : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω : BilateralField d)
    (N n : ℕ) (y : SpatialCoordinates d) : ℝ :=
  coarseBMatrixNorm (originCube d 0)
      (Jc.chart y ((3 : ℝ)^(-(n : ℤ))) (by positivity)
        (cutoffPositiveCoefficient M Hc ω N y (by positivity)) y ((3 : ℝ)^(-(n : ℤ)))) +
    coarseSigmaStarInvMatrixNorm (originCube d 0)
      (Jc.chart y ((3 : ℝ)^(-(n : ℤ))) (by positivity)
        (cutoffPositiveCoefficient M Hc ω N y (by positivity)) y ((3 : ℝ)^(-(n : ℤ))))

/-- **Rechart into the physical family.** A descendant `R` of depth `k ≥ j` of
the root chart `(z, 3^j)` is the unit chart at the physical centre
`z + r c_R ∈ aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters z r j (k - j)`, at physical depth `k - j`. -/
theorem aux_lem_as_coarse_shallow_grid_parent_local_fraction_parent_cell_unit {d : ℕ} (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hc : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω : BilateralField d)
    (N k n : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (j : ℤ)
    (hrj : r = (3 : ℝ) ^ j) (hn : (n : ℤ) = k - j)
    (R : TriadicCube d) (hR : R ∈ descendantsAtScale (originCube d 0) (-(k : ℤ))) :
    (fun i => z i + r * cubeCenter R i : SpatialCoordinates d) ∈
        aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters z r j n ∧
      coarseBMatrixNorm R (Jc.chart z r hr (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
          coarseSigmaStarInvMatrixNorm R
            (Jc.chart z r hr (cutoffPositiveCoefficient M Hc ω N z hr) z r) =
        aux_lem_as_coarse_shallow_grid_parent_local_fraction_cellNorm Jc M Hc ω N n (fun i => z i + r * cubeCenter R i) := by
  refine ⟨Finset.mem_image.mpr ⟨R, ?_, rfl⟩, ?_⟩
  · rw [show -((n : ℤ) + j) = -(k : ℤ) by omega]
    exact hR
  · have hρ : (3 : ℝ) ^ (-(n : ℤ)) = r * (3 : ℝ) ^ (-(k : ℤ)) := by
      rw [hrj, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      omega
    have hm := aux_rechart_actual_descendant_core Jc M Hc ω N k z r hr R hR
      (fun i => z i + r * cubeCenter R i) ((3 : ℝ) ^ (-(n : ℤ))) (by positivity) rfl hρ
    unfold aux_lem_as_coarse_shallow_grid_parent_local_fraction_cellNorm coarseBMatrixNorm coarseSigmaStarInvMatrixNorm
    rw [hm.1, hm.2]

theorem aux_lem_as_coarse_shallow_grid_parent_local_fraction_norms_nonneg {d : ℕ} (R : TriadicCube d) (A : TriadicCoeffFamily d) :
    0 ≤ coarseBMatrixNorm R A ∧ 0 ≤ coarseSigmaStarInvMatrixNorm R A :=
  ⟨matrixNorm_nonneg _, matrixNorm_nonneg _⟩

/-- A uniform bound on the two matrix norms in every descendant bounds the sum
of the two separate finite descendant maxima. -/
theorem aux_lem_as_coarse_shallow_grid_parent_local_fraction_maxima_of_cells {d : ℕ}
    (Q : TriadicCube d) (s : ℤ) (A : TriadicCoeffFamily d)
    (C : ℝ) (hC : 0 ≤ C)
    (hcell : ∀ R ∈ descendantsAtScale Q s,
      coarseBMatrixNorm R A + coarseSigmaStarInvMatrixNorm R A ≤ C) :
    maxDescendantBMatrixNormAtScale Q s A +
      maxDescendantSigmaStarInvMatrixNormAtScale Q s A ≤ 2 * C := by
  have hB_le_C : ∀ R ∈ descendantsAtScale Q s, coarseBMatrixNorm R A ≤ C := by
    intro R hR
    have := hcell R hR
    have := (aux_lem_as_coarse_shallow_grid_parent_local_fraction_norms_nonneg R A).2
    linarith
  have hS_le_C : ∀ R ∈ descendantsAtScale Q s, coarseSigmaStarInvMatrixNorm R A ≤ C := by
    intro R hR
    have := hcell R hR
    have := (aux_lem_as_coarse_shallow_grid_parent_local_fraction_norms_nonneg R A).1
    linarith
  by_cases hne : (descendantsAtScale Q s).Nonempty
  · have hmaxB : maxDescendantBMatrixNormAtScale Q s A ≤ C := by
      unfold maxDescendantBMatrixNormAtScale
      exact finsetSupReal_le (descendantsAtScale Q s) hne hB_le_C
    have hmaxS : maxDescendantSigmaStarInvMatrixNormAtScale Q s A ≤ C := by
      unfold maxDescendantSigmaStarInvMatrixNormAtScale
      exact finsetSupReal_le (descendantsAtScale Q s) hne hS_le_C
    linarith
  · have hempty : descendantsAtScale Q s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    unfold maxDescendantBMatrixNormAtScale maxDescendantSigmaStarInvMatrixNormAtScale
    unfold finsetSupReal
    simp [hempty, Real.sSup_empty]
    linarith

/-- **Deterministic parent-chart cell bound.** If the unit-chart norm pair is at
most `KB 3^{ρ n}` at every physical centre of every physical depth `n ≤ nmax`,
then every descendant of depth `k` of the root chart `(z, 3^j)` has norm pair at
most `2 KB 3^{ρ(k + |j|)}`, provided `k + |j| ≤ nmax`. Super-unit cells
(`k < j`) are bounded through their unit descendants. -/
theorem aux_lem_as_coarse_shallow_grid_parent_local_fraction_parent_cell_bound {d : ℕ} [NeZero d] (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hc : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (j : ℤ)
    (hrj : r = (3 : ℝ) ^ j) (rho KB : ℝ) (hrho : 0 ≤ rho) (hKB : 0 ≤ KB) (nmax : ℕ)
    (hcell : ∀ n : ℕ, n ≤ nmax → ∀ y ∈ aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters z r j n,
      aux_lem_as_coarse_shallow_grid_parent_local_fraction_cellNorm Jc M Hc ω N n y ≤ KB * (3 : ℝ) ^ (rho * (n : ℝ)))
    (k : ℕ) (hk : k + j.natAbs ≤ nmax)
    (R : TriadicCube d) (hR : R ∈ descendantsAtScale (originCube d 0) (-(k : ℤ))) :
    coarseBMatrixNorm R (Jc.chart z r hr (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
        coarseSigmaStarInvMatrixNorm R
          (Jc.chart z r hr (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
      2 * (KB * (3 : ℝ) ^ (rho * ((k : ℝ) + (j.natAbs : ℝ)))) := by
  set A := Jc.chart z r hr (cutoffPositiveCoefficient M Hc ω N z hr) z r with hA
  have hbig : KB ≤ KB * (3 : ℝ) ^ (rho * ((k : ℝ) + (j.natAbs : ℝ))) :=
    le_mul_of_one_le_right hKB (Real.one_le_rpow (by norm_num) (by positivity))
  by_cases hjk : j ≤ (k : ℤ)
  · -- unit or sub-unit cell: physical depth `k - j`
    let n : ℕ := Int.toNat ((k : ℤ) - j)
    have hn : (n : ℤ) = k - j := Int.toNat_of_nonneg (by omega)
    have hnle : n ≤ k + j.natAbs := by omega
    obtain ⟨hmem, heq⟩ := aux_lem_as_coarse_shallow_grid_parent_local_fraction_parent_cell_unit Jc M Hc ω N k n z r hr j hrj hn R hR
    rw [heq]
    have h1 := hcell n (hnle.trans hk) _ hmem
    have h2 : (3 : ℝ) ^ (rho * (n : ℝ)) ≤ (3 : ℝ) ^ (rho * ((k : ℝ) + (j.natAbs : ℝ))) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      apply mul_le_mul_of_nonneg_left _ hrho
      exact_mod_cast hnle
    have h3 : 0 ≤ KB * (3 : ℝ) ^ (rho * ((k : ℝ) + (j.natAbs : ℝ))) := by positivity
    calc _ ≤ KB * (3 : ℝ) ^ (rho * (n : ℝ)) := h1
      _ ≤ KB * (3 : ℝ) ^ (rho * ((k : ℝ) + (j.natAbs : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 hKB
      _ ≤ 2 * (KB * (3 : ℝ) ^ (rho * ((k : ℝ) + (j.natAbs : ℝ)))) := by linarith
  · -- super-unit cell: bound by its unit descendants at depth `j`
    have hj0 : 0 < j := by omega
    let kj : ℕ := j.toNat
    have hkj : (kj : ℤ) = j := Int.toNat_of_nonneg hj0.le
    have hRscale : R.scale = -(k : ℤ) := (aux_rechart_descendant_facts k hR).2
    have hsc : -(kj : ℤ) ≤ R.scale := by rw [hRscale]; omega
    have hunit : ∀ R' ∈ descendantsAtScale R (-(kj : ℤ)),
        coarseBMatrixNorm R' A + coarseSigmaStarInvMatrixNorm R' A ≤ KB := by
      intro R' hR'
      have hR'0 : R' ∈ descendantsAtScale (originCube d 0) (-(kj : ℤ)) :=
        mem_descendantsAtScale_trans hR hR'
      obtain ⟨hmem, heq⟩ := aux_lem_as_coarse_shallow_grid_parent_local_fraction_parent_cell_unit Jc M Hc ω N kj 0 z r hr j hrj
        (by omega) R' hR'0
      rw [heq]
      have := hcell 0 (Nat.zero_le _) _ hmem
      simpa using this
    have hne := descendantsAtScale_nonempty R hsc
    have hB : coarseBMatrixNorm R A ≤ KB := by
      refine (coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale R hsc A).trans ?_
      unfold maxDescendantBMatrixNormAtScale
      refine finsetSupReal_le _ hne fun R' hR' => ?_
      have := hunit R' hR'
      have := (aux_lem_as_coarse_shallow_grid_parent_local_fraction_norms_nonneg R' A).2
      linarith
    have hS : coarseSigmaStarInvMatrixNorm R A ≤ KB := by
      refine (coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale
        R hsc A).trans ?_
      unfold maxDescendantSigmaStarInvMatrixNormAtScale
      refine finsetSupReal_le _ hne fun R' hR' => ?_
      have := hunit R' hR'
      have := (aux_lem_as_coarse_shallow_grid_parent_local_fraction_norms_nonneg R' A).1
      linarith
    linarith



theorem lem_as_coarse_shallow_grid_parent_local_fraction
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M Hir →
        M.delta ≤ min 1 delta1 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
        ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ theta' : ℝ, 0 < theta' ∧
          ∃ K : ℝ, 0 < K ∧
          ∀ withIR : Bool,
            let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
              if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
            ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
              ∀ k : ℕ, (k : ℝ) ≤ theta' * (N : ℝ) →
                Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
                  Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                    (Homogenization.originCube d 0) (-(k : ℤ))
                    (Jc.chart z r hr
                      (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
                  K * (3 : ℝ) ^ (rho * (k : ℝ)) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨δ0, hδ0, _hδ01, hB⟩ := lem_as_coarse_shallow_grid_translated_cell_bridge d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp rho hrho
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm Sreg It Hir HI hMd z r hr hj
  obtain ⟨j, hrj⟩ := hj
  obtain ⟨θP, hθP0, _hθP1, hBM⟩ := hB M Rm Sreg It Hir HI (hMd.trans (min_le_right _ _))
  have hev := hBM (aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters z r j) ((3 : ℝ) ^ ((d : ℝ) * (j.toNat : ℝ)))
    (aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters_card z r j) z r (aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters_dist z r hr.le j)
  filter_upwards [hev] with ω hω
  obtain ⟨KB, hKB, N0, hcellB⟩ := hω
  let Kj : ℝ := 4 * KB * (3 : ℝ) ^ (rho * (j.natAbs : ℝ))
  refine ⟨θP / 2, half_pos hθP0, Kj, by positivity, ?_⟩
  intro withIR Hc
  -- `|j| ≤ θP N / 2` for large `N`
  have hlarge : ∀ᶠ N : ℕ in atTop, (j.natAbs : ℝ) ≤ θP / 2 * (N : ℝ) :=
    (Tendsto.const_mul_atTop (half_pos hθP0) tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hlarge
  refine ⟨max N0 N1, ?_⟩
  intro N hN k hk
  have hN0 : N0 ≤ N := (le_max_left _ _).trans hN
  have hjN : (j.natAbs : ℝ) ≤ θP / 2 * (N : ℝ) := hN1 N ((le_max_right _ _).trans hN)
  have hkmax : k + j.natAbs ≤ ⌊θP * (N : ℝ)⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  have hcell : ∀ n : ℕ, n ≤ ⌊θP * (N : ℝ)⌋₊ → ∀ y ∈ aux_lem_as_coarse_shallow_grid_parent_local_fraction_rootCenters z r j n,
      aux_lem_as_coarse_shallow_grid_parent_local_fraction_cellNorm Jc M Hc ω N n y ≤ KB * (3 : ℝ) ^ (rho * (n : ℝ)) :=
    fun n hn y hy => hcellB withIR N hN0 n hn y hy
  have hmax := aux_lem_as_coarse_shallow_grid_parent_local_fraction_maxima_of_cells (originCube d 0) (-(k : ℤ))
    (Jc.chart z r hr (cutoffPositiveCoefficient M Hc ω N z hr) z r)
    (2 * (KB * (3 : ℝ) ^ (rho * ((k : ℝ) + (j.natAbs : ℝ))))) (by positivity)
    (fun R hR => aux_lem_as_coarse_shallow_grid_parent_local_fraction_parent_cell_bound Jc M Hc ω N z r hr j hrj rho KB hrho.le hKB.le
      _ hcell k hkmax R hR)
  refine hmax.trans (le_of_eq ?_)
  have hsplit : (3 : ℝ) ^ (rho * ((k : ℝ) + (j.natAbs : ℝ))) =
      (3 : ℝ) ^ (rho * (j.natAbs : ℝ)) * (3 : ℝ) ^ (rho * (k : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hsplit]
  ring


end SubdiffusiveProcess.Paper


