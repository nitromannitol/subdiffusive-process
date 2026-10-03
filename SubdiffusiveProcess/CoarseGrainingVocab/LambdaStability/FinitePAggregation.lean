-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/Homogenization/HomFinitePTranslate.lean
/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridStabilityGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridStabilityArith

@[expose] public section

/-!
# Finite-exponent maximal-cube packing

This is the bounded-overlap/reindexing layer needed by the finite spatial
exponent in `mathcal E` stability.  It mirrors the packing core of
`Algsuperdiff/.../HomFinitePTranslate.lean`; unlike the shell-maximum route, it
keeps the normalized finite sum over physical cubes.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The depth of a maximal grid cube below the off-grid shape cube. -/
def finitePOffDepth (P Q : TriadicCube d) : ℕ := (P.scale - Q.scale).toNat

omit [NeZero d] in
theorem finitePOffDepth_spec {P Q : TriadicCube d} (h : Q.scale ≤ P.scale) :
    Q.scale = P.scale - (finitePOffDepth P Q : ℤ) := by
  rw [finitePOffDepth, Int.toNat_of_nonneg (by omega)]
  omega

/-- The geometric factor for lifting a volume-weighted grid bound through a
maximal-cube decomposition. -/
def finitePAggregationGeomFactor (r : ℝ) : ℝ :=
  (1 - (3 : ℝ) ^ (-(1 - r)))⁻¹

private theorem geom_sum_range_le_inv_one_sub {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), r ^ i) ≤ (1 - r)⁻¹ := by
  have hden : (0 : ℝ) < 1 - r := by linarith only [hr1]
  have hid : (∑ i ∈ Finset.range (N + 1), r ^ i) * (1 - r) =
      1 - r ^ (N + 1) := by
    have h := geom_sum_mul r (N + 1)
    have hneg : (∑ i ∈ Finset.range (N + 1), r ^ i) * (1 - r) =
        -((∑ i ∈ Finset.range (N + 1), r ^ i) * (r - 1)) := by ring
    rw [hneg, h]
    ring
  have hnn : (0 : ℝ) ≤ r ^ (N + 1) := pow_nonneg hr0 _
  rw [show (1 - r)⁻¹ = 1 / (1 - r) by rw [one_div], le_div_iff₀ hden, hid]
  linarith only [hnn]

/-- At one depth, every finite subfamily of maximal cubes satisfies the
printed `2 d 3^(1-j)` packing bound. -/
theorem sum_cubeVolume_maximalCubesAtDepth_le (w : Vec d) (P : TriadicCube d)
    (j : ℕ) (S : Finset (TriadicCube d))
    (hS : ∀ Q ∈ S,
      MaximalCubeIn (offGridCube w P) Q ∧ Q.scale = P.scale - (j : ℤ)) :
    ∑ Q ∈ S, cubeVolume Q ≤
      2 * (d : ℝ) * (3 : ℝ) ^ (1 - (j : ℤ)) * cubeVolume P := by
  classical
  set k : ℤ := P.scale - (j : ℤ) with hk
  have hdisj : ∀ Q ∈ (S : Set (TriadicCube d)),
      ∀ R ∈ (S : Set (TriadicCube d)), Q ≠ R →
        Disjoint (cubeSet Q) (cubeSet R) := by
    intro Q hQ R hR hne
    exact disjoint_cubeSet_of_maximalCubeIn
      (hS Q (by exact_mod_cast hQ)).1 (hS R (by exact_mod_cast hR)).1 hne
  have hunion : volume (⋃ Q ∈ S, cubeSet Q) = ∑ Q ∈ S, volume (cubeSet Q) :=
    MeasureTheory.measure_biUnion_finset hdisj fun Q _ => measurableSet_cubeSet Q
  have hsubset : (⋃ Q ∈ S, cubeSet Q) ⊆
      ⋃ Q ∈ maximalCubesAtScale (offGridCube w P) k, cubeSet Q := by
    refine Set.iUnion₂_subset ?_
    intro Q hQ
    refine Set.subset_iUnion₂
      (s := fun Q (_ : Q ∈ maximalCubesAtScale (offGridCube w P) k) => cubeSet Q) Q ?_
    exact ⟨(hS Q hQ).1, (hS Q hQ).2⟩
  have htop : volume
      (⋃ Q ∈ maximalCubesAtScale (offGridCube w P) k, cubeSet Q) ≠ ⊤ :=
    volume_iUnion_maximalCubesAtScale_ne_top w P k
  have hmono : (volume (⋃ Q ∈ S, cubeSet Q)).toReal ≤
      (volume (⋃ Q ∈ maximalCubesAtScale (offGridCube w P) k, cubeSet Q)).toReal :=
    ENNReal.toReal_mono htop (MeasureTheory.measure_mono hsubset)
  have hsumreal : (volume (⋃ Q ∈ S, cubeSet Q)).toReal =
      ∑ Q ∈ S, cubeVolume Q := by
    rw [hunion, ENNReal.toReal_sum fun Q _ => (volume_cubeSet_lt_top Q).ne]
    exact Finset.sum_congr rfl fun Q _ => volume_cubeSet_toReal Q
  have hpack := volume_iUnion_maximalCubesAtScale_toReal_le w P k
  have hexp : k + 1 - P.scale = 1 - (j : ℤ) := by rw [hk]; omega
  rw [hexp] at hpack
  rw [hsumreal] at hmono
  exact hmono.trans hpack

/-- The finite-subsum bounded-overlap estimate after reindexing the maximal
cubes by depth. -/
theorem finset_sum_maximalCubes_weight_le (w : Vec d) (P : TriadicCube d)
    {r : ℝ} (hr1 : r < 1) (S : Finset (TriadicCube d))
    (hS : ∀ Q ∈ S, MaximalCubeIn (offGridCube w P) Q) :
    ∑ Q ∈ S, cubeVolume Q *
        (3 : ℝ) ^ (r * ((P.scale : ℝ) - (Q.scale : ℝ))) ≤
      6 * (d : ℝ) * finitePAggregationGeomFactor r * cubeVolume P := by
  classical
  set N : ℕ := S.sup (finitePOffDepth P) with hN
  have hmaps : ∀ Q ∈ S, finitePOffDepth P Q ∈ Finset.range (N + 1) := by
    intro Q hQ
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.le_sup (f := finitePOffDepth P) hQ))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun Q => cubeVolume Q *
      (3 : ℝ) ^ (r * ((P.scale : ℝ) - (Q.scale : ℝ))))]
  have hfiber : ∀ j ∈ Finset.range (N + 1),
      (∑ Q ∈ S.filter fun Q => finitePOffDepth P Q = j,
          cubeVolume Q *
            (3 : ℝ) ^ (r * ((P.scale : ℝ) - (Q.scale : ℝ)))) ≤
        6 * (d : ℝ) * cubeVolume P *
          ((3 : ℝ) ^ (-(1 - r))) ^ j := by
    intro j _
    have hscale : ∀ Q ∈ S.filter fun Q => finitePOffDepth P Q = j,
        Q.scale = P.scale - (j : ℤ) := by
      intro Q hQ
      obtain ⟨hQS, hQj⟩ := Finset.mem_filter.mp hQ
      have hle := scale_le_of_maximalCubeIn_offGridCube (hS Q hQS)
      rw [← hQj]
      exact finitePOffDepth_spec hle
    have hconst : ∀ Q ∈ S.filter fun Q => finitePOffDepth P Q = j,
        cubeVolume Q *
            (3 : ℝ) ^ (r * ((P.scale : ℝ) - (Q.scale : ℝ))) =
          (3 : ℝ) ^ (r * (j : ℝ)) * cubeVolume Q := by
      intro Q hQ
      rw [hscale Q hQ]
      push_cast
      rw [show (P.scale : ℝ) - ((P.scale : ℝ) - (j : ℝ)) = (j : ℝ) by ring]
      ring
    rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum]
    have hpack := sum_cubeVolume_maximalCubesAtDepth_le w P j
      (S.filter fun Q => finitePOffDepth P Q = j)
      (fun Q hQ => ⟨hS Q (Finset.mem_filter.mp hQ).1, hscale Q hQ⟩)
    have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (r * (j : ℝ)) := Real.rpow_nonneg (by norm_num) _
    refine (mul_le_mul_of_nonneg_left hpack hw).trans (le_of_eq ?_)
    have hzpow : (3 : ℝ) ^ (1 - (j : ℤ)) =
        3 * (3 : ℝ) ^ (-(j : ℝ)) := by
      rw [show (1 : ℤ) - (j : ℤ) = 1 + (-(j : ℤ)) by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one,
        ← Real.rpow_intCast (3 : ℝ) (-(j : ℤ))]
      push_cast
      ring
    have hrpow : ((3 : ℝ) ^ (-(1 - r))) ^ j =
        (3 : ℝ) ^ (-(1 - r) * (j : ℝ)) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 - r))) j,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [hzpow, hrpow]
    have hcombine : (3 : ℝ) ^ (r * (j : ℝ)) *
        (3 : ℝ) ^ (-(j : ℝ)) =
          (3 : ℝ) ^ (-(1 - r) * (j : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    calc
      (3 : ℝ) ^ (r * (j : ℝ)) *
          (2 * (d : ℝ) * (3 * (3 : ℝ) ^ (-(j : ℝ))) * cubeVolume P) =
        6 * (d : ℝ) * cubeVolume P *
          ((3 : ℝ) ^ (r * (j : ℝ)) * (3 : ℝ) ^ (-(j : ℝ))) := by ring
      _ = _ := by rw [hcombine]
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [← Finset.mul_sum]
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 - r)) := Real.rpow_nonneg (by norm_num) _
  have hrLt : (3 : ℝ) ^ (-(1 - r)) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hr1])
  have hgeom := geom_sum_range_le_inv_one_sub hr0 hrLt N
  have hnn : (0 : ℝ) ≤ 6 * (d : ℝ) * cubeVolume P :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) (cubeVolume_nonneg P)
  refine (mul_le_mul_of_nonneg_left hgeom hnn).trans (le_of_eq ?_)
  rw [finitePAggregationGeomFactor]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
