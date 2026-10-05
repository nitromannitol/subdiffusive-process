module

public import SubdiffusiveProcess.Analysis.HolderDilationToolkit
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry
public import Mathlib.Tactic

@[expose] public section

/-! A Holder seminorm bounds the full norm after subtracting a basepoint value.
The dimensional diameter factor is retained; no regularity of a function is asserted. -/

open Set _root_.SubdiffusiveProcess.EllipticRegularity
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- A bounded Holder quotient set controls every increment between distinct points. -/
theorem holderSeminorm_pair_bound {d : ℕ} {alpha K : ℝ}
    {S : Set (SpatialCoordinates d)} {G : SpatialCoordinates d → ℝ}
    (hH : IsHolderOn alpha S G) (hK : holderSeminorm alpha S G ≤ K)
    {x y : SpatialCoordinates d} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    |G x - G y| ≤ K * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  have hs : 0 < ∑ j : Fin d, (x j - y j) ^ 2 :=
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hi)).trans_le
      (Finset.single_le_sum (fun j _ => sq_nonneg (x j - y j)) (Finset.mem_univ i))
  have hp := Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hs) alpha
  apply (div_le_iff₀ hp).mp
  exact (le_csSup hH ⟨x, hx, y, hy, hxy, rfl⟩).trans hK

/-- Subtracting a basepoint controls the full Holder norm by its seminorm and the radius. -/
theorem cAlphaNorm_sub_base_le {d : ℕ} {alpha K R : ℝ}
    (halpha : 0 ≤ alpha) (hK0 : 0 ≤ K) (hR0 : 0 ≤ R)
    {S : Set (SpatialCoordinates d)} {G : SpatialCoordinates d → ℝ}
    {x0 : SpatialCoordinates d} (hx0 : x0 ∈ S)
    (hR : ∀ x ∈ S, Real.sqrt (∑ i : Fin d, (x i - x0 i) ^ 2) ≤ R)
    (hH : IsHolderOn alpha S G) (hK : holderSeminorm alpha S G ≤ K) :
    IsHolderOn alpha S (fun x => G x - G x0) ∧
      cAlphaNorm alpha S (fun x => G x - G x0) ≤ (R ^ alpha + 1) * K := by
  have hdiff (x y : SpatialCoordinates d) :
      (G x - G x0) - (G y - G x0) = G x - G y := by ring
  have hratio : holderRatioSet alpha S (fun x => G x - G x0) =
      holderRatioSet alpha S G := by simp only [holderRatioSet, hdiff]
  refine ⟨by simpa only [IsHolderOn, hratio] using hH, ?_⟩
  have hsup : sSup {v : ℝ | ∃ x ∈ S, v = |G x - G x0|} ≤ K * R ^ alpha := by
    apply Real.sSup_le
    · rintro v ⟨x, hx, rfl⟩
      by_cases hxx : x = x0
      · subst x
        simpa only [sub_self, abs_zero] using mul_nonneg hK0 (Real.rpow_nonneg hR0 alpha)
      · exact (holderSeminorm_pair_bound hH hK hx hx0 hxx).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Real.sqrt_nonneg _) (hR x hx) halpha) hK0)
    · exact mul_nonneg hK0 (Real.rpow_nonneg hR0 alpha)
  unfold cAlphaNorm holderSeminorm
  rw [hratio]
  dsimp only [holderSeminorm] at hK
  nlinarith only [hsup, hK]

/-- The closed unit cube has Euclidean radius at most the dimension plus one. -/
theorem unitClosed_euclidean_radius_le {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) :
    Real.sqrt (∑ i : Fin d, (x i - (0 : SpatialCoordinates d) i) ^ 2) ≤ (d : ℝ) + 1 := by
  have hnorm : ‖x‖ ≤ 1 / 2 := by
    change dist x 0 ≤ 1 / 2 at hx
    simpa only [dist_zero_right] using hx
  have h := Homogenization.euclideanNorm_le_dimension_mul_norm x
  have hb : Homogenization.euclideanNorm x ≤ (d : ℝ) + 1 := by
    have hn := Nat.cast_nonneg (α := ℝ) d
    nlinarith only [h, hnorm, hn]
  simpa only [Pi.zero_apply, sub_zero, Homogenization.euclideanNorm,
    Homogenization.vecNormSq, Homogenization.vecDot, pow_two] using hb

/-- Dilation and anchoring give the full Holder norm on the closed unit cube. -/
theorem scaled_cAlphaNorm_sub_center_le {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) {alpha K : ℝ} (halpha : 0 ≤ alpha) (hK0 : 0 ≤ K)
    (G : SpatialCoordinates d → ℝ)
    (hH : IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) G)
    (hK : holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) G ≤ K) :
    IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => G (z + r • x) - G z) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => G (z + r • x) - G z) ≤ (((d : ℝ) + 1) ^ alpha + 1) * (r ^ alpha * K) := by
  have hH' := aux_hDet_isHolderOn_dilation z r hr alpha G _ _
    (aux_hDet_mem_closedCube_dilation z r hr) hH
  have hK' : holderSeminorm alpha
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => G (cubeDilation z 0 r x)) ≤ r ^ alpha * K := by
    rw [aux_hDet_holderSeminorm_dilation z r hr alpha G _ _
      (aux_hDet_mem_closedCube_dilation z r hr)]
    exact mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg hr.le _)
  have hx0 : (0 : SpatialCoordinates d) ∈
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    exact Metric.mem_closedBall_self (by norm_num)
  have h := cAlphaNorm_sub_base_le halpha (mul_nonneg (Real.rpow_nonneg hr.le _) hK0)
    (by positivity : 0 ≤ (d : ℝ) + 1) hx0
    (fun _ hx => unitClosed_euclidean_radius_le hx) hH' hK'
  have hdil (x : SpatialCoordinates d) : cubeDilation z 0 r x = z + r • x := by
    ext i
    simp only [cubeDilation, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, sub_zero, smul_eq_mul]
  simpa only [hdil, smul_zero, add_zero] using h

end SubdiffusiveProcess
