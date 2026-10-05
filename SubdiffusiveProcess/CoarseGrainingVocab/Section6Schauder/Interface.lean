module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Producer


-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/OneStepSchauderChain.lean

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec basisVec euclideanBall openCubeSet originCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ### The constant -/



def schauderInteriorConst (d : ℕ) [NeZero d] : ℝ := 27 * (d : ℝ) * schauderWindowConst d

theorem schauderInteriorConst_nonneg (d : ℕ) [NeZero d] : 0 ≤ schauderInteriorConst d :=
  mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) (schauderWindowConst_nonneg d)

/-! ### The three translations -/



theorem three_rpow_half_offset (n : ℤ) :
    ((3 : ℝ) ^ (-(n - 2))) ^ (1 / 2 : ℝ) = 3 * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) := by
  have hsplit : (3 : ℝ) ^ (-(n - 2)) = 9 * (3 : ℝ) ^ (-n) := by
    rw [show -(n - 2) = (2 : ℤ) + -n by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  rw [hsplit, Real.mul_rpow (by norm_num) (by positivity)]
  congr 1
  rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (3 : ℝ) 2,
    ← Real.rpow_mul (by norm_num)]
  norm_num

/-- The normalizer: on a truncated window the volume normalizer is at most `9`
times the paper's scale normalizer, so `affineExcess ≤ 9 · excess`. -/
theorem affineExcess_le_excess_truncatedCube (hd : d ≠ 0) {m j : ℤ} {x : Vec d}
    (hx : x ∈ cube d m) (hjm : j - 1 ≤ m) (v : Vec d → ℝ) :
    affineExcess (truncatedCube d m j x) v ≤ 9 * excess j (truncatedCube d m j x) v := by
  have hraw : 0 ≤ affineExcessRaw (truncatedCube d m j x) v :=
    affineExcessRaw_nonneg _ _
  have hnorm := (rpow_volume_truncatedWindow_bounds (d := d) hd x hx hjm).2
  rw [excess_eq_affineExcessScaled, affineExcess, affineExcessScaled, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hnorm hraw

/-! ### The estimate section 6 reads -/

/-- **The Schauder gradient-Hölder estimate, interior branch, in the section 6
carriers.**

For `v` harmonic on the replacement window `U_{m,n-4}(x)` of the interior branch
(`x + □_{n-4} ⊆ □_m`), the gradient field `gradField v` realizes exactly the
four slots `hint / hgrad / hhol / hschauder` of
`SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.excess_oneStep_of_schauder`, with

```text
  Csch = schauderInteriorConst d ,   K_h = 0 .
```
-/
theorem exists_gradientHolder_truncatedCube [NeZero d] (hd : d ≠ 0) {m n : ℤ} {x : Vec d}
    (hx : x ∈ cube d m) (hnm : n - 5 ≤ m)
    (hcube : translatedCube d (n - 4) x ⊆ cube d m)
    {v : Vec d → ℝ}
    (hharm : HarmonicOnNhd (v ∘ toEuc.symm)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedCube d m (n - 4) x))
    (hv : MemLp v 2 (volume.restrict (truncatedCube d m (n - 4) x))) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ i, IntegrableOn (fun p => gradField v p i) (truncatedCube d m (n - 5) x) volume) ∧
      HasGradientOn (truncatedCube d m (n - 5) x) v (gradField v) ∧
      HolderSeminormBoundOn (truncatedCube d m (n - 5) x) (1 / 2 : ℝ) K (gradField v) ∧
      K ≤ schauderInteriorConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) *
            excess (n - 4) (truncatedCube d m (n - 4) x) v + 0 := by
  have h42 : n - 2 - 2 = n - 4 := by ring
  have h53 : n - 2 - 3 = n - 5 := by ring
  
  obtain ⟨K, hK0, hint, hgrad, hhol, hbound⟩ :=
    exists_gradientHolder_interior (d := d) (m := m) (n := n - 2) (x := x) hd hx
      (by omega : n - 2 - 3 ≤ m) (by rw [h42]; exact hcube)
      (v := v) (by rw [truncatedWindow_eq, h42]; exact hharm)
      (fun c g => by
        rw [truncatedWindow_eq, h42]
        exact integrableOn_sub_affineEval_sq_truncatedCube x hv c g)
  rw [truncatedWindow_eq, h42] at hbound
  rw [truncatedWindow_eq, h53] at hint hgrad hhol
  refine ⟨(d : ℝ) * K, mul_nonneg (Nat.cast_nonneg d) hK0, hint, hgrad,
    holderSeminormBoundOn_of_supHolderBoundOn hK0 (by norm_num) hhol, ?_⟩
  -- the two remaining translations
  set W : Set (Vec d) := truncatedCube d m (n - 4) x with hW
  have hE : 0 ≤ excess (n - 4) W v := by
    rw [excess_eq_affineExcessScaled]
    exact affineExcessScaled_nonneg _ _ _
  have hC0 : 0 ≤ schauderWindowConst d := schauderWindowConst_nonneg d
  have hpow : 0 ≤ ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hnorm : affineExcess W v ≤ 9 * excess (n - 4) W v :=
    affineExcess_le_excess_truncatedCube hd hx (by omega) v
  have hstep : schauderWindowConst d * ((3 : ℝ) ^ (-(n - 2))) ^ (1 / 2 : ℝ) * affineExcess W v
      ≤ 27 * schauderWindowConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) * excess (n - 4) W v := by
    rw [three_rpow_half_offset]
    have hcoef : 0 ≤ schauderWindowConst d * (3 * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)) := by
      positivity
    calc schauderWindowConst d * (3 * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)) * affineExcess W v
        ≤ schauderWindowConst d * (3 * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ)) *
            (9 * excess (n - 4) W v) := mul_le_mul_of_nonneg_left hnorm hcoef
      _ = 27 * schauderWindowConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) * excess (n - 4) W v := by
          ring
  rw [add_zero] at hbound ⊢
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  calc (d : ℝ) * K
      ≤ (d : ℝ) * (schauderWindowConst d * ((3 : ℝ) ^ (-(n - 2))) ^ (1 / 2 : ℝ) *
          affineExcess W v) := mul_le_mul_of_nonneg_left hbound hd0
    _ ≤ (d : ℝ) * (27 * schauderWindowConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) *
          excess (n - 4) W v) := mul_le_mul_of_nonneg_left hstep hd0
    _ = schauderInteriorConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) * excess (n - 4) W v := by
        rw [schauderInteriorConst]; ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
